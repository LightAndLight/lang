{-# language DeriveFunctor #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language ScopedTypeVariables #-}
module Elaborate where

import Biscope (fromBiscopeL, toBiscopeL, fromBiscopeR, toBiscopeR)
import Bound.Scope.Simple (fromScope, toScope, instantiate1)
import Bound.Var (Var(..), unvar)
import Control.Applicative ((<|>))
import Control.Monad (unless, when)
import Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (MonadReader, ReaderT, runReaderT, asks, withReaderT)
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.Bifunctor (bimap)
import Data.DList (DList)
import Data.Foldable (traverse_)
import Data.Maybe (fromJust, fromMaybe)
import Data.Map (Map)
import Data.Text (Text)
import Data.Traversable (for)

import qualified Data.DList as DList
import qualified Data.Map as Map

import Core (Core)
import qualified Core
import qualified Core.Type as Core
import Operators (Op(..))
import Rep (Rep(..))
import Syntax (Syntax)
import qualified Syntax
import qualified Syntax.Type as Syntax

data Warning
  = WOverflow Integer (Core.Type Text)
  deriving Show

data TypeError
  = TypeNotInScope Text
  | VarNotInScope Text
  | ExpectedKPi (Core.Type Text)
  | ExpectedKForall (Core.Type Text)
  | ExpectedKType (Core.Type Text)
  | ExpectedKType0 (Core.Type Text)
  | ExpectedKTypeN (Core.Type Text)
  | KindMismatch (Core.Type Text) (Core.Type Text)
  | KindEscaped Text (Core.Type Text)
  | Can'tInferKind (Core.Type Text)
  | NotSubkindOf (Core.Type Text) (Core.Type Text)
  | TypeMismatch (Core.Type Text) (Core.Type Text)
  | NaturalIsNot (Core.Type Text)
  | ExpectedArrow (Core.Type Text)
  | LamIsNot (Core.Type Text)
  | AbsTypeIsNot (Core.Type Text)
  | ExpectedForall (Core.Type Text)
  | Can'tInferType (Syntax Text Text)
  | DuplicateDefinition Text
  | SigMissingBody Text
  | DefMissingSig Text
  deriving Show

data ElabEnv ty tm
  = ElabEnv
  { eKinds :: ty -> Maybe (Core.Type ty)
  , eTypeNames :: ty -> Text
  , eTypes :: tm -> Maybe (Core.Type ty)
  , eVarNames :: tm -> Text
  }

newElabEnv :: (ty -> Text) -> (tm -> Text) -> ElabEnv ty tm
newElabEnv tys tms =
  ElabEnv
  { eKinds = const Nothing
  , eTypeNames = tys
  , eTypes = const Nothing
  , eVarNames = tms
  }

addTy ::
  Core.Type ty -> -- kind
  Maybe Text -> -- optional name
  ElabEnv ty tm ->
  ElabEnv (Var () ty) tm
addTy k mn e =
  e
  { eKinds = (fmap.fmap) F . unvar (\() -> Just k) (eKinds e)
  , eTypeNames = unvar (\() -> unnamed mn) (eTypeNames e)
  , eTypes = (fmap.fmap) F . eTypes e
  }

addVar ::
  Core.Type ty -> -- type
  Maybe Text -> -- optional name
  ElabEnv ty tm ->
  ElabEnv ty (Var () tm)
addVar t mn e =
  e
  { eTypes = unvar (\() -> Just t) (eTypes e)
  , eVarNames = unvar (\() -> unnamed mn) (eVarNames e)
  }

newtype Elab ty tm a
  = Elab
  { unElab ::
      ReaderT (ElabEnv ty tm)
      (ExceptT TypeError (Writer (DList Warning))) a
  } deriving
  ( Functor, Applicative, Monad
  , MonadError TypeError, MonadReader (ElabEnv ty tm)
  , MonadFix
  )

data ElabResult a
  = ElabResult
  { eWarnings :: [Warning]
  , eResult :: Either TypeError a
  } deriving (Show, Functor)

elab :: ElabEnv ty tm -> Elab ty tm a -> ElabResult a
elab e m = ElabResult (DList.toList ws) a
  where
    (a, ws) = runWriter $ runExceptT (runReaderT (unElab m) e)

mapElabEnv ::
  (ElabEnv tm' ty' -> ElabEnv tm ty) ->
  Elab tm ty a ->
  Elab tm' ty' a
mapElabEnv f = Elab . withReaderT f . unElab

unnamed :: Maybe Text -> Text
unnamed = fromMaybe "<unnamed>"

warn :: Warning -> Elab ty tm ()
warn = Elab . tell . DList.singleton

lookupKind :: ty -> Elab ty tm (Core.Type ty)
lookupKind t = do
  res <- asks eKinds
  case res t of
    Nothing -> do
      tyNames <- Elab $ asks eTypeNames
      throwError $ TypeNotInScope (tyNames t)
    Just k -> pure k

lookupType :: tm -> Elab ty tm (Core.Type ty)
lookupType t = do
  res <- asks eTypes
  case res t of
    Nothing -> do
      varNames <- Elab $ asks eVarNames
      throwError $ VarNotInScope (varNames t)
    Just k -> pure k

subkindOf :: Eq ty => Core.Kind ty -> Core.Kind ty -> Bool
subkindOf (Core.TKType n a) (Core.TKType n' b) =
  Core.eqType a b && n <= n'
subkindOf (Core.TKPi _ _ s t) (Core.TKPi _ _ s' t') =
  Core.eqType s s' &&
  subkindOf (fromScope t) (fromScope t')
subkindOf k1 k2 = Core.eqType k1 k2

checkKind ::
  Eq ty =>
  Syntax.Type ty ->
  Core.Kind ty ->
  Elab ty tm (Core.Type ty)
checkKind ty ki = do
  (ty', tKind) <- inferKind ty
  unless (tKind `subkindOf` ki) $ do
    typeNames <- asks eTypeNames
    throwError $
      KindMismatch
        (typeNames <$> ki)
        (typeNames <$> tKind)
  pure ty'

inferKind ::
  Eq ty =>
  Syntax.Type ty ->
  Elab ty tm (Core.Type ty, Core.Kind ty)
inferKind ty =
  case ty of
    Syntax.TVar a -> do
      k <- lookupKind a
      pure (Core.TVar a, k)
    Syntax.TForall mn k a -> do
      k' <- checkKind k $ Core.TKType 1 (Core.TRep RPtr)
      (a', aKind) <- mapElabEnv (addTy k' mn) (inferKind $ fromScope a)
      aKind' <-
        for aKind $
        \case
          B () -> do
            typeNames <- asks eTypeNames
            throwError $ KindEscaped (unnamed mn) (typeNames <$> k')
          F x -> pure x
      pure (Core.TForall aKind' mn k' $ toScope a', aKind')
    Syntax.TApp a b -> do
      (a', aKind) <- inferKind a
      case aKind of
        Core.TKPi _ _ s t -> do
          b' <- checkKind b s
          let k = instantiate1 b' t
          pure (Core.TApp k a' b', k)
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedKPi (typeNames <$> aKind)
    Syntax.TUInt64 ->
      pure (Core.TUInt64, Core.TKType 0 $ Core.TRep RI64)
    Syntax.TArr -> do
      let
        t = Core.TKType 1 (Core.TRep RPtr)
        k =
          Core.TKPi t (Just "r1") Core.TKRep . toScope $
          Core.TKPi t (Just "r2") Core.TKRep . toScope $
          Core.TKPi t Nothing (Core.TKType 0 . Core.TVar $ F$B()) . toScope $
          Core.TKPi t Nothing (Core.TKType 0 . Core.TVar $ F$B()) . toScope $
          Core.TKType 0 (Core.TRep RPtr)
      pure (Core.TArr, k)
    Syntax.TRep r ->
      pure (Core.TRep r, Core.TKRep)
    Syntax.TKRep ->
      pure (Core.TKRep, Core.TKType 0 $ Core.TRep RPtr)
    Syntax.TKType n t -> do
      t' <- checkKind t Core.TKRep
      pure (Core.TKType n t', Core.TKType (n+1) $ Core.TRep RPtr)
    Syntax.TKPi mn s t -> do
      (s', sKind) <- inferKind s
      sn <-
        case sKind of
          Core.TKType n _ -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (typeNames <$> sKind)
      (t', tKind) <- mapElabEnv (addTy s' mn) $ inferKind (fromScope t)
      tn <-
        case tKind of
          Core.TKType n _ -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (typeNames <$> sKind)
      let k = Core.TKType (max sn tn + 1) (Core.TRep RPtr)
      pure
        ( Core.TKPi k mn s' $ toScope t'
        , k
        )

check :: Eq ty => Syntax ty tm -> Core.Type ty -> Elab ty tm (Core ty tm)
check tm ty = do
  case tm of
    Syntax.Natural n -> do
      typeNames <- asks eTypeNames
      case ty of
        Core.TUInt64{} -> do
          unless (n < 2^(64::Integer)) . warn $ WOverflow n (typeNames <$> ty)
          pure $ Core.UInt64 (fromIntegral n)
        _ -> throwError $ NaturalIsNot (typeNames <$> ty)
    Syntax.Lam mn a -> do
      case ty of
        Core.TApp _ (Core.TApp _ (Core.TApp _ (Core.TApp _ Core.TArr{} r1) r2) s) t -> do
          a' <- mapElabEnv (addVar s mn) $ check (fromBiscopeR a) t
          pure (Core.Lam (Core.LamInfo r1 r2 s t) mn s $ toBiscopeR a')
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ LamIsNot (typeNames <$> ty)
    Syntax.AbsType mn k rest ->
      case ty of
        Core.TForall _ _ k' restTy -> do
          k2 <- checkKind k $ Core.TKType 1 (Core.TRep RPtr)
          unless (k2 `Core.eqType` k') $ do
            typeNames <- asks eTypeNames
            throwError $ KindMismatch (typeNames <$> k') (typeNames <$> k2)
          rest' <- mapElabEnv (addTy k2 mn) $ check (fromBiscopeL rest) (fromScope restTy)
          pure $ Core.AbsType mn k2 (toBiscopeL rest')
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ AbsTypeIsNot (typeNames <$> ty)
    _ -> do
      (tm', ty') <- infer tm
      unless (ty == ty') $ do
        typeNames <- asks eTypeNames
        throwError $ TypeMismatch (typeNames <$> ty) (typeNames <$> ty')
      pure tm'

infer :: Eq ty => Syntax ty tm -> Elab ty tm (Core ty tm, Core.Type ty)
infer tm =
  case tm of
    Syntax.Var a -> (,) (Core.Var a) <$> lookupType a
    Syntax.Bin op a b ->
      case op of
        Mult -> do
          a' <- check a Core.TUInt64
          b' <- check b Core.TUInt64
          pure (Core.Bin op a' b', Core.TUInt64)
        Add -> do
          a' <- check a Core.TUInt64
          b' <- check b Core.TUInt64
          pure (Core.Bin op a' b', Core.TUInt64)
    Syntax.App a b -> do
      (a', aType) <- infer a
      case aType of
        Core.TApp _ (Core.TApp _ (Core.TApp _ (Core.TApp _ Core.TArr{} r1) r2) s) t -> do
          b' <- check b s
          pure (Core.App (Core.AppInfo r1 r2) a' b', t)
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedArrow (typeNames <$> aType)
    Syntax.AppType a t -> do
      (a', aType) <- infer a
      case aType of
        Core.TForall _ _ k rest -> do
          t' <- checkKind t k
          pure (Core.AppType a' t', instantiate1 t' rest)
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedForall (typeNames <$> aType)
    Syntax.AbsType mn k a -> do
      k' <- checkKind k $ Core.TKType 1 (Core.TRep RPtr)
      (a', aTy) <- mapElabEnv (addTy k' mn) $ infer (fromBiscopeL a)
      resKind <-
        traverse
          (unvar
             (\() -> do
                 typeNames <- asks eTypeNames
                 throwError $ KindEscaped (unnamed mn) (typeNames <$> k'))
             pure)
          (Core.getKind Core.TVar aTy)
      pure (Core.AbsType mn k' $ toBiscopeL a', Core.TForall resKind mn k' $ toScope aTy)
    _ -> do
      varNames <- asks eVarNames
      typeNames <- asks eTypeNames
      throwError $ Can'tInferType (bimap typeNames varNames tm)

checkDefsThen ::
  forall ty tm a.
  (Eq ty, Ord tm) =>
  (tm -> Text) ->
  [Syntax.Def ty tm] ->
  Elab ty tm a ->
  Elab ty tm ([Core.Def ty tm], a)
checkDefsThen name defs ma = do
  (paired, loneDefs, loneSigs) <- zipDefs mempty mempty mempty defs

  traverse_ (throwError . DefMissingSig . name) loneDefs
  traverse_ (throwError . SigMissingBody . name) loneSigs

  paired' <-
    traverse
      (\(v, t) -> (,) v <$> checkKind t (Core.TKType 0 $ Core.TRep RPtr))
      paired

  types <- asks eTypes
  let types' n = fmap snd (Map.lookup n paired') <|> types n

  (defs', a) <-
    mapElabEnv (\e -> e { eTypes = types' }) $
    (,) <$> traverse (uncurry check) paired' <*> ma


  pure (Map.foldrWithKey (\n v -> (Core.Def n v (fromJust $ types' n) :)) [] defs', a)
  where
    zipDefs ::
      Ord tm =>
      Map tm (Syntax ty tm, Syntax.Type ty) -> -- paired
      Map tm (Syntax ty tm) -> -- unpaired
      Map tm (Syntax.Type ty) -> -- unpaired
      [Syntax.Def ty tm] ->
      Elab ty tm
        ( Map tm (Syntax ty tm, Syntax.Type ty)
        , [tm]
        , [tm]
        )
    zipDefs paired loneDefs loneSigs [] =
      pure
        ( paired
        , Map.keys loneDefs
        , Map.keys loneSigs
        )
    zipDefs paired loneDefs loneSigs (d:ds) =
      case d of
        Syntax.Def n v -> do
          checkNotPaired n paired
          when (Map.member n loneDefs) . throwError $ DuplicateDefinition (name n)
          case Map.lookup n loneSigs of
            Nothing ->
              zipDefs paired (Map.insert n v loneDefs) loneSigs ds
            Just sig ->
              zipDefs (Map.insert n (v, sig) paired) loneDefs (Map.delete n loneSigs) ds
        Syntax.Sig n t -> do
          checkNotPaired n paired
          when (Map.member n loneSigs) . throwError $ DuplicateDefinition (name n)
          case Map.lookup n loneDefs of
            Nothing ->
              zipDefs paired loneDefs (Map.insert n t loneSigs) ds
            Just def ->
              zipDefs (Map.insert n (def, t) paired) (Map.delete n loneDefs) loneSigs ds

    checkNotPaired :: Ord tm => tm -> Map tm x -> Elab ty tm ()
    checkNotPaired n mp =
      when (Map.member n mp) . throwError $ DuplicateDefinition (name n)
