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
import Data.Maybe (fromMaybe)
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
subkindOf (Core.TApp _ (Core.TKType _ n) a) (Core.TApp _ (Core.TKType _ n') b) =
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
      aKind <- mapElabEnv (addTy k mn) (inferKind $ fromScope a)
      for aKind $
        \case
          B () -> do
            typeNames <- asks eTypeNames
            throwError $ KindEscaped (unnamed mn) (typeNames <$> k)
          F x -> pure x
    Syntax.TApp a b -> do
      aKind <- inferKind a
      case aKind of
        Syntax.TKPi _ s t -> instantiate1 b t <$ checkKind b s
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedKPi (typeNames <$> aKind)
    Syntax.TUInt64 -> pure $ Core.TApp (Core.TKType 0) (Core.TRep RI64)
    Syntax.TArr ->
      pure $
      Core.TKPi (Just "r1") Core.TKRep . toScope $
      Core.TKPi (Just "r2") Core.TKRep . toScope $
      Core.TKPi Nothing (Core.TApp (Core.TKType 0) . Core.TVar $ F$B()) . toScope $
      Core.TKPi Nothing (Core.TApp (Core.TKType 0) . Core.TVar $ F$B()) . toScope $
      Core.TApp (Core.TKType 0) (Core.TRep RPtr)
    Syntax.TRep{} -> pure Core.TKRep
    Syntax.TKRep -> pure $ Core.TApp (Core.TKType 0) (Core.TRep RPtr)
    Syntax.TKType n ->
      pure $
      Core.TKPi Nothing Core.TKRep . toScope $
      Core.TKType (n+1)
    Syntax.TKPi mn s t -> do
      sKind <- inferKind s
      sn <-
        case sKind of
          Syntax.TApp (Syntax.TKType n) _ -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (typeNames <$> sKind)
      tKind <- mapElabEnv (addTy s mn) $ inferKind (fromScope t)
      tn <-
        case tKind of
          Syntax.TApp (Syntax.TKType n) _ -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (typeNames <$> sKind)
      pure $ Core.TApp (Core.TKType $ max sn tn + 1) (Core.TRep RPtr)

check :: Eq ty => Syntax ty tm -> Syntax.Type ty -> Elab ty tm (Core ty tm)
check tm ty =
  case tm of
    Syntax.Natural n ->
      case ty of
        Syntax.TUInt64 -> do
          unless (n < 2^(64::Integer)) . warn $ WOverflow n TUInt64
          pure $ Core.UInt64 ty (fromIntegral n)
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ NaturalIsNot (typeNames <$> ty)
    Syntax.Lam mn a ->
      case ty of
        Syntax.TApp (Syntax.TApp (Syntax.TApp (Syntax.TApp Syntax.TArr r1) r2) s) t -> do
          a' <- mapElabEnv (addVar s mn) $ check (fromBiscopeR a) t
          pure (Core.Lam ty mn s r1 r2 $ toBiscopeR a')
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ LamIsNot (typeNames <$> ty)
    Syntax.AbsType mn k rest ->
      case ty of
        Syntax.TForall _ k' restTy -> do
          unless (k == k') $ do
            typeNames <- asks eTypeNames
            throwError $ KindMismatch (typeNames <$> k') (typeNames <$> k)
          rest' <- mapElabEnv (addTy k mn) $ check (fromBiscopeL rest) (fromScope restTy)
          pure $ Core.AbsType ty mn k (toBiscopeL rest')
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
          a' <- check a TUInt64
          b' <- check b TUInt64
          let ty = TUInt64
          pure (Core.Bin ty op a' b', ty)
        Add -> do
          a' <- check a TUInt64
          b' <- check b TUInt64
          let ty = TUInt64
          pure (Core.Bin ty op a' b', ty)
    Syntax.App a b -> do
      (a', aType) <- infer a
      case aType of
        Syntax.TApp (Syntax.TApp (Syntax.TApp (Syntax.TApp Syntax.TArr r1) r2) s) t -> do
          b' <- check b s
          pure (Core.App t a' b' r1 r2, t)
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedArrow (typeNames <$> aType)
    Syntax.AppType a t -> do
      (a', aType) <- infer a
      case aType of
        Core.TForall _ k rest -> do
          checkKind t k
          let ty = instantiate1 t rest
          pure (Core.AppType ty a' t, ty)
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedForall (typeNames <$> aType)
    Syntax.AbsType mn k a -> do
      (a', aTy) <- mapElabEnv (addTy k mn) $ infer (fromBiscopeL a)
      let ty = TForall mn k $ toScope aTy
      pure (Core.AbsType ty mn k $ toBiscopeL a', ty)
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

  tys <- traverse (\(_, t) -> t <$ checkKind t (TApp (TKType 0) (TRep RPtr))) paired

  (defs', a) <-
    mapElabEnv (\e -> e { eTypes = \n -> Map.lookup n tys <|> eTypes e n }) $
    (,) <$> traverse (uncurry check) paired <*> ma

  pure (Map.foldrWithKey (\n v -> (Core.Def n v :)) [] defs', a)
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
