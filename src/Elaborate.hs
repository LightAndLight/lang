{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Elaborate where

import Biscope (fromBiscopeL, toBiscopeL, fromBiscopeR, toBiscopeR)
import Bound.Scope.Simple (fromScope, toScope, instantiate1)
import Bound.Var (Var(..), unvar)
import Control.Applicative ((<|>))
import Control.Lens.Setter ((.=), (%=), over)
import Control.Lens.TH (makeLenses)
import Control.Monad (unless, when)
import Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError)
import Control.Monad.Fix (MonadFix)
import Control.Monad.Reader (MonadReader, ReaderT, runReaderT, asks)
import Control.Monad.State (MonadState, StateT, evalStateT, runStateT, gets, put)
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.Bifunctor (bimap)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.DList (DList)
import Data.Foldable (traverse_)
import Data.Functor.Classes (Eq1, Show1, eq1, showsPrec1)
import Data.Functor.Compose (Compose(..))
import Data.Maybe (fromJust, fromMaybe)
import Data.Map (Map)
import Data.Text (Text)
import Data.Traversable (for)
import Data.Validation (Validation(..), toEither)
import Data.Witherable (mapMaybe)

import qualified Data.DList as DList
import qualified Data.Map as Map
import qualified Data.Text as Text

import Core (Core)
import qualified Core
import qualified Core.Type as Core
import Operators (Op(..))
import Rep (Rep(..))
import Syntax (Syntax)
import qualified Syntax
import qualified Syntax.Type as Syntax

newtype Solving f a = Solving { unSolving :: f (Either Int a) }
  deriving (Functor, Foldable, Traversable)
deriveEq1 ''Solving
deriveShow1 ''Solving
instance (Eq1 f, Eq a) => Eq (Solving f a) where; (==) = eq1
instance (Show1 f, Show a) => Show (Solving f a) where; showsPrec = showsPrec1
instance Applicative f => Applicative (Solving f) where
  pure = Solving . pure . pure
  Solving mf <*> Solving ma = Solving $ (<*>) <$> mf <*> ma
instance Monad f => Monad (Solving f) where
  Solving ma >>= f =
    Solving $ do
      a <- ma
      case a of
        Left e -> pure $ Left e
        Right x -> unSolving $ f x
instance MonadTrans Solving where
  lift = Solving . fmap Right

type Solved f = f

metaName :: Int -> Text
metaName = Text.pack . ('?' :) . show

data Warning
  = WOverflow Integer (Solving Core.Type Text)
  deriving Show

data TypeError
  = TypeNotInScope Text
  | VarNotInScope Text
  | ExpectedKPi (Solving Core.Kind Text)
  | ExpectedKForall (Solving Core.Kind Text)
  | ExpectedKRep (Solving Core.Kind Text)
  | ExpectedKType (Solving Core.Kind Text)
  | ExpectedKType0 (Solving Core.Kind Text)
  | ExpectedKTypeN (Solving Core.Kind Text)
  | KindMismatch (Solving Core.Type Text) (Solving Core.Type Text)
  | KindEscaped Text (Solving Core.Kind Text)
  | Can'tInferKind (Core.Type Text)
  | NotSubkindOf (Core.Type Text) (Core.Type Text)
  | TypeMismatch (Solving Core.Type Text) (Solving Core.Type Text)
  | NaturalIsNot (Solving Core.Type Text)
  | ExpectedArrow (Solving Core.Type Text)
  | LamIsNot (Solving Core.Type Text)
  | AbsTypeIsNot (Solving Core.Type Text)
  | ExpectedForall (Solving Core.Type Text)
  | Can'tInferType (Syntax Text Text)
  | DuplicateDefinition Text
  | SigMissingBody Text
  | DefMissingSig Text
  | AbstractRepKind Text
  | Can'tInferHoleKind
  deriving Show

data ElabEnv ty tm
  = ElabEnv
  { eKinds :: ty -> Maybe (Solving Core.Kind ty)
  , eTypeNames :: ty -> Text
  , eTypes :: tm -> Maybe (Solving Core.Type ty)
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

unnamed :: Maybe Text -> Text
unnamed = fromMaybe "<unnamed>"

addTy ::
  Solving Core.Kind ty -> -- kind
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
  Solving Core.Type ty -> -- type
  Maybe Text -> -- optional name
  ElabEnv ty tm ->
  ElabEnv ty (Var () tm)
addVar t mn e =
  e
  { eTypes = unvar (\() -> Just t) (eTypes e)
  , eVarNames = unvar (\() -> unnamed mn) (eVarNames e)
  }

data Constraint ty
  = LEQ (Solving Core.Type ty) (Solving Core.Type ty)
  | EQ (Solving Core.Type ty) (Solving Core.Type ty)
  deriving (Eq, Show, Functor, Foldable, Traversable)

data ElabState ty
  = ElabState
  { _eCounter :: Int
  , _eMetaKinds :: Map Int (Solving Core.Kind ty)
  , _eConstraints :: [Constraint ty]
  } deriving (Eq, Show, Functor, Foldable, Traversable)
makeLenses ''ElabState

freshTyVar :: Elab ty tm Int
freshTyVar = Elab $ do
  n <- gets _eCounter
  n <$ (eCounter .= n+1)

newtype Elab ty tm a
  = Elab
  { unElab ::
      ReaderT (ElabEnv ty tm)
        (StateT (ElabState ty)
           (ExceptT TypeError
              (Writer (DList Warning))))
      a
  } deriving
  ( Functor, Applicative, Monad
  , MonadError TypeError
  , MonadReader (ElabEnv ty tm)
  , MonadState (ElabState ty)
  , MonadFix
  )

data ElabResult a
  = ElabResult
  { eWarnings :: [Warning]
  , eResult :: Either TypeError a
  } deriving (Show, Functor)

elab :: ElabEnv ty tm -> ElabState ty -> Elab ty tm a -> ElabResult a
elab e s m = ElabResult (DList.toList ws) a
  where
    (a, ws) =
      runWriter .
      runExceptT .
      flip evalStateT s .
      flip runReaderT e $
      unElab m

mapElab ::
  (ElabEnv ty' tm' -> ElabEnv ty tm) ->
  (ElabState ty' -> ElabState ty) ->
  (ElabState ty -> ElabState ty') ->
  Elab ty tm a ->
  Elab ty' tm' a
mapElab f g h (Elab m) =
  Elab $ do
    env <- asks f
    st <- gets g
    (res, st') <- lift . lift $ runStateT (runReaderT m env) st
    res <$ put (h st')

warn :: Warning -> Elab ty tm ()
warn = Elab . tell . DList.singleton

lookupMetaKind :: Int -> Elab ty tm (Solving Core.Kind ty)
lookupMetaKind t = do
  res <- gets _eMetaKinds
  case Map.lookup t res of
    Nothing -> throwError $ TypeNotInScope (metaName t)
    Just k -> pure k

lookupKind :: ty -> Elab ty tm (Solving Core.Kind ty)
lookupKind t = do
  res <- asks eKinds
  case res t of
    Nothing -> do
      tyNames <- Elab $ asks eTypeNames
      throwError $ TypeNotInScope (tyNames t)
    Just k -> pure k

lookupType :: tm -> Elab ty tm (Solving Core.Type ty)
lookupType t = do
  res <- asks eTypes
  case res t of
    Nothing -> do
      varNames <- Elab $ asks eVarNames
      throwError $ VarNotInScope (varNames t)
    Just k -> pure k

subkindOf ::
  Eq ty =>
  Solving Core.Kind ty ->
  Solving Core.Kind ty ->
  Elab ty tm ()
subkindOf k1 k2 =
  case (unSolving k1, unSolving k2) of
    (Core.TVar v, k2') -> _
    (k1', Core.TVar v) -> _
    (Core.TKType n a, Core.TKType n' b) ->
      unless (Core.eqType a b && n <= n') . throwError $ _
    (Core.TKPi _ s t, Core.TKPi _ s' t') -> do
      unless (Core.eqType s s') . throwError $ _
      subkindOf
        (Solving $ sequence <$> fromScope t)
        (Solving $ sequence <$> fromScope t')
    (Core.TApp a b, Core.TApp a' b') -> _
    (Core.TUInt64, Core.TUInt64) -> pure ()
    (Core.TArr, Core.TArr) -> pure ()
    (Core.TRep a, Core.TRep b) -> unless (a == b) . throwError $ _
    (Core.TForall _ a b, Core.TForall _ a' b') -> _
    (Core.TKRep, Core.TKRep) -> pure ()
    (_, _) -> throwError _
    -- (k1', k2') -> Core.eqType k1' k2'

unescapeKind ::
  Text ->
  Solving Core.Kind ty ->
  Solving Core.Kind (Var () ty) ->
  Elab ty tm (Solving Core.Kind ty)
unescapeKind n k' =
  traverse $
  \case
    B () -> do
      typeNames <- asks eTypeNames
      throwError $ KindEscaped n (typeNames <$> k')
    F x -> pure x

deleteBoundKindMetas :: ElabState (Var () ty) -> ElabState ty
deleteBoundKindMetas es =
  es
  { _eMetaKinds =
    mapMaybe
      (traverse $ unvar (\() -> Nothing) Just)
      (_eMetaKinds es)
  , _eConstraints = _
  }

inferKind ::
  Eq ty =>
  Syntax.Type ty ->
  Elab ty tm (Solving Core.Type ty, Solving Core.Kind ty)
inferKind ty =
  case ty of
    Syntax.THole -> throwError Can'tInferHoleKind
    Syntax.TVar a -> do
      k <- lookupKind a
      pure (lift $ Core.TVar a, k)
    Syntax.TForall mn k a -> do
      k' <- checkKind k $ Solving (Core.TKType 1 $ Core.TRep RPtr)
      (Solving a', aKind) <-
        mapElab
          (addTy k' mn)
          (F <$>)
          deleteBoundKindMetas
          (inferKind $ fromScope a)
      aKind' <- unescapeKind (unnamed mn) k' aKind
      pure
        ( Solving .
          Core.TForall mn (unSolving k') $
          toScope (sequence <$> a')
        , aKind'
        )
    Syntax.TApp a b -> do
      (Solving a', aKind) <- inferKind a
      case unSolving aKind of
        Core.TKPi _ s t -> do
          Solving b' <- checkKind b $ Solving s
          pure (Solving $ Core.TApp a' b', Solving $ instantiate1 b' t)
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedKPi (typeNames <$> aKind)
    Syntax.TUInt64 ->
      pure
        ( Solving Core.TUInt64
        , Solving . Core.TKType 0 $ Core.TRep RI64
        )
    Syntax.TArr -> do
      let
        k =
          Solving .
          Core.TKPi (Just "r1") Core.TKRep . toScope $
          Core.TKPi (Just "r2") Core.TKRep . toScope $
          Core.TKPi Nothing (Core.TKType 0 . Core.TVar $ F$B()) . toScope $
          Core.TKPi Nothing (Core.TKType 0 . Core.TVar $ F$B()) . toScope $
          Core.TKType 0 (Core.TRep RPtr)
      pure (Solving Core.TArr, k)
    Syntax.TRep r ->
      pure (Solving $ Core.TRep r, Solving Core.TKRep)
    Syntax.TKRep ->
      pure (Solving Core.TKRep, Solving . Core.TKType 0 $ Core.TRep RPtr)
    Syntax.TKType n t -> do
      Solving t' <- checkKind t $ Solving Core.TKRep
      pure
        ( Solving $ Core.TKType n t'
        , Solving . Core.TKType (n+1) $ Core.TRep RPtr
        )
    Syntax.TKPi mn s t -> do
      (s', sKind) <- inferKind s
      sn <-
        case unSolving sKind of
          Core.TKType n _ -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (typeNames <$> sKind)
      (Solving t', tKind) <-
        mapElab
          (addTy s' mn)
          (F <$>)
          deleteBoundKindMetas
          (inferKind $ fromScope t)
      tn <-
        case unSolving tKind of
          Core.TKType n _ -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (typeNames <$> sKind)
      pure
        ( Solving $ Core.TKPi mn (unSolving s') $ toScope (sequence <$> t')
        , Solving $ Core.TKType (max sn tn + 1) (Core.TRep RPtr)
        )

getRep :: Solving Core.Kind ty -> Elab ty tm Rep
getRep r2 =
  case unSolving r2 of
    Core.TRep r -> pure r
    Core.TVar v  -> do
      typeNames <- asks eTypeNames
      throwError $ AbstractRepKind (either metaName typeNames v)
    _  -> do
      typeNames <- asks eTypeNames
      throwError $ ExpectedKRep (typeNames <$> r2)

check ::
  Eq ty =>
  Syntax ty tm ->
  Solving Core.Type ty ->
  Elab ty tm (Core (Solving Core.Type) ty tm)
check tm ty =
  case tm of
    Syntax.Natural n -> do
      typeNames <- asks eTypeNames
      case unSolving ty of
        Core.TUInt64{} -> do
          unless (n < 2^(64::Integer)) . warn $ WOverflow n (typeNames <$> ty)
          pure $ Core.UInt64 (fromIntegral n)
        _ -> throwError $ NaturalIsNot (typeNames <$> ty)
    Syntax.Lam mn a ->
      case unSolving ty of
        Core.TApp (Core.TApp (Core.TApp (Core.TApp Core.TArr{} r1) r2) s) t -> do
          a' <- mapElab (addVar (Solving s) mn) id id $ check (fromBiscopeR a) (Solving t)
          r1' <- getRep $ Solving r1
          r2' <- getRep $ Solving r2
          pure (Core.Lam (Core.LamInfo r1' r2') mn (Solving s) $ toBiscopeR a')
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ LamIsNot (typeNames <$> ty)
    Syntax.AbsType mn k rest ->
      case unSolving ty of
        Core.TForall _ k' restTy -> do
          k2 <- checkKind k $ Solving (Core.TKType 1 $ Core.TRep RPtr)
          unless (unSolving k2 `Core.eqType` k') $ do
            typeNames <- asks eTypeNames
            throwError $
              KindMismatch (typeNames <$> Solving k') (typeNames <$> k2)
          rest' <-
            mapElab
              (addTy k2 mn)
              (F <$>)
              deleteBoundKindMetas
              (check (fromBiscopeL rest) (Solving $ sequence <$> fromScope restTy))
          pure $
            Core.AbsType mn
              k2
              (toBiscopeL rest')
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ AbsTypeIsNot (typeNames <$> ty)
    _ -> do
      (tm', ty') <- infer tm
      unless (ty == ty') $ do
        typeNames <- asks eTypeNames
        throwError $ TypeMismatch (typeNames <$> ty) (typeNames <$> ty')
      pure tm'

infer ::
  Eq ty =>
  Syntax ty tm ->
  Elab ty tm (Core (Solving Core.Type) ty tm, Solving Core.Type ty)
infer tm =
  case tm of
    Syntax.Var a -> (,) (Core.Var a) <$> lookupType a
    Syntax.Bin op a b ->
      case op of
        Mult -> do
          a' <- check a $ Solving Core.TUInt64
          b' <- check b $ Solving Core.TUInt64
          pure (Core.Bin op a' b', Solving Core.TUInt64)
        Add -> do
          a' <- check a $ Solving Core.TUInt64
          b' <- check b $ Solving Core.TUInt64
          pure (Core.Bin op a' b', Solving Core.TUInt64)
    Syntax.App a b -> do
      (a', aType) <- infer a
      case unSolving aType of
        Core.TApp (Core.TApp (Core.TApp (Core.TApp Core.TArr{} r1) r2) s) t -> do
          b' <- check b $ Solving s
          r1' <- getRep $ Solving r1
          r2' <- getRep $ Solving r2
          pure (Core.App (Core.AppInfo r1' r2') a' b', Solving t)
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedArrow (typeNames <$> aType)
    Syntax.AppType a t -> do
      (a', aType) <- infer a
      case unSolving aType of
        Core.TForall _ k rest -> do
          t' <- checkKind t $ Solving k
          pure
            ( Core.AppType a' t'
            , Solving $ instantiate1 (unSolving t') rest
            )
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedForall (typeNames <$> aType)
    Syntax.AbsType mn k a -> do
      k' <- checkKind k $ Solving (Core.TKType 1 $ Core.TRep RPtr)
      (a', Solving aTy) <-
        mapElab
          (addTy k' mn)
          (F <$>)
          deleteBoundKindMetas
          (infer $ fromBiscopeL a)
      pure
        ( Core.AbsType mn k' $ toBiscopeL a'
        , Solving .
          Core.TForall mn (unSolving k') $
          toScope (sequence <$> aTy)
        )
    _ -> do
      varNames <- asks eVarNames
      typeNames <- asks eTypeNames
      throwError $ Can'tInferType (bimap typeNames varNames tm)

checkKind ::
  Eq ty =>
  Syntax.Type ty ->
  Solving Core.Kind ty ->
  Elab ty tm (Solving Core.Type ty)
checkKind ty ki =
  case ty of
    Syntax.THole -> do
      v <- freshTyVar
      eMetaKinds %= Map.insert v ki
      pure . Solving $ Core.TVar (Left v)
    _ -> do
      (ty', tKind) <- inferKind ty
      unless (tKind `subkindOf` ki) $ do
        typeNames <- asks eTypeNames
        throwError $
          KindMismatch
            (typeNames <$> ki)
            (typeNames <$> tKind)
      pure ty'

checkDefsThen ::
  forall ty tm a.
  (Eq ty, Ord tm) =>
  (tm -> Text) ->
  [Syntax.Def ty tm] ->
  Elab ty tm a ->
  Elab ty tm ([Core.Def (Solving Core.Type) ty tm], a)
checkDefsThen name defs ma = do
  (paired, loneDefs, loneSigs) <- zipDefs mempty mempty mempty defs

  traverse_ (throwError . DefMissingSig . name) loneDefs
  traverse_ (throwError . SigMissingBody . name) loneSigs

  paired' <-
    traverse
      (\(v, t) ->
         (,) v <$>
         checkKind t (Solving . Core.TKType 0 $ Core.TRep RPtr))
      paired

  types <- asks eTypes
  let types' n = fmap snd (Map.lookup n paired') <|> types n

  (defs', a) <-
    mapElab (\e -> e { eTypes = types' }) id id $
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

zonkType ::
  Solving Core.Type ty ->
  Elab ty tm (Either [(Int, Solving Core.Kind ty)] (Core.Type ty))
zonkType (Solving ty) =
  fmap toEither . getCompose . for ty $
  Compose .
  either
    (\n -> do
        k <- lookupMetaKind n
        pure $ Failure [(n, k)])
    (pure . Success)