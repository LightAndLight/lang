{-# language DeriveFunctor #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
module Elaborate where

import Biscope (fromBiscopeL, toBiscopeL, fromBiscopeR, toBiscopeR)
import Bound.Scope.Simple (fromScope, toScope, instantiate1)
import Bound.Var (Var(..), unvar)
import Control.Monad (unless)
import Control.Monad.Except (MonadError, ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader, ReaderT, runReaderT, asks, withReaderT)
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.Bifunctor (bimap)
import Data.DList (DList)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Traversable (for)

import qualified Data.DList as DList

import Core (Core)
import qualified Core
import Core.Type (Type(..), Rep(..), pattern TArrow)
import Operators (Op(..))
import Syntax (Syntax)
import qualified Syntax

data Warning
  = WOverflow Integer (Type Text)
  deriving Show

data TypeError
  = TypeNotInScope Text
  | VarNotInScope Text
  | ExpectedKPi (Type Text)
  | ExpectedKForall (Type Text)
  | ExpectedKType (Type Text)
  | ExpectedKType0 (Type Text)
  | ExpectedKTypeN (Type Text)
  | KindMismatch (Type Text) (Type Text)
  | KindEscaped Text (Type Text)
  | Can'tInferKind (Type Text)
  | NotSubkindOf (Type Text) (Type Text)
  | TypeMismatch (Type Text) (Type Text)
  | ExpectedNumeric (Type Text)
  | ExpectedArrow (Type Text)
  | LamIsNot (Type Text)
  | ExpectedForall (Type Text)
  | Can'tInferType (Syntax Text Text)
  deriving Show

data ElabEnv ty tm
  = ElabEnv
  { eKinds :: ty -> Maybe (Type ty)
  , eTypeNames :: ty -> Maybe Text
  , eTypes :: tm -> Maybe (Type ty)
  , eVarNames :: tm -> Maybe Text
  }

newElabEnv :: ElabEnv ty tm
newElabEnv =
  ElabEnv
  { eKinds = const Nothing
  , eTypeNames = const Nothing
  , eTypes = const Nothing
  , eVarNames = const Nothing
  }

addTy ::
  Type ty -> -- kind
  Maybe Text -> -- optional name
  ElabEnv ty tm ->
  ElabEnv (Var () ty) tm
addTy k mn e =
  e
  { eKinds = (fmap.fmap) F . unvar (\() -> Just k) (eKinds e)
  , eTypeNames = unvar (\() -> mn) (eTypeNames e)
  , eTypes = (fmap.fmap) F . eTypes e
  }

addVar ::
  Type ty -> -- type
  Maybe Text -> -- optional name
  ElabEnv ty tm ->
  ElabEnv ty (Var () tm)
addVar t mn e =
  e
  { eTypes = unvar (\() -> Just t) (eTypes e)
  , eVarNames = unvar (\() -> mn) (eVarNames e)
  }

newtype Elab ty tm a
  = Elab
  { unElab ::
      ReaderT (ElabEnv ty tm)
      (ExceptT TypeError (Writer (DList Warning))) a
  } deriving (Functor, Applicative, Monad, MonadError TypeError, MonadReader (ElabEnv ty tm))

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

lookupKind :: ty -> Elab ty tm (Type ty)
lookupKind t = do
  res <- asks eKinds
  case res t of
    Nothing -> do
      tyNames <- Elab $ asks eTypeNames
      throwError $ TypeNotInScope (unnamed $ tyNames t)
    Just k -> pure k

lookupType :: tm -> Elab ty tm (Type ty)
lookupType t = do
  res <- asks eTypes
  case res t of
    Nothing -> do
      varNames <- Elab $ asks eVarNames
      throwError $ VarNotInScope (unnamed $ varNames t)
    Just k -> pure k

subkindOf :: Eq ty => Type ty -> Type ty -> Bool
subkindOf (TApp (TKType n) a) (TApp (TKType n') b) =
  a == b && n <= n'
subkindOf (TKPi _ s t) (TKPi _ s' t') =
  s == s' &&
  subkindOf (fromScope t) (fromScope t')
subkindOf k1 k2 = k1 == k2

checkKind ::
  Eq ty =>
  Type ty -> -- type
  Type ty -> -- kind
  Elab ty tm ()
checkKind ty ki = do
  tKind <- inferKind ty
  unless (tKind `subkindOf` ki) $ do
    typeNames <- asks eTypeNames
    throwError $
      KindMismatch
        (unnamed . typeNames <$> ki)
        (unnamed . typeNames <$> tKind)

inferKind ::
  Eq ty =>
  Type ty -> -- type
  Elab ty tm (Type ty) -- inferred kind
inferKind ty =
  case ty of
    TVar a -> lookupKind a
    TForall mn k a -> do
      aKind <- mapElabEnv (addTy k mn) (inferKind $ fromScope a)
      for aKind $
        \case
          B () -> do
            typeNames <- asks eTypeNames
            throwError $ KindEscaped (unnamed mn) (unnamed . typeNames <$> k)
          F x -> pure x
    TApp a b -> do
      aKind <- inferKind a
      case aKind of
        TKPi _ s t -> instantiate1 b t <$ checkKind b s
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedKPi (unnamed . typeNames <$> aKind)
    TUInt64 -> pure $ TApp (TKType 0) (TRep RI64)
    TArr ->
      pure $
      TKPi (Just "r1") TKRep . toScope $
      TKPi (Just "r2") TKRep . toScope $
      TKPi Nothing (TApp (TKType 0) . TVar $ F$B()) . toScope $
      TKPi Nothing (TApp (TKType 0) . TVar $ F$B()) . toScope $
      TApp (TKType 0) (TRep RPtr)
    TRep{} -> pure TKRep
    TKRep -> pure $ TApp (TKType 0) (TRep RPtr)
    TKType n ->
      pure $
      TKPi Nothing TKRep . toScope $
      TKType (n+1)
    TKPi mn s t -> do
      sKind <- inferKind s
      sn <-
        case sKind of
          TKType n -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (unnamed . typeNames <$> sKind)
      tKind <- mapElabEnv (addTy s mn) $ inferKind (fromScope t)
      tn <-
        case tKind of
          TKType n -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (unnamed . typeNames <$> sKind)
      pure $ TApp (TKType $ max sn tn + 1) (TRep RPtr)

check :: Eq ty => Syntax ty tm -> Type ty -> Elab ty tm (Core ty tm)
check tm ty =
  case tm of
    Syntax.Natural n ->
      case ty of
        TUInt64 -> do
          unless (n < 2^(64::Integer)) . warn $ WOverflow n TUInt64
          pure $ Core.UInt64 (fromIntegral n)
        _ -> do
          typeNames <- (unnamed .) <$> asks eTypeNames
          throwError $ ExpectedNumeric (typeNames <$> ty)
    Syntax.Lam mn a ->
      case ty of
        TArrow _ _ s t -> do
          a' <- mapElabEnv (addVar s mn) $ check (fromBiscopeR a) t
          pure (Core.Lam mn s $ toBiscopeR a')
        _ -> do
          typeNames <- (unnamed .) <$> asks eTypeNames
          throwError $ LamIsNot (typeNames <$> ty)
    _ -> do
      (tm', ty') <- infer tm
      unless (ty == ty') $ do
        typeNames <- (unnamed .) <$> asks eTypeNames
        throwError $ TypeMismatch (typeNames <$> ty) (typeNames <$> ty')
      pure tm'

infer :: Eq ty => Syntax ty tm -> Elab ty tm (Core ty tm, Type ty)
infer tm =
  case tm of
    Syntax.Var a -> (,) (Core.Var a) <$> lookupType a
    Syntax.Bin op a b ->
      case op of
        Mult -> do
          a' <- check a TUInt64
          b' <- check b TUInt64
          pure (Core.Bin op a' b', TUInt64)
        Add -> do
          a' <- check a TUInt64
          b' <- check b TUInt64
          pure (Core.Bin op a' b', TUInt64)
    Syntax.App a b -> do
      (a', aType) <- infer a
      case aType of
        TArrow _ _ s t -> do
          b' <- check b s
          pure (Core.App a' b', t)
        _ -> do
          typeNames <- (unnamed .) <$> asks eTypeNames
          throwError $ ExpectedArrow (typeNames <$> aType)
    Syntax.AppType a t -> do
      (a', aType) <- infer a
      case aType of
        TForall _ k rest -> do
          checkKind t k
          pure (Core.AppType a' t, instantiate1 t rest)
        _ -> do
          typeNames <- (unnamed .) <$> asks eTypeNames
          throwError $ ExpectedForall (typeNames <$> aType)
    Syntax.AbsType mn k a -> do
      (a', aTy) <- mapElabEnv (addTy k mn) $ infer (fromBiscopeL a)
      pure (Core.AbsType mn k $ toBiscopeL a', TForall mn k $ toScope aTy)
    _ -> do
      varNames <- (unnamed .) <$> asks eVarNames
      typeNames <- (unnamed .) <$> asks eTypeNames
      throwError $ Can'tInferType (bimap typeNames varNames tm)
