{-# language DeriveFunctor #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
module Elaborate where

import Biscope (fromBiscopeR)
import Bound.Scope.Simple (fromScope, toScope, instantiate1)
import Bound.Var (Var(..), unvar)
import Control.Monad (unless)
import Control.Monad.Except (MonadError, ExceptT, throwError)
import Control.Monad.Reader (MonadReader, ReaderT, asks, withReaderT)
import Control.Monad.Writer (Writer)
import Data.DList (DList)
import Data.Maybe (fromMaybe)
import Data.Text (Text)

import Core (Core)
import Core.Type (Type(..), Rep(..))
import Syntax (Syntax)

data Warning
data TypeError
  = TypeNotInScope Text
  | ExpectedKPi (Type Text)
  | ExpectedKForall (Type Text)
  | KindMismatch (Type Text) (Type Text)
  deriving Show

data ElabEnv ty
  = ElabEnv
  { eKindNames :: ty -> Maybe Text
  , eKinds :: ty -> Maybe (Type ty)
  , eTypeNames :: ty -> Maybe Text
  }

addKind ::
  Type ty -> -- kind
  Maybe Text -> -- optional name
  ElabEnv ty ->
  ElabEnv (Var () ty)
addKind k mn e =
  e
  { eKinds = (fmap.fmap) F . unvar (\() -> Just k) (eKinds e)
  , eKindNames = unvar (\() -> mn) (eTypeNames e)
  , eTypeNames = unvar (const Nothing) (eKindNames e)
  }

addTy ::
  Type ty -> -- kind
  Maybe Text -> -- optional name
  ElabEnv ty ->
  ElabEnv (Var () ty)
addTy k mn e =
  e
  { eKinds = (fmap.fmap) F . unvar (\() -> Just k) (eKinds e)
  , eKindNames = unvar (const Nothing) (eKindNames e)
  , eTypeNames = unvar (\() -> mn) (eTypeNames e)
  }

newtype Elab ty a
  = Elab
  { unElab ::
      ReaderT (ElabEnv ty)
      (ExceptT TypeError (Writer (DList Warning))) a
  } deriving (Functor, Applicative, Monad, MonadError TypeError, MonadReader (ElabEnv ty))

mapElabEnv :: (ElabEnv ty' -> ElabEnv ty) -> Elab ty a -> Elab ty' a
mapElabEnv f = Elab . withReaderT f . unElab

lookupKind :: ty -> Elab ty (Type ty)
lookupKind t = do
  res <- asks eKinds
  case res t of
    Nothing -> do
      tyNames <- Elab $ asks eTypeNames
      throwError $ TypeNotInScope (fromMaybe "<unnamed>" $ tyNames t)
    Just k -> pure k

checkKind ::
  Eq ty =>
  Type ty -> -- type
  Type ty -> -- kind
  Elab ty ()
checkKind ty ki = do
  tKind <- inferKind ty
  unless (tKind == ki) $ do
    kindNames <- asks eKindNames
    throwError $
      KindMismatch
        (fromMaybe "<unnamed>" . kindNames <$> ki)
        (fromMaybe "<unnamed>" . kindNames <$> tKind)

inferKind ::
  Eq ty =>
  Type ty -> -- type
  Elab ty (Type ty) -- inferred kind
inferKind ty =
  case ty of
    TVar a -> lookupKind a
    TForall mn k a ->
      mapElabEnv (addTy k mn) (inferKind $ fromScope a)
    TApp a b -> do
      aKind <- inferKind a
      case aKind of
        TKPi mn s t -> instantiate1 a t <$ checkKind b s
        _ -> do
          kindNames <- asks eKindNames
          throwError $ ExpectedKPi (fromMaybe "<unnamed>" . kindNames <$> aKind)
    TUInt64 -> pure $ TKType0 (TRep RI64)
    TArr ->
      pure $
      TKPi (Just "r1") TKRep . toScope $
      TKPi (Just "r2") TKRep . toScope $
      TKPi Nothing (TKType0 . TVar $ F$B()) . toScope $
      TKPi Nothing (TKType0 . TVar $ B()) . toScope $
      TKType0 (TRep RPtr)

check :: Syntax ty tm -> Type ty -> Elab ty (Core tm)
check = undefined

infer :: Syntax ty tm -> Elab ty (Core tm, Type ty)
infer = undefined