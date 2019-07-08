{-# language DeriveFunctor #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings #-}
module Elaborate where

import Bound.Scope.Simple (fromScope, toScope, instantiate1)
import Bound.Var (Var(..), unvar)
import Control.Monad (unless)
import Control.Monad.Except (MonadError, ExceptT, throwError)
import Control.Monad.Reader (MonadReader, ReaderT, asks, withReaderT)
import Control.Monad.Writer (Writer)
import Data.DList (DList)
import Data.Maybe (fromMaybe)
import Data.Text (Text)

import Biscope (Biscope(..))
import Core (Core)
import Core.Type (Type(..), Kind(..))
import Syntax (Syntax)

data Warning
data TypeError
  = TypeNotInScope Text
  | ExpectedKArr (Kind Text)
  | ExpectedKForall (Kind Text)
  | KindMismatch (Kind Text) (Kind Text)
  deriving Show

data ElabEnv ki ty
  = ElabEnv
  { eKindNames :: ki -> Maybe Text
  , eKinds :: ty -> Maybe (Kind ki)
  , eTypeNames :: ty -> Maybe Text
  }

addTy ::
  Kind ki ->
  Maybe Text ->
  ElabEnv ki ty ->
  ElabEnv ki (Var () ty)
addTy k mn e =
  e
  { eKinds = unvar (\() -> Just k) (eKinds e)
  , eTypeNames = unvar (\() -> mn) (eTypeNames e)
  }

newtype Elab ki ty a
  = Elab
  { unElab ::
      ReaderT (ElabEnv ki ty)
      (ExceptT TypeError (Writer (DList Warning))) a
  } deriving (Functor, Applicative, Monad, MonadError TypeError, MonadReader (ElabEnv ki ty))

mapElabEnv :: (ElabEnv ki' ty' -> ElabEnv ki ty) -> Elab ki ty a -> Elab ki' ty' a
mapElabEnv f = Elab . withReaderT f . unElab

lookupType :: ty -> Elab ki ty (Kind ki)
lookupType t = do
  res <- asks eKinds
  case res t of
    Nothing -> do
      tyNames <- Elab $ asks eTypeNames
      throwError $ TypeNotInScope (fromMaybe "<unnamed>" $ tyNames t)
    Just k -> pure k

checkKind :: Eq ki => Type ki ty -> Kind ki -> Elab ki ty ()
checkKind t ki = do
  tKind <- inferKind t
  unless (tKind == ki) $ do
    kindNames <- asks eKindNames
    throwError $
      KindMismatch
        (fromMaybe "<unnamed>" . kindNames <$> ki)
        (fromMaybe "<unnamed>" . kindNames <$> tKind)

inferKind :: Eq ki => Type ki ty -> Elab ki ty (Kind ki)
inferKind ty =
  case ty of
    TVar a -> lookupType a
    TForall mn k (Biscope a) ->
      KArr k <$> mapElabEnv (addTy k mn) (inferKind $ fromScope a)
    TApp a b -> do
      aKind <- inferKind a
      case aKind of
        KArr x y -> y <$ checkKind b x
        _ -> do
          kindNames <- asks eKindNames
          throwError $ ExpectedKArr (fromMaybe "<unnamed>" . kindNames <$> aKind)
    TAppKind t k -> do
      tKind <- inferKind t
      case tKind of
        KForall _ a -> pure $ instantiate1 k a
        _ -> do
          kindNames <- asks eKindNames
          throwError $ ExpectedKForall (fromMaybe "<unnamed>" . kindNames <$> tKind)
    TUInt64 -> pure $ KType KIntRep
    TArr ->
      pure $
      KForall (Just "r1") . toScope $
      KForall (Just "r2") . toScope $
      KArr (KType . KVar $ F$B()) $
      KArr (KType . KVar $ B()) $
      KType KBoxedRep

check :: Syntax a -> Type ki ty -> Elab ki ty (Core tm)
check = undefined

infer :: Syntax a -> Elab ki ty (Core tm, Type ki ty)
infer = undefined