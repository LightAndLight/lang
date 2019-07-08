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
import Data.Traversable (for)

import Core (Core)
import Core.Type (Type(..), Rep(..))
import Syntax (Syntax)

data Warning
data TypeError
  = TypeNotInScope Text
  | ExpectedKPi (Type Text)
  | ExpectedKForall (Type Text)
  | ExpectedKType (Type Text)
  | ExpectedKType0 (Type Text)
  | ExpectedKTypeN (Type Text)
  | KindMismatch (Type Text) (Type Text)
  | KindEscaped Text (Type Text)
  | Can'tInferKind (Type Text)
  | NotSubkindOf (Type Text) (Type Text)
  deriving Show

data ElabEnv ty
  = ElabEnv
  { eKinds :: ty -> Maybe (Type ty)
  , eTypeNames :: ty -> Maybe Text
  }

addTy ::
  Type ty -> -- kind
  Maybe Text -> -- optional name
  ElabEnv ty ->
  ElabEnv (Var () ty)
addTy k mn e =
  e
  { eKinds = (fmap.fmap) F . unvar (\() -> Just k) (eKinds e)
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

unnamed :: Maybe Text -> Text
unnamed = fromMaybe "<unnamed>"

lookupKind :: ty -> Elab ty (Type ty)
lookupKind t = do
  res <- asks eKinds
  case res t of
    Nothing -> do
      tyNames <- Elab $ asks eTypeNames
      throwError $ TypeNotInScope (unnamed $ tyNames t)
    Just k -> pure k

subkindOf :: Eq ty => Type ty -> Type ty -> Bool
subkindOf TKType0{} TKTypeN{} = True
subkindOf (TKTypeN n) (TKTypeN n') = n <= n'
subkindOf (TKPi _ s t) (TKPi _ s' t') =
  s == s' &&
  subkindOf (fromScope t) (fromScope t')
subkindOf k1 k2 = k1 == k2

checkKind ::
  Eq ty =>
  Type ty -> -- type
  Type ty -> -- kind
  Elab ty ()
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
  Elab ty (Type ty) -- inferred kind
inferKind ty =
  case ty of
    TVar a -> lookupKind a
    TForall mn k a -> do
      aKind <- mapElabEnv (addTy k mn) (inferKind $ fromScope a)
      for aKind $ \v ->
        case v of
          B () -> do
            typeNames <- asks eTypeNames
            throwError $ KindEscaped (unnamed mn) (unnamed . typeNames <$> k)
          F x -> pure x
    TApp a b -> do
      aKind <- inferKind a
      case aKind of
        TKPi _ s t -> instantiate1 a t <$ checkKind b s
        _ -> do
          typeNames <- asks eTypeNames
          throwError $ ExpectedKPi (unnamed . typeNames <$> aKind)
    TUInt64 -> pure $ TKType0 (TRep RI64)
    TArr ->
      pure $
      TKPi (Just "r1") TKRep . toScope $
      TKPi (Just "r2") TKRep . toScope $
      TKPi Nothing (TKType0 . TVar $ F$B()) . toScope $
      TKPi Nothing (TKType0 . TVar $ B()) . toScope $
      TKType0 (TRep RPtr)
    TRep{} -> pure TKRep
    TKRep -> pure $ TKType0 (TRep RPtr)
    TKType0 a -> TKTypeN 1 <$ checkKind a TKRep
    TKTypeN n -> pure $ TKTypeN (n+1)
    TKPi mn s t -> do
      sKind <- inferKind s
      sn <-
        case sKind of
          TKType0{} -> pure 0
          TKTypeN n -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (unnamed . typeNames <$> sKind)
      tKind <- mapElabEnv (addTy s mn) $ inferKind (fromScope t)
      tn <-
        case tKind of
          TKType0{} -> pure 0
          TKTypeN n -> pure n
          _ -> do
            typeNames <- asks eTypeNames
            throwError $ ExpectedKType (unnamed . typeNames <$> sKind)
      pure $ case (sn, tn) of
        (0, 0) -> TKType0 (TRep RPtr)
        (n, m) -> TKTypeN (max n m)

check :: Syntax ty tm -> Type ty -> Elab ty (Core tm)
check = undefined

infer :: Syntax ty tm -> Elab ty (Core tm, Type ty)
infer = undefined