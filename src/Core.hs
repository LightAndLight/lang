{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language OverloadedStrings #-}
{-# language RankNTypes #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Core where

import Biscope (Bisubst(..), BiscopeL, BiscopeR, bisubstBiscopeR, bisubstBiscopeL)
import Control.Monad (ap)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Deriving (deriveEq2, deriveShow2)
import Data.Functor.Classes (Eq1(..), Show1(..), liftEq2, liftShowsPrec2, eq1, showsPrec1)
import Data.Word (Word64)
import Data.Text (Text)

import Operators (Op)
import Rep (Rep)

data LamInfo
  = LamInfo
  { liInRep :: Rep
  , liOutRep :: Rep
  } deriving (Eq, Show)

data AppInfo
  = AppInfo
  { aiInKind :: Rep
  , aiOutKind :: Rep
  } deriving (Eq, Show)

data Core f ty tm
  = Var tm
  | UInt64 !Word64
  | Bin Op (Core f ty tm) (Core f ty tm)
  | Lam LamInfo (Maybe Text) (f ty) (BiscopeR () f (Core f) ty tm)
  | App AppInfo (Core f ty tm) (Core f ty tm)
  | AppType (Core f ty tm) (f ty)
  | AbsType (Maybe Text) (f ty) (BiscopeL () f (Core f) ty tm)
  deriving (Functor, Foldable, Traversable)
deriveBifunctor ''Core
deriveBifoldable ''Core
deriveBitraversable ''Core

instance Monad f => Bisubst (Core f) where
  type Inner (Core f) = f
  bireturn = Var
  bisubst f g tm =
    case tm of
      Var a -> g a
      UInt64 a -> UInt64 a
      Bin a b c -> Bin a (bisubst f g b) (bisubst f g c)
      Lam x a b c ->
        Lam x a (b >>= f) (bisubstBiscopeR f g c)
      App x a b -> App x (bisubst f g a) (bisubst f g b)
      AppType a b -> AppType (bisubst f g a) (b >>= f)
      AbsType a b c -> AbsType a (b >>= f) (bisubstBiscopeL f g c)

instance Monad f => Applicative (Core f ty) where; pure = return; (<*>) = ap
instance Monad f => Monad (Core f ty) where; return = bireturn; (>>=) a f = bisubst pure f a

deriveEq2 ''Core
deriveShow2 ''Core
instance (Eq1 f, Eq ty) => Eq1 (Core f ty) where
  liftEq = liftEq2 (==)
instance (Show1 f, Show ty) => Show1 (Core f ty) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList
instance (Eq1 f, Eq ty, Eq tm) => Eq (Core f ty tm) where; (==) = eq1
instance (Show1 f, Show ty, Show tm) => Show (Core f ty tm) where; showsPrec = showsPrec1

data Def f ty tm = Def tm (Core f ty tm) (f ty)
  deriving Show