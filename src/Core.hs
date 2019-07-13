{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language RankNTypes #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Core where

import Biscope (Bisubst(..), BiscopeL, BiscopeR, bisubstBiscopeR, bisubstBiscopeL)
import Control.Monad (ap)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Deriving (deriveEq2, deriveShow2, deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Word (Word64)
import Data.Text (Text)

import Core.Type (Type, Kind)
import Operators (Op)

data Core ty tm
  = Var tm
  | UInt64 (Type ty) !Word64
  | Bin (Type ty) Op (Core ty tm) (Core ty tm)
  | Lam (Type ty) (Maybe Text) (Type ty) (BiscopeR () Type Core ty tm)
  | App (Type ty) (Core ty tm) (Core ty tm)
  | AppType (Type ty) (Core ty tm) (Type ty)
  | AbsType (Type ty) (Maybe Text) (Kind ty) (BiscopeL () Type Core ty tm)
  deriving (Functor, Foldable, Traversable)
deriveBifunctor ''Core
deriveBifoldable ''Core
deriveBitraversable ''Core

instance Bisubst Core where
  type Inner Core = Type
  bireturn = Var
  bisubst f g tm =
    case tm of
      Var a -> g a
      UInt64 x a -> UInt64 (x >>= f) a
      Bin x a b c -> Bin (x >>= f) a (bisubst f g b) (bisubst f g c)
      Lam x a b c ->
        Lam (x >>= f) a (b >>= f) (bisubstBiscopeR f g c)
      App x a b -> App (x >>= f) (bisubst f g a) (bisubst f g b)
      AppType x a b -> AppType (x >>= f) (bisubst f g a) (b >>= f)
      AbsType x a b c -> AbsType (x >>= f) a (b >>= f) (bisubstBiscopeL f g c)

instance Applicative (Core ty) where; pure = return; (<*>) = ap
instance Monad (Core ty) where; return = bireturn; (>>=) a f = bisubst pure f a

deriveEq2 ''Core
deriveShow2 ''Core
deriveEq1 ''Core
deriveShow1 ''Core
instance (Eq ty, Eq tm) => Eq (Core ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Core ty tm) where; showsPrec = showsPrec1

data Def ty tm = Def tm (Core ty tm) (Type ty)
  deriving Show

getType :: (tm -> Type ty) -> Core ty tm -> Type ty
getType f ty =
  case ty of
    Var a -> f a
    UInt64 a _ -> a
    Bin a _ _ _ -> a
    Lam a _ _ _ -> a
    App a _ _ -> a
    AppType a _ _ -> a
    AbsType a _ _ _ -> a