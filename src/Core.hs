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

import Core.Type (Type)
import Operators (Op)

data Core ty tm
  = Var tm
  | UInt64 !Word64
  | Bin Op (Core ty tm) (Core ty tm)
  | Lam (Maybe Text) (Type ty) (BiscopeR () Type Core ty tm)
  | App (Core ty tm) (Core ty tm)
  | AppType (Core ty tm) (Type ty)
  | AbsType (Maybe Text) (Type ty) (BiscopeL () Type Core ty tm)
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
      UInt64 a -> UInt64 a
      Bin a b c -> Bin a (bisubst f g b) (bisubst f g c)
      Lam a b c -> Lam a (b >>= f) (bisubstBiscopeR f g c)
      App a b -> App (bisubst f g a) (bisubst f g b)
      AppType a b -> AppType (bisubst f g a) (b >>= f)
      AbsType a b c -> AbsType a (b >>= f) (bisubstBiscopeL f g c)

instance Applicative (Core ty) where; pure = return; (<*>) = ap
instance Monad (Core ty) where; return = bireturn; (>>=) a f = bisubst pure f a

deriveEq2 ''Core
deriveShow2 ''Core
deriveEq1 ''Core
deriveShow1 ''Core
instance (Eq ty, Eq tm) => Eq (Core ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Core ty tm) where; showsPrec = showsPrec1