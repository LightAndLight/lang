{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language StandaloneDeriving #-}
{-# language FlexibleContexts, RecursiveDo, ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
module Syntax where

import Bound.Class ((>>>=))
import Bound.Scope.Simple (Scope, bitraverseScope)
import Bound.TH (makeBound)
import Bound.Var (Var)
import Control.Monad (ap)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Identity (Identity(..))
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

import Biscope (Bisubst(..), BiscopeL, BiscopeR)
import Core.Type (Type, Kind)
import Operators (Op(..))

data Syntax ki ty tm
  = Var tm
  | Natural !Integer
  | Bin Op (Syntax ki ty tm) (Syntax ki ty tm)
  | Lam (Maybe Text) (BiscopeR () (Type ki) (Syntax ki) ty tm)
  | App (Syntax ki ty tm) (Syntax ki ty tm)
  | AppType (Syntax ki ty tm) (Type ki ty)
  | AbsType (Maybe Text) (Kind ki) (BiscopeL () (Type ki) (Syntax ki) ty tm)
  deriving (Functor, Foldable, Traversable)
deriveBifunctor ''Syntax
deriveBifoldable ''Syntax
deriveBitraversable ''Syntax

instance Bisubst (Syntax ki) (Type ki) where
  bireturn = Var
  bisubst f g tm =
    case tm of
      Var a -> _
      Natural a -> _
      Bin a b c -> _
      Lam a b -> _
      App a b -> _
      AppType a b -> _
      AbsType a b c -> _

instance Applicative (Syntax ki ty) where; pure = return; (<*>) = ap
instance Monad (Syntax ki ty) where; return = bireturn; (>>=) a f = bisubst pure f a

deriveEq1 ''Syntax
deriveShow1 ''Syntax
instance (Eq ki, Eq ty, Eq tm) => Eq (Syntax ki ty tm) where; (==) = eq1
instance (Show ki, Show ty, Show tm) => Show (Syntax ki ty tm) where; showsPrec = showsPrec1

instTy :: Type ki ty -> Syntax ki (Var () ty) tm -> Syntax ki ty tm
instTy = _