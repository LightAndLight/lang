{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language StandaloneDeriving #-}
{-# language FlexibleContexts, RecursiveDo, ScopedTypeVariables #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Syntax where

import Biscope
  ( Bisubst(..), BiscopeL, BiscopeR, bisubstBiscopeR, bisubstBiscopeL
  , abs1BiscopeL, abs1BiscopeR
  )
import Bound.Var (Var, unvar)
import Control.Monad (ap)
import Data.Bifunctor.TH (deriveBifunctor, deriveBifoldable, deriveBitraversable)
import Data.Deriving (deriveEq2, deriveShow2, deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

import Core.Type (Type)
import Operators (Op(..))

data Syntax ty tm
  = Var tm
  | Natural !Integer
  | Bin Op (Syntax ty tm) (Syntax ty tm)
  | Lam (Maybe Text) (BiscopeR () Type Syntax ty tm)
  | App (Syntax ty tm) (Syntax ty tm)
  | AppType (Syntax ty tm) (Type ty)
  | AbsType (Maybe Text) (Type ty) (BiscopeL () Type Syntax ty tm)
  deriving (Functor, Foldable, Traversable)
deriveBifunctor ''Syntax
deriveBifoldable ''Syntax
deriveBitraversable ''Syntax

lam :: Text -> Syntax ty Text -> Syntax ty Text
lam n = Lam (Just n) . abs1BiscopeR n

absType :: (Text, Type Text) -> Syntax Text tm -> Syntax Text tm
absType (n, k) = AbsType (Just n) k . abs1BiscopeL n

instance Bisubst Syntax where
  type Inner Syntax = Type
  bireturn = Var
  bisubst f g tm =
    case tm of
      Var a -> g a
      Natural a -> Natural a
      Bin a b c -> Bin a (bisubst f g b) (bisubst f g c)
      Lam a b -> Lam a (bisubstBiscopeR f g b)
      App a b -> App (bisubst f g a) (bisubst f g b)
      AppType a b -> AppType (bisubst f g a) (b >>= f)
      AbsType a b c -> AbsType a (b >>= f) (bisubstBiscopeL f g c)

instance Applicative (Syntax ty) where; pure = return; (<*>) = ap
instance Monad (Syntax ty) where; return = bireturn; (>>=) a f = bisubst pure f a

deriveEq2 ''Syntax
deriveShow2 ''Syntax
deriveEq1 ''Syntax
deriveShow1 ''Syntax
instance (Eq ty, Eq tm) => Eq (Syntax ty tm) where; (==) = eq1
instance (Show ty, Show tm) => Show (Syntax ty tm) where; showsPrec = showsPrec1

instTy :: Type ty -> Syntax (Var () ty) tm -> Syntax ty tm
instTy t = bisubst (unvar (\() -> t) pure) pure

data Def ty tm
  = Sig tm (Type ty)
  | Def tm (Syntax ty tm)
  deriving Show