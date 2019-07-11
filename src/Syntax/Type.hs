{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Syntax.Type where

import Bound.Scope.Simple (Scope, abstract1)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

import Rep

data Type ty
  -- 'types'
  = TVar ty
  | TApp (Type ty) (Type ty)
  | TUInt64
  | TArr
  | TRep Rep
  | TForall (Maybe Text) (Type ty) (Scope () Type ty)

  -- 'kinds'
  | TKRep
  | TKPi (Maybe Text) (Type ty) (Scope () Type ty)
  | TKType !Integer
  deriving (Functor, Foldable, Traversable)
type Kind = Type
infixl 5 `TApp`
makeBound ''Type
deriveEq1 ''Type
deriveShow1 ''Type
instance Eq ty => Eq (Type ty) where; (==) = eq1
instance Show ty => Show (Type ty) where; showsPrec = showsPrec1

tforall_ :: (Text, Type Text) -> Type Text -> Type Text
tforall_ (a, s) = TForall (Just a) s . abstract1 a