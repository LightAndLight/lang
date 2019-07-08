{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Core.Type where

import Bound.Scope.Simple (Scope, abstract1)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Text (Text)

data Rep = RPtr | RI64 | RList [Rep]
  deriving (Eq, Show)

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
  | TKType0 (Type ty)
  | TKTypeN !Integer
  deriving (Functor, Foldable, Traversable)
makeBound ''Type
deriveEq1 ''Type
deriveShow1 ''Type
instance Eq ty => Eq (Type ty) where; (==) = eq1
instance Show ty => Show (Type ty) where; showsPrec = showsPrec1

tforall_ :: (Text, Type Text) -> Type Text -> Type Text
tforall_ (a, s) = TForall (Just a) s . abstract1 a