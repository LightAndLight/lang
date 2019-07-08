{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language RankNTypes #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
module Core where

import Bound.Scope.Simple (Scope)
import Bound.TH (makeBound)
import Data.Deriving (deriveEq1, deriveShow1)
import Data.Functor.Classes (eq1, showsPrec1)
import Data.Word (Word64)
import Data.Text (Text)

import Operators (Op)

data Core a
  = Var a
  | UInt64 !Word64
  | Bin Op (Core a) (Core a)
  | Lam (Maybe Text) (Scope () Core a)
  | App (Core a) (Core a)
  deriving (Functor, Foldable, Traversable)
makeBound ''Core
deriveEq1 ''Core
deriveShow1 ''Core
instance Eq a => Eq (Core a) where; (==) = eq1
instance Show a => Show (Core a) where; showsPrec = showsPrec1
