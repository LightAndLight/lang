module Syntax where

import Data.Word (Word64)

data Expr
  = UInt64 !Word64
  | Add Expr Expr
  | Mult Expr Expr
  deriving Show
