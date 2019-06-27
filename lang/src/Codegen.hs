module Codegen where

import IR (IR)
import qualified IR

import Syntax

cg_expr :: Expr -> IR IR.Val
cg_expr e =
  case e of
    UInt64 a -> pure $ IR.C (IR.W64 a)
    Add a b -> do
      va <- cg_expr a
      vb <- cg_expr b
      IR.R <$> IR.add va vb
    Mult a b -> do
      va <- cg_expr a
      vb <- cg_expr b
      IR.R <$> IR.mul va vb
