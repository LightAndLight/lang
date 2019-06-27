{-# language BangPatterns #-}
module Codegen where

import Data.Foldable (for_)
import IR (IR)
import qualified IR

import Syntax

cg_expr :: (a -> IR IR.Val) -> C_Expr a -> IR IR.Val
cg_expr var = go (error "not in function")
  where
    go env ex =
      case ex of
        C_Var a -> var a
        C_Bound -> IR.R <$> IR.load0 (IR.R IR.sp)
        C_Env n -> seq env $ IR.R <$> IR.load (IR.C $ IR.W64 n) (IR.R env)
        C_UInt64 a -> pure $ IR.C (IR.W64 a)
        C_Add a b -> do
          va <- go env a
          vb <- go env b
          IR.R <$> IR.add va vb
        C_Mult a b -> do
          va <- go env a
          vb <- go env b
          IR.R <$> IR.mul va vb
        C_Lam e body -> do
          let el = length e
          envp <- do
            p <- IR.alloc (IR.C . IR.W64 $ fromIntegral el)
            for_ (zip [0..] e) $ \(ix, val) -> do
              v <- go env val
              IR.store (IR.C $ IR.W64 ix) v (IR.R p)
            pure p
          res <- go envp body
          IR.mov res IR.rv
          IR.R IR.rv <$ IR.ret
        C_App f x -> do
          vf <- go env f
          vx <- go env x
          loc <- do
            envp <- IR.load0 vf
            IR.add (IR.R envp) (IR.C $ IR.W64 1)
          IR.push vx
          IR.R IR.rv <$ IR.icall (IR.R loc)
