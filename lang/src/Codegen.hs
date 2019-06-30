{-# language BangPatterns #-}
module Codegen where

import Data.Foldable (for_)
import Data.Word (Word64)
import IR (IR)
import qualified IR

import Syntax

cg_expr :: (String -> IR IR.Val) -> (a -> IR IR.Val) -> LL a -> IR IR.Val
cg_expr name var = go (error "not in function")
  where
    go env ex =
      case ex of
        LVar a -> var a
        LName a -> name a
        LUInt64 a -> pure $ IR.C (IR.W64 a)
        LProduct as -> do
          let las = length as
          loc <- IR.alloc (IR.C . IR.W64 $ fromIntegral las)
          for_ (zip [0::Word64 ..] as) $ \(n, a) -> do
            a' <- go env a
            IR.store a' (IR.C $ IR.W64 n) (IR.R loc)
          pure $ IR.R loc
        LProj n a -> do
          a' <- go env a
          IR.R <$> IR.load (IR.C $ IR.W64 n) a'
        LBin o a b -> do
          va <- go env a
          vb <- go env b
          case o of
            Add -> IR.R <$> IR.add va vb
            Mult -> IR.R <$> IR.mul va vb
        LApp f e x -> do
          vf <- go env f
          ve <- go env e
          vx <- go env x
          IR.push ve
          IR.push vx
          IR.R IR.rv <$ IR.icall vf
