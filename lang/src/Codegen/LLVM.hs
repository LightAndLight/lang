{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
module Codegen.LLVM where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Control.Monad.Fix (MonadFix)
import Data.Foldable (for_, foldrM)
import Data.Map (Map)
import Data.Maybe (fromJust)
import LLVM.AST.Operand (Operand)
import LLVM.IRBuilder (MonadIRBuilder)
import LLVM.IRBuilder.Module (MonadModuleBuilder)

import qualified Data.Map as Map
import qualified LLVM.AST.Name as LLVM
import qualified LLVM.IRBuilder.Constant as LLVM
import qualified LLVM.IRBuilder.Instruction as LLVM
import qualified LLVM.IRBuilder.Module as LLVM

import Syntax

cg_def :: MonadModuleBuilder m => (String -> Operand) -> (a -> Operand) -> LDef a -> m (Map String Operand)
cg_def names var (LDef ln lb) = do
  n <-
    LLVM.function (LLVM.mkName ln) _ _ $ \[env, arg] -> do
      a' <-
        cg_expr
          names
          (unvar (\case; LEnv -> env; LArg -> arg) var)
          (fromScope lb)
      LLVM.ret a'
  pure $ Map.singleton ln n

cg_expr ::
  forall m a.
  (MonadIRBuilder m, MonadModuleBuilder m) =>
  (String -> Operand) -> (a -> Operand) -> LL a -> m Operand
cg_expr names = go
  where
    go :: forall b. (b -> Operand) -> LL b -> m Operand
    go var ex =
      case ex of
        LVar a -> pure $ var a
        LName a -> pure $ names a
        LUInt64 a -> LLVM.int64 $ fromIntegral a
        LProduct as -> do
          let las = length as
          loc <- _ las
          for_ (zip [0::Integer ..] as) $ \(n, a) -> do
            _0 <- LLVM.int32 0
            ix <- LLVM.int32 n
            ptr <- LLVM.gep loc [_0, ix]
            a' <- go var a
            LLVM.store a' 0 ptr
          pure loc
        LProj n a -> do
          a' <- go var a
          _0 <- LLVM.int32 0
          ix <- LLVM.int32 $ fromIntegral n
          ptr <- LLVM.gep a' [_0, ix]
          LLVM.load ptr 0
        LBin o a b -> do
          va <- go var a
          vb <- go var b
          case o of
            Add -> LLVM.add va vb
            Mult -> LLVM.mul va vb
        LApp f e x -> do
          f' <- go var f
          e' <- go var e
          x' <- go var x
          LLVM.call f' [(e', _), (x', _)]
        LClosure a b -> do
          loc <- _ 2

          a' <- go var a
          _0 <- LLVM.int32 0
          ix0 <- LLVM.int32 0
          ptr0 <- LLVM.gep loc [_0, ix0]
          LLVM.store a' 0 ptr0

          b' <- go var b
          _0 <- LLVM.int32 0
          ix1 <- LLVM.int32 1
          ptr1 <- LLVM.gep loc [_0, ix1]
          LLVM.store b' 0 ptr1

          pure loc
        LUnpack a b -> do
          a' <- go var a

          _0 <- LLVM.int32 0
          ix0 <- LLVM.int32 0
          ptr0 <- LLVM.gep a' [_0, ix0]
          a1 <- LLVM.load ptr0 0

          _0 <- LLVM.int32 0
          ix1 <- LLVM.int32 1
          ptr1 <- LLVM.gep a' [_0, ix1]
          a2 <- LLVM.load ptr1 0

          go
            (unvar (\case; Fst -> a1; Snd -> a2) var)
            (fromScope b)

cg ::
  (MonadModuleBuilder m, MonadIRBuilder m, MonadFix m) =>
  (a -> Operand) -> (LL a, [LDef a]) -> m Operand
cg var (val, ds) = do
  rec
    let
      names :: String -> Operand
      names = fromJust . flip Map.lookup ds'
    ds' <- foldrM (\d rest -> (<> rest) <$> cg_def names var d) mempty ds
  LLVM.function "main" _ _ $ \_ -> do
    val' <- cg_expr names var val
    LLVM.ret val'