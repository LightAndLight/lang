{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language RecursiveDo #-}
{-# language ScopedTypeVariables #-}
module Codegen where

import Bound.Scope.Simple (fromScope)
import Bound.Var (unvar)
import Control.Monad.Fix (MonadFix)
import Data.Foldable (for_, foldrM)
import Data.Map (Map)
import Data.Maybe (fromJust)
import Data.String (fromString)
import Data.Void (Void, absurd)
import LLVM.AST.Operand (Operand)
import LLVM.IRBuilder (MonadIRBuilder)
import LLVM.IRBuilder.Module (MonadModuleBuilder)

import qualified Data.Map as Map
import qualified LLVM.AST as LLVM (Module)
import qualified LLVM.AST.Name as LLVM
import qualified LLVM.AST.Type as LLVM
import qualified LLVM.IRBuilder.Constant as LLVM
import qualified LLVM.IRBuilder.Instruction as LLVM
import qualified LLVM.IRBuilder.Monad as LLVM
import qualified LLVM.IRBuilder.Module as LLVM

import Closure
import Operators (Op(..))

opaquePtr :: LLVM.Type
opaquePtr = LLVM.ptr LLVM.i8

toOpaquePtr :: MonadIRBuilder m => Operand -> m Operand
toOpaquePtr o = LLVM.bitcast o opaquePtr

fromOpaquePtr :: MonadIRBuilder m => LLVM.Type -> Operand -> m Operand
fromOpaquePtr = flip LLVM.bitcast

cg_def ::
  MonadModuleBuilder m =>
  LLVM.Type ->
  Operand ->
  (String -> Operand) ->
  (a -> Operand) ->
  LDef a ->
  m (Map String Operand)
cg_def closureType malloc names var (LDef ln lb) = do
  let
    name = LLVM.mkName ln
    argTys = [(opaquePtr, LLVM.NoParameterName), (opaquePtr, LLVM.NoParameterName)]
    retTy = opaquePtr
  n <-
    LLVM.function name argTys retTy $ \[env, arg] -> do
      a' <-
        cg_expr
          closureType
          malloc
          names
          (unvar (\case; LEnv -> env; LArg -> arg) var)
          (fromScope lb)
      LLVM.ret a'
  pure $ Map.singleton ln n

cg_expr ::
  forall m a.
  (MonadIRBuilder m, MonadModuleBuilder m) =>
  LLVM.Type ->
  Operand ->
  (String -> Operand) ->
  (a -> Operand) ->
  Closure a ->
  m Operand
cg_expr closureType malloc names = go
  where
    go :: forall b. (b -> Operand) -> Closure b -> m Operand
    go var ex =
      case ex of
        Var a -> pure $ var a
        Name a -> pure $ names a
        UInt64 a -> do
          size <- LLVM.int32 8
          ptr <- fromOpaquePtr (LLVM.ptr LLVM.i64) =<< LLVM.call malloc [(size, [])]

          val <- LLVM.int64 $ fromIntegral a
          LLVM.store ptr 0 val

          toOpaquePtr ptr
        Product as -> do
          let las = length as
          size <- LLVM.int32 $ fromIntegral las
          loc <-
            fromOpaquePtr (LLVM.ptr $ LLVM.ArrayType (fromIntegral las) opaquePtr) =<<
            LLVM.call malloc [(size, [])]
          for_ (zip [0::Integer ..] as) $ \(n, a) -> do
            _0 <- LLVM.int32 0
            ix <- LLVM.int32 n
            ptr <- LLVM.gep loc [_0, ix]
            a' <- go var a
            LLVM.store ptr 0 a'
          toOpaquePtr loc
        Proj n a -> do
          a' <- fromOpaquePtr (LLVM.ptr $ LLVM.ArrayType (n+1) opaquePtr) =<< go var a
          _0 <- LLVM.int32 0
          ix <- LLVM.int32 $ fromIntegral n
          ptr <- LLVM.gep a' [_0, ix]
          LLVM.load ptr 0
        Bin o a b -> do
          va <- flip LLVM.load 0 =<< fromOpaquePtr (LLVM.ptr LLVM.i64) =<< go var a
          vb <- flip LLVM.load 0 =<< fromOpaquePtr (LLVM.ptr LLVM.i64) =<< go var b

          size <- LLVM.int32 8
          ptr <- fromOpaquePtr (LLVM.ptr LLVM.i64) =<< LLVM.call malloc [(size, [])]
          val <- case o of
            Add -> LLVM.add va vb
            Mult -> LLVM.mul va vb
          LLVM.store ptr 0 val

          toOpaquePtr ptr
        App f e x -> do
          f' <- go var f
          e' <- go var e
          x' <- go var x
          LLVM.call f' [(e', []), (x', [])]
        Closure a b -> do
          size <- LLVM.int32 2
          loc <-
            fromOpaquePtr (LLVM.ptr closureType) =<<
            LLVM.call malloc [(size, [])]

          a' <- go var a
          _0 <- LLVM.int32 0
          ix0 <- LLVM.int32 0
          ptr0 <- LLVM.gep loc [_0, ix0]
          LLVM.store ptr0 0 a'

          b' <- go var b
          _0 <- LLVM.int32 0
          ix1 <- LLVM.int32 1
          ptr1 <- LLVM.gep loc [_0, ix1]
          LLVM.store ptr1 0 b'

          toOpaquePtr loc
        Unpack a b -> do
          a' <- fromOpaquePtr (LLVM.ptr closureType) =<< go var a

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

cgWithResult ::
  (MonadModuleBuilder m, MonadIRBuilder m, MonadFix m) =>
  (a -> Operand) ->
  (Operand -> LLVM.IRBuilderT m ()) ->
  LLVM.Type ->
  (Closure a, [LDef a]) ->
  m Operand
cgWithResult var k ktype (val, ds) = do
  closureType <-
    LLVM.typedef "Closure" . Just $
    LLVM.StructureType
      False
      [ LLVM.ptr $ LLVM.FunctionType opaquePtr [opaquePtr, opaquePtr] False
      , opaquePtr
      ]
  malloc <- LLVM.extern "malloc" [LLVM.i32] (LLVM.ptr LLVM.i8)
  rec
    let
      names :: String -> Operand
      names = fromJust . flip Map.lookup ds'
    ds' <- foldrM (\d rest -> (<> rest) <$> cg_def closureType malloc names var d) mempty ds
  LLVM.function "main" [] ktype $ \_ -> do
    val' <- cg_expr closureType malloc names var val
    k val'

cgModule_intres :: String -> (Closure Void, [LDef Void]) -> LLVM.Module
cgModule_intres modName code =
  LLVM.buildModule (fromString modName) .
  LLVM.runIRBuilderT LLVM.emptyIRBuilder $ do
    printInt <- LLVM.extern "printInt" [LLVM.i64] LLVM.void
    cgWithResult
      absurd
      (\res -> do
          n <- flip LLVM.load 0 =<< fromOpaquePtr (LLVM.ptr LLVM.i64) res
          _ <- LLVM.call printInt [(n, [])]
          LLVM.ret =<< LLVM.int64 0)
      LLVM.i64
      code
