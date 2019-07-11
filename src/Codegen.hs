{-# language BangPatterns #-}
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
import Data.Maybe (fromMaybe, fromJust)
import Data.String (fromString)
import Data.Text (Text)
import LLVM.AST.Operand (Operand)
import LLVM.IRBuilder (MonadIRBuilder)
import LLVM.IRBuilder.Module (MonadModuleBuilder)

import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified LLVM.AST as LLVM (Module)
import qualified LLVM.AST.Name as LLVM
import qualified LLVM.AST.Type as LLVM
import qualified LLVM.IRBuilder.Constant as LLVM
import qualified LLVM.IRBuilder.Instruction as LLVM
import qualified LLVM.IRBuilder.Monad as LLVM
import qualified LLVM.IRBuilder.Module as LLVM

import Closure
import Core.Type (Type(..), Kind)
import Operators (Op(..))
import Rep (Rep(..))

opaquePtr :: LLVM.Type
opaquePtr = LLVM.ptr LLVM.i8

toOpaquePtr :: MonadIRBuilder m => Operand -> m Operand
toOpaquePtr o = LLVM.bitcast o opaquePtr

fromOpaquePtr :: MonadIRBuilder m => LLVM.Type -> Operand -> m Operand
fromOpaquePtr = flip LLVM.bitcast

kindToLLVM :: Show a => Kind a -> LLVM.Type
kindToLLVM (TRep _ r) = goRep r
  where
    goRep rep =
      case rep of
        RPtr -> opaquePtr
        RI64 -> LLVM.i64
        RList rs -> LLVM.StructureType False (goRep <$> rs)
kindToLLVM a = error $ "argKindToLLVM: invalid input: " <> show a

closureType :: Show a => Kind a -> Kind a -> LLVM.Type
closureType kin kout =
  let
    !kin' = kindToLLVM kin
    !kout' = kindToLLVM kout
  in
  LLVM.StructureType
    False
    [ LLVM.ptr $ LLVM.FunctionType kout' [opaquePtr, kin'] False
    , opaquePtr
    ]

gennedNames :: (Text -> a) -> Text -> a
gennedNames ns = ns . ("closure$" <>)

definedNames :: (Text -> a) -> Text -> a
definedNames ns = ns . ("def$" <>)

valdefName :: ValDef Text Text -> Text
valdefName (ValDef ln _) = "def$" <> ln

cg_valdef ::
  (MonadModuleBuilder m, MonadIRBuilder m) =>
  Operand ->
  (Text -> Operand) ->
  ValDef Text Text ->
  m Operand
cg_valdef malloc names (ValDef _ lb) =
  cg_expr malloc names lb

cg_fundef ::
  MonadModuleBuilder m =>
  Operand ->
  (Text -> Operand) ->
  FunDef Text Text ->
  m (Map Text Operand)
cg_fundef malloc names (FunDef ln argKind retKind lb) = do
  let
    name = "closure$" <> ln
    funName = LLVM.mkName $ Text.unpack name
    !argTy = kindToLLVM argKind
    argTys = [(opaquePtr, LLVM.NoParameterName), (argTy, LLVM.NoParameterName)]
    retTy = kindToLLVM retKind
  n <-
    LLVM.function funName argTys retTy $ \[env, arg] -> do
      a' <-
        cg_expr_inner
          malloc
          (gennedNames names)
          (pure . unvar (\case; LEnv -> env; LArg -> arg) (definedNames names))
          (fromScope lb)
      LLVM.ret a'
  pure $ Map.singleton name n

cg_expr ::
  forall m.
  (MonadIRBuilder m, MonadModuleBuilder m) =>
  Operand ->
  (Text -> Operand) ->
  Closure Text Text ->
  m Operand
cg_expr malloc names =
  cg_expr_inner malloc (gennedNames names) (pure . definedNames names)

cg_expr_inner ::
  forall m a.
  (MonadIRBuilder m, MonadModuleBuilder m) =>
  Operand ->
  (Text -> Operand) ->
  (a -> m Operand) ->
  Closure Text a ->
  m Operand
cg_expr_inner malloc names = go
  where
    go :: forall b. (b -> m Operand) -> Closure Text b -> m Operand
    go var ex =
      case ex of
        Var a -> var a
        Name a -> pure $ names a
        UInt64 a -> LLVM.int64 (fromIntegral a)
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
        Closure a b kin kout -> do
          size <- LLVM.int32 2
          loc <-
            fromOpaquePtr (LLVM.ptr $ closureType kin kout) =<<
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
        Unpack a b bk abk -> do
          a' <-
            fromOpaquePtr (LLVM.ptr $ closureType bk abk) =<<
            go var a

          _0 <- LLVM.int32 0
          ix0 <- LLVM.int32 0
          ptr0 <- LLVM.gep a' [_0, ix0]
          a1 <- LLVM.load ptr0 0

          _0 <- LLVM.int32 0
          ix1 <- LLVM.int32 1
          ptr1 <- LLVM.gep a' [_0, ix1]
          a2 <- LLVM.load ptr1 0

          go
            (unvar (\case; Fst -> pure a1; Snd -> pure a2) var)
            (fromScope b)

cgWithResult ::
  (MonadModuleBuilder m, MonadIRBuilder m, MonadFix m) =>
  (Operand -> LLVM.IRBuilderT m ()) ->
  LLVM.Type ->
  ([FunDef Text Text], [ValDef Text Text], Closure Text Text) ->
  m Operand
cgWithResult k ktype (fds, vds, val) = do
  malloc <- LLVM.extern "malloc" [LLVM.i32] (LLVM.ptr LLVM.i8)
  rec
    let
      names :: Text -> Operand
      names = fromJust . flip Map.lookup fds'
    fds' <-
      foldrM
        (\d rest -> (<> rest) <$> cg_fundef malloc names d)
        mempty
        fds
  LLVM.function "main" [] ktype $ \_ -> do
    rec
      let names' n = fromMaybe (names n) (Map.lookup n vds')
      vds' <-
        snd <$>
        foldrM
          (\d (next, rest) -> do
              let n = valdefName d
              _ <- LLVM.block `LLVM.named` fromString (Text.unpack n)
              o <- cg_valdef malloc names' d
              LLVM.br next
              pure (LLVM.mkName $ Text.unpack n, Map.insert n o rest))
          ("def$main", mempty)
          vds
    _ <- LLVM.block `LLVM.named` "def$main"
    k =<< cg_expr malloc names' val

cgModule_intres ::
  String ->
  ([FunDef Text Text], [ValDef Text Text], Closure Text Text) ->
  LLVM.Module
cgModule_intres modName code =
  LLVM.buildModule (fromString modName) .
  LLVM.runIRBuilderT LLVM.emptyIRBuilder $ do
    printInt <- LLVM.extern "printInt" [LLVM.i64] LLVM.void
    cgWithResult
      (\res -> do
          n <- fromOpaquePtr LLVM.i64 res
          _ <- LLVM.call printInt [(n, [])]
          LLVM.ret =<< LLVM.int64 0)
      LLVM.i64
      code
