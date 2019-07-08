module Compile where

import Data.Void (Void)
import LLVM.Pretty (ppllvm)
import System.Process (callProcess)

import qualified Data.Text.Lazy.IO as LazyText
import qualified LLVM.AST as LLVM
import qualified LLVM.Context as LLVM
import qualified LLVM.Module as LLVM
import qualified LLVM.Target as LLVM

import Syntax
import Codegen

genLLVM :: FilePath -> Syntax Void -> IO ()
genLLVM fp ex =
  LLVM.withHostTargetMachine $ \tm -> do
    tt <- LLVM.getTargetMachineTriple tm
    let _mod = (cgModule $ trans ex) { LLVM.moduleTargetTriple = Just tt }
    LazyText.writeFile fp $ ppllvm _mod

genObject :: FilePath -> Syntax Void -> IO ()
genObject fp ex =
  LLVM.withHostTargetMachine $ \tm ->
  LLVM.withContext $ \ctx -> do
    tt <- LLVM.getTargetMachineTriple tm
    let _mod = (cgModule $ trans ex) { LLVM.moduleTargetTriple = Just tt }
    LLVM.withModuleFromAST ctx _mod $ \_mod' ->
      LLVM.writeObjectToFile tm (LLVM.File fp) _mod'

genBinary :: FilePath -> Syntax Void -> IO ()
genBinary fp ex = do
  let obj = fp <> ".o"
  genObject obj ex
  callProcess "clang" ["lib/support.c", obj, "-o", fp]