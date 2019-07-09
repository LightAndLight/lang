module Compile where

import Data.Foldable (traverse_)
import Data.Void (Void)
import LLVM.Pretty (ppllvm)
import System.Exit (exitFailure)
import System.Process (callProcess)

import qualified Data.Text.Lazy.IO as LazyText
import qualified LLVM.AST as LLVM
import qualified LLVM.Context as LLVM
import qualified LLVM.Module as LLVM
import qualified LLVM.Target as LLVM

import Closure
import Elaborate
import Syntax
import Core (Core)
import Core.Type
import Codegen

checkType :: Syntax Void Void -> Type Void -> IO (Core Void Void)
checkType ex ty = do
  let ee = elab newElabEnv (check ex ty)
  traverse_ print (eWarnings ee)
  either (\err -> print err *> exitFailure) pure $ eResult ee

genLLVM :: FilePath -> Syntax Void Void -> IO ()
genLLVM fp ex = do
  core <- checkType ex TUInt64
  LLVM.withHostTargetMachine $ \tm -> do
    tt <- LLVM.getTargetMachineTriple tm
    let _mod = (cgModule_intres fp $ trans core) { LLVM.moduleTargetTriple = Just tt }
    LazyText.writeFile fp $ ppllvm _mod

genObject :: FilePath -> Syntax Void Void -> IO ()
genObject fp ex = do
  core <- checkType ex TUInt64
  LLVM.withHostTargetMachine $ \tm ->
    LLVM.withContext $ \ctx -> do
      tt <- LLVM.getTargetMachineTriple tm
      let _mod = (cgModule_intres fp $ trans core) { LLVM.moduleTargetTriple = Just tt }
      LLVM.withModuleFromAST ctx _mod $ \_mod' ->
        LLVM.writeObjectToFile tm (LLVM.File fp) _mod'

genBinary :: FilePath -> Syntax Void Void -> IO ()
genBinary fp ex = do
  let obj = fp <> ".o"
  genObject obj ex
  callProcess "clang" ["lib/support.c", obj, "-o", fp]
