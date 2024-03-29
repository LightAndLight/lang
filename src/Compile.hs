module Compile where

import Data.Foldable (traverse_)
import Data.Text (Text)
import LLVM.Pretty (ppllvm)
import System.Exit (exitFailure)
import System.Process (callProcess)

import qualified Data.Text.Lazy.IO as LazyText
import qualified LLVM.AST as LLVM
import qualified LLVM.Context as LLVM
import qualified LLVM.Module as LLVM
import qualified LLVM.Target as LLVM

import Closure (transProgram)
import qualified Closure
import Elaborate
import Syntax
import Syntax.Type
import Codegen

checkProgram ::
  ([Def Text Text], Syntax Text Text) ->
  Type Text ->
  IO
    ( [Closure.FunDef Text Text]
    , [Closure.ValDef Text Text]
    , Closure.Closure Text Text
    )
checkProgram (ds, ex) ty = do
  let ee = elab (newElabEnv id id) (checkDefsThen id ds $ check ex . fst =<< inferKind ty)
  traverse_ print (eWarnings ee)
  prog <- either (\err -> print err *> exitFailure) pure $ eResult ee
  either (\err -> print err *> exitFailure) pure $ transProgram undefined prog

genLLVM :: FilePath -> ([Def Text Text], Syntax Text Text) -> IO ()
genLLVM fp prog = do
  prog' <- checkProgram prog TUInt64
  LLVM.withHostTargetMachine $ \tm -> do
    tt <- LLVM.getTargetMachineTriple tm
    let _mod = (cgModule_intres fp prog') { LLVM.moduleTargetTriple = Just tt }
    LazyText.writeFile fp $ ppllvm _mod

genObject :: FilePath -> ([Def Text Text], Syntax Text Text) -> IO ()
genObject fp prog = do
  prog' <- checkProgram prog TUInt64
  LLVM.withHostTargetMachine $ \tm ->
    LLVM.withContext $ \ctx -> do
      tt <- LLVM.getTargetMachineTriple tm
      let _mod = (cgModule_intres fp prog') { LLVM.moduleTargetTriple = Just tt }
      LLVM.withModuleFromAST ctx _mod $ \_mod' ->
        LLVM.writeObjectToFile tm (LLVM.File fp) _mod'

genBinary :: FilePath -> ([Def Text Text], Syntax Text Text) -> IO ()
genBinary fp ex = do
  let obj = fp <> ".o"
  genObject obj ex
  callProcess "clang" ["lib/support.c", obj, "-o", fp]
