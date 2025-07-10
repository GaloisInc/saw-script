{- |
Module      : SAWCentral.Value
Description : Value datatype for SAW-Script interpreter.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}

module SAWCentral.Value (
    Value(..),

    -- used by SAWCentral.Builtins, SAWScript.Interpreter, SAWServer.SAWServer
    SAWSimpset,
    -- used by SAWCentral.Builtins, SAWScript.Interpreter
    SAWRefnset,
    -- used by SAWCentral.Builtins
    AIGNetwork(..),
    -- used by SAWCentral.Prover.Exporter, SAWCentral.Builtins,
    --    SAWScript.Interpreter and more, SAWServer.SAWServer
    AIGProxy(..),
    -- used by SAWCentral.Crucible.LLVM.Builtins, SAWScript.HeapsterBuiltins
    SAW_CFG(..),
    -- used by SAWScript.Interpreter, SAWScript.HeapsterBuiltins,
    --    SAWServer.SAWServer, SAWServer.*CrucibleSetup
    BuiltinContext(..),
    -- used by SAWScript.HeapsterBuiltins (and the Value type)
    HeapsterEnv(..),
    -- used by SAWCentral.Builtins.hs, and appears in the Value type and showsSatResult
    SatResult(..),
    -- used by SAWCentral.Bisimulation, SAWCentral.Builtins, SAWScript.REPL.Monad
    showsProofResult,
    -- used by SAWCentral.Builtins
    showsSatResult,
    -- used by SAWCentral.Builtins, SAWScript.Interpreter
    showsPrecValue,
    -- used by SAWCentral.Builtins, SAWScript.Interpreter
    evaluateTypedTerm,
    -- used by SAWScript.Interpreter (and in LocalEnv)
    LocalBinding(..),
    -- used by SAWScript.Interpreter, and appears in TopLevelRO
    LocalEnv,
    -- used by SAWScript.Interpreter, and in mergeLocalEnv
    addTypedef,
    -- used by SAWScript.REPL.Monad, and by getMergedEnv
    mergeLocalEnv,
    -- used by SAWCentral.Builtins, SAWScript.Interpreter, and by getCryptolEnv
    getMergedEnv, getMergedEnv',
    -- used by SAWCentral.Crucible.LLVM.FFI
    getCryptolEnv,
    -- used by SAWScript.Automatch, SAWScript.REPL.*, SAWScript.Interpreter,
    --    SAWServer.SAWServer
    TopLevelRO(..),
    -- used by ... a lot of places, let's not try to make a list just yet
    TopLevelRW(..),
    -- used by ... a lot of places, let's not try to make a list just yet
    TopLevel(..),
    -- used by SAWCentral.Builtins, SAWScript.REPL.Monad, SAWScript.Interpreter,
    --    SAWServer.TopLevel
    runTopLevel,
    -- used by ... a lot of places, let's not try to make a list just yet
    io,
    -- used in various places in SAWCentral
    throwTopLevel,
    -- used by SAWScript.Interpreter plus locally in a bunch of GetValue instances
    pushPosition, popPosition,
    -- used by SAWScript.Interpreter plus appears in getMergedEnv
    getLocalEnv,
    -- used in various places in SAWCentral
    getPosition,
    -- used all over the place
    getSharedContext,
    -- used in SAWCentral.Crucible.JVM.Builtins{,JVM} and SAWScript.AutoMatch
    getJavaCodebase,
    -- used in SAWCentral.Builtins
    getTheoremDB,
    -- used in SAWCentral.Builtins
    putTheoremDB,
    -- used in various places in SAWCentral, plus SAWScript.Interpreter
    getOptions,
    -- used in SAWCentral.Prover.Exporter, SAWCentral.Builtins
    getProxy,
    -- used in SAWCentral.Crucible.LLVM.{X86,Builtins}
    getBasicSS,
    -- used in various places in SAWCentral, plus SAWScript.Interpreter
    printOutLnTop,
    -- used in SAWCentral.Crucible.*, SAWCentral.Builtins,
    --    SAWServer.SAWServer, SAWServer.Ghost, SAWServer.LLVMCrucibleSetup
    getHandleAlloc,
    -- used in SAWCentral.Builtins SAWScript.REPL.Monad, SAWScript.AutoMatch
    -- also accessible via SAWCentral.TopLevel
    getTopLevelRO,
    -- used in SAWCentral.Crucible.*.Builtins.hs, SAWCentral.Crucible.X86,
    --    SAWCentral.Bisimulation, SAWCentral.Builtins,
    --    SAWScript.Interpreter, SAWScript.AutoMatch,
    --    SAWServer.Yosys
    getTopLevelRW,
    -- used in SAWCentral.Crucible.LLVM.X86, SAWCentral.Crucible.LLVM.Builtins,
    --    SAWCentral.Builtins, SAWScript.Interpreter
    putTopLevelRW,
    -- used in various places in SAWCentral
    recordTheoremProof, returnTheoremProof, returnLLVMProof, returnJVMProof, returnMIRProof,
    -- used in SAWCentral.Builtins, SAWScript.Interpreter
    onSolverCache,
    -- used by SAWCentral.Crucible.JVM.Builtins*
    getJVMTrans,
    -- used by SAWCentral.Crucible.JVM.Builtins*
    putJVMTrans,
    -- XXX: apparently unused
    addJVMTrans,
    -- used by SAWCentral.Crucible.LLVM.Builtins, SAWScript.Interpreter
    --    ... the use in LLVM is the abusive insertion done by llvm_compositional_extract
    --    XXX: we're going to need to clean that up
    --    (also appears in mergeLocalEnv)
    extendEnv,
    -- used by various places in SAWCentral.Crucible, SAWCentral.Builtins
    --    XXX: it wraps TopLevel rather than being part of it; is that necessary?
    CrucibleSetup,
    -- used in SAWCentral.Crucible.LLVM.*,
    --    SAWServer.SAWServer, SAWServer.LLVMCrucibleSetup
    LLVMCrucibleSetupM(..),
    -- used in SAWCentral.Crucible.*.Builtins
    throwCrucibleSetup,
    -- used in SAWCentral.Crucible.LLVM.Skeleton.Builtins,
    --    SAWCentral.Crucible.LLVM.FFI
    throwLLVMFun,
    -- used in SAWCentral.Crucible.*.Builtins, SAWCentral.Builtins
    getW4Position,
    -- used by SAWServer.SAWServer, SAWServer.JVMVerify, SAWScript.Interpreter
    JVMSetup,
    -- used by SAWCentral.Crucible.JVM.Builtins,
    --    SAWServer.SAWServer, SAWServer.JVMCrucibleSetup
    JVMSetupM(..),
    -- used by SAWCentral.Crucible.MIR.ResolveSetupValue,
    --    SAWServer.SAWServer, SAWServer.MIRVerify, SAWScript.Interpreter
    JavaCodebase(..),
    -- Used to initialize things; probably only need `JavaUninitialized`.
    MIRSetup,
    -- used by SAWCentral.Crucible.MIR.Builtins, SAWServer.MIRCrucibleSetup
    MIRSetupM(..),
    -- used in SAWCentral.Crucible.LLVM.X86, SAWCentral.Crucible.*.Builtins,
    --    SAWCentral.Crucible.Common.Vacuity,
    --    SAWCentral.Bisimulation, SAWCentral.Yosys, SAWCentral.Builtins
    --    SAWScript.REPL.Monad, SAWScript.Typechecker, SAWScript.Interpreter,
    --    SAWServer.SAWServer, SAWServer.ProofScript, SAWServer.*Verify,
    --    SAWServer.VerifyCommon, SAWServer.Yosys, saw-remote-api Main
    ProofScript(..),
    -- used by SAWCentral.Crucible.LLVM.X86, SAWCentral.Crucible.*.Builtins,
    --    SAWCentral.Crucible.Common.Vacuity,
    --    SAWCentral.Bisimulation, SAWCentral.Builtins
    runProofScript,
    -- used by SAWCentral.Builtins, SAWScript.Interpreter
    scriptTopLevel,
    llvmTopLevel,
    jvmTopLevel,
    mirTopLevel,
    -- used in SAWScript.Interpreter
    -- XXX: probably belongs in SAWSupport
    underStateT,
    -- used in SAWScript.ValueOps
    -- XXX: probably belongs in SAWSupport
    underReaderT,
    -- used in SAWScript.Interpreter
    -- XXX: probably belongs in SAWSupport
    underExceptT,
    -- used by SAWCentral.Crucible.LLVM.Skeleton.Builtins
    SkeletonState(..), skelArgs
 ) where

import Prelude hiding (fail)

import Control.Lens
import Control.Monad.Fail (MonadFail(..))
import Control.Monad.Catch (MonadThrow(..), MonadCatch(..), catches, Handler(..))
import Control.Monad.Except (ExceptT(..), runExceptT, MonadError(..))
import Control.Monad.Reader (MonadReader)
import qualified Control.Exception as X
import qualified System.IO.Error as IOError
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.Reader (ReaderT(..), ask, asks)
import Control.Monad.State (StateT(..), MonadState(..), gets, modify)
import Control.Monad.Trans.Class (MonadTrans(lift))
import Data.IORef
import Data.Foldable(foldrM)
import Data.List ( intersperse )
import Data.List.Extra ( dropEnd )
import qualified Data.Map as M
import Data.Map ( Map )
import Data.Set ( Set )
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Parameterized.Some
import Data.Typeable
import qualified Prettyprinter as PP
import System.FilePath((</>))

import qualified Data.AIG as AIG

import qualified SAWSupport.Pretty as PPS (Opts, defaultOpts, showBrackets, showBraces, showCommaSep)

import qualified SAWCentral.AST as SS
import qualified SAWCentral.ASTUtil as SS (substituteTyVars)
import SAWCentral.BisimulationTheorem (BisimTheorem)
import qualified SAWCentral.Exceptions as SS
import qualified SAWCentral.Position as SS
import qualified SAWCentral.Crucible.Common as Common
import qualified SAWCentral.Crucible.Common.Setup.Type as Setup
import qualified SAWCentral.Crucible.Common.MethodSpec as CMS
import qualified SAWCentral.Crucible.LLVM.MethodSpecIR as CMSLLVM
import qualified SAWCentral.Crucible.LLVM.CrucibleLLVM as Crucible
import qualified SAWCentral.Crucible.JVM.MethodSpecIR ()
import qualified SAWCentral.Crucible.MIR.MethodSpecIR ()
import qualified Lang.JVM.Codebase as JSS
import qualified Text.LLVM.AST as LLVM (Type)
import SAWCentral.JavaExpr (JavaType(..))
import SAWCentral.JavaPretty (prettyClass)
import SAWCentral.Options (Options, printOutLn, Verbosity(..))
import qualified SAWCentral.Options as Opt
import SAWCentral.Proof
import SAWCentral.Prover.SolverStats
import SAWCentral.MRSolver.Term (funNameTerm, mrVarCtxInnerToOuter, ppTermAppInCtx)
import SAWCentral.MRSolver.Evidence as MRSolver
import SAWCentral.SolverCache
import SAWCentral.Crucible.LLVM.Skeleton
import SAWCentral.X86 (X86Unsupported(..), X86Error(..))
import SAWCentral.Yosys.IR
import SAWCentral.Yosys.Theorem (YosysImport, YosysTheorem)
import SAWCentral.Yosys.State (YosysSequential)

import SAWCore.Name (toShortName, DisplayNameEnv, emptyDisplayNameEnv)
import CryptolSAWCore.CryptolEnv as CEnv
import CryptolSAWCore.Monadify as Monadify
import SAWCore.FiniteValue (FirstOrderValue, ppFirstOrderValue)
import SAWCore.Rewriter (Simpset, lhsRewriteRule, rhsRewriteRule, listRules)
import SAWCore.SharedTerm
import qualified SAWCore.Term.Pretty as SAWCorePP
import CryptolSAWCore.TypedTerm
import SAWCore.Term.Functor (ModuleName)

import qualified SAWCore.Simulator.Concrete as Concrete
import qualified Cryptol.Eval as C
import qualified Cryptol.Eval.Concrete as C
import CryptolSAWCore.Cryptol (exportValueWithSchema)
import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Utils.Ident as T (mkIdent, packModName)
import Cryptol.Utils.PP (pretty)

import qualified Lang.Crucible.CFG.Core as Crucible (AnyCFG)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator)

import           Lang.Crucible.JVM (JVM)
import qualified Lang.Crucible.JVM as CJ
import qualified Lang.JVM.JavaTools as CJ

import           Lang.Crucible.LLVM.ArraySizeProfile
import qualified Lang.Crucible.LLVM.PrettyPrint as Crucible.LLVM

import           Mir.Generator
import           Mir.Intrinsics (MIR)
import qualified Mir.Mir as MIR

import           What4.ProgramLoc (ProgramLoc(..))

import Heapster.Permissions
import Heapster.SAWTranslation (ChecksFlag,SomeTypedCFG(..))

-- Values ----------------------------------------------------------------------

data Value
  = VBool Bool
  | VString Text
  | VInteger Integer
  | VArray [Value]
  | VTuple [Value]
  | VRecord (Map SS.Name Value)
  | VLambda LocalEnv SS.Pattern SS.Expr
    -- | Function-shaped value that's a Haskell-level function. This
    --   is how builtins appear.
    --
    -- XXX: Calling this "VBuiltin" was optimistic. It actually covers
    -- everything function-shaped that isn't a SAWScript-level lambda,
    -- which includes not just builtins but also the closures used to
    -- implement stack traces and possibly other messes, all of which
    -- should be removed.
  | VBuiltin (Value -> TopLevel Value)
  | VTerm TypedTerm
  | VType Cryptol.Schema
    -- | Returned value in unspecified monad
  | VReturn Value
    -- | Not-yet-executed do-block in unspecified monad
    --
    --   The string is a hack hook for the current implementation of
    --   stack traces. See the commit message that added it for further
    --   information. XXX: to be removed along with the stack trace code
  | VDo SS.Pos (Maybe String) LocalEnv [SS.Stmt]
    -- | Single monadic bind in unspecified monad.
    --   This exists only to support the "for" builtin; see notes there
    --   for why this is so. XXX: remove it once that's no longer needed
  | VBindOnce Value Value
  | VTopLevel (TopLevel Value)
  | VProofScript (ProofScript Value)
  | VSimpset SAWSimpset
  | VRefnset SAWRefnset
  | VTheorem Theorem
  | VBisimTheorem BisimTheorem
  -----
  | VLLVMCrucibleSetup !(LLVMCrucibleSetupM Value)
  | VLLVMCrucibleMethodSpec (CMSLLVM.SomeLLVM CMS.ProvedSpec)
  | VLLVMCrucibleSetupValue (CMSLLVM.AllLLVM CMS.SetupValue)
  -----
  | VJVMSetup !(JVMSetupM Value)
  | VJVMMethodSpec !(CMS.ProvedSpec CJ.JVM)
  | VJVMSetupValue !(CMS.SetupValue CJ.JVM)
  -----
  | VMIRSetup !(MIRSetupM Value)
  | VMIRMethodSpec !(CMS.ProvedSpec MIR)
  | VMIRSetupValue !(CMS.SetupValue MIR)
  -----
  | VLLVMModuleSkeleton ModuleSkeleton
  | VLLVMFunctionSkeleton FunctionSkeleton
  | VLLVMSkeletonState SkeletonState
  | VLLVMFunctionProfile FunctionProfile
  -----
  | VJavaType JavaType
  | VLLVMType LLVM.Type
  | VMIRType MIR.Ty
  | VCryptolModule CryptolModule
  | VJavaClass JSS.Class
  | VLLVMModule (Some CMSLLVM.LLVMModule)
  | VMIRModule RustModule
  | VMIRAdt MIR.Adt
  | VHeapsterEnv HeapsterEnv
  | VSatResult SatResult
  | VProofResult ProofResult
  | VUninterp Uninterp
  | VAIG AIGNetwork
  | VCFG SAW_CFG
  | VGhostVar CMS.GhostGlobal
  | VYosysModule YosysIR
  | VYosysImport YosysImport
  | VYosysSequential YosysSequential
  | VYosysTheorem YosysTheorem

type SAWSimpset = Simpset TheoremNonce
type SAWRefnset = MRSolver.Refnset TheoremNonce

data AIGNetwork where
  AIGNetwork :: (Typeable l, Typeable g, AIG.IsAIG l g) => AIG.Network l g -> AIGNetwork

data AIGProxy where
  AIGProxy :: (Typeable l, Typeable g, AIG.IsAIG l g) => AIG.Proxy l g -> AIGProxy

data SAW_CFG where
  LLVM_CFG :: Crucible.AnyCFG Crucible.LLVM -> SAW_CFG
  JVM_CFG :: Crucible.AnyCFG JVM -> SAW_CFG

data BuiltinContext = BuiltinContext { biSharedContext :: SharedContext
                                     , biBasicSS       :: SAWSimpset
                                     }

-- | All the context maintained by Heapster
data HeapsterEnv = HeapsterEnv {
  heapsterEnvSAWModule :: ModuleName,
  -- ^ The SAW module containing all our Heapster definitions
  heapsterEnvPermEnvRef :: IORef PermEnv,
  -- ^ The current permissions environment
  heapsterEnvLLVMModules :: [Some CMSLLVM.LLVMModule],
  -- ^ The list of underlying 'LLVMModule's that we are translating
  heapsterEnvTCFGs :: IORef [Some SomeTypedCFG],
  -- ^ The typed CFGs for output debugging/IDE info
  heapsterEnvDebugLevel :: IORef DebugLevel,
  -- ^ The current debug level
  heapsterEnvChecksFlag :: IORef ChecksFlag
  -- ^ Whether translation checks are currently enabled
  }

showHeapsterEnv :: HeapsterEnv -> String
showHeapsterEnv env =
  concat $ intersperse "\n\n" $
  map (\some_lm -> case some_lm of
          Some lm -> CMSLLVM.showLLVMModule lm) $
  heapsterEnvLLVMModules env

data SatResult
  = Unsat SolverStats
  | Sat SolverStats [(ExtCns Term, FirstOrderValue)]
  | SatUnknown
    deriving (Show)

showsProofResult :: PPS.Opts -> ProofResult -> ShowS
showsProofResult opts r =
  case r of
    ValidProof _ _ -> showString "Valid"
    InvalidProof _ ts _ -> showString "Invalid: [" . showMulti "" ts
    UnfinishedProof st  -> showString "Unfinished: " . shows (length (psGoals st)) . showString " goals remaining"
  where
    showVal t = shows (ppFirstOrderValue opts t)
    showEqn (x, t) = showEC x . showString " = " . showVal t
    showEC ec = showString (Text.unpack (toShortName (ecName ec)))

    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns

showsSatResult :: PPS.Opts -> SatResult -> ShowS
showsSatResult opts r =
  case r of
    Unsat _ -> showString "Unsat"
    Sat _ ts -> showString "Sat: [" . showMulti "" ts
    SatUnknown  -> showString "Unknown"
  where
    showVal t = shows (ppFirstOrderValue opts t)
    showEC ec = showString (Text.unpack (toShortName (ecName ec)))
    showEqn (x, t) = showEC x . showString " = " . showVal t
    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns

showSimpset :: PPS.Opts -> Simpset a -> String
showSimpset opts ss =
  unlines ("Rewrite Rules" : "=============" : map (show . ppRule) (listRules ss))
  where
    ppRule r =
      PP.pretty '*' PP.<+>
      (PP.nest 2 $ PP.fillSep
       [ ppTerm (lhsRewriteRule r)
       , PP.pretty '=' PP.<+> ppTerm (rhsRewriteRule r) ])
    ppTerm t = SAWCorePP.ppTerm opts t

-- | Pretty-print a 'Refnset' to a 'String'
showRefnset :: PPS.Opts -> MRSolver.Refnset a -> String
showRefnset opts ss =
  unlines ("Refinements" : "=============" : map (show . ppFunAssump)
                                                 (MRSolver.listFunAssumps ss))
  where
    ppFunAssump (MRSolver.FunAssump ctx f args rhs _) =
      PP.pretty '*' PP.<+>
      (PP.nest 2 $ PP.fillSep
       [ ppTermAppInCtx opts ctx (funNameTerm f) args
       , PP.pretty ("|=" :: String) PP.<+> ppFunAssumpRHS ctx rhs ])
    ppFunAssumpRHS ctx (OpaqueFunAssump f args) =
      ppTermAppInCtx opts ctx (funNameTerm f) args
    ppFunAssumpRHS ctx (RewriteFunAssump rhs) =
      SAWCorePP.ppTermInCtx opts (map fst $ mrVarCtxInnerToOuter ctx) rhs

-- XXX the precedence in here needs to be cleaned up
showsPrecValue :: PPS.Opts -> DisplayNameEnv -> Int -> Value -> ShowS
showsPrecValue opts nenv p v =
  case v of
    VBool True -> showString "true"
    VBool False -> showString "false"
    VString s -> shows s
    VInteger n -> shows n
    VArray vs -> PPS.showBrackets $ PPS.showCommaSep $ map (showsPrecValue opts nenv 0) vs
    VTuple vs -> showParen True $ PPS.showCommaSep $ map (showsPrecValue opts nenv 0) vs
    VRecord m ->
      PPS.showBraces $ PPS.showCommaSep $ map showFld (M.toList m)
        where
          showFld (n, fv) =
            showString (Text.unpack n) . showString "=" . showsPrecValue opts nenv 0 fv

    VLambda _env pat e ->
      let pat' = PP.pretty pat
          e' = PP.pretty e
      in
      shows $ PP.sep ["\\", pat', "->", e']

    VBuiltin {} -> showString "<<builtin>>"
    VTerm t -> showString (SAWCorePP.showTermWithNames opts nenv (ttTerm t))
    VType sig -> showString (pretty sig)
    VReturn v' -> showString "return " . showsPrecValue opts nenv (p + 1) v'
    VDo pos _name _env stmts ->
      let e = SS.Block pos stmts in
      shows (PP.pretty e)
    VBindOnce v1 v2 ->
      let v1' = showsPrecValue opts nenv 0 v1
          v2' = showsPrecValue opts nenv 0 v2
      in
      v1' . showString " >>= " . v2'
    VTopLevel {} -> showString "<<TopLevel>>"
    VSimpset ss -> showString (showSimpset opts ss)
    VRefnset ss -> showString (showRefnset opts ss)
    VProofScript {} -> showString "<<proof script>>"
    VTheorem thm ->
      showString "Theorem " .
      showParen True (showString (prettyProp opts nenv (thmProp thm)))
    VBisimTheorem _ -> showString "<<Bisimulation theorem>>"
    VLLVMCrucibleSetup{} -> showString "<<Crucible Setup>>"
    VLLVMCrucibleSetupValue{} -> showString "<<Crucible SetupValue>>"
    VLLVMCrucibleMethodSpec{} -> showString "<<Crucible MethodSpec>>"
    VLLVMModuleSkeleton s -> shows s
    VLLVMFunctionSkeleton s -> shows s
    VLLVMSkeletonState _ -> showString "<<Skeleton state>>"
    VLLVMFunctionProfile _ -> showString "<<Array sizes for function>>"
    VJavaType {} -> showString "<<Java type>>"
    VLLVMType t -> showString (show (Crucible.LLVM.ppType t))
    VMIRType t -> showString (show (PP.pretty t))
    VCryptolModule m -> showString (showCryptolModule m)
    VLLVMModule (Some m) -> showString (CMSLLVM.showLLVMModule m)
    VMIRModule m -> shows (PP.pretty (m^.rmCS^.collection))
    VMIRAdt adt -> shows (PP.pretty adt)
    VHeapsterEnv env -> showString (showHeapsterEnv env)
    VJavaClass c -> shows (prettyClass c)
    VProofResult r -> showsProofResult opts r
    VSatResult r -> showsSatResult opts r
    VUninterp u -> showString "Uninterp: " . shows u
    VAIG _ -> showString "<<AIG>>"
    VCFG (LLVM_CFG g) -> showString (show g)
    VCFG (JVM_CFG g) -> showString (show g)
    VGhostVar x -> showParen (p > 10)
                 $ showString "Ghost " . showsPrec 11 x
    VYosysModule _ -> showString "<<Yosys module>>"
    VYosysImport _ -> showString "<<Yosys import>>"
    VYosysSequential _ -> showString "<<Yosys sequential>>"
    VYosysTheorem _ -> showString "<<Yosys theorem>>"
    VJVMSetup _      -> showString "<<JVM Setup>>"
    VJVMMethodSpec _ -> showString "<<JVM MethodSpec>>"
    VJVMSetupValue x -> shows x
    VMIRSetup{} -> showString "<<MIR Setup>>"
    VMIRMethodSpec{} -> showString "<<MIR MethodSpec>>"
    VMIRSetupValue x -> shows x

instance Show Value where
    showsPrec p v = showsPrecValue PPS.defaultOpts emptyDisplayNameEnv p v

evaluateTerm:: SharedContext -> Term -> IO Concrete.CValue
evaluateTerm sc t =
  (\modmap -> Concrete.evalSharedTerm modmap mempty mempty t) <$>
  scGetModuleMap sc

evaluateTypedTerm :: SharedContext -> TypedTerm -> IO C.Value
evaluateTypedTerm sc (TypedTerm (TypedTermSchema schema) trm) =
  C.runEval mempty . exportValueWithSchema schema =<< evaluateTerm sc trm
evaluateTypedTerm _sc (TypedTerm tp _) =
  fail $ unlines [ "Could not evaluate term with type"
                 , show (ppTypedTermType tp)
                 ]


-- TopLevel Monad --------------------------------------------------------------

data LocalBinding
  = LocalLet SS.LName SS.Schema (Maybe String) Value
  | LocalTypedef SS.Name SS.Type
 deriving (Show)

type LocalEnv = [LocalBinding]

-- Note that the expansion type should have already been through the
-- typechecker, so it's ok to panic if it turns out to be broken.
addTypedef :: SS.Name -> SS.Type -> TopLevelRW -> TopLevelRW
addTypedef name ty rw =
  let primsAvail = rwPrimsAvail rw
      typeInfo = rwTypeInfo rw
      ty' = SS.substituteTyVars primsAvail typeInfo ty
      typeInfo' = M.insert name (SS.Current, SS.ConcreteType ty') typeInfo
  in
  rw { rwTypeInfo = typeInfo' }

mergeLocalEnv :: SharedContext -> LocalEnv -> TopLevelRW -> IO TopLevelRW
mergeLocalEnv sc env rw = foldrM addBinding rw env
  where addBinding (LocalLet x ty md v) = extendEnv sc x ty md v
        addBinding (LocalTypedef n ty) = pure . addTypedef n ty

-- XXX: it is not sane to both be in the TopLevel monad and return a TopLevelRW
-- (especially since the one returned is specifically not the same as the one
-- in the monad state)
getMergedEnv :: TopLevel TopLevelRW
getMergedEnv =
  do sc <- getSharedContext
     env <- getLocalEnv
     rw <- getTopLevelRW
     liftIO $ mergeLocalEnv sc env rw

-- Variant of getMergedEnv that takes an explicit local part
-- (this avoids trying to use it with withLocalEnv, which doesn't work)
getMergedEnv' :: LocalEnv -> TopLevel TopLevelRW
getMergedEnv' env = do
    sc <- getSharedContext
    rw <- getTopLevelRW
    liftIO $ mergeLocalEnv sc env rw

getCryptolEnv :: TopLevel CEnv.CryptolEnv
getCryptolEnv = do
  env <- getMergedEnv
  return $ rwCryptol env

-- | TopLevel Read-Only Environment.
data TopLevelRO =
  TopLevelRO
  { roOptions       :: Options
  , roHandleAlloc   :: Crucible.HandleAllocator
  , roProxy         :: AIGProxy
  , roInitWorkDir   :: FilePath
  , roBasicSS       :: SAWSimpset
  , roSubshell      :: TopLevel ()
    -- ^ An action for entering a subshell.  This
    --   may raise an error if the current execution
    --   mode doesn't support subshells (e.g., the remote API)

  , roProofSubshell :: ProofScript ()
    -- ^ An action for entering a subshell in proof mode.  This
    --   may raise an error if the current execution
    --   mode doesn't support subshells (e.g., the remote API)

  }

-- | Current state of the Java sub-system.
data JavaCodebase =
    JavaUninitialized
    -- ^ No Java-related commands have been invoked yet.
  | JavaInitialized JSS.Codebase
    -- ^ At least one Java-related command has been invoked successfully.
    -- We cache the resulting 'JSS.Codebase' for subsequent commands.

data TopLevelRW =
  TopLevelRW
  { rwValueInfo  :: Map SS.LName (SS.PrimitiveLifecycle, SS.Schema, Value)
  , rwTypeInfo   :: Map SS.Name (SS.PrimitiveLifecycle, SS.NamedType)
  , rwDocs       :: Map SS.Name String
  , rwCryptol    :: CEnv.CryptolEnv
  , rwPosition   :: SS.Pos
  , rwStackTrace :: [String]
    -- ^ SAWScript-internal backtrace for use
    --   when displaying exceptions and such
    --   NB, stored with most recent calls on
    --   top of the stack.
  , rwLocalEnv   :: LocalEnv

  , rwJavaCodebase  :: JavaCodebase -- ^ Current state of Java sub-system.

  , rwMonadify   :: Monadify.MonadifyEnv
  , rwMRSolverEnv :: MRSolver.MREnv
  , rwProofs  :: [Value] {- ^ Values, generated anywhere, that represent proofs. -}
  , rwPPOpts  :: PPS.Opts
  , rwSharedContext :: SharedContext
  , rwSolverCache :: Maybe SolverCache
  , rwTheoremDB :: TheoremDB

  -- , rwCrucibleLLVMCtx :: Crucible.LLVMContext
  , rwJVMTrans :: CJ.JVMContext
  -- ^ crucible-jvm: Handles and info for classes that have already been translated
  , rwPrimsAvail :: Set SS.PrimitiveLifecycle
  , rwSMTArrayMemoryModel :: Bool
  , rwCrucibleAssertThenAssume :: Bool
  , rwProfilingFile :: Maybe FilePath
  , rwLaxArith :: Bool
  , rwLaxLoadsAndStores :: Bool
  , rwLaxPointerOrdering :: Bool
  , rwDebugIntrinsics :: Bool

  -- FIXME: These might be better split into "simulator hash-consing" and "tactic hash-consing"
  , rwWhat4HashConsing :: Bool
  , rwWhat4HashConsingX86 :: Bool

  , rwWhat4Eval :: Bool

  , rwPreservedRegs :: [Text]
  , rwStackBaseAlign :: Integer

  , rwAllocSymInitCheck :: Bool

  , rwWhat4PushMuxOps :: Bool
  , rwNoSatisfyingWriteFreshConstant :: Bool

  , rwCrucibleTimeout :: Integer

  , rwPathSatSolver :: Common.PathSatSolver
  , rwSkipSafetyProofs :: Bool
  , rwSingleOverrideSpecialCase :: Bool
  , rwSequentGoals :: Bool
  }

newtype TopLevel a =
  TopLevel_ (ReaderT TopLevelRO (StateT TopLevelRW IO) a)
 deriving (Applicative, Functor, Monad, MonadThrow, MonadCatch)

deriving instance MonadReader TopLevelRO TopLevel
deriving instance MonadState TopLevelRW TopLevel

instance MonadFail TopLevel where
  fail = throwTopLevel

runTopLevel :: TopLevel a -> TopLevelRO -> TopLevelRW -> IO (a, TopLevelRW)
runTopLevel (TopLevel_ m) ro rw =
  runStateT (runReaderT m ro) rw

instance MonadIO TopLevel where
  liftIO = io

io :: IO a -> TopLevel a
io f = (TopLevel_ (liftIO f))
       `catches`
       [ Handler (\(ex :: X86Unsupported) -> handleX86Unsupported ex)
       , Handler (\(ex :: X86Error) -> handleX86Error ex)
       , Handler handleTopLevel
       , Handler handleIO
       ]
  where
    rethrow :: X.Exception ex => ex -> TopLevel a
    rethrow ex =
      do stk <- getStackTrace
         throwM (SS.TraceException stk (X.SomeException ex))

    handleTopLevel :: SS.TopLevelException -> TopLevel a
    handleTopLevel e = rethrow e

    handleIO :: X.IOException -> TopLevel a
    handleIO e
      | IOError.isUserError e =
          do pos <- getPosition
             rethrow (SS.TopLevelException pos (dropEnd 1 . drop 12 $ show e))
      | otherwise = rethrow e

    handleX86Unsupported (X86Unsupported path s) =
      do let pos = SS.FileOnlyPos path
         rethrow (SS.TopLevelException pos ("Unsupported x86 feature: " ++ s))

    handleX86Error (X86Error path optfunc s) =
      do let pos = case optfunc of
               Nothing -> SS.FileOnlyPos path
               Just func -> SS.FileAndFunctionPos path (Text.unpack func)
         rethrow (SS.TopLevelException pos ("Error in x86 code: " ++ Text.unpack s))

throwTopLevel :: String -> TopLevel a
throwTopLevel msg = do
  pos <- getPosition
  stk <- getStackTrace
  throwM (SS.TraceException stk (X.SomeException (SS.TopLevelException pos msg)))

-- deprecated
--withPosition :: SS.Pos -> TopLevel a -> TopLevel a
--withPosition pos (TopLevel_ m) = TopLevel_ (local (\ro -> ro{ roPosition = pos }) m)

-- | Replacement pair for withPosition.
--   Usage:
--      savepos = pushPosition newpos
--      ...
--      popPosition savepos
--
pushPosition :: SS.Pos -> TopLevel SS.Pos
pushPosition newpos = do
  oldpos <- gets rwPosition
  modifyTopLevelRW (\rw -> rw { rwPosition = newpos })
  return oldpos

popPosition :: SS.Pos -> TopLevel ()
popPosition restorepos = do
  modifyTopLevelRW (\rw -> rw { rwPosition = restorepos })

getLocalEnv :: TopLevel LocalEnv
getLocalEnv =
  gets rwLocalEnv

getPosition :: TopLevel SS.Pos
getPosition =
  gets rwPosition

getStackTrace :: TopLevel [String]
getStackTrace =
  reverse <$> gets rwStackTrace

getSharedContext :: TopLevel SharedContext
getSharedContext = TopLevel_ (rwSharedContext <$> get)

getJavaCodebase :: TopLevel JSS.Codebase
getJavaCodebase =
  do
    status <- gets rwJavaCodebase
    case status of
      JavaInitialized s -> pure s
      JavaUninitialized   ->
        do
          opts <- getOptions
          mb   <- liftIO (X.try (initJava opts))
          case mb of
            Right jcb ->
              modifyTopLevelRW (\s -> s { rwJavaCodebase = JavaInitialized jcb }) >>
              pure jcb
            Left err ->
              fail $ unlines $
                "Error: failed to initialize Java." :
                [ "  " ++ l | l <- lines (X.displayException (err :: X.SomeException)) ]
  where
  -- If a Java executable's path is specified (either by way of
  -- --java-bin-dirs or PATH, see the Haddocks for findJavaIn), then use that
  -- to detect the path to Java's standard rt.jar file and add it to the
  -- jarList on Java 8 or earlier. (Later versions of Java do not use
  -- rt.jar—see Note [Loading classes from JIMAGE files] in
  -- Lang.JVM.Codebase in crucible-jvm.)
  -- If Java's path is not specified, return the Options unchanged.
  initJava opts =
    do
      mbJavaPath <- CJ.findJavaIn (Opt.javaBinDirs opts)
      javaPath <-
        case mbJavaPath of
          Nothing   -> fail "Failed to find a `java` executable."
          Just path -> pure path
      version <- CJ.findJavaMajorVersion javaPath
      jars <-
        -- rt.jar lives in a standard location relative to @java.home@. At least,
        -- this is the case on every operating system I've tested.
        if version < 9 then
          do
            mbJavaHome <- CJ.findJavaProperty javaPath "java.home"
            case mbJavaHome of
              Nothing ->
                fail ("Could not find where rt.jar lives for " ++ javaPath)
              Just javaHome ->
                let jar = javaHome </> "lib" </> "rt.jar"
                in pure (jar : Opt.jarList opts)
        else pure (Opt.jarList opts)
      JSS.loadCodebase jars (Opt.classPath opts) (Opt.javaBinDirs opts)

          


getTheoremDB :: TopLevel TheoremDB
getTheoremDB = gets rwTheoremDB

putTheoremDB :: TheoremDB -> TopLevel ()
putTheoremDB db = modifyTopLevelRW (\tl -> tl { rwTheoremDB = db })

getOptions :: TopLevel Options
getOptions = TopLevel_ (asks roOptions)

getProxy :: TopLevel AIGProxy
getProxy = TopLevel_ (asks roProxy)

getBasicSS :: TopLevel SAWSimpset
getBasicSS = TopLevel_ (asks roBasicSS)

printOutLnTop :: Verbosity -> String -> TopLevel ()
printOutLnTop v s =
    do opts <- getOptions
       io $ printOutLn opts v s

getHandleAlloc :: TopLevel Crucible.HandleAllocator
getHandleAlloc = TopLevel_ (asks roHandleAlloc)

getTopLevelRO :: TopLevel TopLevelRO
getTopLevelRO = TopLevel_ ask

getTopLevelRW :: TopLevel TopLevelRW
getTopLevelRW = get

putTopLevelRW :: TopLevelRW -> TopLevel ()
putTopLevelRW rw = put rw

modifyTopLevelRW :: (TopLevelRW -> TopLevelRW) -> TopLevel ()
modifyTopLevelRW = modify

-- FUTURE: maybe change these back to using IsValue when things are less tangly
--
-- Note that the "return" variants record the proof as well as just returning it.

recordProof :: Value -> TopLevel ()
recordProof v =
  do rw <- getTopLevelRW
     putTopLevelRW rw { rwProofs = v : rwProofs rw }

returnTheoremProof :: Theorem -> TopLevel Theorem
returnTheoremProof thm = recordProof (VTheorem thm) >> return thm

recordTheoremProof :: Theorem -> TopLevel ()
recordTheoremProof thm = recordProof (VTheorem thm)

returnLLVMProof :: CMSLLVM.SomeLLVM CMS.ProvedSpec -> TopLevel (CMSLLVM.SomeLLVM CMS.ProvedSpec)
returnLLVMProof ms = recordProof (VLLVMCrucibleMethodSpec ms) >> return ms

returnJVMProof :: CMS.ProvedSpec CJ.JVM -> TopLevel (CMS.ProvedSpec CJ.JVM)
returnJVMProof ms = recordProof (VJVMMethodSpec ms) >> return ms

returnMIRProof :: CMS.ProvedSpec MIR -> TopLevel (CMS.ProvedSpec MIR)
returnMIRProof ms = recordProof (VMIRMethodSpec ms) >> return ms

-- | Perform an operation on the 'SolverCache', returning a default value or
-- failing (depending on the first element of the 'SolverCacheOp') if there
-- is no enabled 'SolverCache'
onSolverCache :: SolverCacheOp a -> TopLevel a
onSolverCache cacheOp =
  do opts <- getOptions
     rw <- getTopLevelRW
     case rwSolverCache rw of
       Just cache -> do (a, cache') <- io $ solverCacheOp cacheOp opts cache
                        putTopLevelRW rw { rwSolverCache = Just cache' }
                        return a
       Nothing -> case solverCacheOpDefault cacheOp of
        Just a -> return a
        Nothing -> fail "Solver result cache not enabled!"

-- | Access the current state of Java Class translation
getJVMTrans :: TopLevel CJ.JVMContext
getJVMTrans = gets rwJVMTrans

-- | Access the current state of Java Class translation
putJVMTrans :: CJ.JVMContext -> TopLevel ()
putJVMTrans jc =
  do rw <- getTopLevelRW
     putTopLevelRW rw { rwJVMTrans = jc }

-- | Add a newly translated class to the translation
addJVMTrans :: CJ.JVMContext -> TopLevel ()
addJVMTrans trans = do
  rw <- getTopLevelRW
  let jvmt = rwJVMTrans rw
  putTopLevelRW ( rw { rwJVMTrans = trans <> jvmt })

maybeInsert :: Ord k => k -> Maybe a -> Map k a -> Map k a
maybeInsert _ Nothing m = m
maybeInsert k (Just x) m = M.insert k x m

extendEnv ::
  SharedContext ->
  SS.LName -> SS.Schema -> Maybe String -> Value -> TopLevelRW -> IO TopLevelRW
extendEnv sc x ty md v rw =
  do ce' <-
       case v of
         VTerm t ->
           pure $ CEnv.bindTypedTerm (ident, t) ce
         VType s ->
           pure $ CEnv.bindType (ident, s) ce
         VInteger n ->
           pure $ CEnv.bindInteger (ident, n) ce
         VCryptolModule m ->
           pure $ CEnv.bindCryptolModule (modname, m) ce
         VString s ->
           do tt <- typedTermOfString sc (Text.unpack s)
              pure $ CEnv.bindTypedTerm (ident, tt) ce
         VBool b ->
           do tt <- typedTermOfBool sc b
              pure $ CEnv.bindTypedTerm (ident, tt) ce
         _ ->
           pure ce
     pure $
      rw { rwValueInfo  = M.insert name (SS.Current, ty, v) (rwValueInfo rw)
         , rwDocs    = maybeInsert (SS.getVal name) md (rwDocs rw)
         , rwCryptol = ce'
         }
  where
    name = x
    -- XXX why is this using getOrig?
    ident = T.mkIdent (SS.getOrig x)
    modname = T.packModName [SS.getOrig x]
    ce = rwCryptol rw

typedTermOfString :: SharedContext -> String -> IO TypedTerm
typedTermOfString sc str =
  do let schema = Cryptol.tMono (Cryptol.tString (length str))
     bvNat <- scGlobalDef sc "Prelude.bvNat"
     bvNat8 <- scApply sc bvNat =<< scNat sc 8
     byteT <- scBitvector sc 8
     let scChar c = scApply sc bvNat8 =<< scNat sc (fromIntegral (fromEnum c))
     ts <- traverse scChar str
     trm <- scVector sc byteT ts
     pure (TypedTerm (TypedTermSchema schema) trm)

typedTermOfBool :: SharedContext -> Bool -> IO TypedTerm
typedTermOfBool sc b =
  do let schema = Cryptol.tMono Cryptol.tBit
     trm <- scBool sc b
     pure (TypedTerm (TypedTermSchema schema) trm)


-- Other SAWScript Monads ------------------------------------------------------

type CrucibleSetup ext = Setup.CrucibleSetupT ext TopLevel

-- | 'CrucibleMethodSpecIR' requires a specific syntax extension, but our method
--   specifications should be polymorphic in the underlying architecture
-- type LLVMCrucibleMethodSpecIR = CMSLLVM.AllLLVM CMS.CrucibleMethodSpecIR

newtype LLVMCrucibleSetupM a =
  LLVMCrucibleSetupM
    { runLLVMCrucibleSetupM ::
        forall arch.
        (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
        CrucibleSetup (CMSLLVM.LLVM arch) a
    }
  deriving Functor

instance Applicative LLVMCrucibleSetupM where
  pure x = LLVMCrucibleSetupM (pure x)
  LLVMCrucibleSetupM f <*> LLVMCrucibleSetupM m = LLVMCrucibleSetupM (f <*> m)

instance Monad LLVMCrucibleSetupM where
  return = pure
  LLVMCrucibleSetupM m >>= f =
    LLVMCrucibleSetupM (m >>= \x -> runLLVMCrucibleSetupM (f x))

-- XXX this is required for the moment in the interpreter, and should
-- be removed when we clean out error handling.
instance MonadFail LLVMCrucibleSetupM where
   fail msg = LLVMCrucibleSetupM $ lift $ lift $ fail msg

throwCrucibleSetup :: ProgramLoc -> String -> CrucibleSetup ext a
throwCrucibleSetup loc msg = X.throw $ SS.CrucibleSetupException loc msg

throwLLVM :: ProgramLoc -> String -> LLVMCrucibleSetupM a
throwLLVM loc msg = LLVMCrucibleSetupM $ throwCrucibleSetup loc msg

throwLLVMFun :: Text -> String -> LLVMCrucibleSetupM a
throwLLVMFun nm msg = do
  loc <- LLVMCrucibleSetupM $ getW4Position nm
  throwLLVM loc msg

-- | Get the current interpreter position and convert to a What4 position.
getW4Position :: Text -> CrucibleSetup arch ProgramLoc
getW4Position s = do
  pos <- lift $ lift $ getPosition
  return $ SS.toW4Loc s pos

--

type JVMSetup = CrucibleSetup CJ.JVM

newtype JVMSetupM a = JVMSetupM { runJVMSetupM :: JVMSetup a }
  deriving (Applicative, Functor, Monad)

-- XXX this is required for the moment in the interpreter, and should
-- be removed when we clean out error handling.
instance MonadFail JVMSetupM where
   fail msg = JVMSetupM $ lift $ lift $ fail msg

--

type MIRSetup = CrucibleSetup MIR

newtype MIRSetupM a = MIRSetupM { runMIRSetupM :: MIRSetup a }
  deriving (Applicative, Functor, Monad)

-- XXX this is required for the moment in the interpreter, and should
-- be removed when we clean out error handling.
instance MonadFail MIRSetupM where
   fail msg = MIRSetupM $ lift $ lift $ fail msg

--
newtype ProofScript a = ProofScript { unProofScript :: ExceptT (SolverStats, CEX) (StateT ProofState TopLevel) a }
 deriving (Functor, Applicative, Monad)

-- TODO: remove the "reason" parameter and compute it from the
--       initial proof goal instead
runProofScript ::
  ProofScript a ->
  Prop ->
  ProofGoal ->
  Maybe ProgramLoc ->
  Text ->
  Bool {- ^ record the theorem in the database? -} ->
  Bool {- ^ do we need to normalize the sequent goal? -} ->
  TopLevel ProofResult
runProofScript (ProofScript m) concl gl ploc rsn recordThm useSequentGoals =
  do pos <- getPosition
     ps <- io (startProof gl pos ploc rsn)
     (r,pstate) <- runStateT (runExceptT m) ps
     case r of
       Left (stats,cex) -> return (SAWCentral.Proof.InvalidProof stats cex pstate)
       Right _ ->
         do sc <- getSharedContext
            db <- getTheoremDB
            what4PushMuxOps <- gets rwWhat4PushMuxOps
            (thmResult, db') <- io (finishProof sc db concl pstate recordThm useSequentGoals what4PushMuxOps)
            putTheoremDB db'
            pure thmResult


scriptTopLevel :: TopLevel a -> ProofScript a
scriptTopLevel m = ProofScript (lift (lift m))

llvmTopLevel :: TopLevel a -> LLVMCrucibleSetupM a
llvmTopLevel m = LLVMCrucibleSetupM (lift (lift m))

jvmTopLevel :: TopLevel a -> JVMSetupM a
jvmTopLevel m = JVMSetupM (lift (lift m))

mirTopLevel :: TopLevel a -> MIRSetupM a
mirTopLevel m = MIRSetupM (lift (lift m))

instance MonadIO ProofScript where
  liftIO m = ProofScript (liftIO m)

instance MonadFail ProofScript where
  fail msg = ProofScript (fail msg)

instance MonadState ProofState ProofScript where
  get = ProofScript get
  put x = ProofScript (put x)

instance MonadError (SolverStats, CEX) ProofScript where
  throwError cex = ProofScript (throwError cex)
  catchError (ProofScript m) f = ProofScript (catchError m (unProofScript . f))


-- Error handling --------------------------------------------------------------

underStateT :: (forall b. m b -> m b) -> StateT s m a -> StateT s m a
underStateT doUnder action = StateT $ \s -> doUnder (runStateT action s)

underReaderT :: (forall b. m b -> m b) -> ReaderT s m a -> ReaderT s m a
underReaderT doUnder action = ReaderT $ \env -> doUnder (runReaderT action env)

underExceptT :: (forall b. m b -> m b) -> ExceptT s m a -> ExceptT s m a
underExceptT doUnder action = ExceptT $ doUnder (runExceptT action)


data SkeletonState = SkeletonState
  { _skelArgs :: [(Maybe TypedTerm, Maybe (CMSLLVM.AllLLVM CMS.SetupValue), Maybe Text)]
  }
makeLenses ''SkeletonState
