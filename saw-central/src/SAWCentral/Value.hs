{- |
Module      : SAWCentral.Value
Description : Value datatype for SAW-Script interpreter.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module SAWCentral.Value (
    BuiltinWrapper(..),
    Value(..),

    -- used by SAWCentral.Builtins, SAWScript.Interpreter, SAWServer.SAWServer
    SAWSimpset,
    -- used by SAWCentral.Builtins
    AIGNetwork(..),
    -- used by SAWCentral.Prover.Exporter, SAWCentral.Builtins,
    --    SAWScript.Interpreter and more, SAWServer.SAWServer
    AIGProxy(..),
    -- used by SAWCentral.Crucible.LLVM.Builtins
    SAW_CFG(..),
    -- used by SAWScript.Interpreter
    --    SAWServer.SAWServer, SAWServer.*CrucibleSetup
    BuiltinContext(..),
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
    -- used by SAWScript.Search, SAWScript.Typechecker
    TyEnv, VarEnv,
    -- used by SAWCentral.Builtins, SAWScript.ValueOps, SAWScript.Interpreter,
    -- SAWScript.REPL.Command, SAWScript.REPL.Monad, SAWServer.SAWServer
    Environ(..),
    -- used by SAWScript.Interpreter
    pushScope, popScope,
    -- used by SAWCentral.Builtins, SAWScript.ValueOps, SAWScript.Interpreter,
    -- SAWServer.SAWServer
    CryptolEnvStack(..),
    -- used by SAWCentral.Crucible.LLVM.FFI, SAWCentral.Crucible.LLVM.X86,
    -- SAWCentral.Crucible.MIR.Builtins, SAWCentral.Builtins,
    -- SAWScript.Interpreter, SAWScript.REPL.Monad
    getCryptolEnv,
    -- used by SAWCentral.Builtins
    getCryptolEnvStack,
    -- used by SAWCentral.Builtins, SAWScript.Interpreter, SAWScript.REPL.Monad
    setCryptolEnv,
    -- used by SAWScript.REPL.Monad, SAWServer.Eval,
    -- SAWServer.ProofScript, SAWServer.CryptolSetup, SAWServer.CryptolExpression,
    -- SAWServer.LLVMVerify, SAWServer.JVMVerify, SAWServer.MIRVerify, SAWServer.Yosys,
    rwGetCryptolEnv,
    -- used by SAWScript.ValueOps
    rwGetCryptolEnvStack,
    -- used by SAWServer.CryptolSetup
    rwSetCryptolEnv,
    -- used by SAWScript.ValueOps
    rwSetCryptolEnvStack,
    -- used by SAWScript.REPL.Monad, SAWServer.SAWServer, SAWServer.Yosys
    rwModifyCryptolEnv,
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
    -- used by SAWScript.Interpreter
    setPosition,
    -- used by SAWScript.Interpreter
    getStackTrace,
    pushTraceFrame, popTraceFrame,
    pushTraceFrames, popTraceFrames,
    -- used by SAWScript.Interpreter
    RefChain,
    -- used in various places in SAWCentral, and in selected builtins in
    -- SAWScript.Interpreter
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
    extendEnv,
    extendEnvMulti,
    -- used by SAWScript.Interpreter
    addTypedef,
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
    crucibleSetupTopLevel,
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
import Data.List.Extra ( dropEnd )
import qualified Data.Map as Map
import Data.Map ( Map )
import Data.Set ( Set )
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Parameterized.Some
import Data.Sequence (Seq)
import Data.Typeable
import qualified Prettyprinter as PP
import System.FilePath((</>))

import qualified Data.AIG as AIG

import qualified SAWSupport.ScopedMap as ScopedMap
import SAWSupport.ScopedMap (ScopedMap)
import qualified SAWSupport.Pretty as PPS (Opts, defaultOpts, showBrackets, showBraces, showCommaSep)

import SAWCentral.Panic (panic)
import SAWCentral.Trace (Trace)
import qualified SAWCentral.Trace as Trace

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
import SAWCentral.SolverCache
import SAWCentral.Crucible.LLVM.Skeleton
import SAWCentral.X86 (X86Unsupported(..), X86Error(..))
import SAWCentral.Yosys.IR
import SAWCentral.Yosys.Theorem (YosysImport, YosysTheorem)
import SAWCentral.Yosys.State (YosysSequential)

import SAWCore.Name (VarName(..), DisplayNameEnv, emptyDisplayNameEnv)
import CryptolSAWCore.CryptolEnv as CEnv
import SAWCore.FiniteValue (FirstOrderValue, ppFirstOrderValue)
import SAWCore.Rewriter (Simpset, lhsRewriteRule, rhsRewriteRule, ctxtRewriteRule, listRules)
import SAWCore.SharedTerm
import qualified SAWCore.Term.Pretty as SAWCorePP
import CryptolSAWCore.TypedTerm

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

-- Values ----------------------------------------------------------------------

data BuiltinWrapper
  = OneMoreArg (Value -> TopLevel Value)
  | ManyMoreArgs (Value -> TopLevel BuiltinWrapper)

-- | A type to hold the chain of references to a value that arise
--   during execution. This appears in the monadic value types
--   (VTopLevel, VProofScript, etc.) in order to trace let-bindings of
--   monadic objects and treat them as part of the call chain.
--
--   It starts empty for builtins in the builtins table, and gets an
--   entry consed onto it each time a value is either read out of the
--   environment (for plain values) or created by function
--   application.
--
--   Each reference is a position and a name (the position of the
--   reference and the name that was used to refer to the value) and
--   is used as a call site when handling stack traces.
--
--   For example,
--      1: let x = print_stack;
--      2: let y = x;
--      3: y;
--
--   will flow as follows:
--      (a) We load print_stack from the global environment and add an
--          entry containing the reference position (line 1, columns
--          9-20) and the name "print_stack". The resulting value is
--          saved as "x".
--      (b) We load "x" from the environment, and add an entry with
--          the reference position (line 2, columns 9-10) and the name
--          "x". The value already contains the entry from (a), so now
--          there are two, and the one from "x" is on the front of the
--          list.
--      (c) We load "y" from the environment, and add a similar entry
--          with "y".
--      (d) Then we bind y to execute it, and that loads the sequence
--          y -> x -> print_stack onto the call stack.
--      (e) The resulting trace printed by print_stack will look like:
--             (builtin) in print_stack
--             foo.saw:1:9-20 in x
--             foo.saw:2:9-10 in y
--             foo.saw:3:1-2 at top level
--
type RefChain = [(SS.Pos, SS.Name)]

-- | The SAWScript interpreter's base value type.
--
--   The interpreter executes from AST elements (expressions,
--   statements) to values. Unfortunately, for the time being, values
--   are a (considerable) superset of what the AST can represent, so
--   values can't be injected back into unexecuted AST elements.
--   FUTURE: this should be fixed, but not until it can be done
--   without tying a gigantic knot in the module dependencies.
--
--   Because monadic values are irreducible until executed (they're
--   effectively lambdas) but we also want to be able to know what
--   they are when we execute them (for stack traces and error
--   reporting) we carry around a bunch of metadata with each one.
--
--   Values that can have monadic type are:
--      - the compound monadic values, that reduce to plain ones
--        by executing in the interpreter:
--           VReturn
--           VDo
--           VBindOnce
--      - the plain monadic values, which contain Haskell-level
--        monadic actions:
--           VTopLevel
--           VProofScript
--           VLLVMCrucibleSetup
--           VJVMSetup
--           VMIRSetup
--
--   Furthermore, VLambda and VBuiltin can produce monadic values
--   after application of an argument, and need to carry certain
--   metadata of their own to populate their results.
--
--   In general, monadic values carry the following metadata until
--   executed:
--      - Position of last reference
--      - a RefChain (q.v.)
--
--   Function-class values that might produce monadic values when an
--   argument is applied (VLambda and VBuiltin) carry the following
--   metadata:
--      - a name
--      - an argument list
--
--   The position of last reference is kept for VReturn and the plain
--   monadic values. For plain monadic values, the position is loaded
--   into the interpreter's last position state before the
--   Haskell-level monadic action is executed.
--
--   For VReturn, it propagates to the result. (Whether this is
--   necessary, useful, or even desirable isn't entirely clear -- it
--   has no effect if you return a scalar, obviously, and if you
--   return out a monadic value, that should already have its own
--   reference position and it's not clear that updating it with the
--   return's position is helpful. FUTURE: investigate.)
--
--   VBindOnce contains a position; however, it's the position of the
--   bind operation (comparable to the position in a StmtBind) and not
--   relevant to this discussion.
--
--   The RefChain is kept for plain monadic values, and for VReturn
--   for propagation purposes. (Again, that may or may not be the best
--   way. FUTURE.) VDo (and VBindOnce) also have a RefChain, which
--   propagates to the resultant plain monadic value when the do-block
--   is executed in the interpreter. The do-block RefChain tracks the
--   names the do-block gets passed around under before it gets
--   evaluated. (And then the chain in the resulting value could
--   theoretically accumulate more entries as it gets passed around,
--   except that there's no way to do that: we always execute the
--   resultant Haskell-level action immediately after interpreting any
--   do-block.)
--
--   We could in principle also carry a RefChain in VLambda so if
--   you pass a lambda around it gets traced the same way a monadic
--   value does. There's not as much call for it, but it might be
--   useful. FUTURE.
--
--   VLambda and VBuiltin carry their names. When the last argument is
--   applied, and the resulting value is monadic, the name is used to
--   seed its RefChain. The RefChain then tracks the whole sequence of
--   names used to refer to that value, in order; this is why plain
--   monadic values don't specifically carry their "own" names. Note
--   that for VLambda the name is optional, because lambdas don't
--   necessarily have names. There's no such thing as an anonymous
--   builtin though.
--
--   VBuiltin also carries a list of values (it is actually a
--   snoc-list manifested as a `Seq`) that are the arguments already
--   applied to the builtin. This is purely for printing in stack
--   traces. FUTURE: VLambda should have this as well, but it doesn't
--   make sense to make such a list separate from the variable
--   environment handling, and that needs a through mucking-out of its
--   own first.
--
--   The flow for the position of last reference is as follows:
--      (a) Builtins in the global environment are initialized with
--          `atRestPos`. This should never be seen by a user because
--          stuff in the environment should not be seen without being
--          referenced somehow.
--      (b) When a variable is looked up in the environment, the
--          value returned has its last reference position updated
--          with the position of the variable name.
--      (c) Before an argument is applied to a function (or lambda)
--          the _argument's_ last reference position is updated with
--          the position of the argument expression. For arguments
--          to builtins that are monadic value callbacks, this
--          causes the last reference position to be the point where
--          the value was passed to the builtin. Alas, I no longer
--          remember what special case this was needed to handle,
--          and it's possible it's no longer necessary.
--      (d) Somewhat similarly, the first argument of VBindOnce is
--          updated before it is executed, using the position in
--          the VBindOnce.
--      (e) The same goes for statements in do-blocks, using the
--          position of the BindStmt, or for the last expression in a
--          do-block, the position of the expression.
--      (f) When the Haskell-level monadic action in a plan monadic
--          value is extracted with fromValue, we use the position to
--          call setPosition to update the interpreter's last
--          execution position.
--      (g) The idea is that anytime we leave the interpreter to
--          execute a builtin, there's a setPosition call that sets
--          the last execution position to something that makes sense
--          to report to the user if the builtin errors out.
--      (h) FUTURE: consider clearing a value's position (setting it
--          to `atRestPos`) when added to the environment, so the
--          position of last reference for everything in the
--          environment is the same.
--
--   The flow for names is as follows:
--      (a) toValue is given a name to insert. This allows the
--          typeclass-based construction process for builtins to
--          propagate the name to every VBuiltin. (The name itself is
--          provided from the builtins table.)
--      (b) The names of lambdas are applied by the parser in
--          `buildFunction`. Every let-binding that's written with a
--          function head is converted to a chain of lambdas there,
--          and that conversion inserts the name from the let-binding.
--          Other lambdas are by definition anonymous and get Nothing.
--      (c) As mentioned above, when the last argument is applied to a
--          function, the name is used to seed the RefChain of the
--          resulting value, if there is one. At this time we'll also
--          be generating a stack trace frame while the function
--          executes, using that name.
--
--   See above for notes on the flow for RefChains.
--
--   In principle the position of last reference should be the same as
--   the position at the top of the RefChain, and we should not get
--   empty RefChains (same as we should never see the default position
--   that appears in the builtins table) so it may be sufficient to
--   use the RefChain to call setPosition. However, not all the places
--   that update the position of last reference add to the RefChain
--   (they were tried and found to produce unwanted or incorrect stack
--   traces) so this may not be true and/or those position updates may
--   not be needed, all of which should probably be investigated
--   further in the FUTURE.
--
--   Also note that because the bits of metadata aren't quite the same
--   in each case and don't update in exactly the same places, it
--   currently doesn't work very well to try to wrap them together in
--   their own type. If things become more regular, it might be worth
--   revisiting that proposition.
--
--   In addition to all of the above, VLambda and VDo carry an
--   environment (the interpreter's name -> value environment) which
--   closes in the naming environment they're run against. This
--   environment is collected when the corresponding lambda or do
--   expression is evaluated (basically, where it appears in the input
--   source), and arguments get added to it as they're applied. This
--   produces the expected lexical scoping behavior.
--
--   VBuiltin, even though it's effectively also a lambda, does _not_
--   carry an environment. Closing in a copy of the partly-built
--   default environment that exists when the VBuiltin values are
--   constructed, or even the whole default environment, wouldn't
--   serve any purpose.

--   Furthermore, VBuiltin is used to bind in Haskell functions, which
--   don't themselves run in SAWScript and don't need or use the
--   naming environment; they just need their arguments. The exception
--   is the subshell and proof_subshell builtins, which intentionally
--   inherit the SAWScript environment they're invoked in. Any
--   otherwise pointless environment capturing we indulged in for
--   uniformity's sake would break that behavior.

--
data Value
  = VBool Bool
  | VString Text
  | VInteger Integer
  | VArray [Value]
  | VTuple [Value]
  | VRecord (Map SS.Name Value)
  | VLambda Environ (Maybe SS.Name) SS.Pattern SS.Expr
    -- | Function-shaped value that's a Haskell-level function. This
    --   is how builtins appear. Includes the name of the builtin and
    --   the list of arguments applied so far, as a Seq to allow
    --   appending to the end reasonably.
  | VBuiltin SS.Name (Seq Value) BuiltinWrapper
    -- XXX: This should go away. Fortunately, it's only used by the
    -- closures that implement stack traces, which are scheduled for
    -- removal soon.
  | VTerm TypedTerm
  | VType Cryptol.Schema
    -- | Returned value in unspecified monad.
  | VReturn SS.Pos RefChain Value
    -- | Not-yet-executed do-block in unspecified monad.
  | VDo RefChain Environ ([SS.Stmt], SS.Expr)
    -- | Single monadic bind in unspecified monad.
    --
    --   This exists only to support the "for" builtin; see notes there
    --   for why this is so. XXX: remove it once that's no longer needed.
    --   A sequence of these is effectively equivalent to a do-block.
    --
    --   The position is the position of the bind operation,
    --   comparable to the position in a StmtBind.
  | VBindOnce SS.Pos RefChain Value Value
    -- | A plain value containing a Haskell-level action in TopLevel
    --   (that itself yields a Value).
  | VTopLevel SS.Pos RefChain (TopLevel Value)
    -- | A plain value containing a Haskell-level action in ProofScript.
    --   Like a VTopLevel, except in the other monad.
  | VProofScript SS.Pos RefChain (ProofScript Value)
  | VSimpset SAWSimpset
  | VTheorem Theorem
  | VBisimTheorem BisimTheorem
  -----
    -- | A plain value containing a Haskell-level action in LLVMSetup.
    --   Like a VTopLevel, except in the other monad.
  | VLLVMCrucibleSetup SS.Pos RefChain !(LLVMCrucibleSetupM Value)
  | VLLVMCrucibleMethodSpec (CMSLLVM.SomeLLVM CMS.ProvedSpec)
  | VLLVMCrucibleSetupValue (CMSLLVM.AllLLVM CMS.SetupValue)
  -----
    -- | A plain value containing a Haskell-level action in JVMSetup.
    --   Like a VTopLevel, except in the other monad.
  | VJVMSetup SS.Pos RefChain !(JVMSetupM Value)
  | VJVMMethodSpec !(CMS.ProvedSpec CJ.JVM)
  | VJVMSetupValue !(CMS.SetupValue CJ.JVM)
  -----
    -- | A plain value containing a Haskell-level action in MIRSetup.
    --   Like a VTopLevel, except in the other monad.
  | VMIRSetup SS.Pos RefChain !(MIRSetupM Value)
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
  | VCryptolModule CEnv.ExtCryptolModule
  | VJavaClass JSS.Class
  | VLLVMModule (Some CMSLLVM.LLVMModule)
  | VMIRModule RustModule
  | VMIRAdt MIR.Adt
  | VSatResult SatResult
  | VProofResult ProofResult
  | VAIG AIGNetwork
  | VCFG SAW_CFG
  | VGhostVar CMS.GhostGlobal
  | VYosysModule YosysIR
  | VYosysImport YosysImport
  | VYosysSequential YosysSequential
  | VYosysTheorem YosysTheorem

type SAWSimpset = Simpset TheoremNonce

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

data SatResult
  = Unsat SolverStats
  | Sat SolverStats [(VarName, FirstOrderValue)]
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
    showEqn (x, t) = showVarName x . showString " = " . showVal t
    showVarName vn = showString (Text.unpack (vnName vn))

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
    showVarName vn = showString (Text.unpack (vnName vn))
    showEqn (x, t) = showVarName x . showString " = " . showVal t
    showMulti _ [] = showString "]"
    showMulti s (eqn : eqns) = showString s . showEqn eqn . showMulti ", " eqns

showSimpset :: PPS.Opts -> Simpset a -> String
showSimpset opts ss =
  unlines ("Rewrite Rules" : "=============" : map (show . ppRule) (listRules ss))
  where
    ppRule r =
      PP.pretty '*' PP.<+>
      (PP.nest 2 $ PP.fillSep
       [ ppTerm vars (lhsRewriteRule r)
       , PP.pretty '=' PP.<+> ppTerm vars (rhsRewriteRule r) ])
      where vars = map fst (ctxtRewriteRule r)
    ppTerm vars t = SAWCorePP.ppTermInCtx opts vars t

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
      PPS.showBraces $ PPS.showCommaSep $ map showFld (Map.toList m)
        where
          showFld (n, fv) =
            showString (Text.unpack n) . showString "=" . showsPrecValue opts nenv 0 fv

    VLambda _env _mname pat e ->
      let pat' = PP.pretty pat
          e' = PP.pretty e
      in
      shows $ PP.sep ["\\", pat', "->", e']

    VBuiltin name _args _wrapper ->
      let name' = PP.pretty name in
      shows $ PP.sep ["<<", "builtin", name', ">>"]

    VTerm t -> showString (SAWCorePP.showTermWithNames opts nenv (ttTerm t))
    VType sig -> showString (pretty sig)
    VReturn _pos _chain v' ->
      showString "return " . showsPrecValue opts nenv (p + 1) v'
    VDo _chain _env body ->
      -- The printer for expressions doesn't print positions, so we can
      -- feed in a dummy.
      let pos = SS.PosInternal "<<do-block>>"
          e = SS.Block pos body
      in
      shows (PP.pretty e)
    VBindOnce _pos _chain v1 v2 ->
      let v1' = showsPrecValue opts nenv 0 v1
          v2' = showsPrecValue opts nenv 0 v2
      in
      v1' . showString " >>= " . v2'
    VTopLevel {} -> showString "<<TopLevel>>"
    VSimpset ss -> showString (showSimpset opts ss)
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
    VCryptolModule m -> showString (CEnv.showExtCryptolModule m)
    VLLVMModule (Some m) -> showString (CMSLLVM.showLLVMModule m)
    VMIRModule m -> shows (PP.pretty (m^.rmCS^.collection))
    VMIRAdt adt -> shows (PP.pretty adt)
    VJavaClass c -> shows (prettyClass c)
    VProofResult r -> showsProofResult opts r
    VSatResult r -> showsSatResult opts r
    VAIG _ -> showString "<<AIG>>"
    VCFG (LLVM_CFG g) -> showString (show g)
    VCFG (JVM_CFG g) -> showString (show g)
    VGhostVar x -> showParen (p > 10)
                 $ showString "Ghost " . showsPrec 11 x
    VYosysModule _ -> showString "<<Yosys module>>"
    VYosysImport _ -> showString "<<Yosys import>>"
    VYosysSequential _ -> showString "<<Yosys sequential>>"
    VYosysTheorem _ -> showString "<<Yosys theorem>>"
    VJVMSetup{}      -> showString "<<JVM Setup>>"
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

-- | The variable environment: a map from variable names to:
--      - the definition position
--      - the lifecycle setting (experimental/current/deprecated/etc)
--      - the type scheme
--      - the value
--      - the help text if any
type VarEnv = ScopedMap SS.Name (SS.Pos, SS.PrimitiveLifecycle,
                                 SS.Schema, Value, Maybe [Text])

-- | The type environment: a map from type names to:
--      - the lifecycle setting (experimental/current/deprecated/etc)
--      - the expansion, which might be another type (this is how
--        typedefs/type aliases appear) or "abstract" (this is how
--        builtin types that aren't special cases in the AST appear)
type TyEnv = ScopedMap SS.Name (SS.PrimitiveLifecycle, SS.NamedType)

-- | The full Cryptol environment. We maintain a stack of plain
--   Cryptol environments and push/pop them as we enter and leave
--   scopes; otherwise the Cryptol environment doesn't track SAWScript
--   scopes and horribly confusing wrong things happen.
data CryptolEnvStack = CryptolEnvStack CEnv.CryptolEnv [CEnv.CryptolEnv]

-- | Type for the ordinary interpreter environment.
--
--   There's one environment that maps variable names to values, and
--   one that maps type names to types. A third handles the Cryptol
--   domain. All three get closed in with lambdas and do-blocks at the
--   appropriate times.
--
--   Note that rebindable variables are sold separately. This is so
--   they don't get closed in; references to rebindable variables
--   always retrieve the most recent version.
data Environ = Environ {
    eVarEnv :: VarEnv,
    eTyEnv :: TyEnv,
    eCryptol :: CryptolEnvStack
}

-- | The extra environment for rebindable globals.
--
--   Note: because no builtins are rebindable, there are no lifecycle
--   or help text fields. There is, currently at least, no way to
--   populate those for non-builtins.
type RebindableEnv = Map SS.Name (SS.Pos, SS.Schema, Value)

-- | Enter a scope.
pushScope :: TopLevel ()
pushScope = do
    Environ varenv tyenv cryenv <- gets rwEnviron
    let varenv' = ScopedMap.push varenv
        tyenv' = ScopedMap.push tyenv
        cryenv' = cryptolPush cryenv
    modifyTopLevelRW (\rw -> rw { rwEnviron = Environ varenv' tyenv' cryenv' })

-- | Leave a scope. This will panic if you try to leave the last scope;
--   pushes and pops should be matched.
popScope  :: TopLevel ()
popScope = do
    Environ varenv tyenv cryenv <- gets rwEnviron
    let varenv' = ScopedMap.pop varenv
        tyenv' = ScopedMap.pop tyenv
        cryenv' = cryptolPop cryenv
    modifyTopLevelRW (\rw -> rw { rwEnviron = Environ varenv' tyenv' cryenv' })


-- | Get the current Cryptol environment.
getCryptolEnv :: TopLevel CEnv.CryptolEnv
getCryptolEnv = do
    Environ _varenv _tyenv cryenvs <- gets rwEnviron
    let CryptolEnvStack ce _ = cryenvs
    return ce

-- | Get the current full stack of Cryptol environments.
getCryptolEnvStack :: TopLevel CryptolEnvStack
getCryptolEnvStack = do
    Environ _varenv _tyenv cryenvs <- gets rwEnviron
    return cryenvs

-- | Update the current Cryptol environment.
--
--   Overwrites the previous value; the caller must ensure that the
--   value applied has not become stale.
setCryptolEnv :: CEnv.CryptolEnv -> TopLevel ()
setCryptolEnv ce = do
    Environ varenv tyenv cryenvs <- gets rwEnviron
    let CryptolEnvStack _ ces = cryenvs
    let cryenvs' = CryptolEnvStack ce ces
    modify (\rw -> rw { rwEnviron = Environ varenv tyenv cryenvs' })

-- | Get the current Cryptol environment from a TopLevelRW.
--
--   (Accessor method for use in SAWServer and SAWScript.REPL, which
--   have their own monads and thus different access to TopLevelRW.)
--
--   XXX: SAWServer shouldn't be using, or need to use, TopLevelRW at
--   all.
rwGetCryptolEnv :: TopLevelRW -> CEnv.CryptolEnv
rwGetCryptolEnv rw =
    let Environ _varenv _tyenv cryenvs = rwEnviron rw
        CryptolEnvStack ce _ = cryenvs
    in
    ce

-- | Get the current full stack of Cryptol environments from a
--   TopLevelRW. Used by the checkpointing logic, in a fairly dubious
--   way. (XXX)
rwGetCryptolEnvStack :: TopLevelRW -> CryptolEnvStack
rwGetCryptolEnvStack rw =
    let Environ _varenv _tyenv cryenvs = rwEnviron rw in
    cryenvs

-- | Update the current Cryptol environment in a TopLevelRW.
--
--   Overwrites the previous environment; caller must ensure they
--   haven't done anything to make the value they're working with
--   stale.
--
--   (Accessor method for use in SAWServer and SAWScript.REPL, which
--   have their own monads and thus different access to TopLevelRW.)
--
--   XXX: SAWServer shouldn't be using, or need to use, TopLevelRW at
--   all.
rwSetCryptolEnv :: CEnv.CryptolEnv -> TopLevelRW -> TopLevelRW
rwSetCryptolEnv ce rw =
    let Environ varenv tyenv cryenvs = rwEnviron rw
        CryptolEnvStack _ ces = cryenvs
        cryenvs' = CryptolEnvStack ce ces
    in
    rw { rwEnviron = Environ varenv tyenv cryenvs' }

-- | Update the current full stack of Cryptol environments in a
--   TopLevelRW. Used by the checkpointing logic, in a fairly
--   dubious way. (XXX)
--
--   Overwrites the previous stack; caller must ensure they haven't
--   done anything to make the value they're working with stale.
rwSetCryptolEnvStack :: CryptolEnvStack -> TopLevelRW -> TopLevelRW
rwSetCryptolEnvStack cryenvs rw =
    let Environ varenv tyenv _ = rwEnviron rw in
    rw { rwEnviron = Environ varenv tyenv cryenvs }

-- | Modify the current Cryptol environment in a TopLevelRW.
--
--   (Accessor method for use in SAWServer and SAWScript.REPL, which
--   have their own monads and thus different access to TopLevelRW.)
--
--   XXX: SAWServer shouldn't be using, or need to use, TopLevelRW at
--   all.
rwModifyCryptolEnv :: (CEnv.CryptolEnv -> CEnv.CryptolEnv) -> TopLevelRW -> TopLevelRW
rwModifyCryptolEnv f rw =
    let Environ varenv tyenv cryenvs = rwEnviron rw
        CryptolEnvStack ce ces = cryenvs
        ce' = f ce
        cryenvs' = CryptolEnvStack ce' ces 
    in
    rw { rwEnviron = Environ varenv tyenv cryenvs' }

-- | Push a new scope on the Cryptol environment stack.
cryptolPush :: CryptolEnvStack -> CryptolEnvStack
cryptolPush (CryptolEnvStack ce ces) =
    -- Each entry is the whole environment, so duplicate the top entry
    CryptolEnvStack ce (ce : ces)

-- | Pop the current scope off the Cryptol environment stack.
cryptolPop :: CryptolEnvStack -> CryptolEnvStack
cryptolPop (CryptolEnvStack _ ces) =
    -- Discard the top
    case ces of
        [] -> panic "cryptolPop" ["Cryptol environment scope stack ran out"]
        ce : ces' -> CryptolEnvStack ce ces'


-- | TopLevel Read-Only Environment.
data TopLevelRO =
  TopLevelRO
  { roOptions       :: Options
  , roArgv          :: [Text]
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
  {
    -- | The variable and type naming environment.
    rwEnviron :: Environ
  , rwRebindables :: RebindableEnv

    -- | The current execution position. This is only valid when the
    --   interpreter is calling out into saw-central to execute a
    --   builtin. Within the interpreter, the current position is
    --   either passed around or the position in the current AST
    --   element, and those positions should be used instead.
  , rwPosition :: SS.Pos

    -- | The current stack trace. The most recent frame is at the front.
  , rwStackTrace :: Trace

  , rwJavaCodebase  :: JavaCodebase -- ^ Current state of Java sub-system.

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
         -- XXX: assumes the exception came from inside a builtin somewhere,
         -- and hardwires PosInsideBuiltin. This is not going to always be
         -- true and this logic should be reworked when we're doing the error
         -- printing cleanup.
         throwM (SS.TraceException stk SS.PosInsideBuiltin (X.SomeException ex))

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
  stk <- getStackTrace
  -- All current uses of throwTopLevel are inside builtins.
  let pos = SS.PosInsideBuiltin
  throwM (SS.TraceException stk pos (X.SomeException (SS.TopLevelException pos msg)))

-- | Set the current execution position.
setPosition :: SS.Pos -> TopLevel ()
setPosition newpos = do
  modifyTopLevelRW (\rw -> rw { rwPosition = newpos })

-- | Add a stack trace frame. Takes the call site position and the
--   function name.
pushTraceFrame :: SS.Pos -> Text -> TopLevel ()
pushTraceFrame pos func =
  modifyTopLevelRW (\rw -> rw { rwStackTrace = Trace.push pos func (rwStackTrace rw) })

-- | Add multiple stack trace frames. Takes a list of call site and
--   function name pairs.
--
--   The topmost entry in the argument list goes onto the stack first
--   and becomes the deepest entry and thus the caller of the rest.
--
--   This is backwards from what one might expect if the list were
--   itself a call stack. However, the use case we have produces
--   entries in that order naturally (it is a chain of references to /
--   assignments of monadic values, with the most recent and therefore
--   first/deepest when run at the top of the list), so I'm not
--   inclined to reverse the list both here and in the caller to match
--   a rather vague expectation.
--
pushTraceFrames :: [(SS.Pos, Text)] -> TopLevel ()
pushTraceFrames frames =
  mapM_ (\(pos, name) -> pushTraceFrame pos name) frames

-- | Drop a stack trace frame.
popTraceFrame :: TopLevel ()
popTraceFrame =
  modifyTopLevelRW (\rw -> rw { rwStackTrace = Trace.pop (rwStackTrace rw) })

-- | Drop multiple stack trace frames. Takes a list of the corresponding
--   length for caller convenience.
popTraceFrames :: [a] -> TopLevel ()
popTraceFrames frames =
  mapM_ (\_ -> popTraceFrame) frames

-- | Get the current execution position.
getPosition :: TopLevel SS.Pos
getPosition =
  gets rwPosition

-- | Get the current stack trace.
getStackTrace :: TopLevel Trace
getStackTrace = gets rwStackTrace

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

extendEnv :: SS.Pos -> SS.Name -> SS.Rebindable -> SS.Schema -> Maybe [Text] -> Value -> TopLevel ()
extendEnv pos name rb ty doc v = do
     sc <- gets rwSharedContext
     let ident = T.mkIdent name
         modname = T.packModName [name]

     -- Update the SAWScript environment.
     Environ varenv tyenv cryenvs <- gets rwEnviron
     rbenv <- gets rwRebindables
     let (varenv', rbenv') = case rb of
           SS.ReadOnlyVar ->
             -- If we replace a rebindable variable at the top level with a
             -- readonly one, the readonly version in varenv will hide it
             -- ever after. We ought to remove it from rbenv; however, it's
             -- not easy to know here whether we're at the top level or not.
             -- FUTURE: maybe this will become easier in the long run.
             let ve' = ScopedMap.insert name (pos, SS.Current, ty, v, doc) varenv in
             (ve', rbenv)
           SS.RebindableVar ->
             -- The typechecker restricts this to happen only at the
             -- top level and only if any existing variable is already
             -- rebindable, so we don't have to update varenv.
             let re' = Map.insert name (pos, ty, v) rbenv in
             (varenv, re')

     -- Mirror the value into the Cryptol environment if appropriate.
     let CryptolEnvStack ce ces = cryenvs
     ce' <-
       case v of
         VTerm t ->
           pure $ CEnv.bindTypedTerm (ident, t) ce
         VType s ->
           pure $ CEnv.bindType (ident, s) ce
         VInteger n ->
           pure $ CEnv.bindInteger (ident, n) ce
         VCryptolModule m ->
           pure $ CEnv.bindExtCryptolModule (modname, m) ce
         VString s ->
           do tt <- io $ typedTermOfString sc (Text.unpack s)
              pure $ CEnv.bindTypedTerm (ident, tt) ce
         VBool b ->
           do tt <- io $ typedTermOfBool sc b
              pure $ CEnv.bindTypedTerm (ident, tt) ce
         _ ->
           pure ce
     let cryenvs' = CryptolEnvStack ce' ces

     -- Drop the new bits into place.
     modify (\rw -> rw {
         rwEnviron = Environ varenv' tyenv cryenvs',
         rwRebindables = rbenv'
     })

extendEnvMulti :: [(SS.Pos, SS.Name, SS.Rebindable, SS.Schema, Maybe [Text], Environ -> Value)] -> TopLevel ()
extendEnvMulti bindings = do

     -- Update the SAWScript environment.
     Environ varenv tyenv cryenv <- gets rwEnviron

     -- Insert all the bindings at once, and feed the final resulting
     -- interpreter environment into each value. This circular
     -- definition only works because of laziness and it's only legal
     -- when the pieces are in a single let-block.
     --
     -- Only allow lambda values because that's the only use case
     -- (functions in mutually recursive "rec" sets) and it lets us
     -- ignore the Cryptol environment.
     --
     -- Be sure to insert v' (rather than v) so the panic check is
     -- actually performed.
     let insert (pos, name, rb, ty, doc, fv) tmpenv =
             let v = fv environ'
                 v' = case v of
                     VLambda{} -> v
                     _ ->
                         panic "extendEnvMulti" [
                             "Non-lambda value: " <> Text.pack (show v),
                             "Source position: " <> Text.pack (show pos)
                         ]
                 v'' = case rb of
                     SS.ReadOnlyVar -> v'
                     SS.RebindableVar ->
                         -- "rec" declarations can't be rebindable
                         panic "extendEnvMulti" [
                             "Rebindable variable: " <> name,
                             "Source position: " <> Text.pack (show pos)
                         ]
             in
             ScopedMap.insert name (pos, SS.Current, ty, v'', doc) tmpenv
         varenv' = foldr insert varenv bindings
         environ' = Environ varenv' tyenv cryenv

     -- Drop the new bits into place.
     modify (\rw -> rw { rwEnviron = environ' })

-- Note that the expansion type should have already been through the
-- typechecker, so it's ok to panic if it turns out to be broken.
addTypedef :: SS.Name -> SS.Type -> TopLevel ()
addTypedef name ty = do
    avail <- gets rwPrimsAvail
    Environ varenv tyenv cryenv <- gets rwEnviron
    let ty' = SS.substituteTyVars avail tyenv ty
        tyenv' = ScopedMap.insert name (SS.Current, SS.ConcreteType ty') tyenv
    modify (\rw -> rw { rwEnviron = Environ varenv tyenv' cryenv })

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


crucibleSetupTopLevel :: TopLevel a -> CrucibleSetup ext a
crucibleSetupTopLevel m = lift (lift m)

scriptTopLevel :: TopLevel a -> ProofScript a
scriptTopLevel m = ProofScript (lift (lift m))

llvmTopLevel :: TopLevel a -> LLVMCrucibleSetupM a
llvmTopLevel m = LLVMCrucibleSetupM (crucibleSetupTopLevel m)

jvmTopLevel :: TopLevel a -> JVMSetupM a
jvmTopLevel m = JVMSetupM (crucibleSetupTopLevel m)

mirTopLevel :: TopLevel a -> MIRSetupM a
mirTopLevel m = MIRSetupM (crucibleSetupTopLevel m)

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
