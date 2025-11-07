{- |
Module      : SAWScript.Interpreter
Description : Interpreter for SAW-Script files and statements.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- See Note [-Wincomplete-uni-patterns and irrefutable patterns] in
-- SAWScript.Typechecker
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module SAWScript.Interpreter
  ( interpretTopStmt
  , processFile
  , buildTopLevelEnv
  )
  where

import qualified Control.Exception as X
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (ask)
import Control.Monad.State (gets, get, put)
import qualified Data.ByteString as BS
import Data.Maybe (fromMaybe, mapMaybe)
import Data.List (genericLength)
import qualified Data.Map as Map
import Data.Map ( Map )
import Data.Sequence (Seq( (:|>) ))
import qualified Data.Sequence as Seq (empty)
import qualified Data.Set as Set
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO
import System.Directory (getCurrentDirectory, setCurrentDirectory)
import System.FilePath (takeDirectory)
import System.Environment (lookupEnv)
import System.Process (readProcess)

import Data.Parameterized.Some

import qualified Data.AIG.CompactGraph as AIG

import qualified Text.LLVM.AST as LLVM (Type)

import qualified Lang.JVM.Codebase as JSS

import qualified Cryptol.TypeCheck.AST as Cryptol

import qualified Lang.Crucible.JVM as CJ
import Lang.Crucible.LLVM.ArraySizeProfile (FunctionProfile)
import Mir.Intrinsics (MIR)
import qualified Mir.Generator as MIR (RustModule)
import qualified Mir.Mir as MIR

import qualified SAWSupport.ScopedMap as ScopedMap
--import SAWSupport.ScopedMap (ScopedMap)
import qualified SAWSupport.Pretty as PPS (MemoStyle(..), Opts(..), defaultOpts, pShow, pShowText)

import SAWCore.FiniteValue (FirstOrderValue(..))

import CryptolSAWCore.TypedTerm

--import SAWCentral.Trace (Trace)
import qualified SAWCentral.Trace as Trace

import qualified SAWCentral.AST as SS
import qualified SAWCentral.Position as SS
import SAWCentral.AST (Import(..), PrimitiveLifecycle(..), defaultAvailable)
import SAWCentral.Bisimulation
import SAWCentral.Builtins
import SAWCentral.Exceptions (failTypecheck)
import qualified SAWScript.Loader as Loader
import SAWCentral.JavaExpr
import SAWCentral.LLVMBuiltins
import SAWCentral.Options
import SAWScript.Typechecker (checkStmt, typesMatch)
import SAWScript.Panic (panic)
import SAWCentral.TopLevel
import SAWCentral.Utils
import SAWCentral.Value
import SAWScript.ValueOps
import SAWCentral.SolverCache
import SAWCentral.SolverVersions
import SAWCentral.Proof (ProofResult(..), Theorem, emptyTheoremDB)
import SAWCentral.Prover.Rewrite(basic_ss)
import SAWCentral.Prover.Exporter
import SAWCentral.Yosys -- XXX remove in favor of the following later
import qualified SAWCentral.Yosys as Yo (YosysIR)
import qualified SAWCentral.Yosys.State as Yo (YosysSequential)
import qualified SAWCentral.Yosys.Theorem as Yo (YosysImport, YosysTheorem)

import SAWCore.Module (emptyModule)
import SAWCore.Name (mkModuleName)
import SAWCore.Prim (rethrowEvalError)
import SAWCore.Rewriter (emptySimpset)
import SAWCore.SharedTerm
import SAWCore.Term.Raw (closedTerm)
import qualified CryptolSAWCore.CryptolEnv as CEnv

import qualified CryptolSAWCore.Prelude as CryptolSAW

-- Crucible
import qualified SAWCentral.Crucible.Common as CC
import qualified SAWCentral.Crucible.Common.MethodSpec as CMS
import qualified SAWCentral.Crucible.JVM.BuiltinsJVM as CJ
import           SAWCentral.Crucible.LLVM.Builtins
import           SAWCentral.Crucible.JVM.Builtins
import           SAWCentral.Crucible.MIR.Builtins
import           SAWCentral.Crucible.LLVM.X86
import           SAWCentral.Crucible.LLVM.Boilerplate
import           SAWCentral.Crucible.LLVM.Skeleton (ModuleSkeleton, FunctionSkeleton)
import           SAWCentral.Crucible.LLVM.Skeleton.Builtins
import           SAWCentral.Crucible.LLVM.FFI
import qualified SAWCentral.Crucible.LLVM.MethodSpecIR as CIR

-- Cryptol
import qualified Cryptol.Eval as V (PPOpts(..))
import qualified Cryptol.Backend.Monad as V (runEval)
import qualified Cryptol.Eval.Value as V (defaultPPOpts, ppValue)
import qualified Cryptol.Eval.Concrete as V (Concrete(..))

import qualified Prettyprinter as PP (pretty)
import qualified Prettyprinter.Render.Text as PP (putDoc)

import SAWScript.AutoMatch

import qualified Lang.Crucible.FunctionHandle as Crucible



------------------------------------------------------------
-- Support

-- This is used to reject top-level execution of polymorphic
-- expressions. Assumes we aren't inside an uninstantiated forall
-- quantifier. Also assumes the typechecker has already approved the
-- type. This means we know it doesn't contain unbound named type
-- variables. Fail if we encounter a unification var.
--
-- XXX: this serves little purpose. A polymorphic expression must
-- either be a partially applied (or unapplied) polymorphic function,
-- in which case we aren't going to actually execute anything anyway,
-- or be fully applied but have a polymorphic return type, and the
-- only such functions we can have are those that don't return (like
-- "fail") so we don't actually care what they produce. So this code
-- and the check that calls it should probably be removed.
--
-- XXX: also, this is here transiently so that the rejection continues
-- to work while the interaction between the interpreter and the
-- typechecker is rationalized. In the long run, the rejection should
-- really belong only to the repl for repl purposes and the
-- polymorphism check should be part of the currently nonexistent
-- incremental interface to the typechecker. Alternatively, if there
-- are cases that really require rejection of polymorphic expressions
-- at the top level, they also require rejection of polymorphic
-- expressions in nested do-blocks that aren't inside functions, and
-- it can and should all happen inside the typechecker.
isPolymorphic :: SS.Type -> Bool
isPolymorphic ty0 = case ty0 of
    SS.TyCon _pos _tycon args -> any isPolymorphic args
    SS.TyRecord _pos fields -> any isPolymorphic fields
    SS.TyVar _pos _a -> False
    SS.TyUnifyVar _pos _ix -> True

-- Get the type of an AST element. For now, only patterns because that's
-- what we're using.
--
-- Assumes we have been through the typechecker and the types are filled in.
--
-- XXX: this should be a typeclass function with instances for all the AST
-- types.
--
-- XXX: also it should be moved to ASTUtil once we have such a place.
getType :: SS.Pattern -> SS.Type
getType pat = case pat of
    SS.PWild _pos ~(Just t) -> t
    SS.PVar _allpos _xpos _x ~(Just t) -> t
    SS.PTuple tuplepos pats ->
        SS.TyCon tuplepos (SS.TupleCon (genericLength pats)) (map getType pats)

-- Convert some text to an InputText for cryptol-saw-core.
toInputText :: SS.Pos -> Text -> CEnv.InputText
toInputText pos0 txt =
  CEnv.InputText {
    CEnv.inpText = txt,
    CEnv.inpFile = file,
    CEnv.inpLine = ln,
    CEnv.inpCol  = col + 2 -- for dropped }}
  }
  where
  (file, ln, col) = extract pos0
  extract pos = case pos of
      SS.Range f sl sc _ _ -> (f,sl, sc)
      SS.FileOnlyPos f -> (f, 1, 1)
      SS.FileAndFunctionPos f _ -> (f, 1, 1)
      SS.PosInferred _ pos' -> extract pos'
      SS.PosInternal s -> (s,1,1)
      SS.PosInsideBuiltin -> ("(builtin)", 1, 1)
      SS.PosREPL       -> ("<interactive>", 1, 1)
      SS.Unknown       -> ("Unknown", 1, 1)

-- | "Position of last reference" for values that haven't been
--   referenced.
--
--   Used in toValue so it'll appear in the builtin table. However,
--   it should always be replaced when the value is retrieved and
--   before it's returned out or passed on by the interpreter for
--   execution. So users should never see it.
--
--   FUTURE: might make sense to set this to a panic.
atRestPos :: SS.Pos
atRestPos = SS.PosInternal "<<position of value at rest; shouldn't be seen>>"

-- | Update the position in a plain monadic value.
injectPositionIntoMonadicValue :: SS.Pos -> Value -> Value
injectPositionIntoMonadicValue pos v = case v of
    VTopLevel _oldpos chain f -> VTopLevel pos chain f
    VProofScript _oldpos chain f -> VProofScript pos chain f
    VLLVMCrucibleSetup _oldpos chain f -> VLLVMCrucibleSetup pos chain f
    VJVMSetup _oldpos chain f -> VJVMSetup pos chain f
    VMIRSetup _oldpos chain f -> VMIRSetup pos chain f
    _ -> v

-- | Insert an entry in a plain monadic value's RefChain.
insertRefChain :: SS.Pos -> SS.Name -> Value -> Value
insertRefChain pos name v =
  let insert chain = (pos, name) : chain in
  case v of
    VDo chain env body -> VDo (insert chain) env body
    VBindOnce bindpos chain v1 v2 -> VBindOnce bindpos (insert chain) v1 v2
    VTopLevel vpos chain f -> VTopLevel vpos (insert chain) f
    VProofScript vpos chain f -> VProofScript vpos (insert chain) f
    VLLVMCrucibleSetup vpos chain f -> VLLVMCrucibleSetup vpos (insert chain) f
    VJVMSetup vpos chain f -> VJVMSetup vpos (insert chain) f
    VMIRSetup vpos chain f -> VMIRSetup vpos (insert chain) f
    _ -> v

-- | Merge an ancestor RefChain (e.g. from a generating do block) into
--   a downstream one.
propagateRefChain :: RefChain -> Value -> Value
propagateRefChain chain1 v =
  let insert chain2 =
        -- concatenate the chain (older goes at the end)
        chain2 ++ chain1
  in
  case v of
    VDo chain2 env body -> VDo (insert chain2) env body
    VBindOnce pos chain2 v1 v2 -> VBindOnce pos (insert chain2) v1 v2
    VTopLevel pos chain2 f -> VTopLevel pos (insert chain2) f
    VProofScript pos chain2 f -> VProofScript pos (insert chain2) f
    VLLVMCrucibleSetup pos chain2 f -> VLLVMCrucibleSetup pos (insert chain2) f
    VJVMSetup pos chain2 f -> VJVMSetup pos (insert chain2) f
    VMIRSetup pos chain2 f -> VMIRSetup pos (insert chain2) f
    _ -> v


------------------------------------------------------------
-- Environment updates

-- The second argument (the schema, aka type) is Nothing in most
-- cases, but for Decls is taken from the Decl. This will always be
-- Just s for Decls that have been typechecked, which are the only
-- ones we should be handling here.
--
-- Meanwhile the Maybe Type field of PVar is also always Just ty for
-- patterns that have been typechecked, and the typechecker will have
-- established that the type of the pattern matches the type of the
-- Decl if there is one.
--
-- So we should be able to remove the schema argument (and with it the
-- mess for dividing up a passed-in tuple), but for the moment I'm
-- unwilling to in case there's something weird going on somewhere.
-- For the time being we'll just panic if the pattern type is missing
-- and use it to fill in the schema if there isn't a schema passed
-- down. We could also assert that the schema type and the pattern
-- type actually match, but it's intentionally difficult to do that
-- outside the typechecker and not really worthwhile.
--
-- XXX: at some point clean this up further.
--
-- Update: there _is_ something weird going on. The typechecker wasn't
-- updating the types in patterns after doing its generalize step, so
-- for polymorphic bindings the types in patterns weren't usable. But
-- even after fixing that, using the types in the patterns produces
-- the wrong results -- they are not the same tyvars as the ones that
-- appear in the the schema. There's still something going on in
-- there that I don't understand.
--
bindPattern :: SS.Rebindable -> SS.Pattern -> Maybe SS.Schema -> Value -> TopLevel ()
bindPattern rb pat ms v =
  case pat of
    SS.PWild _pos _ ->
      pure ()
    SS.PVar allpos _xpos _x Nothing ->
      panic "bindPattern" [
          "Found pattern with no type in it",
          "Source position: " <> Text.pack (show allpos),
          "Pattern: " <> Text.pack (show pat)
      ]
    SS.PVar _allpos xpos x (Just ty) ->
      let s = fromMaybe (SS.tMono ty) ms in
      extendEnv xpos x rb s Nothing v
    SS.PTuple _pos ps ->
      case v of
        VTuple vs -> do
            let mss = case ms of
                    Nothing ->
                        repeat Nothing
                    Just (SS.Forall ks (SS.TyCon _ (SS.TupleCon _) ts)) ->
                        [ Just (SS.Forall ks t) | t <- ts ]
                    Just t ->
                        panic "bindPattern" [
                            "Expected tuple type, got " <> Text.pack (show t)
                        ]
            sequence_ $ zipWith3 (bindPattern rb) ps mss vs
        _ ->
            panic "bindPatternLocal" [
                "Expected tuple value; got " <> Text.pack (show v)
            ]


------------------------------------------------------------
-- InterpreterMonad

-- Monad class to allow the interpreter to run in the Haskell
-- projection of the five SAWScript monads.
--
-- Note that `getMonadContext` is only used when interpreting at the
-- syntactic top level and thus only applies to the `TopLevel` and
-- `ProofScript` monads. In fact, it used to be that if anything other
-- than one of those was passed down into the typechecker from where
-- `getMonadContext` is called, it would panic. Therefore, it's ok for
-- `getMonadContext` itself to panic for the three Setup cases
-- instead.

class (Monad m, MonadFail m) => InterpreterMonad m where
  liftTopLevel :: TopLevel a -> m a
  actionFromValue :: FromValue a => FromValueHow -> Value -> m a
  mkValue :: SS.Pos -> RefChain -> m Value -> Value
  getMonadContext :: m SS.Context
  pushScopeAny :: m ()
  popScopeAny :: m ()
  withEnvironAny :: Environ -> m a -> m a

instance InterpreterMonad TopLevel where
  liftTopLevel m = m
  actionFromValue = fromValue
  mkValue pos chain m = VTopLevel pos chain m
  getMonadContext = return SS.TopLevel
  pushScopeAny = pushScope
  popScopeAny = popScope
  withEnvironAny = withEnviron

instance InterpreterMonad ProofScript where
  liftTopLevel m = scriptTopLevel m
  actionFromValue = fromValue
  mkValue pos chain m = VProofScript pos chain m
  getMonadContext = return SS.ProofScript
  pushScopeAny = scriptTopLevel pushScope
  popScopeAny = scriptTopLevel popScope
  withEnvironAny = withEnvironProofScript

instance InterpreterMonad LLVMCrucibleSetupM where
  liftTopLevel m = llvmTopLevel m
  actionFromValue = fromValue
  mkValue pos chain m = VLLVMCrucibleSetup pos chain m
  getMonadContext = panic "getMonadContext" ["Called in LLVMSetup"]
  pushScopeAny = llvmTopLevel pushScope
  popScopeAny = llvmTopLevel popScope
  withEnvironAny = withEnvironLLVM

instance InterpreterMonad JVMSetupM where
  liftTopLevel m = jvmTopLevel m
  actionFromValue = fromValue
  mkValue pos chain m = VJVMSetup pos chain m
  getMonadContext = panic "getMonadContext" ["Called in JVMSetup"]
  pushScopeAny = jvmTopLevel pushScope
  popScopeAny = jvmTopLevel popScope
  withEnvironAny = withEnvironJVM

instance InterpreterMonad MIRSetupM where
  liftTopLevel m = mirTopLevel m
  actionFromValue = fromValue
  mkValue pos chain m = VMIRSetup pos chain m
  getMonadContext = panic "getMonadContext" ["Called in MIRSetup"]
  pushScopeAny = mirTopLevel pushScope
  popScopeAny = mirTopLevel popScope
  withEnvironAny = withEnvironMIR


------------------------------------------------------------
-- Typechecker

-- Process a typechecker result.
-- Wraps the typechecker in the stuff needed to print its warnings and errors.
--
-- XXX: this code should probably live inside the typechecker.
--
-- Usage is processTypeCheck $ checkStmt ...
type MsgList = [(SS.Pos, String)]
processTypeCheck :: InterpreterMonad m => (Either MsgList a, MsgList) -> m a
processTypeCheck (errs_or_output, warns) =
  liftTopLevel $ do
    let issueWarning (pos, msg) =
          -- XXX the print functions should be what knows how to show positions...
          printOutLnTop Warn (show pos ++ ": Warning: " ++ msg)
    mapM_ issueWarning warns
    either failTypecheck return errs_or_output


------------------------------------------------------------
-- Interpreter core

-- | Apply an argument value to a function value.
--   v1 must have type a -> b; v2 must have type a.
--   The first (position) argument is the position where the
--   application happens.
--   The second (Text) argument is printed as part of the panic if v1
--   turns out not to be a function value.
applyValue :: SS.Pos -> Text -> Value -> Value -> TopLevel Value
applyValue pos v1info v1 v2 =
  let enter name = pushTraceFrame pos name
      leave = popTraceFrame
  in
  case v1 of
    VLambda env mname pat e -> do
        let name = fromMaybe "(lambda)" mname
        enter name
        r <- withEnviron env $ do
            pushScope
            bindPattern SS.ReadOnlyVar pat Nothing v2
            r' <- interpretExpr e
            popScope
            return r'
        leave
        return $ insertRefChain pos name r
    VBuiltin name args wf -> case wf of
        OneMoreArg f -> do
            setPosition pos
            enter name
            r <- f v2
            leave
            return $ insertRefChain pos name r
        ManyMoreArgs f ->
            -- f will still be partially applied after this, so it
            -- won't do anything and there's no need to enter/leave.
            VBuiltin name (args :|> v2) <$> f v2
    _ ->
        panic "applyValue" [
            "Called object is not a function",
            "Call site: " <> Text.pack (show pos),
            "Value found: " <> Text.pack (show v1),
            v1info
        ]

-- Eval an expression.
--
-- This executes purely: when we see a do-block, return it as a value.
-- If the caller is executing in a monad, it'll intercept that and
-- eval it.
--
-- This code lives in the interpreter monad anyway for two reasons:
-- first, properly, because it needs (readonly) access to the Cryptol
-- environment. This could conceivably just be passed in instead.
--
-- Second, improperly, a randomly-chosen selection of SAWScript
-- builtins are pure in SAWScript but not in Haskell; these execute
-- in TopLevel when the last argument is applied by applyValue, and
-- that happens inside here.
--
interpretExpr :: SS.Expr -> TopLevel Value
interpretExpr expr =
    let ?fileReader = BS.readFile in
    case expr of
      SS.Bool _ b ->
          return $ VBool b
      SS.String _ s ->
          return $ VString s
      SS.Int _ z ->
          return $ VInteger z
      SS.Code pos str -> do
          sc <- getSharedContext
          cenv <- getCryptolEnv
          --io $ putStrLn $ "Parsing code: " ++ show str
          --showCryptolEnv' cenv
          let str' = toInputText pos str
          t <- io $ CEnv.parseTypedTerm sc cenv str'
          return (VTerm t)
      SS.CType pos str -> do
          cenv <- getCryptolEnv
          let str' = toInputText pos str
          s <- io $ CEnv.parseSchema cenv str'
          return (VType s)
      SS.Array _pos es ->
          VArray <$> traverse interpretExpr es
      SS.Block _pos stmts -> do
          env <- gets rwEnviron
          return $ VDo [] env stmts
      SS.Tuple _pos es ->
          VTuple <$> traverse interpretExpr es
      SS.Record _pos bs ->
          VRecord <$> traverse interpretExpr bs
      SS.Index pos e1 e2 -> do
          a <- interpretExpr e1
          i <- interpretExpr e2
          return (indexValue pos a i)
      SS.Lookup pos e n -> do
          a <- interpretExpr e
          return (lookupValue pos a n)
      SS.TLookup pos e i -> do
          a <- interpretExpr e
          return (tupleLookupValue pos a i)
      SS.Var pos x -> do
          avail <- gets rwPrimsAvail
          Environ varenv _tyenv _cryenv <- gets rwEnviron
          rbenv <- gets rwRebindables
          let info = case ScopedMap.lookup x varenv of
                  Nothing ->
                      -- Try the rebindable environment
                      case Map.lookup x rbenv of
                          Nothing -> Nothing
                          Just (_defpos, _ty, v) -> Just (Current, v)
                  Just (_defpos, lc, _ty, v, _doc) -> Just (lc, v)
          case info of
              Nothing ->
                  -- This should be rejected by the typechecker; panic
                  panic "interpretExpr" [
                      "Read of unknown variable " <> x
                  ]
              Just (lc, v)
                | Set.member lc avail -> do
                      let v' = injectPositionIntoMonadicValue pos v
                          v'' = insertRefChain pos x v'
                      return v''
                | otherwise ->
                      -- This case is also rejected by the typechecker
                      panic "interpretExpr" [
                           "Read of inaccessible variable " <> x
                      ]
      SS.Lambda _pos mname pat e -> do
          env <- gets rwEnviron
          return $ VLambda env mname pat e
      SS.Application pos e1 e2 -> do
          let v1info = "Expression: " <> PPS.pShowText e1
          v1 <- interpretExpr e1
          v2 <- interpretExpr e2
          let v2' = injectPositionIntoMonadicValue (SS.getPos e2) v2
          applyValue pos v1info v1 v2'
      SS.Let _ dg e -> do
          pushScope
          interpretDeclGroup SS.ReadOnlyVar dg
          v <- interpretExpr e
          popScope
          return v
      SS.TSig _ e _ ->
          interpretExpr e
      SS.IfThenElse pos e1 e2 e3 -> do
          v1 <- interpretExpr e1
          case v1 of
            VBool b ->
              interpretExpr (if b then e2 else e3)
            _ ->
              panic "interpretExpr" [
                  "Ill-typed value in if-expression (should be Bool)",
                  "Source position: " <> Text.pack (show pos),
                  "Value found: " <> Text.pack (show v1),
                  "Expression: " <> PPS.pShowText e1
              ]

-- Eval a "decl group", which is a let-binding or group of mutually
-- recursive let-bindings.
--
-- The bodies are interpreted purely.
interpretDeclGroup :: SS.Rebindable -> SS.DeclGroup -> TopLevel ()
interpretDeclGroup rebindable dg = case dg of
    SS.NonRecursive (SS.Decl _ pat mt expr) -> do
        v <- interpretExpr expr
        bindPattern rebindable pat mt v
    SS.Recursive ds -> do
        let

            -- Get a value for the body of one of the declarations.
            -- Recursive declaration sets are only allowed to contain
            -- functions; panic if we get anything else.
            --
            -- We return a function taking an environment because we
            -- need to close in the environment containing _all_ the
            -- declarations _into_ all the declarations, which is a
            -- circular knot that can only be constructed in very
            -- specific ways.
            extractFunction x e0 = case e0 of
                SS.Lambda _ mname pat e1 ->
                    \env -> VLambda env mname pat e1
                SS.TSig _ e1 _ ->
                    extractFunction x e1
                _ ->
                    panic "interpretDeclGroup" [
                        "Found non-function in a recursive declaration group",
                        "Name: " <> x,
                        "Expression found: " <> PPS.pShowText e0
                    ]

            -- Get the type (scheme) for one of the declarations.
            extractType x mty = case mty of
                Nothing ->
                    panic "interpretDeclGroup" [
                        "Found declaration with no type in a recursive decl group",
                        "Variable: " <> x
                    ]
                Just ty -> ty

            -- Get the name for one of the declarations.
            -- Recursive declaration sets are only allowed to contain
            -- functions, so the pattern cannot be a tuple.
            extractName pat = case pat of
                SS.PWild _ _ -> Nothing
                SS.PVar _ xpos x _mty -> Just (xpos, x)
                SS.PTuple{} ->
                    panic "interpretDeclGroup" [
                        "Found tuple pattern in a recursive declaration group",
                        "Pattern: " <> Text.pack (show (PP.pretty pat))
                    ]

            -- Get all the info for a decl.
            extractBoth (SS.Decl _ pat mty e) =
                case extractName pat of
                    Nothing -> Nothing
                    Just (xpos, x) ->
                        let ty = extractType x mty
                            fv = extractFunction x e
                        in
                        Just (xpos, x, rebindable, ty, Nothing, fv)

            -- Extract all the info for all decls.
            ds' = mapMaybe extractBoth ds

        -- Now add all the declarations.
        --
        -- Note that the lambdas in all the declarations need the final
        -- resulting environment that contains all the declarations,
        -- which is something of a headache to arrange in Haskell.
        extendEnvMulti ds'

-- Bind a monadic value into the monadic execution sequence.
--
-- Takes a monadic value that might be a VDo, VBindOnce, VReturn, or
-- plain monadic value, run it through the interpreter as necessary to
-- get a plain monadic value, then bind it in Haskell to get a result.
-- Returns the resulting Value. Runs in any interpreter monad.
--
-- Even though this is called from multiple places, in each case it's
-- the interpreter doing a SAWScript-level bind so we are always
-- coming from the interpreter.
--
-- There are three steps:
--    - Run it in the interpreter with interpretMonadAction, in case
--      it's a do-block. (plainVal should then always be a plain
--      monadic value with a Haskell monadic action in it.)
--    - Update the value metadata. (Specifically: insert the bind
--      position into the plain monadic value we get back from the
--      interpreter, as its position of last reference.)
--    - Fetch the Haskell-level monadic action with fromValue and bind
--      that in Haskell to execute it.
--
-- Note that calling interpretMonadAction here is necessary for the
-- moment (even though it's also called from fromValue /
-- actionFromValue) because we need the result to do the position
-- update.
--
bindMonadAction :: forall m. InterpreterMonad m => SS.Pos -> Value -> m Value
bindMonadAction pos baseVal = do
    plainVal <- interpretMonadAction FromInterpreter baseVal
    let plainVal' = injectPositionIntoMonadicValue pos plainVal
    result <- actionFromValue FromInterpreter plainVal'
    return result

-- Execute a monad action. This happens in any of the interpreter
-- monads.
interpretMonadAction :: forall m. InterpreterMonad m => FromValueHow -> Value -> m Value
interpretMonadAction fromHow v = case v of
  VReturn pos chain v' -> do
    -- VReturn ... v' -> VProofScript ... (return v')
    -- (or whichever value for whichever monad)
    let v'' :: m Value = return v'
    return $ mkValue pos chain v''
  VDo chain env body -> do
    liftTopLevel $ do
      case fromHow of
          FromInterpreter -> pure ()
          FromArgument -> pushTraceFrame SS.PosInsideBuiltin "(callback)"
      pushTraceFrames chain

    r <- withEnvironAny env $ do
        pushScopeAny
        r' <- interpretDoStmts body
        popScopeAny
        return r'

    liftTopLevel $ do
      popTraceFrames chain
      case fromHow of
          FromInterpreter -> pure ()
          FromArgument -> popTraceFrame
    return $ propagateRefChain chain r
  VBindOnce pos chain baseVal1 val2 -> do
    -- baseVal1 is a monadic value of the same class as returned by
    -- interpretExpr (that is, it might be a VDo or a VBindOnce).
    -- Bind it.
    --
    -- Note that even if the _bind_ is triggered with FromArgument,
    -- the contents are executed right here from the interpreter.
    --
    -- Wrap the execution (of the whole sequence of binds) in the frames
    -- from the RefChain the same way as a do-block.
    liftTopLevel $ do
      case fromHow of
          FromInterpreter -> pure ()
          FromArgument -> pushTraceFrame SS.PosInsideBuiltin "(callback)"
      pushTraceFrames chain

    result1 <- bindMonadAction pos baseVal1
    -- val2 is a lambda or equivalent that expects the result as an
    -- argument (the traditional >>= form of monad bind)
    result2 <- liftTopLevel $ applyValue pos "Value in a VBindOnce" val2 result1
    result3 <- interpretMonadAction FromInterpreter result2

    liftTopLevel $ do
      popTraceFrames chain
      case fromHow of
          FromInterpreter -> pure ()
          FromArgument -> popTraceFrame
    -- Handle the RefChain the same way as a do-block. Note that with
    -- luck we don't have to worry about unwanted additional RefChain
    -- entries in the second and subsequent VBindOnce values in a
    -- sequence of them; they should never have the opportunity to
    -- grow their own references. If we had an explicit bind operator
    -- in the language, that might be a problem, but we don't and we
    -- aren't getting one. So the only bind sequences we have are
    -- canned. (And in particular there's only one, in the "for"
    -- builtin.)
    return $ propagateRefChain chain result3
  _ -> pure v


-- Eval a statement from a do-block. This happens in some monad; we
-- only come here once the monad action is executed. Therefore, we can
-- execute binds: if we get a do-block back, execute it recursively.
-- (Such a do-block must be in the same monad in order to be well
-- typed.)
--
-- In let-bindings the RHS is evaluated purely.
--
-- Returns the updated local environment.
-- (XXX: should that be stored into the monad context or not? Apparently
-- not, currently.)
--
interpretDoStmt :: forall m. InterpreterMonad m => SS.Stmt -> m ()
interpretDoStmt stmt =
    let ?fileReader = BS.readFile in
    -- XXX are the uses of push/popPosition here suitable? not super clear
    case stmt of
      SS.StmtBind pos pat e -> do
          -- Execute the expression purely first. ("purely")
          baseVal :: Value <- liftTopLevel $ interpretExpr e
          -- Now bind the resulting value to execute it.
          --
          -- No trace frames here because the logic is inside
          -- interpretMonadAction and fromValue (for the interpreter
          -- and Haskell-level execution respectively).
          result :: Value <- bindMonadAction pos baseVal
          -- Bind (in the name-binding, not monad-binding sense) the
          -- result to the pattern.
          liftTopLevel $ bindPattern SS.ReadOnlyVar pat Nothing result
      SS.StmtLet _pos rebindable dg -> do
          -- Process the declarations
          liftTopLevel $ interpretDeclGroup rebindable dg
      SS.StmtCode _ spos str -> do
          liftTopLevel $ do
            sc <- getSharedContext
            ce <- getCryptolEnv
            let str' = toInputText spos str
            ce' <- io $ CEnv.parseDecls sc ce str'
            setCryptolEnv ce'
      SS.StmtImport _ _ ->
          fail "block-level import unimplemented"
      SS.StmtTypedef _ _ name ty -> do
          liftTopLevel $ addTypedef name ty

-- Eval some statements from a do-block.
--
-- The last statement is special because it produces the value of the
-- do-block; it is just an expression and not a statement, and appears
-- as a bind of _. The typechecker enforces that we won't see a block
-- with something else at the end.
--
-- FUTURE: after fixing the environment handling this should be able
-- to just use mapM on the statements and not need to nest the last
-- expression inside recursing on the statements.
--
interpretDoStmts :: forall m. InterpreterMonad m => ([SS.Stmt], SS.Expr) -> m Value
interpretDoStmts (stmts, lastexpr) =
    case stmts of
      [] -> do
          -- The position for the bind we're about to do will be the
          -- source position of the expression.
          let pos = SS.getPos lastexpr

          -- Execute the expression purely first.
          baseVal :: Value <- liftTopLevel $ interpretExpr lastexpr

          -- Now (monad-)bind the resulting value and execute it.

          -- If we got a do-block or similar back, execute it now.
          --
          -- In principle we should return the plain monadic value as
          -- the result of the block and let the caller execute
          -- it. Instead, bind it now and construct a return of the
          -- result. (As in: replace "do { ...; e; }" with "do { ...;
          -- r <- e; return r; }".) In the common case where the last
          -- expression is just a return, this has no effect, and
          -- these are semantically equivalent; but if it actually
          -- does something, letting the caller execute it is akin to
          -- tail-call optimization and breaks stack traces.
          --
          -- FUTURE: do this transform on the AST upstream before
          -- executing; that can more readily avoid doing the
          -- transform if the last expression is already a return.
          --
          -- No trace frames here because the logic is inside
          -- interpretMonadAction and fromValue (for the interpreter
          -- and Haskell-level execution respectively).
          --
          result :: Value <- bindMonadAction pos baseVal

          -- Don't return a VReturn here, because there isn't
          -- necessarily a following call to interpretMonadAction to
          -- unfold it. Instead, produce the unfolded form directly.
          -- Which requires some gyrations to feed the monad type in.
          let result' :: m Value = return result
          return $ mkValue pos [] result'

      stmt : more -> do
          -- Execute the expression and update the environment
          interpretDoStmt stmt
          -- Run the rest of the block with the updated environment
          v <- interpretDoStmts (more, lastexpr)
          return v

-- Execute a top-level bind.
processStmtBind ::
  InterpreterMonad m =>
  Bool ->
  SS.Pos ->
  SS.Pattern ->
  SS.Expr ->
  m ()
processStmtBind printBinds pos pat expr = do

  -- Eval the expression
  baseVal <- liftTopLevel $ interpretExpr expr

  -- Fetch the type from updated pattern, since the typechecker will
  -- have filled it in there.
  --
  -- Note that this type won't include the current monad type, because
  -- it's the type of the value that the pattern on the left of <- is
  -- trying to bind.
  let ty = getType pat

  -- Reject polymorphic values. XXX: as noted above this should either
  -- be inside the typechecker or restricted to the repl.
  when (isPolymorphic ty) $ fail $ "Not a monomorphic type: " ++ PPS.pShow ty

  -- Now bind the resulting value using bindMonadAction.
  --
  -- No trace frames here because the logic is inside
  -- interpretMonadAction and fromValue (for the interpreter and
  -- Haskell-level execution respectively).
  --
  result <- bindMonadAction pos baseVal

  --io $ putStrLn $ "Top-level bind: " ++ show mx
  --showCryptolEnv

  -- When in the repl, print the result.
  when printBinds $ do
    opts <- liftTopLevel $ gets rwPPOpts

    -- Extract the variable, if any, from the pattern. If there isn't
    -- any single variable use "it".
    let name = case pat of
          SS.PWild _patpos _t -> "it"
          SS.PVar _patpos _xpos x _t -> x
          SS.PTuple _patpos _pats -> "it"

    -- Print non-unit result if it was not bound to a variable
    case pat of
      SS.PWild _ _ | not (isVUnit result) ->
        liftTopLevel $
        do nenv <- io . scGetNamingEnv =<< getSharedContext
           printOutLnTop Info (showsPrecValue opts nenv 0 result "")
      _ -> return ()

    -- Print function type if result was a function
    case ty of
      SS.TyCon _ SS.FunCon _ ->
        liftTopLevel $ printOutLnTop Info $ Text.unpack $ name <> " : " <> PPS.pShowText ty
      _ -> return ()

  liftTopLevel $ bindPattern SS.ReadOnlyVar pat (Just (SS.tMono ty)) result

-- | Interpret a top-level statement in an interpreter monad (any of the SAWScript monads)
--   This duplicates the logic in interpretDoStmt for no particularly good reason.
interpretTopStmt :: InterpreterMonad m =>
  Bool {-^ whether to print non-unit result values -} ->
  SS.Stmt ->
  m ()
interpretTopStmt printBinds stmt = do
  let ?fileReader = BS.readFile

  avail <- liftTopLevel $ gets rwPrimsAvail
  ctx <- getMonadContext

  stmt' <- do
      -- XXX this is not the right way to do this
      --    - shouldn't have to flatten the environments
      --    - shouldn't be typechecking one statement at a time regardless
      Environ varenv tyenv _cryenvs <- liftTopLevel $ gets rwEnviron
      rbenv <- liftTopLevel $ gets rwRebindables
      let varenv' = Map.map (\(pos, lc, ty, _v, _doc) -> (pos, lc, SS.ReadOnlyVar, ty)) $ ScopedMap.flatten varenv
          rbenv' = Map.map (\(pos, ty, _v) -> (pos, SS.Current, SS.RebindableVar, ty)) rbenv
          -- If anything appears in both, favor the real environment
          varenv'' = Map.union varenv' rbenv'

      let tyenv' = ScopedMap.flatten tyenv
      processTypeCheck $ checkStmt avail varenv'' tyenv' ctx stmt

  case stmt' of

    SS.StmtBind pos pat expr -> do
      -- Note that while liftTopLevel $ processStmtBind will typecheck,
      -- that runs it in TopLevel and not the current monad, which might
      -- be ProofScript, and then things come unstuck. See #2494.
      processStmtBind printBinds pos pat expr

    SS.StmtLet _pos rebindable dg ->
      liftTopLevel $ interpretDeclGroup rebindable dg

    SS.StmtCode _ spos str ->
      liftTopLevel $ do
         sc <- getSharedContext
         cenv <- getCryptolEnv
         --io $ putStrLn $ "Processing toplevel code: " ++ show str
         --showCryptolEnv
         cenv' <- io $ CEnv.parseDecls sc cenv $ toInputText spos str
         setCryptolEnv cenv'
         --showCryptolEnv

    SS.StmtImport _ imp ->
      liftTopLevel $ do
         sc <- getSharedContext
         cenv <- getCryptolEnv
         --showCryptolEnv
         let mLoc = iModule imp
             qual = iAs imp
             spec = iSpec imp
         cenv' <- io $ CEnv.importCryptolModule sc cenv mLoc qual CEnv.PublicAndPrivate spec
         setCryptolEnv cenv'
         --showCryptolEnv

    SS.StmtTypedef _ _ name ty ->
      liftTopLevel $ addTypedef name ty

-- Hook for AutoMatch
stmtInterpreter :: StmtInterpreter
stmtInterpreter ro rw stmts =
  -- What AutoMatch provides is supposed to be a full script for the
  -- syntactic top level, not a do-block. Run it with interpretTopStmt
  -- so as to (a) get the right behavior (as long as interpretTopStmt
  -- and interpretDoStmt are different, which they are) and (b) avoid
  -- needing to provide a block result value.
  --
  -- XXX what scope should this use? Prior to #2720 it substituted an
  -- empty "local environment" for the current "local environment",
  -- which would have dropped an ill-specified part of the namespace.
  -- That wasn't particularly sensible and probably wasn't correct,
  -- but we could reasonably here want either the current environment
  -- or a copy of the environment captured when we start AutoMatch,
  -- and it's not obvious which. For the moment, we'll use the current
  -- environment because that doesn't require any fiddling.
  fst <$> runTopLevel (mapM_ (interpretTopStmt False) stmts) ro rw

interpretFile :: FilePath -> Bool {- ^ run main? -} -> TopLevel ()
interpretFile file runMain =
  bracketTopLevel (io getCurrentDirectory) (io . setCurrentDirectory) (const interp)
  where
    interp = do
      opts <- getOptions
      errs_or_stmts <- io $ Loader.findAndLoadFileUnchecked opts file
      stmts <- do
        case errs_or_stmts of
          Left errs -> do
            -- Don't use Text.unlines here; it inserts a newline at
            -- the end and that produces extra blank lines in the
            -- output.
            throwTopLevel $ Text.unpack $ Text.intercalate "\n" errs
          Right stmts -> pure stmts
      io $ setCurrentDirectory (takeDirectory file)
      mapM_ stmtWithPrint stmts
      when runMain interpretMain
      writeVerificationSummary

    stmtWithPrint s = do
      let withPos str =
            unlines $ ("[output] at " ++ show (SS.getPos s) ++ ": ") :
                      map (\l -> "\t"  ++ l) (lines str)
      showLoc <- printShowPos <$> getOptions
      if showLoc then
        let wrapPrint oldFn = \lvl str -> oldFn lvl (withPos str)
            withPrint opts = opts { printOutFn = wrapPrint (printOutFn opts) }
        in
        withOptions withPrint (interpretTopStmt False s)
      else
        interpretTopStmt False s

-- | Evaluate the value called 'main' from the current environment.
interpretMain :: TopLevel ()
interpretMain = do
  avail <- gets rwPrimsAvail
  Environ varenv tyenv _cryenv <- gets rwEnviron
  rbenv <- gets rwRebindables
  let pos = SS.PosInternal "entry"
      -- We need the type to be "TopLevel a", not just "TopLevel ()".
      -- There are several (old) tests in the test suite whose main
      -- returns something, e.g. several are TopLevel Theorem because
      -- they call prove_print or prove_sat or whatever and don't
      -- explicitly throw away the result.
      tyRet = SS.TyVar pos "a"
      tyMonadic = SS.tBlock pos (SS.tContext pos SS.TopLevel) tyRet
      tyExpected = SS.Forall [(pos, "a")] tyMonadic
  let main = case ScopedMap.lookup "main" varenv of
          Just (_defpos, lc, tyFound, v, _doc) -> Just (lc, tyFound, v)
          -- Having main be rebindable doesn't make much sense, but
          -- it's easier to have this code than to spend time
          -- explaining that it's not allowed.
          Nothing -> case Map.lookup "main" rbenv of
              Nothing -> Nothing
              Just (_defpos, tyFound, v) -> Just (Current, tyFound, v)
  case main of
    Nothing ->
      -- Don't fail or complain if there's no main.
      return ()
    Just (Current, tyFound, v) -> case tyFound of
        SS.Forall _ (SS.TyCon _ SS.BlockCon [_, _]) ->
            -- XXX shouldn't have to do this
            let tyenv' = ScopedMap.flatten tyenv in
            -- It looks like a monadic value, so check more carefully.
            case typesMatch avail tyenv' tyFound tyExpected of
              False ->
                  -- While we accept any TopLevel a, don't encourage people
                  -- to do that.
                  fail "There is a 'main' defined but its type is not TopLevel ()"
              True -> do
                  let v' = injectPositionIntoMonadicValue pos v
                      v'' = insertRefChain pos "main" v'
                  fromValue FromInterpreter v''
        _ ->
            -- If the type is something entirely random, like a Term or a
            -- String or something, just ignore it.
            return ()
    Just (lc, _ty, _v) ->
      -- There is no way for things other than primitives to get marked
      -- experimental or deprecated, so this isn't possible. If we allow
      -- users to deprecate their own functions in the future, change
      -- this message to an actual error that says something snarky :-)
      panic "Interpreter" [
          "Unexpected lifecycle state " <> Text.pack (show lc) <> " for main"
      ]


buildTopLevelEnv :: Options
                 -> [Text]
                 -> TopLevelShellHook
                 -> ProofScriptShellHook
                 -> IO (TopLevelRO, TopLevelRW)
buildTopLevelEnv opts scriptArgv tlhook pshook = do
       let proxy = AIGProxy AIG.compactProxy
       let mn = mkModuleName ["SAWScript"]
       sc <- mkSharedContext
       let ?fileReader = BS.readFile
       CryptolSAW.scLoadPreludeModule sc
       CryptolSAW.scLoadCryptolModule sc
       scLoadModule sc (emptyModule mn)
       ss <- basic_ss sc
       currDir <- getCurrentDirectory
       mb_cache <- lookupEnv "SAW_SOLVER_CACHE_PATH" >>= \case
         Just path | not (null path) -> Just <$> lazyOpenSolverCache path
         _ -> return Nothing
       Crucible.withHandleAllocator $ \halloc -> do
       let ro0 = TopLevelRO
                   { roOptions = opts
                   , roArgv = scriptArgv
                   , roHandleAlloc = halloc
                   , roProxy = proxy
                   , roInitWorkDir = currDir
                   , roBasicSS = ss
                   , roSubshell = tlhook
                   , roProofSubshell = pshook
                   }
       let bic = BuiltinContext {
                   biSharedContext = sc
                 , biBasicSS = ss
                 }
       ce0 <- CEnv.initCryptolEnv sc
       let cryenv0 = CryptolEnvStack ce0 []

       jvmTrans <- CJ.mkInitialJVMContext halloc

       let rw0 = TopLevelRW
                   { rwEnviron = primEnviron opts bic cryenv0
                   , rwRebindables = Map.empty
                   , rwPosition = SS.Unknown
                   , rwStackTrace = Trace.empty
                   , rwProofs     = []
                   , rwPPOpts     = PPS.defaultOpts
                   , rwSharedContext = sc
                   , rwSolverCache = mb_cache
                   , rwTheoremDB = emptyTheoremDB
                   , rwJVMTrans   = jvmTrans
                   , rwPrimsAvail = defaultAvailable
                   , rwSMTArrayMemoryModel = False
                   , rwCrucibleAssertThenAssume = False
                   , rwProfilingFile = Nothing
                   , rwLaxArith = False
                   , rwLaxPointerOrdering = False
                   , rwLaxLoadsAndStores = False
                   , rwDebugIntrinsics = True
                   , rwWhat4HashConsing = False
                   , rwWhat4HashConsingX86 = False
                   , rwWhat4Eval = False
                   , rwPreservedRegs = []
                   , rwStackBaseAlign = defaultStackBaseAlign
                   , rwAllocSymInitCheck = True
                   , rwWhat4PushMuxOps = False
                   , rwNoSatisfyingWriteFreshConstant = True
                   , rwCrucibleTimeout = CC.defaultSAWCoreBackendTimeout
                   , rwPathSatSolver = CC.PathSat_Z3
                   , rwSkipSafetyProofs = False
                   , rwSingleOverrideSpecialCase = False
                   , rwSequentGoals = False
                   , rwJavaCodebase = JavaUninitialized
                   }
       return (ro0, rw0)

processFile ::
  Options ->
  FilePath ->
  [Text] ->
  TopLevelShellHook ->
  ProofScriptShellHook ->
  IO ()
processFile opts file scriptArgv tlhook pshook = do
  (ro, rw) <- buildTopLevelEnv opts scriptArgv tlhook pshook
  _ <- runTopLevel (interpretFile file True) ro rw
            `X.catch` (handleException opts)
  return ()


------------------------------------------------------------
-- IsValue and FromValue

-- | Class for injecting Haskell values into SAWScript values. This
--   is straightforward for scalars. For functions, it gets a bit
--   wibbly.
--
--   First, some history. Until July 2025 there was a relatively
--   straightforward IsValue instance for (a -> b) that matched any
--   argument type a that supported FromValue, and any result type
--   supporting IsValue, including functions. Thus, because Haskell
--   functions are curried, functions of more than one argument would
--   generate a Value that took one argument and produced a result
--   recursively using the IsValue instance for the rest of the
--   function. This produced a chain of Values, each being a closure
--   of type Value -> TopLevel Value, and the interpreter could call
--   them by applying argument Values one at a time.
--
--   This is fine as long as you're ok with blindly applying arguments
--   until you get something else back, which is fine as long as all
--   the interpreter does is execute. However, there are some other
--   things we'd like to have: correct stack traces require knowing
--   the name of the function being called at the application of the
--   last argument. Nice stack traces also involve having the
--   arguments to the function at that point. Furthermore, if all you
--   have in the Value is a closure, and someone wants to print it for
--   debugging, all you can print is "<<closure>>" or "<<function>>"
--   or similar. It would be much nicer to at least be able to print
--   the name of the builtin hiding in the closure.
--
--   For all of these things, one wants additional info in the Value
--   besides just the closure, and critically, that info needs to be
--   carried over when an argument is applied. It is really ugly to do
--   that if you just have a closure that returns an arbitrary Value;
--   you have to apply the argument, unwrap the result and then try to
--   guess if you just applied the last argument and got a return
--   value (which might also be a lambda from somewhere else) or you
--   didn't and you should cary the metadata over. That really won't
--   do.
--
--   Therefore, in July 2025, we added another type BuiltinWrapper to
--   hold the closure chain. There are two cases of BuiltinWrapper,
--   one where you apply the last arg and get a Value back, and one
--   where you apply something less than the last arg and get a new
--   BuiltinWrapper back. Therefore, when applying an argument to a
--   value holding a builtin function, you can branch on the cases,
--   and if what you have is still a partly applied builtin, you can
--   carry over the metadata and update it accordingly. Furthermore,
--   for the purposes of managing the stack trace, you can know when
--   you're applying the last argument, because that's the time when
--   you need to add a frame to the trace.
--
--   In this environment, IsValue for a function must generate a chain
--   of BuiltinWrappers rather than a chain of Values. This turns out
--   to be problematic. A tidy way to do it would be to have a
--   separate IsFuncValue class that recursively collects that chain,
--   then have a single flat IsValue instance for functions that
--   splices it in. Or, alternatively, make IsFuncValue and
--   IsBaseValue classes, and then an umbrella IsValue class that
--   pulls them both in. None of this works. You can't have instances
--   of the form "instance IsBaseValue a => IsValue a"; Haskell treats
--   this as one instance for all types a, rather than as a derivation
--   rule to generate an instance for any type a that matches the
--   constraints.
--
--   Instead, we keep a single `IsValue` class and instead add more
--   members to it.
--
--   The `toValue` member produces a Value; this is the external entry
--   point, so it gets called on scalars and all full complete
--   function types in the builtins table.
--
--   The `isFunction` member returns a boolean indicating whether the
--   value type we're handling is a function. This function requires a
--   value of the appropriate type in order to allow the typeclass to
--   match, but doesn't use it. The class provides a default
--   implementation of False, which is overridden explicitly only in
--   the instance for functions.
--
--   The `toWrapper` member produces a `BuiltinWrapper`. The instance
--   for functions uses this to recurse and produce the chain of
--   `BuiltinWrapper` values containing closures. It uses
--   `isBaseValue` on the function return type to check whether it's
--   on the last argument or not, and constructs the wrapper
--   accordingly. A default implementation that panics is provided;
--   only the function instance overrides that.
--
--   Be careful: there's a possible hole in this logic, which is that
--   we treat Value itself as a non-function value. There needs to be
--   an IsValue instance for Value, because there are a number of
--   builtins whose Haskell type involves Value, generally in order to
--   be polymorphic at the SAWScript level. Any builtin that _returns_
--   Value (arguments use FromValue and are safe from these concerns),
--   and want that Value to wrap a Haskell function, need to cons up
--   the proper BuiltinWrapper chain by hand. A few examples exist.
--
--   (Also note that it must work this way; we _cannot_ examine the
--   argument to `isFunction` because the `toWrapper` logic for
--   functions must decide which case it's looking at without calling
--   its function to get a value of the proper type and there isn't
--   any other concrete one to use.)
--
--   There is no FromValue instance for functions. If we want to have
--   builtins taking callback arguments, we'll need to do something
--   about that, and it'll probably get complicated. (Currently
--   everything that looks like a callback is a monadic action taking
--   no arguments.)
--
--   Note if working on this code that any change to the logic that
--   involves additional annotations or explicitly distinguishing
--   functions from scalars will require touching ~every entry in the
--   builtins table, and there are a _lot_ of builtins.
--
--   Also be aware that there are a handful of builtins that _execute_
--   in TopLevel when applied, rather than returning a SAWScript
--   TopLevel action.  As things stand these _must_ circumvent this
--   logic and not use toValue directly; there is no way to get the
--   function values generated herein to behave that way, because
--   there's no difference in the types to work from.
--
class IsValue a where
    toValue :: Text -> a -> Value
    -- these will be overridden on the function instance
    isFunction :: a -> Bool
    isFunction _ = False
    toWrapper :: Text -> a -> BuiltinWrapper
    toWrapper _ _ = panic "toWrapper" ["Invalid call on base value"]

-- | Flag to indicate where/how fromValue was triggered.
--   (Could be just a Bool, but having it be its own thing increases
--   legibility and this whole set of arrangements is delicate.)
data FromValueHow = FromInterpreter | FromArgument

class FromValue a where
    fromValue :: FromValueHow -> Value -> a

instance (FromValue a, IsValue b) => IsValue (a -> b) where
    toValue name f = VBuiltin name Seq.empty $ toWrapper name f
    isFunction _ = True
    toWrapper name f =
        -- | isFunction needs a value of type b, which we don't have,
        --   but doesn't look at it, so we can use a placeholder, and
        --   it's ok for it to be a bomb.
        let hook :: b = panic "toWrapper" ["isFunction must have used its argument"] in
        if isFunction hook then
          let f' v = return $ toWrapper name (f (fromValue FromArgument v)) in
          ManyMoreArgs f'
        else
          let f' v = return $ toValue name (f (fromValue FromArgument v)) in
          OneMoreArg f'

instance FromValue Value where
    fromValue _ x = x

instance IsValue Value where
    toValue _name x = x

instance IsValue () where
    toValue _name _ = VTuple []

instance FromValue () where
    fromValue _ _ = ()

instance (IsValue a, IsValue b) => IsValue (a, b) where
    toValue name (x, y) = VTuple [toValue name x, toValue name y]

instance (FromValue a, FromValue b) => FromValue (a, b) where
    fromValue how (VTuple [x, y]) = (fromValue how x, fromValue how y)
    fromValue _ _ = error "fromValue (,)"

instance (IsValue a, IsValue b, IsValue c) => IsValue (a, b, c) where
    toValue name (x, y, z) = VTuple [toValue name x, toValue name y, toValue name z]

instance (FromValue a, FromValue b, FromValue c) => FromValue (a, b, c) where
    fromValue how (VTuple [x, y, z]) = (fromValue how x, fromValue how y, fromValue how z)
    fromValue _ _ = error "fromValue (,,)"

instance IsValue a => IsValue [a] where
    toValue name xs = VArray (map (toValue name) xs)


instance FromValue a => FromValue [a] where
    fromValue how (VArray xs) = map (fromValue how) xs
    fromValue _ _ = error "fromValue []"


-- | Common logic for the FromValue instances for plain monadic values.
--   Runs in any interpreter monad.
--
--   Note: this won't actually run until the result action is bound into
--   the execution sequence somewhere (downstream from fromValue).
preparePlainMonadicAction ::
  forall m a. InterpreterMonad m => FromValueHow -> SS.Pos -> RefChain -> m a -> m a
preparePlainMonadicAction how pos chain action = do
  liftTopLevel $ do
    setPosition pos
    case how of
        FromInterpreter -> pure ()
        FromArgument -> pushTraceFrame SS.PosInsideBuiltin "(callback)"
    pushTraceFrames chain
  ret <- action
  liftTopLevel $ do
    popTraceFrames chain
    case how of
        FromInterpreter -> pure ()
        FromArgument -> popTraceFrame
  return ret

instance IsValue a => IsValue (IO a) where
    toValue name action = toValue name (io action)

instance IsValue a => IsValue (TopLevel a) where
    toValue name action =
      VTopLevel atRestPos [] (fmap (toValue name) action)

instance FromValue a => FromValue (TopLevel a) where
    fromValue how v = do
      v' <- interpretMonadAction how v
      case v' of
        VTopLevel pos chain action ->
          fromValue how <$> preparePlainMonadicAction how pos chain action
        _ ->
          panic "fromValue (TopLevel)" [
              "Invalid/ill-typed value: " <> Text.pack (show v')
          ]

instance IsValue a => IsValue (ProofScript a) where
    toValue name m =
      VProofScript atRestPos [] (fmap (toValue name) m)

instance FromValue a => FromValue (ProofScript a) where
    fromValue how v = do
      v' <- interpretMonadAction how v
      case v' of
        VProofScript pos chain action ->
          fromValue how <$> preparePlainMonadicAction how pos chain action
        _ ->
          panic "fromValue (ProofScript)" [
              "Invalid/ill-typed value: " <> Text.pack (show v')
          ]

instance IsValue a => IsValue (LLVMCrucibleSetupM a) where
    toValue name m =
      VLLVMCrucibleSetup atRestPos [] (fmap (toValue name) m)

instance FromValue a => FromValue (LLVMCrucibleSetupM a) where
    fromValue how v = do
      v' <- interpretMonadAction how v
      case v' of
        VLLVMCrucibleSetup pos chain action ->
          fromValue how <$> preparePlainMonadicAction how pos chain action
        _ ->
          panic "fromValue (LLVMSetup)" [
              "Invalid/ill-typed value: " <> Text.pack (show v')
          ]

instance IsValue a => IsValue (JVMSetupM a) where
    toValue name m =
      VJVMSetup atRestPos [] (fmap (toValue name) m)

instance FromValue a => FromValue (JVMSetupM a) where
    fromValue how v = do
      v' <- interpretMonadAction how v
      case v' of
        VJVMSetup pos chain action ->
          fromValue how <$> preparePlainMonadicAction how pos chain action
        _ ->
          panic "fromValue (JVMSetup)" [
              "Invalid/ill-typed value: " <> Text.pack (show v')
          ]

instance IsValue a => IsValue (MIRSetupM a) where
    toValue name m =
      VMIRSetup atRestPos [] (fmap (toValue name) m)

instance FromValue a => FromValue (MIRSetupM a) where
    fromValue how v = do
      v' <- interpretMonadAction how v
      case v' of
        VMIRSetup pos chain action ->
          fromValue how <$> preparePlainMonadicAction how pos chain action
        _ ->
          panic "fromValue (MIRSetup)" [
              "Invalid/ill-typed value: " <> Text.pack (show v')
          ]

instance IsValue (CIR.AllLLVM CMS.SetupValue) where
  toValue _name v = VLLVMCrucibleSetupValue v

instance FromValue (CIR.AllLLVM CMS.SetupValue) where
  fromValue _ (VLLVMCrucibleSetupValue v) = v
  fromValue _ _ = error "fromValue Crucible.SetupValue"

instance IsValue (CMS.SetupValue CJ.JVM) where
  toValue _name v = VJVMSetupValue v

instance FromValue (CMS.SetupValue CJ.JVM) where
  fromValue _ (VJVMSetupValue v) = v
  fromValue _ _ = error "fromValue Crucible.SetupValue"

instance IsValue (CMS.SetupValue MIR) where
  toValue _name v = VMIRSetupValue v

instance FromValue (CMS.SetupValue MIR) where
  fromValue _ (VMIRSetupValue v) = v
  fromValue _ _ = error "fromValue Crucible.SetupValue"

instance IsValue SAW_CFG where
    toValue _name t = VCFG t

instance FromValue SAW_CFG where
    fromValue _ (VCFG t) = t
    fromValue _ _ = error "fromValue CFG"

instance IsValue (CIR.SomeLLVM CMS.ProvedSpec) where
    toValue _name mir = VLLVMCrucibleMethodSpec mir

instance FromValue (CIR.SomeLLVM CMS.ProvedSpec) where
    fromValue _ (VLLVMCrucibleMethodSpec mir) = mir
    fromValue _ _ = error "fromValue ProvedSpec LLVM"

instance IsValue (CMS.ProvedSpec CJ.JVM) where
    toValue _name t = VJVMMethodSpec t

instance FromValue (CMS.ProvedSpec CJ.JVM) where
    fromValue _ (VJVMMethodSpec t) = t
    fromValue _ _ = error "fromValue ProvedSpec JVM"

instance IsValue (CMS.ProvedSpec MIR) where
    toValue _name t = VMIRMethodSpec t

instance FromValue (CMS.ProvedSpec MIR) where
    fromValue _ (VMIRMethodSpec t) = t
    fromValue _ _ = error "fromValue ProvedSpec MIR"

instance IsValue ModuleSkeleton where
    toValue _name s = VLLVMModuleSkeleton s

instance FromValue ModuleSkeleton where
    fromValue _ (VLLVMModuleSkeleton s) = s
    fromValue _ _ = error "fromValue ModuleSkeleton"

instance IsValue FunctionSkeleton where
    toValue _name s = VLLVMFunctionSkeleton s

instance FromValue FunctionSkeleton where
    fromValue _ (VLLVMFunctionSkeleton s) = s
    fromValue _ _ = error "fromValue FunctionSkeleton"

instance IsValue SkeletonState where
    toValue _name s = VLLVMSkeletonState s

instance FromValue SkeletonState where
    fromValue _ (VLLVMSkeletonState s) = s
    fromValue _ _ = error "fromValue SkeletonState"

instance IsValue FunctionProfile where
    toValue _name s = VLLVMFunctionProfile s

instance FromValue FunctionProfile where
    fromValue _ (VLLVMFunctionProfile s) = s
    fromValue _ _ = error "fromValue FunctionProfile"

instance IsValue (AIGNetwork) where
    toValue _name t = VAIG t

instance FromValue (AIGNetwork) where
    fromValue _ (VAIG t) = t
    fromValue _ _ = error "fromValue AIGNetwork"

instance IsValue TypedTerm where
    toValue _name t = VTerm t

instance FromValue TypedTerm where
    fromValue _ (VTerm t) = t
    fromValue _ _ = error "fromValue TypedTerm"

instance FromValue Term where
    fromValue _ (VTerm t) = ttTerm t
    fromValue _ _ = error "fromValue SharedTerm"

instance IsValue Cryptol.Schema where
    toValue _name s = VType s

instance FromValue Cryptol.Schema where
    fromValue _ (VType s) = s
    fromValue _ _ = error "fromValue Schema"

instance IsValue Text where
    toValue _name n = VString n

instance FromValue Text where
    fromValue _ (VString n) = n
    fromValue _ _ = error "fromValue Text"

instance IsValue Integer where
    toValue _name n = VInteger n

instance FromValue Integer where
    fromValue _ (VInteger n) = n
    fromValue _ _ = error "fromValue Integer"

instance IsValue Int where
    toValue _name n = VInteger (toInteger n)

instance FromValue Int where
    fromValue _ (VInteger n)
      | toInteger (minBound :: Int) <= n &&
        toInteger (maxBound :: Int) >= n = fromIntegral n
      | otherwise = error $ "fromValue Int: out of range: " ++ show n
    fromValue _ _ = error "fromValue Int"

instance IsValue Bool where
    toValue _name b = VBool b

instance FromValue Bool where
    fromValue _ (VBool b) = b
    fromValue _ _ = error "fromValue Bool"

instance IsValue SAWSimpset where
    toValue _name ss = VSimpset ss

instance FromValue SAWSimpset where
    fromValue _ (VSimpset ss) = ss
    fromValue _ _ = error "fromValue Simpset"

instance IsValue Theorem where
    toValue _name t = VTheorem t

instance FromValue Theorem where
    fromValue _ (VTheorem t) = t
    fromValue _ _ = error "fromValue Theorem"

instance IsValue BisimTheorem where
    toValue _name = VBisimTheorem

instance FromValue BisimTheorem where
    fromValue _ (VBisimTheorem t) = t
    fromValue _ _ = error "fromValue BisimTheorem"

instance IsValue JavaType where
    toValue _name t = VJavaType t

instance FromValue JavaType where
    fromValue _ (VJavaType t) = t
    fromValue _ _ = error "fromValue JavaType"

instance IsValue LLVM.Type where
    toValue _name t = VLLVMType t

instance FromValue LLVM.Type where
    fromValue _ (VLLVMType t) = t
    fromValue _ _ = error "fromValue LLVMType"

instance IsValue MIR.Ty where
    toValue _name t = VMIRType t

instance FromValue MIR.Ty where
    fromValue _ (VMIRType t) = t
    fromValue _ _ = error "fromValue MIRType"

instance IsValue CEnv.ExtCryptolModule where
    toValue _name m = VCryptolModule m

instance FromValue CEnv.ExtCryptolModule where
    fromValue _ (VCryptolModule m) = m
    fromValue _ _ = error "fromValue CryptolModule"

instance IsValue JSS.Class where
    toValue _name c = VJavaClass c

instance FromValue JSS.Class where
    fromValue _ (VJavaClass c) = c
    fromValue _ _ = error "fromValue JavaClass"

instance IsValue (Some CIR.LLVMModule) where
    toValue _name m = VLLVMModule m

instance IsValue (CIR.LLVMModule arch) where
    toValue _name m = VLLVMModule (Some m)

instance FromValue (Some CIR.LLVMModule) where
    fromValue _ (VLLVMModule m) = m
    fromValue _ _ = error "fromValue LLVMModule"

instance IsValue MIR.RustModule where
    toValue _name m = VMIRModule m

instance FromValue MIR.RustModule where
    fromValue _ (VMIRModule m) = m
    fromValue _ _ = error "fromValue RustModule"

instance IsValue MIR.Adt where
    toValue _name adt = VMIRAdt adt

instance FromValue MIR.Adt where
    fromValue _ (VMIRAdt adt) = adt
    fromValue _ _ = error "fromValue Adt"

instance IsValue ProofResult where
   toValue _name r = VProofResult r

instance FromValue ProofResult where
   fromValue _ (VProofResult r) = r
   fromValue _ v = error $ "fromValue ProofResult: " ++ show v

instance IsValue SatResult where
   toValue _name r = VSatResult r

instance FromValue SatResult where
   fromValue _ (VSatResult r) = r
   fromValue _ v = error $ "fromValue SatResult: " ++ show v

instance IsValue CMS.GhostGlobal where
  toValue _name x = VGhostVar x

instance FromValue CMS.GhostGlobal where
  fromValue _ (VGhostVar r) = r
  fromValue _ v = error ("fromValue GlobalVar: " ++ show v)

instance IsValue Yo.YosysIR where
  toValue _name ym = VYosysModule ym

instance FromValue Yo.YosysIR where
  fromValue _ (VYosysModule ir) = ir
  fromValue _ v = error ("fromValue YosysIR: " ++ show v)

instance IsValue Yo.YosysImport where
  toValue _name yi = VYosysImport yi

instance FromValue Yo.YosysImport where
  fromValue _ (VYosysImport i) = i
  fromValue _ v = error ("fromValue YosysImport: " ++ show v)

instance IsValue Yo.YosysSequential where
  toValue _name ysq = VYosysSequential ysq

instance FromValue Yo.YosysSequential where
  fromValue _ (VYosysSequential s) = s
  fromValue _ v = error ("fromValue YosysSequential: " ++ show v)

instance IsValue Yo.YosysTheorem where
  toValue _name yt = VYosysTheorem yt

instance FromValue Yo.YosysTheorem where
  fromValue _ (VYosysTheorem thm) = thm
  fromValue _ v = error ("fromValue YosysTheorem: " ++ show v)


------------------------------------------------------------
-- Primitives

add_primitives :: PrimitiveLifecycle -> BuiltinContext -> Options -> TopLevel ()
add_primitives lc _bic _opts = do
  rw <- getTopLevelRW
  putTopLevelRW rw {
    rwPrimsAvail = Set.insert lc (rwPrimsAvail rw)
  }

-- The subshell command.
--
-- The SubshellHook is an IO action that takes interpreter state and
-- runs the REPL. (Because it recurses back into the repl, it has to
-- be passed down to us as a closure; it's stored in TopLevelRO while
-- we execute.)
--
-- This function is bound into the interpreter with `pureVal`, which
-- means the returned TopLevel action gets wrapped in a `Value` and is
-- not bound into the Haskell-level monad sequencing until the
-- interpreter unwraps it. (That happens when the value is monad-bound
-- in SAWScript and not, in particular, just when the () is applied to
-- the SAWScript name "subshell".)
--
-- This should prevent former weirdnesses like x not appearing in the
-- subshell context in:
--
--    do { let s = subshell (); let x = 3; s; return (); };
--
-- because the TopLevelRW got fetched at the wrong point.
--
-- But note that because the SAWScript interpreter is very fragile it
-- is very easy for these things to regress.
--
toplevelSubshell :: () -> TopLevel Value
toplevelSubshell () = do
    pushScope
    ro <- ask
    rw <- get
    let hook = roSubshell ro
    rw' <- liftIO $ hook ro rw
    put rw'
    popScope
    return $ toValue "subshell" ()

-- The proof_subshell command.
--
-- Much the same as an ordinary subshell, except it runs in the
-- ProofScript monad and handles the additional ProofScript state.
--
proofScriptSubshell :: () -> ProofScript Value
proofScriptSubshell () = do
    (ro, rw) <- scriptTopLevel $ do
        pushScope
        ro_ <- ask
        rw_ <- get
        return (ro_, rw_)
    pst <- get
    let hook = roProofSubshell ro
    (rw', pst') <- liftIO $ hook ro rw pst
    put pst'
    scriptTopLevel $ do
        put rw'
        popScope
    return $ toValue "proof_subshell" ()

-- The "for" builtin.
--
-- XXX: this is the only thing in the tree that uses VBindOnce.
-- Unfortunately, for the time being it needs to be this way:
--    - as a builtin it can only operate in Value;
--    - VDo contains abstract syntax;
--    - there is no way to lift an arbitrary Value into the abstract
--      syntax, and there won't be anytime soon, because there's
--      already enough of a tangle with Value and the interpreter
--      state without also including the entire abstract syntax in
--      the yarn ball;
--    - it needs to be able to do SAWScript-level binds and those
--      are the only ways.
--
-- Probably the best long-term solution is to move the implementation
-- into the SAWScript prelude, once we have one (see #253; that
-- issue's been open a long time), since the only thing stopping that
-- is having a place to put the code.
--
-- Failing that, at some point the SAWScript interpreter will
-- hopefully have been cleaned up to the point where there's a Value
-- case in the abstract syntax, which there properly speaking should
-- be anyway, at which point this can be rewritten with VDo.
--
-- Failing _that_, it's probably possible to open-code the bind here
-- in terms of calling pieces of the interpreter directly, but that's
-- likely to be quite messy.
--
forValue :: [Value] -> Value -> TopLevel Value
forValue [] _ = return $ VReturn atRestPos [] (VArray [])
forValue (x : xs) f = do
   let pos = SS.PosInsideBuiltin
   m1 <- applyValue pos "(value was in a \"for\")" f x
   m2 <- forValue xs f
   return $ VBindOnce pos [] m1 $ VBuiltin "for" Seq.empty $ OneMoreArg $ \v1 ->
     return $ VBindOnce pos [] m2 $ VBuiltin "for" Seq.empty $ OneMoreArg $ \v2 ->
       return $ VReturn atRestPos [] (VArray (v1 : fromValue FromArgument v2))

caseProofResultPrim ::
  ProofResult ->
  Value {- ^ valid case -} ->
  Value {- ^ invalid/unknown case -} ->
  TopLevel Value
caseProofResultPrim pr vValid vInvalid = do
  let infoValid = "(value was the valid case of caseProofResult)"
  let infoInvalid = "(value was the invalid case of caseProofResult)"
  sc <- getSharedContext
  -- This is a builtin; we can use the posted global position
  pos <- getPosition
  case pr of
    ValidProof _ thm ->
      applyValue pos infoValid vValid (VTheorem thm)
    InvalidProof _ pairs _pst -> do
      let fov = FOVTuple (map snd pairs)
      tt <- io $ typedTermOfFirstOrderValue sc fov
      applyValue pos infoInvalid vInvalid (VTerm tt)
    UnfinishedProof _ -> do
      tt <- io $ typedTermOfFirstOrderValue sc (FOVTuple [])
      applyValue pos infoInvalid vInvalid (VTerm tt)

caseSatResultPrim ::
  SatResult ->
  Value {- ^ unsat case -} ->
  Value {- ^ sat/unknown case -} ->
  TopLevel Value
caseSatResultPrim sr vUnsat vSat = do
  let info = "(value was the sat case of caseSatResult)"
  sc <- getSharedContext
  -- This is a builtin; we can use the posted global position
  pos <- getPosition
  case sr of
    Unsat _ -> return vUnsat
    Sat _ pairs -> do
      let fov = FOVTuple (map snd pairs)
      tt <- io $ typedTermOfFirstOrderValue sc fov
      applyValue pos info vSat (VTerm tt)
    SatUnknown -> do
      let fov = FOVTuple []
      tt <- io $ typedTermOfFirstOrderValue sc fov
      applyValue pos info vSat (VTerm tt)

print_stack :: TopLevel ()
print_stack = do
  -- We are inside a builtin here, namely print_stack.
  let pos = SS.PosInsideBuiltin
  trace <- getStackTrace
  let trace' = Trace.ppTrace trace pos
  io $ TextIO.putStrLn "Stack trace:"
  io $ TextIO.putStrLn trace'

proof_stack :: ProofScript ()
proof_stack = scriptTopLevel print_stack

llvm_stack :: LLVMCrucibleSetupM ()
llvm_stack = llvmTopLevel print_stack

jvm_stack :: JVMSetupM ()
jvm_stack = jvmTopLevel print_stack

mir_stack :: MIRSetupM ()
mir_stack = mirTopLevel print_stack

enable_safety_proofs :: TopLevel ()
enable_safety_proofs = do
  rw <- getTopLevelRW
  putTopLevelRW rw{ rwSkipSafetyProofs = False }

disable_safety_proofs :: TopLevel ()
disable_safety_proofs = do
  opts <- getOptions
  io $ printOutLn opts Warn "Safety proofs disabled! This is unsound!"
  rw <- getTopLevelRW
  putTopLevelRW rw{ rwSkipSafetyProofs = True }

enable_sequent_goals :: TopLevel ()
enable_sequent_goals = do
  rw <- getTopLevelRW
  putTopLevelRW rw{ rwSequentGoals = True }

disable_sequent_goals :: TopLevel ()
disable_sequent_goals = do
  rw <- getTopLevelRW
  putTopLevelRW rw{ rwSequentGoals = False }

enable_smt_array_memory_model :: TopLevel ()
enable_smt_array_memory_model = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwSMTArrayMemoryModel = True }

disable_smt_array_memory_model :: TopLevel ()
disable_smt_array_memory_model = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwSMTArrayMemoryModel = False }

enable_crucible_assert_then_assume :: TopLevel ()
enable_crucible_assert_then_assume = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwCrucibleAssertThenAssume = True }

disable_crucible_assert_then_assume :: TopLevel ()
disable_crucible_assert_then_assume = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwCrucibleAssertThenAssume = False }

enable_single_override_special_case :: TopLevel ()
enable_single_override_special_case = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwSingleOverrideSpecialCase = True }

disable_single_override_special_case :: TopLevel ()
disable_single_override_special_case = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwSingleOverrideSpecialCase = False }


enable_crucible_profiling :: Text -> TopLevel ()
enable_crucible_profiling f = do
  let f' :: FilePath = Text.unpack f
  rw <- getTopLevelRW
  putTopLevelRW rw { rwProfilingFile = Just f' }

disable_crucible_profiling :: TopLevel ()
disable_crucible_profiling = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwProfilingFile = Nothing }

enable_lax_arithmetic :: TopLevel ()
enable_lax_arithmetic = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwLaxArith = True }

disable_lax_arithmetic :: TopLevel ()
disable_lax_arithmetic = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwLaxArith = False }

enable_lax_pointer_ordering :: TopLevel ()
enable_lax_pointer_ordering = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwLaxPointerOrdering = True }

disable_lax_pointer_ordering :: TopLevel ()
disable_lax_pointer_ordering = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwLaxPointerOrdering = False }

enable_lax_loads_and_stores :: TopLevel ()
enable_lax_loads_and_stores = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwLaxLoadsAndStores = True }

disable_lax_loads_and_stores :: TopLevel ()
disable_lax_loads_and_stores = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwLaxLoadsAndStores = False }

set_solver_cache_path :: Text -> TopLevel ()
set_solver_cache_path pathtxt = do
  let path :: FilePath = Text.unpack pathtxt
  rw <- getTopLevelRW
  case rwSolverCache rw of
    Just _ -> onSolverCache (setSolverCachePath path)
    Nothing -> do cache <- io $ openSolverCache path
                  putTopLevelRW rw { rwSolverCache = Just cache }

set_solver_cache_timeout :: Int -> TopLevel ()
set_solver_cache_timeout tout =
  onSolverCache (setSolverCacheTimeout tout)

clean_mismatched_versions_solver_cache :: TopLevel ()
clean_mismatched_versions_solver_cache = do
  vs <- io $ getSolverBackendVersions allBackends
  onSolverCache (cleanMismatchedVersionsSolverCache vs)

test_solver_cache_stats :: Integer -> Integer -> Integer -> Integer ->
                           Integer -> TopLevel ()
test_solver_cache_stats sz ls ls_f is is_f =
  onSolverCache (testSolverCacheStats sz ls ls_f is is_f)

enable_debug_intrinsics :: TopLevel ()
enable_debug_intrinsics = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwDebugIntrinsics = True }

disable_debug_intrinsics :: TopLevel ()
disable_debug_intrinsics = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwDebugIntrinsics = False }

enable_what4_hash_consing :: TopLevel ()
enable_what4_hash_consing = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwWhat4HashConsing = True }

disable_what4_hash_consing :: TopLevel ()
disable_what4_hash_consing = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwWhat4HashConsing = False }

enable_x86_what4_hash_consing :: TopLevel ()
enable_x86_what4_hash_consing = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwWhat4HashConsingX86 = True }

disable_x86_what4_hash_consing :: TopLevel ()
disable_x86_what4_hash_consing = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwWhat4HashConsingX86 = False }

enable_what4_eval :: TopLevel ()
enable_what4_eval = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwWhat4Eval = True }

disable_what4_eval :: TopLevel ()
disable_what4_eval = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwWhat4Eval = False }

add_x86_preserved_reg :: Text -> TopLevel ()
add_x86_preserved_reg r = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPreservedRegs = r:rwPreservedRegs rw }

default_x86_preserved_reg :: TopLevel ()
default_x86_preserved_reg = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPreservedRegs = mempty }

set_x86_stack_base_align :: Integer -> TopLevel ()
set_x86_stack_base_align a = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwStackBaseAlign = a }

default_x86_stack_base_align :: TopLevel ()
default_x86_stack_base_align = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwStackBaseAlign = defaultStackBaseAlign }

enable_alloc_sym_init_check :: TopLevel ()
enable_alloc_sym_init_check = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwAllocSymInitCheck = True }

disable_alloc_sym_init_check :: TopLevel ()
disable_alloc_sym_init_check = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwAllocSymInitCheck = False }

enable_no_satisfying_write_fresh_constant :: TopLevel ()
enable_no_satisfying_write_fresh_constant = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwNoSatisfyingWriteFreshConstant = True }

disable_no_satisfying_write_fresh_constant :: TopLevel ()
disable_no_satisfying_write_fresh_constant = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwNoSatisfyingWriteFreshConstant = False }

enable_what4_push_mux_ops :: TopLevel ()
enable_what4_push_mux_ops = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwWhat4PushMuxOps = True }

disable_what4_push_mux_ops :: TopLevel ()
disable_what4_push_mux_ops = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwWhat4PushMuxOps = False }

set_crucible_timeout :: Integer -> TopLevel ()
set_crucible_timeout t = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwCrucibleTimeout = t }

include_value :: Text -> TopLevel ()
include_value file = do
  let file' :: FilePath = Text.unpack file
  interpretFile file' False

set_ascii :: Bool -> TopLevel ()
set_ascii b = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { PPS.ppUseAscii = b } }

set_base :: Int -> TopLevel ()
set_base b = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { PPS.ppBase = b } }

set_color :: Bool -> TopLevel ()
set_color b = do
  rw <- getTopLevelRW
  opts <- getOptions
  -- Keep color disabled if `--no-color` command-line option is present
  let b' = b && useColor opts
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { PPS.ppColor = b' } }

set_min_sharing :: Int -> TopLevel ()
set_min_sharing b = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { PPS.ppMinSharing = b } }

-- | 'set_memoization_hash i' changes the memoization strategy for terms:
-- memoization identifiers will include the first 'i' digits of the hash of the
-- term they memoize. This is useful to help keep memoization identifiers of the
-- same term as constant as possible across different executions of a proof
-- script over the course of its development.
set_memoization_hash :: Int -> TopLevel ()
set_memoization_hash i = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { PPS.ppMemoStyle = PPS.Hash i } }

-- | 'set_memoization_hash_incremental i' changes the memoization strategy for
-- terms: memoization identifiers will include the first 'i' digits of the hash
-- of the term they memoize, as well as the value of a global counter that
-- increments each time a term is memoized. This is useful to help keep
-- memoization identifiers of the same term as constant as possible across
-- different executions of a proof script over the course of its development, as
-- well as to freshen memoization identifiers in the unlikely case of term hash
-- collisions.
set_memoization_hash_incremental :: Int -> TopLevel ()
set_memoization_hash_incremental i = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { PPS.ppMemoStyle = PPS.HashIncremental i } }

-- | `set_memoization_incremental` changes the memoization strategy for terms:
-- memoization identifiers will only include the value of a global counter that
-- increments each time a term is memoized.
set_memoization_incremental :: TopLevel ()
set_memoization_incremental = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { PPS.ppMemoStyle = PPS.Incremental } }

print_value :: Value -> TopLevel ()
print_value (VString s) = printOutLnTop Info (Text.unpack s)
print_value (VTerm t) = do
  sc <- getSharedContext
  cenv <- getCryptolEnv
  let cfg = CEnv.meSolverConfig (CEnv.eModuleEnv cenv)
  unless (closedTerm (ttTerm t)) $
    fail "term contains symbolic variables"
  sawopts <- getOptions
  t' <- io $ defaultTypedTerm sawopts sc cfg t
  opts <- fmap rwPPOpts getTopLevelRW
  let opts' = V.defaultPPOpts { V.useAscii = PPS.ppUseAscii opts
                              , V.useBase = PPS.ppBase opts
                              }
  evaled_t <- io $ evaluateTypedTerm sc t'
  doc <- io $ V.runEval mempty (V.ppValue V.Concrete opts' evaled_t)
  sawOpts <- getOptions
  io (rethrowEvalError $ printOutLn sawOpts Info $ show $ doc)

print_value v = do
  opts <- fmap rwPPOpts getTopLevelRW
  nenv <- io . scGetNamingEnv =<< getSharedContext
  printOutLnTop Info (showsPrecValue opts nenv 0 v "")

dump_file_AST :: BuiltinContext -> Options -> Text -> IO ()
dump_file_AST _bic opts filetxt = do
    let file = Text.unpack filetxt
    errs_or_stmts <- Loader.findAndLoadFileUnchecked opts file
    case errs_or_stmts of
        Left errs ->
            X.throwIO $ userError $ Text.unpack $ Text.unlines errs
        Right stmts ->
            mapM_ print stmts

parser_printer_roundtrip :: BuiltinContext -> Options -> Text -> IO ()
parser_printer_roundtrip _bic opts filetxt = do
    let file = Text.unpack filetxt
    errs_or_stmts <- Loader.findAndLoadFileUnchecked opts file
    case errs_or_stmts of
        Left errs ->
            X.throwIO $ userError $ Text.unpack $ Text.unlines errs
        Right stmts ->
            PP.putDoc $ SS.prettyWholeModule stmts

exec :: Text -> [Text] -> Text -> IO Text
exec name args input = do
  let name' = Text.unpack name
      args' = map Text.unpack args
      input' = Text.unpack input
  output <- readProcess name' args' input'
  return $ Text.pack output

------------------------------------------------------------
-- Filename wrappers

-- The interpreter deals only in Text, and FilePath is actually String.
-- Rather than push Text through the various backend places (which gets
-- messy) we'll unpack Text to FilePath up front. Or at least until the
-- stdlib comes up with a Text-based interface for filenames.

-- | Wrapper for writeAIGviaVerilog because the interpreter deals only in
--   Text and FilePath is actually String.
doWriteAIGviaVerilog :: Text -> Term -> TopLevel ()
doWriteAIGviaVerilog filetext e =
  let file :: FilePath = Text.unpack filetext in
  writeAIGviaVerilog file e

do_offline_aig :: Text -> ProofScript ()
do_offline_aig file =
  offline_aig (Text.unpack file)

do_offline_aig_external :: Text -> ProofScript ()
do_offline_aig_external file =
  offline_aig_external (Text.unpack file)

do_write_cnf :: Text -> TypedTerm -> TopLevel ()
do_write_cnf f tt =
  write_cnf (Text.unpack f) tt

do_write_cnf_external :: Text -> TypedTerm -> TopLevel ()
do_write_cnf_external f tt =
  write_cnf_external (Text.unpack f) tt

do_write_smtlib2 :: Text -> TypedTerm -> TopLevel ()
do_write_smtlib2 f tt =
  write_smtlib2 (Text.unpack f) tt

do_write_smtlib2_w4 :: Text -> TypedTerm -> TopLevel ()
do_write_smtlib2_w4 f tt =
  write_smtlib2_w4 (Text.unpack f) tt

do_write_core :: Text -> Term -> TopLevel ()
do_write_core f t =
  writeCore (Text.unpack f) t

do_write_verilog :: SharedContext -> Text -> Term -> IO ()
do_write_verilog sc f t =
  writeVerilog sc (Text.unpack f) t

do_write_coq_term :: Text -> [(Text, Text)] -> [Text] -> Text -> Term -> TopLevel ()
do_write_coq_term name notations skips path t =
  writeCoqTerm name notations skips (Text.unpack path) t

do_write_coq_cryptol_module :: Text -> Text -> [(Text, Text)] -> [Text] -> TopLevel ()
do_write_coq_cryptol_module infile outfile notations skips =
  writeCoqCryptolModule (Text.unpack infile) (Text.unpack outfile) notations skips

do_write_coq_sawcore_prelude :: Text -> [(Text, Text)] -> [Text] -> IO ()
do_write_coq_sawcore_prelude outfile notations skips =
  writeCoqSAWCorePrelude (Text.unpack outfile) notations skips

do_write_coq_cryptol_primitives_for_sawcore :: Text -> [(Text, Text)] -> [Text] -> IO ()
do_write_coq_cryptol_primitives_for_sawcore cryfile notations skips =
  let cryfile' = Text.unpack cryfile
  in
  writeCoqCryptolPrimitivesForSAWCore cryfile' notations skips

do_offline_coq :: Text -> ProofScript ()
do_offline_coq f =
  offline_coq (Text.unpack f)

do_auto_match :: Text -> Text -> TopLevel ()
do_auto_match f1 f2 =
  autoMatch stmtInterpreter (Text.unpack f1) (Text.unpack f2)

do_write_goal :: Text -> ProofScript ()
do_write_goal f =
  write_goal (Text.unpack f)

do_offline_w4_unint_bitwuzla :: [Text] -> Text -> ProofScript ()
do_offline_w4_unint_bitwuzla unints path =
  offline_w4_unint_bitwuzla unints (Text.unpack path)

do_offline_w4_unint_z3 :: [Text] -> Text -> ProofScript ()
do_offline_w4_unint_z3 unints path =
  offline_w4_unint_z3 unints (Text.unpack path)

do_offline_w4_unint_cvc4 :: [Text] -> Text -> ProofScript ()
do_offline_w4_unint_cvc4 unints path =
  offline_w4_unint_cvc4 unints (Text.unpack path)

do_offline_w4_unint_cvc5 :: [Text] -> Text -> ProofScript ()
do_offline_w4_unint_cvc5 unints path =
  offline_w4_unint_cvc5 unints (Text.unpack path)

do_offline_w4_unint_yices :: [Text] -> Text -> ProofScript ()
do_offline_w4_unint_yices unints path =
  offline_w4_unint_yices unints (Text.unpack path)

do_cryptol_load :: (FilePath -> IO BS.ByteString) -> Text -> TopLevel CEnv.ExtCryptolModule
do_cryptol_load loader path =
  cryptol_load loader (Text.unpack path)

do_offline_cnf :: Text -> ProofScript ()
do_offline_cnf path =
  offline_cnf (Text.unpack path)

do_offline_cnf_external :: Text -> ProofScript ()
do_offline_cnf_external path =
  offline_cnf_external (Text.unpack path)

do_offline_extcore :: Text -> ProofScript ()
do_offline_extcore path =
  offline_extcore (Text.unpack path)

do_offline_smtlib2 :: Text -> ProofScript ()
do_offline_smtlib2 path =
  offline_smtlib2 (Text.unpack path)

do_w4_offline_smtlib2 :: Text -> ProofScript ()
do_w4_offline_smtlib2 path =
  w4_offline_smtlib2 (Text.unpack path)

do_offline_unint_smtlib2 :: [Text] -> Text -> ProofScript ()
do_offline_unint_smtlib2 unints path =
  offline_unint_smtlib2 unints (Text.unpack path)

do_offline_verilog :: Text -> ProofScript ()
do_offline_verilog path =
  offline_verilog (Text.unpack path)

do_cryptol_add_path :: Text -> TopLevel ()
do_cryptol_add_path path =
  cryptol_add_path (Text.unpack path)

do_llvm_load_module :: Text -> TopLevel (Some CIR.LLVMModule)
do_llvm_load_module path =
  llvm_load_module (Text.unpack path)

do_llvm_boilerplate :: Text -> ModuleSkeleton -> Bool -> TopLevel ()
do_llvm_boilerplate path mskel builtins =
  llvm_boilerplate (Text.unpack path) mskel builtins

do_llvm_verify_x86 ::
  Some CIR.LLVMModule -> Text -> Text -> [(Text, Integer)] -> Bool ->
    LLVMCrucibleSetupM () -> ProofScript () -> TopLevel (CIR.SomeLLVM CMS.ProvedSpec)
do_llvm_verify_x86 llvm path nm globsyms checkSat spec ps =
  llvm_verify_x86 llvm (Text.unpack path) nm globsyms checkSat spec ps

do_llvm_verify_fixpoint_x86 ::
  Some CIR.LLVMModule -> Text -> Text -> [(Text, Integer)] -> Bool -> TypedTerm ->
    LLVMCrucibleSetupM () -> ProofScript () -> TopLevel (CIR.SomeLLVM CMS.ProvedSpec)
do_llvm_verify_fixpoint_x86 llvm path nm globsyms checkSat tt spec ps =
  llvm_verify_fixpoint_x86 llvm (Text.unpack path) nm globsyms checkSat tt spec ps

do_llvm_verify_fixpoint_chc_x86 ::
  Some CIR.LLVMModule -> Text -> Text -> [(Text, Integer)] -> Bool -> TypedTerm ->
  LLVMCrucibleSetupM () -> ProofScript ()  -> TopLevel (CIR.SomeLLVM CMS.ProvedSpec)
do_llvm_verify_fixpoint_chc_x86 llvm path nm globsyms checkSat tt spec ps =
  llvm_verify_fixpoint_chc_x86 llvm (Text.unpack path) nm globsyms checkSat tt spec ps

do_llvm_verify_x86_with_invariant ::
  Some CIR.LLVMModule -> Text -> Text -> [(Text, Integer)] -> Bool ->
  (Text, Integer, TypedTerm)  ->
  LLVMCrucibleSetupM () -> ProofScript () -> TopLevel (CIR.SomeLLVM CMS.ProvedSpec)
do_llvm_verify_x86_with_invariant llvm path nm globsyms checkSat info spec ps =
  llvm_verify_x86_with_invariant llvm (Text.unpack path) nm globsyms checkSat info spec ps

do_mir_load_module :: Text -> TopLevel MIR.RustModule
do_mir_load_module file =
  mir_load_module (Text.unpack file)

do_yosys_import :: Text -> TopLevel TypedTerm
do_yosys_import path =
  yosys_import (Text.unpack path)

do_yosys_import_sequential :: Text -> Text -> TopLevel Yo.YosysSequential
do_yosys_import_sequential nm path =
  yosys_import_sequential nm (Text.unpack path)

do_yosys_verify_sequential_sally :: Yo.YosysSequential -> Text -> TypedTerm -> [Text] -> TopLevel ()
do_yosys_verify_sequential_sally s path q fixed =
  yosys_verify_sequential_sally s (Text.unpack path) q fixed

do_load_sawcore_from_file :: BuiltinContext -> Options -> Text -> TopLevel ()
do_load_sawcore_from_file _ _ mod_filename =
  load_sawcore_from_file (Text.unpack mod_filename)

do_summarize_verification_json :: Text -> TopLevel ()
do_summarize_verification_json fpath =
  summarize_verification_json (Text.unpack fpath)


------------------------------------------------------------
-- Primitive tables

data PrimType
  = PrimType
    { primTypeType :: SS.NamedType
    , primTypeLife :: PrimitiveLifecycle
    -- FUTURE: add doc strings for these?
    }

data Primitive
  = Primitive
    { primitiveType :: SS.Schema
    , primitiveLife :: PrimitiveLifecycle
    , primitiveDoc  :: [Text]
    , primitiveFn   :: Options -> BuiltinContext -> Value
    }

-- | Primitive types, that is, builtin types used by the primitives.
--
-- This excludes certain types that are built in more deeply and
-- appear as entries in @TyCon in AST.hs. Note that those are also
-- handled as reserved words in the lexer and parser. XXX: and there's
-- no particular system to which are there and which are here; some of
-- the ones there have no special syntax or semantics and should
-- probably be moved here at some point.
primTypes :: Map SS.Name PrimType
primTypes = foldl doadd Map.empty
  [ abstype "BisimTheorem" Experimental
  , abstype "CryptolModule" Current
  , abstype "FunctionProfile" Experimental
  , abstype "FunctionSkeleton" Experimental
  , abstype "Ghost" Current
  , abstype' SS.kindStarToStar "JVMSetup" Current
  , abstype "JVMValue" Current
  , abstype "JavaClass" Current
  , abstype "JavaType" Current
  , abstype' SS.kindStarToStar "LLVMSetup" Current
  , abstype "LLVMModule" Current
  , abstype "LLVMType" Current
  , abstype' SS.kindStarToStar "MIRSetup" Current
  , abstype "MIRAdt" Experimental
  , abstype "MIRModule" Experimental
  , abstype "MIRType" Experimental
  , abstype "MIRValue" Experimental
  , abstype "ModuleSkeleton" Experimental
  , abstype "ProofResult" Current
  , abstype "SatResult" Current
  , abstype "LLVMValue" Current
  , abstype "Simpset" Current
  , abstype "SkeletonState" Experimental
  , abstype "Theorem" Current
  , abstype "YosysSequential" Experimental
  , abstype "YosysTheorem" Experimental
  , conctype "SetupValue" "LLVMValue" Current
  , abstype "__DEPRECATED__" HideDeprecated
  ]
  where
    -- Thread the map through as we add entries so we can
    -- use it to check the right hand side of any typedefs.
    doadd ::
        Map SS.Name PrimType ->
        (Map SS.Name PrimType -> (SS.Name, PrimType)) ->
        Map SS.Name PrimType
    doadd tyenv constructor =
        let (name, entry) = constructor tyenv in
        Map.insert name entry tyenv

    -- abstract type of arbitrary kind
    abstype' ::
        SS.Kind -> Text -> PrimitiveLifecycle -> Map SS.Name PrimType ->
        (SS.Name, PrimType)
    abstype' kind name lc _tyenv = (name, info)
      where
        info = PrimType
          { primTypeType = SS.AbstractType kind
          , primTypeLife = lc
          }

    -- abstract type of kind *
    abstype :: Text -> PrimitiveLifecycle -> Map SS.Name PrimType -> (SS.Name, PrimType)
    abstype name lc tyenv = abstype' SS.kindStar name lc tyenv

    -- concrete type (not currently used)
    conctype ::
        Text -> Text -> PrimitiveLifecycle -> Map SS.Name PrimType ->
        (SS.Name, PrimType)
    conctype name tystr lc tyenv = (name, info)
      where
        info = PrimType
          { primTypeType = SS.ConcreteType ty
          , primTypeLife = lc
          }
        fakeFileName = Text.unpack $ "<definition of builtin type " <> name <> ">"

        -- We need a Map Name (PrimitiveLifecycle, NamedType) to feed
        -- to readSchemaPure. Construct one from the Map Name PrimType
        -- that we've got. FUTURE: there are too many isomorphic types
        -- floating around in the builtins handling (not just here)
        -- and they should all be simplified away.
        tyenv' = Map.map (\pt -> (primTypeLife pt, primTypeType pt)) tyenv

        ty = case Loader.readSchemaPure fakeFileName lc tyenv' tystr of
            SS.Forall [] ty' ->
                ty'
            _ ->
                panic "primTypes" [
                    "Builtin typedef " <> name <> " not monomorphic"
                ]

--
-- Note: the help/doc strings for the primitives should be
-- formatted to be no more than 64 characters wide. The following
-- ruler can be used when editing:
--     ****************************************************************
--

primitives :: Map SS.Name Primitive
primitives = Map.fromList $
  [
    ------------------------------------------------------------
    -- Constants

    prim "true"                "Bool"
    (pureVal True)
    Current
    [ "A boolean value." ]

  , prim "false"               "Bool"
    (pureVal False)
    Current
    [ "A boolean value." ]

    ------------------------------------------------------------
    -- Language-level operators

  , prim "return"              "{m, a} a -> m a"
    (pureVal (\v -> VReturn atRestPos [] v))
    Current
    [ "Create a monadic action that produces a pure value. The code"
    , "   x <- return e;"
    , "will result in the same value being bound to 'x' as the code"
    , "   let x = e;"
    , "would. Works in any of the SAWScript monads."
    , "Note: not a control-flow operator."
    ]

  , prim "include"             "String -> TopLevel ()"
    (pureVal include_value)
    Current
    [ "Load and execute the given SAWScript file." ]

  , prim "undefined"           "{a} a"
    -- In order to work as expected this has to be "error" in place of
    -- a Value and not a Value (of whatever kind) wrapping "error". So
    -- there must be no toValue and none of the pureVal/funVal/etc.
    -- ops are suitable.
    (\_ _ _ -> error "interpret: undefined")
    Current
    [ "An undefined value. Evaluating 'undefined' makes the program"
    , "crash. Because it does not actually produce a value, it can have"
    , "any type."
    ]

  , prim "fail" "{a} String -> TopLevel a"
    (pureVal failPrim)
    Current
    [ "Fail in the TopLevel monad. This produces the same kind of"
    , "failure as arbitrary other errors during SAWScript execution."
    , ""
    , "Failure in SAWScript is essentially like throwing an exception,"
    , "but there are limited facilities for dealing with the results."
    , "See 'fails'."
    ]

  , prim "fails"               "{a} TopLevel a -> TopLevel ()"
    (pureVal failsPrim)
    Current
    [ "Run the given inner action and convert failure into success."
    , "Fail if the inner action does NOT raise an exception. This is"
    , "primarily used for testing, to check that expected failures"
    , "actually occur."
    , ""
    , "Note: the argument is a monadic action and 'fails' can trap only"
    , "failures that occur while executing that action. To catch a"
    , "failure that occurs in non-monadic code, the non-monadic code"
    , "must be wrapped in a do-block. Otherwise it will be evaluated"
    , "and the result passed to 'fails' as its argument, so the failure"
    , "will happen before 'fails' runs. For example,"
    , "   fails (return (nth [] 1))"
    , "does not trap the out of bounds error, but"
    , "   fails (do { return (nth [] 1); })"
    , "does."
    ]

  , prim "env"                 "TopLevel ()"
    (pureVal envCmd)
    WarnDeprecated
    [ "Print all SAWScript values in scope."
    , "Deprecated; use the :env REPL command instead."
    , ""
    , "Expected to be hidden by default in SAW 1.5."
    ]

  , prim "show"                "{a} a -> String"
    (funVal1 showPrim)
    Current
    [ "Convert the value of the given expression to a string." ]

  , prim "print"               "{a} a -> TopLevel ()"
    (pureVal print_value)
    Current
    [ "Print the value of the given expression." ]

  , prim "type"                "Term -> Type"
    (funVal1 term_type)
    Current
    [ "Return the type of the given term." ]

  , prim "print_type"          "Term -> TopLevel ()"
    (pureVal print_type)
    Current
    [ "Print the SAWCore-level type of the given term."
    , "'print_type t' is thus not equivalent to 'print (type t)'."
    ]

  , prim "caseSatResult"       "{b} SatResult -> b -> (Term -> b) -> b"
    (funVal3 caseSatResultPrim)
    Current
    [ "Branch on the result of SAT solving."
    , ""
    , "Usage: caseSatResult <unsat-code> <sat-code>"
    , ""
    , "For example, given"
    , "   let notsat = print \"unsat\";"
    , "   let issat model = do { print \"sat\"; print model; };"
    , "running"
    , "   r <- sat abc {{ False }}"
    , "   caseSatResult r notsat issat"
    , "will print 'unsat'. Conversely, running"
    , "   r <- sat abc {{ \\(x : [4]) -> x == 3 }}"
    , "   caseSatResult r notsat issat"
    , "will print 'sat' and '3'."
    , ""
    , "The model value passed to the <sat-code> is a Term containing"
    , "the satisfying assignment of variables returned by the solver;"
    , "it will be a tuple if the formula being checked has more than"
    , "one input argument. It will be '()' if the solver gave up and"
    , "returned 'unknown'."
    , ""
    , "See 'sat'."
    ]

  , prim "caseProofResult"
    "{b} ProofResult -> (Theorem -> b) -> (Term -> b) -> b"
    (funVal3 caseProofResultPrim)
    Current
    [ "Branch on the result of proving."
    , ""
    , "Usage: caseProofResult <result> <true-code> <false-code>"
    , ""
    , "For example, given"
    , "   let yup thm = do { print \"Proved!\"; print thm; };"
    , "   let nope cex = do { print \"Counterexample:\"; print cex; };"
    , "running"
    , "   r <- prove abc {{ True }}"
    , "   caseProofResult r yup nope"
    , "will print 'Proved!' and 'Theorem (EqTrue True)'. Running"
    , "   r <- prove z3 {{ \\(x : [8]) -> (x < 2) || (x > 2) }}"
    , "   caseProofResult r yup nope"
    , "will print 'Counterexample:' and '2'."
    , ""
    , "The 'Theorem' passed to the <true-code> is the SAWScript object"
    , "representing the proved theorem, which can then be used in other"
    , "proofs. The 'Term' passed to the <false-code> is the"
    , "counterexample produced by the solver or proof script. It will"
    , "be a tuple if the proposition has more than one input argument."
    , "It will be '()' if the proof failed without generating an"
    , "explicit counterexample."
    , ""
    , "See 'prove'."
    ]

  , prim "enable_experimental" "TopLevel ()"
    (bicVal (add_primitives Experimental))
    Current
    [ "Enable the use of experimental commands." ]

  , prim "enable_deprecated"   "TopLevel ()"
    (bicVal (add_primitives HideDeprecated))
    Current
    [ "Enable the use of deprecated commands. When commands are first"
    , "deprecated they generate warnings. At a later stage they become"
    , "invisible unless explicitly enabled with this command. The next"
    , "stage is to remove them entirely. Therefore, the use of this"
    , "command should always be considered a temporary stopgap until"
    , "your scripts can be updated."
    ]

  , prim "subshell"            "() -> TopLevel ()"
    (pureVal toplevelSubshell)
    Experimental
    [ "Open an interactive subshell instance nested inside the context"
    , "where 'subshell' was called. The resulting REPL is always"
    , "interactive on the terminal regardless of whether the parent"
    , "context was interactive or not."
    , ""
    , "Type end-of-file (usually Ctrl-D) or ':q' into your terminal to"
    , "exit the subshell and resume the prior execution."
    , ""
    , "Note that altering any file or files SAW is executing from while"
    , "in the subshell will not change the copy SAW has loaded into"
    , "memory."
    ]

  , prim "proof_subshell"      "() -> ProofScript ()"
    (pureVal proofScriptSubshell)
    Experimental
    [ "Open an interactive subshell instance nested inside the context"
    , "where 'proof_subshell' was called. The resulting REPL is always"
    , "interactive on the terminal regardless of whether the parent"
    , "context was interactive or not."
    , ""
    , "The subshell runs in proof mode in the 'ProofScript' monad."
    , ""
    , "In proof mode, the command prompt changes to 'proof (n)', where"
    , "the 'n' is the number of proof goals remaining."
    , ""
    , "'proof_subshell' gives a basic interactive proof environment. It"
    , "allows the user to manually execute proof tactics and examine"
    , "their effects. Use 'print_goal' to show the current goal. When"
    , "one goal is completed, the environment automatically switches to"
    , "the next one. The proof is done when all goals have been proved"
    , "and the number shown in the prompt is 0."
    , ""
    , "Use :search ProofScript to list the supported proof tactics."
    , ""
    , "It is possible to use 'proof_checkpoint' to save and restore the"
    , "proof state and thereby gain a limited ability to undo or back"
    , "up. Be warned, however, that as of the current writing the"
    , "checkpoint facility doesn't work reliably and isn't recommended."
    , ""
    , "Type end-of-file (usually Ctrl-D) or ':q' into your terminal to"
    , "exit the proof subshell and resume execution."
    ]

  , prim "dump_file_AST"       "String -> TopLevel ()"
    (bicVal dump_file_AST)
    Current
    [ "Load a SAWScript file and dump an ugly representation of the"
    , "abstract syntax."
    ]

  , prim "parser_printer_roundtrip"       "String -> TopLevel ()"
    (bicVal parser_printer_roundtrip)
    Current
    [ "Load a SAWScript file and transform the results back to the"
    , "SAWScript concrete syntax."
    ]

  , prim "run"                 "{a} TopLevel a -> a"
    (funVal1 (id :: TopLevel Value -> TopLevel Value))
    Current
    [ "Evaluate a monadic TopLevel computation to produce a value."
    , ""
    , "Comparable to 'unsafePerformIO' in Haskell, except somewhat"
    , "safer: SAWScript is eagerly evaluated, so the point where 'run'"
    , "executes is well defined. The ordering of the target action"
    , "relative to the enclosing TopLevel bound action chain is"
    , "unspecified but never incoherent."
    ]

  , prim "checkpoint"          "TopLevel (() -> TopLevel ())"
    (pureVal checkpoint)
    Experimental
    [ "Capture the current state of the SAW interpreter, and return a"
    , "TopLevel monadic action that, if invoked, will reset the state"
    , "of the interpreter back to to what it was when 'checkpoint' was"
    , "invoked."
    , ""
    , "NOTE that this facility is highly experimental and is not"
    , "particularly reliable. It is intended only for proof development"
    , "where it can speed up the process of experimenting with mid-"
    , "proof changes. Finalized proofs should not use this feature."
    ]

  , prim "proof_checkpoint"      "ProofScript (() -> ProofScript ())"
    (pureVal proof_checkpoint)
    Experimental
    [ "Capture the current state of the SAW interpreter, and return a"
    , "ProofScript monadic action that, if invoked, will reset the"
    , "proof state back to to what it was when 'proof_checkpoint' was"
    , "invoked."
    , ""
    , "NOTE that this facility is highly experimental and may not"
    , "particularly reliable. It is intended only for proof development"
    , "where it can speed up the process of experimenting with mid-"
    , "proof changes. Finalized proofs should not use this feature."
    ]

    ------------------------------------------------------------
    -- Test/debug widgets

    -- In principle we could have one monad-polymorphic builtin, but
    -- monad-polymorphic builtins don't currently work.
    --
    -- FUTURE: because these are only intended for use by the test
    -- suite, it might make sense to add a different category for that
    -- instead of Experimental, to make it extra clear that third
    -- parties shouldn't use these.
  , prim "print_stack"         "TopLevel ()"
    (pureVal print_stack)
    Experimental
    [ "Print the SAWScript interpreter's current stack trace, for testing." ]
  , prim "proof_stack"         "ProofScript ()"
    (pureVal proof_stack)
    Experimental
    [ "ProofScript version of print_stack." ]
  , prim "llvm_stack"          "LLVMSetup ()"
    (pureVal llvm_stack)
    Experimental
    [ "LLVMSetup version of print_stack." ]
  , prim "jvm_stack"           "JVMSetup ()"
    (pureVal jvm_stack)
    Experimental
    [ "JVMSetup version of print_stack." ]
  , prim "mir_stack"           "MIRSetup ()"
    (pureVal mir_stack)
    Experimental
    [ "MIRSetup version of print_stack." ]

    ------------------------------------------------------------
    -- List operations

  , prim "null"                "{a} [a] -> Bool"
    (pureVal (null :: [Value] -> Bool))
    Current
    [ "Test whether a list is empty." ]

  , prim "head"                "{a} [a] -> a"
    (funVal1 (headPrim :: [Value] -> TopLevel Value))
    Current
    [ "Get the first element from the list." ]

  , prim "tail"                "{a} [a] -> [a]"
    (funVal1 (tailPrim :: [Value] -> TopLevel [Value]))
    Current
    [ "Drop the first element from a list." ]

  , prim "length"              "{a} [a] -> Int"
    (pureVal (length :: [Value] -> Int))
    Current
    [ "Compute the length of a list." ]

  , prim "concat"              "{a} [a] -> [a] -> [a]"
    (pureVal ((++) :: [Value] -> [Value] -> [Value]))
    Current
    [ "Concatenate two lists to yield a third." ]

  , prim "nth"                 "{a} [a] -> Int -> a"
    (funVal2 (nthPrim :: [Value] -> Int -> TopLevel Value))
    Current
    [ "Look up the value at the given list position." ]

  , prim "for"                 "{m, a, b} [a] -> (a -> m b) -> m [b]"
    (funVal2 forValue)
    Current
    [ "Apply the given monadic action in left-to-right order to a list"
    , "of values. Collect the results and return them as another list."
    ]

    ------------------------------------------------------------
    -- String operations

  , prim "str_concat"          "String -> String -> String"
    (pureVal ((<>) :: Text -> Text -> Text))
    Current
    [ "Concatenate two strings to yield a third." ]

  , prim "str_concats"          "[String] -> String"
    (pureVal Text.concat)
    Current
    [ "Concatenate a list of strings together to yield a single string." ]

    ------------------------------------------------------------
    -- File operations

  , prim "read_bytes"          "String -> TopLevel Term"
    (pureVal readBytes)
    Current
    [ "Read a file, treating it as binary, and return the contents as a"
    , "Term value of type [n][8]."
    ]

    ------------------------------------------------------------
    -- Miscellaneous operations

  , prim "get_opt"            "Int -> String"
    (funVal1 get_opt)
    Current
    [ "Get the nth argument to the current script as a String. Script"
    , "arguments are collected from the SAW command line after the name"
    , "of the script being run. Argument 0 is the script name. The list"
    , "is empty when no script was loaded, e.g. when interactive."
    ]

  , prim "get_nopts"          "() -> Int"
    (funVal1 get_nopts)
    Current
    [ "Get the number of arguments to the current script. Since the 0th"
    , "argument is the script name, the count will normally be at least"
    , "1. If no script was loaded, the count will be 0."
    ]

  , prim "get_env"            "String -> String"
    (funVal1 get_env)
    Current
    [ "Get an environment variable (from the process environment) as a"
    , "string."
    ]

  , prim "exit"                "Int -> TopLevel ()"
    (pureVal exitPrim)
    Current
    [ "Exit SAWScript, returning the supplied exit code to the parent"
    , "process."
    ]

  , prim "exec"               "String -> [String] -> String -> TopLevel String"
    (pureVal exec)
    Current
    [ "Execute an external process with the given executable name"
    , "argument list, and standard input. Collects and returns the"
    , "standard output produced by the process."
    ]

  , prim "time"                "{a} TopLevel a -> TopLevel a"
    (pureVal timePrim)
    Current
    [ "Print the CPU time used by the given TopLevel command." ]

  , prim "with_time"           "{a} TopLevel a -> TopLevel (Int, a)"
    (pureVal withTimePrim)
    Current
    [ "Run the given TopLevel command. Return the elapsed time in"
    , "milliseconds along with the command's own result."
    ]

    ------------------------------------------------------------
    -- Boolean/flag settings

  , prim "enable_smt_array_memory_model" "TopLevel ()"
    (pureVal enable_smt_array_memory_model)
    Current
    [ "Enable the SMT array memory model." ]

  , prim "disable_smt_array_memory_model" "TopLevel ()"
    (pureVal disable_smt_array_memory_model)
    Current
    [ "Disable the SMT array memory model." ]

  , prim "enable_sequent_goals" "TopLevel ()"
    (pureVal enable_sequent_goals)
    Experimental
    [ "When verifying proof obligations arising from 'llvm_verify' and"
    , "similar commands, generate sequents (that is, multiple separate"
    , "goals) for the resulting proof obligations instead of a single"
    , "overarching goal."
    ]

  , prim "disable_sequent_goals" "TopLevel ()"
    (pureVal disable_sequent_goals)
    Experimental
    [ "Restore the default behavior, which is to generate single"
    , "boolean goals for proof obligations arising from verification"
    , "commands."
    ]

  , prim "enable_safety_proofs" "TopLevel ()"
    (pureVal enable_safety_proofs)
    Experimental
    [ "Restore the default state, where safety obligations encountered"
    , "during symbolic execution are proved normally."
    ]

  , prim "disable_safety_proofs" "TopLevel ()"
    (pureVal disable_safety_proofs)
    Experimental
    [ "Disable checking of safety obligations encountered during"
    , "symbolic execution. This is unsound! However, it can be useful"
    , "during initial proof construction to focus only on the stated"
    , "correctness specifications."
    ]

  , prim "enable_single_override_special_case" "TopLevel ()"
    (pureVal enable_single_override_special_case)
    Experimental
    [ "Enable special-case handling when there is exactly one override"
    , "that appies at a given call site after structural matching."
    , "This special case handling asserts the override preconditions as"
    , "separate proof goals, instead of combining them into one. In"
    , "general, this may produce more, but simpler, goals than when"
    , "disabled."
    ]

  , prim "disable_single_override_special_case" "TopLevel ()"
    (pureVal disable_single_override_special_case)
    Experimental
    [ "Disable special case handling for single overrides."
    , "This is the default behavior."
    ]

 , prim "enable_crucible_assert_then_assume" "TopLevel ()"
    (pureVal enable_crucible_assert_then_assume)
    Current
    [ "Assume predicate after asserting it during Crucible symbolic"
    , "execution."
    ]

  , prim "disable_crucible_assert_then_assume" "TopLevel ()"
    (pureVal disable_crucible_assert_then_assume)
    Current
    [ "Do not assume predicate after asserting it during Crucible"
    , "symbolic execution."
    ]

  , prim "enable_lax_arithmetic" "TopLevel ()"
    (pureVal enable_lax_arithmetic)
    Current
    [ "Enable lax rules for arithmetic overflow in Crucible." ]

  , prim "disable_lax_arithmetic" "TopLevel ()"
    (pureVal disable_lax_arithmetic)
    Current
    [ "Disable lax rules for arithmetic overflow in Crucible." ]

  , prim "enable_lax_pointer_ordering" "TopLevel ()"
    (pureVal enable_lax_pointer_ordering)
    Current
    [ "Enable lax rules for pointer ordering comparisons in Crucible." ]

  , prim "disable_lax_pointer_ordering" "TopLevel ()"
    (pureVal disable_lax_pointer_ordering)
    Current
    [ "Disable lax rules for pointer ordering comparisons in Crucible." ]

  , prim "enable_lax_loads_and_stores" "TopLevel ()"
    (pureVal enable_lax_loads_and_stores)
    Current
    [ "Enable relaxed validity checking for memory loads and stores in"
    , "Crucible."
    ]

  , prim "disable_lax_loads_and_stores" "TopLevel ()"
    (pureVal disable_lax_loads_and_stores)
    Current
    [ "Disable relaxed validity checking for memory loads and stores in"
    , "Crucible."
    ]

  , prim "enable_debug_intrinsics" "TopLevel ()"
    (pureVal enable_debug_intrinsics)
    Current
    [ "Enable translating statements using certain llvm.dbg intrinsic"
    , "functions in Crucible."
    ]

  , prim "disable_debug_intrinsics" "TopLevel ()"
    (pureVal disable_debug_intrinsics)
    Current
    [ "Disable translating statements using certain llvm.dbg intrinsic"
    , "functions in Crucible."
    ]

  , prim "enable_what4_hash_consing" "TopLevel ()"
    (pureVal enable_what4_hash_consing)
    Current
    [ "Enable hash-consing for What4 expressions." ]

  , prim "disable_what4_hash_consing" "TopLevel ()"
    (pureVal disable_what4_hash_consing)
    Current
    [ "Disable hash-consing for What4 expressions." ]

  , prim "enable_what4_eval" "TopLevel ()"
    (pureVal enable_what4_eval)
    Experimental
    [ "Enable What4 translation for SAWCore expressions during Crucible"
    , "symbolic execution."
    ]

  , prim "disable_what4_eval" "TopLevel ()"
    (pureVal disable_what4_eval)
    Current
    [ "Disable What4 translation for SAWCore expressions during"
    , "Crucible symbolic execution."
    ]

  , prim "enable_alloc_sym_init_check" "TopLevel ()"
    (pureVal enable_alloc_sym_init_check)
    Experimental
    [ "Enable the allocation initialization check associated with"
    , "'llvm_alloc_sym_init' during override application."
    ]

  , prim "disable_alloc_sym_init_check" "TopLevel ()"
    (pureVal disable_alloc_sym_init_check)
    Current
    [ "Disable the allocation initialization check associated with"
    , "'alloc_sym_init' during override application."
    , ""
    , "Disabling this check allows an override to apply when the memory"
    , "region specified by the 'alloc_sym_init' command in the override"
    , "specification is not written to in the calling context. This"
    , "implicitly assumes that there is some unspecified byte at any"
    , "valid memory address."
    ]

  , prim "enable_no_satisfying_write_fresh_constant" "TopLevel ()"
    (pureVal enable_no_satisfying_write_fresh_constant)
    Experimental
    [ "When simulating LLVM code that performs an invalid write, make a"
    , "fresh constant as a proof obligation. This constant will always"
    , "fail, but it will also not be constant-folded away."
    ]

  , prim "disable_no_satisfying_write_fresh_constant" "TopLevel ()"
    (pureVal disable_no_satisfying_write_fresh_constant)
    Experimental
    [ "When simulating LLVM code that performs an invalid write, return"
    , "'false' as a proof obligation."
    ]

  , prim "enable_what4_push_mux_ops" "TopLevel ()"
    (pureVal enable_what4_push_mux_ops)
    Experimental
    [ "Push certain What4 operations (e.g., 'zext') down to the"
    , "branches of 'ite' expressions as much as possible. In some (but"
    , "not all) circumstances, this can result in operations that are"
    , "easier for SMT solvers to reason about."
    ]

  , prim "disable_what4_push_mux_ops" "TopLevel ()"
    (pureVal disable_what4_push_mux_ops)
    Experimental
    [ "Do not push certain What4 operations (e.g., 'zext') down to the"
    , "branches of 'ite' expressions as much as possible."
    ]

  , prim "enable_crucible_profiling" "String -> TopLevel ()"
    (pureVal enable_crucible_profiling)
    Current
    [ "Record profiling information from symbolic execution and solver"
    , "invocation to the given directory."
    ]

  , prim "disable_crucible_profiling" "TopLevel ()"
    (pureVal disable_crucible_profiling)
    Current
    ["Stop recording profiling information."]

    ------------------------------------------------------------
    -- Other settings

  , prim "set_timeout"         "Int -> ProofScript ()"
    (pureVal set_timeout)
    Experimental
    [ "Set the timeout, in milliseconds, for any automated prover that"
    , "appears at the end of this proof script. For now provers that"
    , "don't support timeouts just ignore the setting."
    ]

  , prim "set_crucible_timeout" "Int -> TopLevel ()"
    (pureVal set_crucible_timeout)
    Experimental
    -- XXX does this really not apply to JVM/MIR verification, or is
    -- the help text just Olde?
    [ "Set the timeout for the SMT solver during the LLVM and x86"
    , "Crucible symbolic execution, in milliseconds. The default is"
    , "10000 (10 seconds). Set it to 0 to disable the timeout."
    , ""
    , "This setting is used for path-satisfiability checks and"
    , "satisfiability checks when applying overrides."
    ]

  , prim "set_path_sat_solver" "String -> TopLevel ()"
    (pureVal set_path_sat_solver)
    Experimental
    [ "Set the path satisfiablity solver to use. Currently accepted"
    , "values are 'z3' and 'yices'."
    ]

  , prim "set_ascii"           "Bool -> TopLevel ()"
    (pureVal set_ascii)
    Current
    [ "Select whether to pretty-print arrays of 8-bit numbers as ASCII"
    , "strings."
    ]

  , prim "set_base"            "Int -> TopLevel ()"
    (pureVal set_base)
    Current
    [ "Set the number base for pretty-printing numeric literals."
    , "Permissible values include 2, 8, 10, and 16."
    ]

  , prim "set_color"           "Bool -> TopLevel ()"
    (pureVal set_color)
    Current
    [ "Select whether to pretty-print SAWCore terms using color." ]

  , prim "set_min_sharing"     "Int -> TopLevel ()"
    (pureVal set_min_sharing)
    Current
    [ "Set the number times a subterm must be shared for it to be"
    , "let-bound in SAWCore printer output."
    ]

  , prim "set_memoization_hash" "Int -> TopLevel ()"
    (pureVal set_memoization_hash)
    Current
    [ "'set_memoization_hash i' changes the memoization strategy for"
    , "terms: memoization identifiers will include the first 'i' digits"
    , "of the hash of the term they memoize. This is useful to help"
    , "keep memoization identifiers of the same term as constant as"
    , "possible across different executions of a proof script over the"
    , "course of its development."
    ]

  , prim "set_memoization_hash_incremental" "Int -> TopLevel ()"
    (pureVal set_memoization_hash_incremental)
    Current
    [ "'set_memoization_hash_incremental i' changes the memoization"
    , "strategy for terms: memoization identifiers will include the"
    , "first 'i' digits of the hash of the term they memoize, as well"
    , "as the value of a global counter that increments each time a"
    , "term is memoized. This is useful to help keep memoization"
    , "identifiers of the same term as constant as possible across"
    , "different executions of a proof script over the course of its"
    , "development, as well as to freshen memoization identifiers in"
    , "the unlikely case of term hash collisions."
    ]

  , prim "set_memoization_incremental" "TopLevel ()"
    (pureVal set_memoization_incremental)
    Current
    [ "'set_memoization_incremental' changes the memoization strategy"
    , "for terms: memoization identifiers will only include the value"
    , "of a global counter that increments each time a term is"
    , "memoized. This is the default."
    ]

    ------------------------------------------------------------
    -- Solver cache

  , prim "set_solver_cache_path" "String -> TopLevel ()"
    (pureVal set_solver_cache_path)
    Current
    [ "Create a solver result cache at the given path, add all results"
    , "in the current solver result cache (if any), then use the newly"
    , "created cache as the solver result cache going forward. Note"
    , "that if the SAW_SOLVER_CACHE_PATH environment variable was set"
    , "at startup but no solver caching has actually been done yet, the"
    , "the value of the environment variable will be ignored."
    ]

  , prim "set_solver_cache_timeout" "Int -> TopLevel ()"
    (pureVal set_solver_cache_timeout)
    Current
    [ "Set the solver result cache's timeout (in microseconds) to use"
    , "for database lookups and inserts. The default timeout is"
    , "2,000,000 microseconds (2 seconds)."
    ]

  , prim "clean_mismatched_versions_solver_cache" "TopLevel ()"
    (pureVal clean_mismatched_versions_solver_cache)
    Current
    [ "Remove all entries in the solver result cache which were created"
    , "using solver backend versions which do not match the versions in"
    , "the current environment."
    ]

  , prim "print_solver_cache" "String -> TopLevel ()"
    (pureVal (onSolverCache . printSolverCacheByHex))
    Current
    [ "Print all entries in the solver result cache whose SHA256 hash"
    , "keys start with the given hex string. Providing an empty string"
    , "results in all entries in the cache being printed."
    ]

  , prim "print_solver_cache_stats" "TopLevel ()"
    (pureVal (onSolverCache printSolverCacheStats))
    Current
    [ "Print out statistics about how the solver cache has been used"
    , "so far in this session, namely:"
    , "   0. Where the cache is stored"
    , "   1. How many entries are in the cache"
    , "   2. How many insertions into the cache have been made"
    , "   3. How many failed insertion attempts have been made"
    , "   4. How times cached results have been used"
    , "   5. How many failed attempted usages have occurred."
    ]

  , prim "test_solver_cache_stats" "Int -> Int -> Int -> Int -> Int -> TopLevel ()"
    (pureVal test_solver_cache_stats)
    Current
    [ "Test whether the values of the statistics printed out by"
    , "'print_solver_cache_stats' are equal to those given, failing if"
    , "this does not hold. Specifically, the arguments represent:"
    , "   1. How many entries are in the cache"
    , "   2. How many insertions into the cache have been made"
    , "   3. How many failed insertion attempts have been made"
    , "   4. How times cached results have been used"
    , "   5. How many failed attempted usages have occurred"
    ]

    ------------------------------------------------------------
    -- SAWCore inspection

  , prim "show_term"           "Term -> String"
    (funVal1 show_term)
    Current
    [ "Pretty-print the given term in SAWCore syntax, yielding a"
    , "String."
    ]

  , prim "term_size"           "Term -> Int"
    (pureVal scSharedSize)
    Current
    [ "Return the size of the given term in the number of DAG nodes." ]

  , prim "term_tree_size"      "Term -> Int"
    (pureVal scTreeSize)
    Current
    [ "Return the size of the given term in the number of nodes it"
    , "would have if treated as a tree instead of a DAG."
    ]

  , prim "term_theories" "[String] -> Term -> [String]"
    (funVal2 term_theories)
    Experimental
    [ "Given a term of type 'Bool', compute the SMT theories required"
    , "to reason about this term. The functions (if any) given in the"
    , "first argument will be treated as uninterpreted."
    , ""
    , "If the returned list is empty, the given term represents a"
    , "problem that can be solved purely by boolean SAT reasoning."
    , ""
    , "Note: the given term will be simplified using the What4 backend"
    , "before inspection.. For simple problems, this may simplify away"
    , "some aspects of the problem altogether and may result in fewer"
    , "theories in the output than one might expect."
    ]

  , prim "is_convertible"  "Term -> Term -> TopLevel Bool"
    (pureVal isConvertiblePrim)
    Current
    [ "Returns true iff the two terms are convertible." ]

  , prim "check_convertible"  "Term -> Term -> TopLevel ()"
    (pureVal checkConvertiblePrim)
    Current
    [ "Check if two terms are convertible and print the result." ]

  , prim "print_term"          "Term -> TopLevel ()"
    (pureVal print_term)
    Current
    [ "Pretty-print the given term in SAWCore syntax." ]

  , prim "print_term_depth"    "Int -> Term -> TopLevel ()"
    (pureVal print_term_depth)
    Current
    [ "Pretty-print the given term in SAWCore syntax up to a given"
    , "depth."
    ]

  , prim "check_term"          "Term -> TopLevel ()"
    (pureVal check_term)
    Current
    [ "Type-check the given term, printing an error message if"
    , "ill-typed. Also see 'check_goal'."
    ]

    ------------------------------------------------------------
    -- SAWCore term construction

  , prim "fresh_symbolic"      "String -> Type -> TopLevel Term"
    (pureVal freshSymbolicPrim)
    Current
    [ "Create a fresh symbolic variable of the given type. The name"
    , "(first argument) is used only for pretty-printing."
    ]

  , prim "abstract_symbolic"   "Term -> Term"
    (funVal1 abstractSymbolicPrim)
    Current
    [ "Take a term containing symbolic variables of the form returned"
    , "by 'fresh_symbolic' and return a new lambda term in which those"
    , "variables have been replaced by parameter references."
    ]

  , prim "lambda"              "Term -> Term -> Term"
    (funVal2 lambda)
    Current
    [ "Take a 'fresh_symbolic' variable and another term containing"
    , "that variable, and return a new lambda abstraction over that"
    , "variable."
    ]

  , prim "lambdas"             "[Term] -> Term -> Term"
    (funVal2 lambdas)
    Current
    [ "Take a list of 'fresh_symbolic' variables and another Term"
    , "containing those variables, and return a new lambda abstraction"
    , "over all the variables in the list."
    ]

  , prim "generalize_term"   "[Term] -> Term -> Term"
    (funVal2 generalize_term)
    Experimental
    [ "Take a list of 'fresh_symbolic' variables and another term"
    , "containing those variables, and return a new Pi generalization"
    , "over all the variables in the list."
    ]

  , prim "int_to_term"      "Int -> Term"
    (funVal1 int_to_term)
    Current
    [ "Convert a concrete integer value into an integer term." ]

  , prim "nat_to_term"      "Int -> Term"
    (funVal1 nat_to_term)
    Current
    [ "Convert a non-negative integer value into a natural number term." ]

  , prim "size_to_term"      "Type -> Term"
    (funVal1 size_to_term)
    Current
    [ "Convert a Cryptol size type into a Term representation." ]

  , prim "term_apply"          "Term -> [Term] -> Term"
    (funVal2 term_apply)
    Current
    [ "Build a term application node that applies the first term (which"
    , "must be a function) to the given list of arguments."
    ]

  , prim "implies_term"      "Term -> Term -> Term"
    (funVal2 implies_term)
    Experimental
    [ "Given two terms 'e1' and 'e2' of underlying type 'Prop',"
    , "construct the SAWCore implication e1 ==> e2."
    ]

    ------------------------------------------------------------
    -- SAWCore term manipulation

  , prim "define"              "String -> Term -> TopLevel Term"
    (pureVal definePrim)
    Current
    [ "Wrap a term with a name that allows its body to be hidden or"
    , "revealed. This can allow any sub-term to be treated as an"
    , "uninterpreted function during proofs."
    ]

  , prim "unfold_term"         "[String] -> Term -> Term"
    (funVal2 unfold_term)
    Current
    [ "Unfold the definitions of the specified constants in the given"
    , "term. Also see 'unfolding'."
    ]

  , prim "replace"             "Term -> Term -> Term -> TopLevel Term"
    (pureVal replacePrim)
    Current
    [ "'replace x y z' rewrites occurences of term x into y inside the"
    , "term z. x and y must be closed terms."
    ]

  , prim "rewrite"             "Simpset -> Term -> Term"
    (funVal2 rewritePrim)
    Current
    [ "Rewrite a term using a set of simplification rules."
    , "Returns the rewritten term."
    ]

  , prim "normalize_term"      "Term -> Term"
    (funVal1 normalize_term)
    Experimental
    [ "Normalize the given term by performing evaluation in SAWCore."
    , "Also see 'goal_normalize'."
    ]

  , prim "normalize_term_opaque" "[String] -> Term -> Term"
    (funVal2 normalize_term_opaque)
    Experimental
    [ "Normalize the given term by performing evaluation in SAWCore."
    , "The named values in the first argument will be treated opaquely"
    , "and not unfolded during evaluation."
    ]

  , prim "term_eval"           "Term -> Term"
    (funVal1 (term_eval []))
    Current
    [ "Evaluate the term to a first-order combination of primitives." ]

  , prim "term_eval_unint"     "[String] -> Term -> Term"
    (funVal2 term_eval)
    Current
    [ "Evaluate the term to a first-order combination of primitives."
    , "Leave the given names, as defined with 'define', uninterpreted." ]

  , prim "default_term" "Term -> Term"
    (funVal1 default_typed_term)
    Experimental
    [ "Apply Cryptol defaulting rules to the given term." ]

  , prim "hoist_ifs"            "Term -> TopLevel Term"
    (pureVal hoistIfsPrim)
    Current
    [ "Hoist all if-then-else expressions as high as possible." ]

  , prim "beta_reduce_term"    "Term -> Term"
    (funVal1 beta_reduce_term)
    Current
    [ "Reduce the given term to beta-normal form." ]

  , prim "congruence_for" "Term -> TopLevel Term"
    (pureVal congruence_for)
    Experimental
    [ "Given a term representing a (nondependent) function, attempt"
    , "to automatically construct the statement of a congruence lemma"
    , "for the function."
    ]

    ------------------------------------------------------------
    -- SAWCore file and text operations

  , prim "parse_core"         "String -> Term"
    (funVal1 parse_core)
    Current
    [ "Parse a Term from a String in SAWCore syntax." ]

  , prim "parse_core_mod"      "String -> String -> Term"
    (funVal2 parse_core_mod)
    Current
    [ "Parse a Term from the second supplied String in SAWCore syntax,"
    , "relative to the module specified by the first String."
    ]

  , prim "load_sawcore_from_file"
    "String -> TopLevel ()"
    (bicVal do_load_sawcore_from_file)
    Experimental
    [ "Load a SAW core module from a file, using the concrete syntax"
    , "parser."
    ]

  , prim "read_core"           "String -> TopLevel Term"
    (pureVal readCore)
    Current
    [ "Read a term from a file in the SAWCore external format." ]

  , prim "write_core"          "String -> Term -> TopLevel ()"
    (pureVal do_write_core)
    Current
    [ "Write out a representation of a term in SAWCore external format." ]

  , prim "offline_extcore"     "String -> ProofScript ()"
    (pureVal do_offline_extcore)
    Current
    [ "Write the current goal to the given file in SAWCore format." ]

    ------------------------------------------------------------
    -- Theorems and theorem statements

  , prim "qc_print"            "Int -> Term -> TopLevel ()"
    (scVal' quickCheckPrintPrim)
    Current
    [ "Quick-check a term by applying it to a sequence of random inputs"
    , "and print the results. The 'Int' arg specifies how many tests to"
    , "run."
    ]

  , prim "sat"                 "ProofScript () -> Term -> TopLevel SatResult"
    (pureVal satPrim)
    Current
    [ "Use the given proof script to attempt to prove that a term is"
    , "satisfiable (evaluates to true for some input). Returns a result"
    , "of type 'SatResult' that can be inspected with 'caseSatResult'."
    , "It either carries a satisfying assignment or indicates"
    , "unsatisfiability."
    ]

  , prim "sat_print"           "ProofScript () -> Term -> TopLevel ()"
    (pureVal satPrintPrim)
    Current
    [ "Use the given proof script to attempt to prove that a term is"
    , "satisfiable (true for any input). Returns nothing if successful,"
    , "and fails if unsuccessful."
    ]

  , prim "sharpSAT"  "Term -> TopLevel Int"
    (pureVal sharpSAT)
    Current
    [ "Use the sharpSAT solver to count the number of solutions to the"
    , "CNF representation of the given Term."
    ]

  , prim "prove"               "ProofScript () -> Term -> TopLevel ProofResult"
    (pureVal provePrim)
    Current
    [ "Use the given proof script to attempt to prove that a term is"
    , "valid (true for all inputs). Returns a ProofResult value that"
    , "can be inspected with 'caseProofResult'. It carries either a"
    , "proved 'Theorem' or a counterexample."
    ]

  , prim "prove_print"         "ProofScript () -> Term -> TopLevel Theorem"
    (pureVal provePrintPrim)
    Current
    [ "Use the given proof script to attempt to prove that a term is"
    , "valid (true for all inputs). Returns a Theorem if successful,"
    , "and fails if unsuccessful."
    ]

  , prim "prove_extcore"         "ProofScript () -> Term -> TopLevel Theorem"
    (pureVal provePropPrim)
    Current
    [ "Use the given proof script to attempt to prove that a term"
    , "representing a proposition is valid. This is useful for proving"
    , "goals obtained with 'offline_extcore' or 'parse_core'. Returns a"
    , "Theorem if successful, and fails if unsuccessful."
    ]

  , prim "prove_core"         "ProofScript () -> String -> TopLevel Theorem"
    (pureVal prove_core)
    Current
    [ "Use the given proof script to attempt to prove that a term is"
    , "valid (true for all inputs). The term is specified as a String"
    , "containing SAWCore concrete syntax. Returns a Theorem if"
    , "successful, and fails if unsuccessful."
    ]

  , prim "core_axiom"         "String -> Theorem"
    (funVal1 core_axiom)
    Current
    [ "Declare the given core expression as an axiomatic rewrite rule."
    , "The input string contains a proof goal in SAWCore concrete"
    , "syntax. The return value is a Theorem that may be added to a"
    , "Simpset."
    ]

  , prim "core_thm"           "String -> Theorem"
    (funVal1 core_thm)
    Current
    [ "Create a theorem from the type of the given core expression." ]

  , prim "specialize_theorem" "Theorem -> [Term] -> TopLevel Theorem"
    (pureVal specialize_theorem)
    Experimental
    [ "Specialize a theorem by instantiating universal quantifiers with"
    , "the given list of terms."
    ]

  , prim "prove_by_bv_induction"  "ProofScript () -> Term -> TopLevel Theorem"
    (pureVal proveByBVInduction)
    Experimental
    [ "Attempt to prove a fact by induction on the less-than order on"
    , "bitvectors. The given term is expected to be a function of one"
    , "or more arguments which returns a tuple containing two values:"
    , "first, a bitvector expression (which will be the expression we"
    , "perform induction on), and second, a boolean value defining the"
    , "theorem to prove."
    , ""
    , "This command will attempt to prove the theorem expressed in the"
    , "second element of the tuple by induction. The goal presented to"
    , "the user-provided tactic will ask to prove the stated goal and"
    , "will be provided with an induction hypothesis which states that"
    , "the goal holds for all values of the variables where the"
    , "expression given in the first element of the tuple has"
    , " decreased."
    ]

  , prim "prove_bisim"         ("ProofScript () -> [BisimTheorem] -> " <>
                                "Term -> Term -> Term -> Term -> " <>
                                "TopLevel BisimTheorem")
    (pureVal proveBisimulation)
    Experimental
    [ "Use bisimulation to prove that two terms simulate each other."
    , "The command takes the following arguments: "
    , "   1. The proof strategy to use"
    , "   2. A list of already proven bisimulation theorems"
    , "   3. A state relation 'srel : lhsState -> rhsState -> Bit'"
    , "   4. An output relation"
    , "      'orel : (lhsState, output) -> (rhsState, output) -> Bit'"
    , "   5. A term 'lhs : (lhsState, input) -> (lhsState, output)'"
    , "   6. A term 'rhs : (rhsState, input) -> (rhsState, output)'"
    , "and considers 'lhs' and 'rhs' bisimilar when the following two"
    , "theorems hold:"
    , "   * OUTPUT RELATION THEOREM:"
    , "      forall s1 s2 in."
    , "      srel s1 s2 -> orel (lhs (s1, in)) (rhs (s2, in))"
    , "   * STATE RELATION THEOREM:"
    , "      forall s1 s2 out1 out2."
    , "      orel (s1, out1) (s2, out2) -> srel s1 s2"
    , ""
    , "LIMITATIONS: For now, the prove_bisim command has a couple"
    , "limitations:"
    , "   * 'lhs' and 'rhs' (arguments 5 and 6) must be named"
    , "     functions."
    , "   * Each subterm present in the list of bisimulation theorems"
    , "     already proven (argument 2) may be invoked at most once in"
    , "     'lhs' or 'rhs'."
    ]

    ------------------------------------------------------------
    -- Proof inspection / reporting

  , prim "summarize_verification" "TopLevel ()"
    (pureVal summarize_verification)
    Experimental
    [ "Print a human-readable summary of all verifications performed so"
    , "far."
    ]

  , prim "summarize_verification_json" "String -> TopLevel ()"
    (pureVal do_summarize_verification_json)
    Experimental
    [ "Print a JSON summary of all verifications performed so far into"
    , "the named file."
    ]

    ------------------------------------------------------------
    -- Simplification sets

  , prim "empty_ss"            "Simpset"
    (pureVal (emptySimpset :: SAWSimpset))
    Current
    [ "The empty simplification rule set, containing no rules." ]

  , prim "addsimp"             "Theorem -> Simpset -> Simpset"
    (funVal2 addsimp)
    Current
    [ "Add a proved equality theorem to a simplification rule set,"
    , "and return a new set."
    ]

  , prim "addsimp_shallow"    "Theorem -> Simpset -> Simpset"
    (funVal2 addsimp_shallow)
    Current
    [ "Add a proved equality theorem to a simplification rule set."
    , "The rule is treated as a 'shallow' rewrite, which means that"
    , "further rewrite rules will not be applied to the result if this"
    , "rule fires. Returns a new set.n"
    ]

  , prim "addsimps"            "[Theorem] -> Simpset -> Simpset"
    (funVal2 addsimps)
    Current
    [ "Add multiple proved equality theorems to a simplification rule"
    , "set. Returns a new set."
    ]

  , prim "addsimp'"            "Term -> Simpset -> Simpset"
    (funVal2 addsimp')
    HideDeprecated
    [ "Add an arbitrary equality term to a simplification rule set."
    , "Deprecated; use 'admit' or 'core_axiom' and 'addsimp' instead."
    , ""
    , "Expected to be removed in SAW 1.5."
    ]

  , prim "addsimps'"           "[Term] -> Simpset -> Simpset"
    (funVal2 addsimps')
    HideDeprecated
    [ "Add multiple arbitrary equality terms to a simplification rule"
    , "set. Deprecated; use 'admit' or 'core_axiom' and 'addsimps'"
    , "instead."
    , ""
    , "Expected to be removed in SAW 1.5."
    ]

  , prim "basic_ss"            "Simpset"
    (bicVal $ \bic _ -> toValue "basic_ss" $ biBasicSS bic)
    Current
    [ "A basic rewriting simplification set containing some boolean"
    , "identities and conversions relating to bitvectors, natural"
    , "numbers, and vectors."
    ]

  , prim "cryptol_ss"          "() -> Simpset"
    (funVal1 (\ () -> cryptolSimpset))
    Current
    [ "A set of simplification rules that will expand definitions from"
    , "the Cryptol import module."
    ]

  , prim "add_prelude_eqs"     "[String] -> Simpset -> Simpset"
    (funVal2 addPreludeEqs)
    Current
    [ "Add the named equality rules from the Prelude module to a"
    , "simplification rule set, and return a new set."
    ]

  , prim "add_cryptol_eqs"     "[String] -> Simpset -> Simpset"
    (funVal2 addCryptolEqs)
    Current
    [ "Add the named equality rules from the Cryptol import module to a"
    , "simplification rule set, and return a new set."
    ]

  , prim "add_prelude_defs"    "[String] -> Simpset -> Simpset"
    (funVal2 add_prelude_defs)
    Current
    [ "Add the named definitions from the Prelude module to a"
    , "simplification rule set, and return a new set."
    ]

  , prim "add_cryptol_defs"    "[String] -> Simpset -> Simpset"
    (funVal2 add_cryptol_defs)
    Current
    [ "Add the named definitions from the Cryptol import module to a"
    , "simplification rule set, and return a new set."
    ]

    ------------------------------------------------------------
    -- Inspection proof tactics

  , prim "goal_num" "ProofScript Int"
    (pureVal goal_num)
    Current
    [ "Returns the number of the current proof goal." ]

  , prim "print_goal"          "ProofScript ()"
    (pureVal print_goal)
    Current
    [ "Print the current goal that a proof script is attempting to"
    , "prove."
    ]

  , prim "print_goal_inline"   "[Int] -> ProofScript ()"
    (pureVal print_goal_inline)
    Current
    [ "Print the current goal that a proof script is attempting to"
    , "prove, without generating 'let' bindings for the provided"
    , "indices. For example, 'print_goal_inline [1,9,3]' will print the"
    , "goal without inlining the variables that would otherwise be"
    , "abstracted as 'x@1', 'x@9', and 'x@3'. These indices are"
    , "assigned deterministically for any given goal, but are not"
    , "persistent across goals. Therefore, such, this command should be"
    , "used primarily for proof debugging."
    , ""
    , "Note: incompatible with non-incremental memoization strategies -"
    , "see 'set_memoization_incremental' and"
    , "'set_memoization_hash_incremental'."
    ]

  , prim "print_goal_depth"    "Int -> ProofScript ()"
    (pureVal print_goal_depth)
    Current
    [ "Print the current goal that a proof script is attempting to"
    , "prove, limited to a maximum depth."
    ]

  , prim "print_goal_size"     "ProofScript ()"
    (pureVal printGoalSize)
    Current
    [ "Print the size of the goal in terms of both the number of DAG"
    , "nodes and the number of nodes it would have if represented as a"
    , "tree."
    ]

  , prim "write_goal" "String -> ProofScript ()"
    (pureVal do_write_goal)
    Current
    [ "Write the current goal that a proof script is attempting to"
    , "prove into the named file."
    ]

  , prim "print_goal_summary" "ProofScript ()"
    (pureVal print_goal_summary)
    Current
    [ "Print the number and description of the goal that a proof script"
    , "is attempting to prove."
    ]

  , prim "print_goal_consts"   "ProofScript ()"
    (pureVal printGoalConsts)
    Current
    [ "Print the list of unfoldable constants in the current proof"
    , "goal."
    ]

  , prim "check_goal"          "ProofScript ()"
    (pureVal check_goal)
    Current
    [ "Type-check the current proof goal, printing an error message if"
    , "ill-typed. Also see 'check_term'."
    ]

    ------------------------------------------------------------
    -- Decomposition-related proof tactics

  , prim "split_goal"          "ProofScript ()"
    (pureVal split_goal)
    Experimental
    [ "Split a goal of the form 'Prelude.and prop1 prop2' into two"
    ,  "separate goals 'prop1' and 'prop2'."
    ]

  , prim "goal_cut" "Term -> ProofScript ()"
    (pureVal goal_cut)
    Experimental
    [ "Given a term provided by the user (which must be a boolean"
    , "expression or a Prop) the current goal is split into two"
    , "subgoals. In the first subgoal, the given proposition is assumed"
    , "as a new hypothesis. In the second subgoal, the given"
    , "proposition is a new focused, conclusion. This implements the"
    , "usual cut rule of sequent calculus."
    ]

    ------------------------------------------------------------
    -- Evaluation-related proof tactics

  , prim "unfolding"           "[String] -> ProofScript ()"
    (pureVal unfoldGoal)
    Current
    [ "Unfold the named subterm(s) within the current goal."
    , "Also see 'unfold_term'."
    ]

  , prim "unfolding_fix_once" "[String] -> ProofScript ()"
    (pureVal unfoldFixOnceGoal)
    Current
    [ "Unfold the named recursive constants once within the current"
    , "goal. Like 'unfolding', except that the recursive constants are"
    , "unfolded only once, avoiding possible infinite evaluation."
    ]

  , prim "simplify"            "Simpset -> ProofScript ()"
    (pureVal simplifyGoal)
    Current
    [ "Apply the given simplification rule set to the current goal." ]

  , prim "simplify_local"       "[Int] -> Simpset -> ProofScript ()"
    (pureVal simplifyGoalWithLocals)
    Current
    [ "Apply the given simplification rule set to the current goal."
    , "Also, use the given numbered hypotheses as rewrites."
    ]

  , prim "goal_normalize"  "[String] -> ProofScript ()"
    (pureVal goal_normalize)
    Experimental
    [ "Evaluate the current proof goal by performing evaluation in"
    , "SAWCore. The currently-focused term will be evaluated. If the"
    , "sequent is unfocused, all terms will be evaluated. The names"
    , "given in the argument will be treated as uninterpreted."
    , "Also see 'normalize_term'."
    ]

  , prim "goal_eval"           "ProofScript ()"
    (pureVal (goal_eval []))
    Current
    [ "Evaluate the proof goal to a first-order combination of"
    , "primitives."
    ]

  , prim "goal_eval_unint"     "[String] -> ProofScript ()"
    (pureVal goal_eval)
    Current
    [ "Evaluate the proof goal to a first-order combination of"
    , "primitives. Leave the given list of names uninterpreted."
    ]

    ------------------------------------------------------------
    -- Rewriting-related proof tactics

  , prim "hoist_ifs_in_goal"            "ProofScript ()"
    (pureVal hoistIfsInGoalPrim)
    Experimental
    [ "Hoist ifs in the current proof goal." ]

  , prim "beta_reduce_goal"    "ProofScript ()"
    (pureVal beta_reduce_goal)
    Current
    [ "Reduce the current goal to beta-normal form." ]

  , prim "goal_intro"          "String -> ProofScript Term"
    (pureVal goal_intro)
    Experimental
    [ "Introduce a quantified variable in the current proof goal,"
    , "returning the variable as a Term."
    ]

  , prim "normalize_sequent" "ProofScript ()"
    (pureVal normalize_sequent)
    Experimental
    [ "Normalize the current goal sequent by applying reversable"
    , "sequent calculus rules. The resulting sequent will be unfocused."
    ]

    ------------------------------------------------------------
    -- Premise-related proof tactics

  , prim "retain_hyps" "[Int] -> ProofScript ()"
    (pureVal retain_hyps)
    Experimental
    [ "Remove all hypotheses from the current sequent other than the"
    , " ones listed."
    ]

  , prim "delete_hyps" "[Int] -> ProofScript ()"
    (pureVal delete_hyps)
    Experimental
    [ "Remove the numbered hypotheses from the current sequent." ]

  , prim "goal_intro_hyp"      "ProofScript ()"
    (pureVal goal_intro_hyp)
    Experimental
    [ "When focused on a conclusion that represents an implication,"
    , "simplify the conclusion by removing the implication and"
    , "introducing a new sequent hypothesis instead."
    ]

  , prim "goal_intro_hyps"     "Int -> ProofScript ()"
    (pureVal goal_intro_hyps)
    Experimental
    [ "When focused on a conclusion that represents an implication,"
    , "simplify the conclusion by removing the implication and"
    , "introducing a new sequent hypothesis instead. The argument gives"
    , "how many hypotheses to introduce."
    ]

  , prim "goal_revert_hyp"     "Int -> ProofScript ()"
    (pureVal goal_revert_hyp)
    Experimental
    [ "When focused on a conclusion, weaken the focused conclusion"
    , "by introducing an implication using the numbered sequent"
    , "hypothesis. This is essentially the reverse of"
    , "'goal_intro_hyp'."
    ]

  , prim "goal_insert"         "Theorem -> ProofScript ()"
    (pureVal goal_insert)
    Experimental
    [ "Insert a Theorem as a new hypothesis in the current proof goal."
    ]

  , prim "goal_insert_and_specialize"  "Theorem -> [Term] -> ProofScript ()"
    (pureVal goal_insert_and_specialize)
    Experimental
    [ "Insert a Theorem as a new hypothesis in the current proof goal,"
    , "after specializing some of its universal quantifiers using the"
    , "given terms."
    ]

  , prim "goal_specialize_hyp" "[Term] -> ProofScript ()"
    (pureVal goal_specialize_hyp)
    Experimental
    [ "Specialize the focused local hypothesis by supplying the values"
    , "for universal quantifiers. A new specialized hypothesis will be"
    , "added to the sequent."
    ]

  , prim "goal_apply_hyp"      "Int -> ProofScript ()"
    (pureVal goal_apply_hyp)
    Experimental
    [ "Apply the numbered local hypothesis to the focused conclusion." ]

  , prim "goal_apply"          "Theorem -> ProofScript ()"
    (pureVal goal_apply)
    Experimental
    [ "Apply an introduction rule to the current goal. Depending on the"
    , "rule, this will result in zero or more new subgoals."
    ]

    ------------------------------------------------------------
    -- Automation-related proof tactics

  , prim "goal_when"           "String -> ProofScript () -> ProofScript ()"
    (pureVal goal_when)
    Experimental
    [ "Run the given proof script only when the goal name contains the"
    , "given string."
    ]

  , prim "goal_num_when"       "Int -> ProofScript () -> ProofScript ()"
    (pureVal goal_num_when)
    Experimental
    [ "Run the given proof script only when the goal number is the"
    , "given number."
    ]

  , prim "goal_num_ite"       ("{a} Int -> ProofScript a -> ProofScript a" <>
                               "-> ProofScript a")
    (pureVal goal_num_ite)
    Experimental
    [ "If the goal number is the given number, runs the first script."
    , "Otherwise runs the second script."
    ]

  , prim "goal_has_tags"      "[String] -> ProofScript Bool"
    (pureVal goal_has_tags)
    Experimental
    [ "Returns true if the current goal is tagged with all the tags"
    , "in the given list. This function returns true for all goals"
    , "when given an empty list. Tags may be added to goals using"
    , "'llvm_setup_with_tag' and similar operations in the"
    , "specification setup phase."
    ]

  , prim "goal_has_some_tag"  "[String] -> ProofScript Bool"
    (pureVal goal_has_some_tag)
    Experimental
    [ "Returns true if the current goal is tagged with any the tags"
    , "in the given list. This function returns false for all goals"
    , "when given an empty list. Tags may be added to goals using"
    , "'llvm_setup_with_tag' and similar operations in the"
    , "specification setup phase."
    ]

    ------------------------------------------------------------
    -- Focus-related proof tactics

  , prim "unfocus"        "ProofScript ()"
    (pureVal unfocus)
    Experimental
    [ "Remove any sequent focus point." ]

  , prim "focus_concl"      "Int -> ProofScript ()"
    (pureVal focus_concl)
    Experimental
    [ "Focus on the numbered conclusion within a sequent. This will"
    , "fail if there are not enough conclusions."
    ]

  , prim "focus_hyp"       "Int -> ProofScript ()"
    (pureVal focus_hyp)
    Experimental
    -- XXX this description doesn't make sense
    [ "Focus on the numbered conclusion with a sequent.  This will fail"
    , "if there are enough hypotheses."
    ]

  , prim "print_focus" "ProofScript ()"
    (pureVal print_focus)
    Experimental
    [ "Print just the focused part of the current goal. Prints a"
    , "message without failing if there is no current focus."
    ]

    ------------------------------------------------------------
    -- Miscellaneous proof tactics

  , prim "quickcheck"          "Int -> ProofScript ()"
    (scVal quickcheckGoal)
    Current
    [ "Quick-check the current goal by applying it to a sequence of"
    , "random inputs. Fail the proof script if the goal returns 'False'"
    , "for any of these inputs."
    ]

  , prim "trivial"             "ProofScript ()"
    (pureVal trivial)
    Current
    [ "Succeeds if the goal is trivial. This tactic recognizes goals"
    , "that are instances of reflexivity, possibly with quantified"
    , "variables. In particular, it will prove goals of the form"
    , "'EqTrue x' when 'x' reduces to the constant value 'True'."
    ]

  , prim "goal_exact"          "Term -> ProofScript ()"
    (pureVal goal_exact)
    Experimental
    [ "Prove the current goal by giving an explicit proof term. This"
    , "will succeed if the type of the given term matches the current"
    , "goal."
    ]

  , prim "assume_valid"        "ProofScript ()"
    (pureVal assumeValid)
    Current
    [ "Assume the current goal is valid, completing the proof."
    , "This command will eventually be removed. Use 'admit' instead."
    ]

  , prim "assume_unsat"        "ProofScript ()"
    (pureVal assumeUnsat)
    Current
    [ "Assume the current goal is unsatisfiable, completing the proof."
    , "This command will eventually be removed. Use 'admit' instead."
    ]

  , prim "admit"               "String -> ProofScript ()"
    (pureVal admitProof)
    Current
    [ "Admit the current goal, completing the proof by assumption."
    , "The string argument should give an explanation of the decision"
    , "to admit this goal."
    ]

  , prim "retain_concl" "[Int] -> ProofScript ()"
    (pureVal retain_concl)
    Experimental
    [ "Remove all conclusions from the current sequent other than the"
    , " ones listed."
    ]

  , prim "delete_concl" "[Int] -> ProofScript ()"
    (pureVal delete_concl)
    Experimental
    [ "Remove the numbered conclusions from the current sequent." ]

    ------------------------------------------------------------
    -- Solvers

    -- abc

  , prim "abc"                 "ProofScript ()"
    (pureVal w4_abc_aiger)
    Current
    [ "Use the ABC theorem prover to prove the current goal." ]

  , prim "sbv_abc"             "ProofScript ()"
    (pureVal proveABC_SBV)
    Current
    [ "Use the ABC theorem prover to prove the current goal." ]

  , prim "w4_abc_aiger"        "ProofScript ()"
    (pureVal w4_abc_aiger)
    Current
    [ "Use the ABC theorem prover as an external process to prove the"
    , "current goal, with AIGER as an interchange format, generated"
    , "using the What4 backend."
    ]

  , prim "w4_abc_smtlib2"        "ProofScript ()"
    (pureVal w4_abc_smtlib2)
    Current
    [ "Use the ABC theorem prover as an external process to prove the"
    , "current goal, with SMT-Lib2 as an interchange format, generated"
    , "using the What4 backend."
    ]

  , prim "w4_abc_verilog"        "ProofScript ()"
    (pureVal w4_abc_verilog)
    Current
    [ "Use the ABC theorem prover as an external process to prove the"
    , "current goal, with Verilog as an interchange format, generated"
    , "using the What4 backend."
    ]

    -- bitwuzla

  , prim "bitwuzla"            "ProofScript ()"
    (pureVal proveBitwuzla)
    Current
    [ "Use the Bitwuzla theorem prover to prove the current goal." ]

  , prim "unint_bitwuzla" "[String] -> ProofScript ()"
    (pureVal proveUnintBitwuzla)
    Current
    [ "Use the Bitwuzla theorem prover to prove the current goal. Leave"
    , "the given list of names as uninterpreted."
    ]

  , prim "sbv_bitwuzla"        "ProofScript ()"
    (pureVal proveBitwuzla)
    Current
    [ "Use the Bitwuzla theorem prover to prove the current goal." ]

  , prim "sbv_unint_bitwuzla" "[String] -> ProofScript ()"
    (pureVal proveUnintBitwuzla)
    Current
    [ "Use the Bitwuzla theorem prover to prove the current goal. Leave"
    , "the given list of names as uninterpreted."
    ]

  , prim "w4_unint_bitwuzla" "[String] -> ProofScript ()"
    (pureVal w4_unint_bitwuzla)
    Current
    [ "Prove the current goal using What4 (Bitwuzla backend). Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "offline_w4_unint_bitwuzla" "[String] -> String -> ProofScript ()"
    (pureVal do_offline_w4_unint_bitwuzla)
    Current
    [ "Write the current goal to the given file using What4 (Bitwuzla"
    , "backend) in SMT-Lib2 format. Leave the given list of names as"
    , "uninterpreted."
    ]

    -- boolector

  , prim "boolector"           "ProofScript ()"
    (pureVal proveBoolector)
    Current
    [ "Use the Boolector theorem prover to prove the current goal." ]

  , prim "sbv_boolector"       "ProofScript ()"
    (pureVal proveBoolector)
    Current
    [ "Use the Boolector theorem prover to prove the current goal." ]

    -- cvc4/5

  , prim "cvc4"                "ProofScript ()"
    (pureVal proveCVC4)
    Current
    [ "Use the CVC4 theorem prover to prove the current goal." ]

  , prim "cvc5"                "ProofScript ()"
    (pureVal proveCVC5)
    Current
    [ "Use the CVC5 theorem prover to prove the current goal." ]

  , prim "unint_cvc4"            "[String] -> ProofScript ()"
    (pureVal proveUnintCVC4)
    Current
    [ "Use the CVC4 theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "unint_cvc5"            "[String] -> ProofScript ()"
    (pureVal proveUnintCVC5)
    Current
    [ "Use the CVC5 theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "sbv_cvc4"            "ProofScript ()"
    (pureVal proveCVC4)
    Current
    [ "Use the CVC4 theorem prover to prove the current goal." ]

  , prim "sbv_cvc5"            "ProofScript ()"
    (pureVal proveCVC5)
    Current
    [ "Use the CVC5 theorem prover to prove the current goal." ]

  , prim "sbv_unint_cvc4"        "[String] -> ProofScript ()"
    (pureVal proveUnintCVC4)
    Current
    [ "Use the CVC4 theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "sbv_unint_cvc5"        "[String] -> ProofScript ()"
    (pureVal proveUnintCVC5)
    Current
    [ "Use the CVC5 theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "w4_unint_cvc4"         "[String] -> ProofScript ()"
    (pureVal w4_unint_cvc4)
    Current
    [ "Prove the current goal using What4 (CVC4 backend). Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "w4_unint_cvc5"         "[String] -> ProofScript ()"
    (pureVal w4_unint_cvc5)
    Current
    [ "Prove the current goal using What4 (CVC5 backend). Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "offline_w4_unint_cvc4"  "[String] -> String -> ProofScript ()"
    (pureVal do_offline_w4_unint_cvc4)
    Current
    [ "Write the current goal to the given file using What4 (CVC4"
    , "backend) in SMT-Lib2 format. Leave the given list of names"
    , "uninterpreted."
    ]

  , prim "offline_w4_unint_cvc5"  "[String] -> String -> ProofScript ()"
    (pureVal do_offline_w4_unint_cvc5)
    Current
    [ "Write the current goal to the given file using What4 (CVC5"
    , "backend) in SMT-Lib2 format. Leave the given list of names"
    , "uninterpreted."
    ]

    -- mathsat

  , prim "mathsat"             "ProofScript ()"
    (pureVal proveMathSAT)
    Current
    [ "Use the MathSAT theorem prover to prove the current goal." ]

  , prim "sbv_mathsat"         "ProofScript ()"
    (pureVal proveMathSAT)
    Current
    [ "Use the MathSAT theorem prover to prove the current goal." ]

    -- rme

  , prim "rme"                 "ProofScript ()"
    (pureVal proveRME)
    Current
    [ "Prove the current goal by expansion to Reed-Muller Normal Form." ]

  , prim "w4_unint_rme" "[String] -> ProofScript ()"
    (pureVal w4_unint_rme)
    Current
    [ "Prove the current goal using What4 (RME backend). Leave the"
    , "given list of names as uninterpreted."
    ]

    -- yices

  , prim "yices"               "ProofScript ()"
    (pureVal proveYices)
    Current
    [ "Use the Yices theorem prover to prove the current goal." ]

  , prim "unint_yices"           "[String] -> ProofScript ()"
    (pureVal proveUnintYices)
    Current
    [ "Use the Yices theorem prover to prove the current goal. Leave"
    , "the given list of names as uninterpreted."
    ]

  , prim "sbv_yices"           "ProofScript ()"
    (pureVal proveYices)
    Current
    [ "Use the Yices theorem prover to prove the current goal." ]

  , prim "sbv_unint_yices"       "[String] -> ProofScript ()"
    (pureVal proveUnintYices)
    Current
    [ "Use the Yices theorem prover to prove the current goal. Leave"
    , "the given list of names as uninterpreted."
    ]

  , prim "w4_unint_yices"         "[String] -> ProofScript ()"
    (pureVal w4_unint_yices)
    Current
    [ "Prove the current goal using What4 (Yices backend). Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "offline_w4_unint_yices" "[String] -> String -> ProofScript ()"
    (pureVal do_offline_w4_unint_yices)
    Current
    [ "Write the current goal to the given file using What4 (Yices"
    , "backend) in SMT-Lib2 format. Leave the given list of names"
    , "uninterpreted."
    ]

    -- z3

  , prim "z3"                  "ProofScript ()"
    (pureVal proveZ3)
    Current
    [ "Use the Z3 theorem prover to prove the current goal." ]

  , prim "unint_z3"            "[String] -> ProofScript ()"
    (pureVal proveUnintZ3)
    Current
    [ "Use the Z3 theorem prover to prove the current goal. Leave the"
    , "given list of names uninterpreted."
    ]

  , prim "sbv_z3"              "ProofScript ()"
    (pureVal proveZ3)
    Current
    [ "Use the Z3 theorem prover to prove the current goal." ]

  , prim "sbv_unint_z3"        "[String] -> ProofScript ()"
    (pureVal proveUnintZ3)
    Current
    [ "Use the Z3 theorem prover to prove the current goal. Leave the"
    , "given list of names uninterpreted."
    ]

  , prim "w4"                  "ProofScript ()"
    (pureVal w4_z3)
    Current
    [ "Prove the current goal using What4 (Z3 backend)." ]

  , prim "w4_unint_z3"         "[String] -> ProofScript ()"
    (pureVal w4_unint_z3)
    Current
    [ "Prove the current goal using What4 (Z3 backend). Leave the given"
    , "list of names uninterpreted."
    ]

  , prim "w4_unint_z3_using" "String -> [String] -> ProofScript ()"
    (pureVal w4_unint_z3_using)
    Current
    [ "Prove the current goal using What4 (Z3 backend) using the given"
    , "Z3 tactic. Leave the given list of names uninterpreted."
    ]

  , prim "offline_w4_unint_z3"    "[String] -> String -> ProofScript ()"
    (pureVal do_offline_w4_unint_z3)
    Current
    [ "Write the current goal to the given file using What4 (Z3"
    , "backend) in SMT-Lib2 format. Leave the given list of names"
    , "uninterpreted."
    ]

    ------------------------------------------------------------
    -- And-inverter graphs (AIGs)

  , prim "load_aig"            "String -> TopLevel AIG"
    (pureVal loadAIGPrim)
    Current
    [ "Read an AIG file in binary AIGER format, yielding an AIG value." ]

  , prim "read_aig"            "String -> TopLevel Term"
    (pureVal readAIGPrim)
    Current
    [ "Read an AIG file in AIGER format and translate to a term." ]

  , prim "save_aig"            "String -> AIG -> TopLevel ()"
    (pureVal saveAIGPrim)
    Current
    [ "Write an AIG to a file in binary AIGER format." ]

  , prim "save_aig_as_cnf"     "String -> AIG -> TopLevel ()"
    (pureVal saveAIGasCNFPrim)
    Current
    [ "Write an AIG representing a boolean function to a file in DIMACS"
    , "CNF format."
    ]

  , prim "write_aig"           "String -> Term -> TopLevel ()"
    (pureVal writeAIGPrim)
    Current
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits."
    ]

  , prim "write_aig_external"  "String -> Term -> TopLevel ()"
    (pureVal doWriteAIGviaVerilog)
    Current
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits. Uses ABC to convert an"
    , "intermediate Verilog file."
    ]

  , prim "write_saig"          "String -> Term -> TopLevel ()"
    (pureVal writeSAIGPrim)
    Current
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits. The type must be of the form"
    , "'(i, s) -> (o, s)' and is interpreted as an"
    , "'[|i| + |s|] -> [|o| + |s|]' AIG with '|s|' latches."
    , ""
    , "Arguments:"
    , "   file to write : String"
    , "   function to translate to sequential AIG : Term"
    ]

  , prim "write_saig'"         "String -> Term -> Int -> TopLevel ()"
    (pureVal writeSAIGComputedPrim)
    Current
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits, '[m] -> [n]'. The int argument,"
    , "'k', must be at most 'min {m, n}', and specifies that the *last*"
    , "'k' input and output bits are joined as latches."
    , ""
    , "Arguments:"
    , "   file to write : String"
    , "   function to translate to sequential AIG : Term"
    , "   number of latches : Int"
    ]

  , prim "bitblast"            "Term -> TopLevel AIG"
    (pureVal bbPrim)
    Current
    [ "Translate a term into an AIG.  The term must be representable as"
    , "a function from a finite number of bits to a finite number of"
    , "bits."
    ]

  , prim "dsec_print"                "Term -> Term -> TopLevel ()"
    (pureVal dsecPrint)
    Current
    [ "Use ABC's 'dsec' command to compare two terms as SAIGs."
    , ""
    , "The terms must have a type as described in ':help write_saig',"
    , "i.e. of the form '(i, s) -> (o, s)'. Note that nothing is"
    , "returned: you must read the output to see what happened."
    , ""
    , "You must have an 'abc' executable on your PATH to use this"
    , "command."
    ]

  , prim "external_aig_solver" "String -> [String] -> ProofScript ()"
    (pureVal (satExternal False))
    Current
    [ "Use an external SAT solver supporting AIG to prove the current"
    , "goal. The first argument is the executable name of the solver,"
    , "and the second is the list of arguments to pass to the solver."
    , "The string '%f' anywhere in the argument list will be replaced"
    , "with the name of the temporary file holding the AIG version of"
    , "the formula."
    ]

  , prim "offline_aig"         "String -> ProofScript ()"
    (pureVal do_offline_aig)
    Current
    [ "Write the current goal to the given file in AIGER format." ]

  , prim "offline_aig_external" "String -> ProofScript ()"
    (pureVal do_offline_aig_external)
    Current
    [ "Write the current goal to the given file in AIGER format."
    , "Uses ABC and an intermediate Verilog file."
    ]

    ------------------------------------------------------------
    -- CNF

  , prim "approxmc"  "Term -> TopLevel ()"
    (pureVal approxmc)
    Current
    [ "Use the approxmc solver to approximate the number of solutions"
    , "to the CNF representation of the given Term."
    ]

  , prim "write_cnf"           "String -> Term -> TopLevel ()"
    (pureVal do_write_cnf)
    Current
    [ "Write the given term to the named file in CNF format." ]

  , prim "write_cnf_external"  "String -> Term -> TopLevel ()"
    (pureVal do_write_cnf_external)
    Current
    [ "Write the given term to the named file in CNF format." ]

  , prim "offline_cnf"         "String -> ProofScript ()"
    (pureVal do_offline_cnf)
    Current
    [ "Write the current goal to the given file in CNF format." ]

  , prim "offline_cnf_external" "String -> ProofScript ()"
    (pureVal do_offline_cnf_external)
    Current
    [ "Write the current goal to the given file in CNF format."
    , "Uses ABC and an intermediate Verilog file."
    ]

  , prim "external_cnf_solver" "String -> [String] -> ProofScript ()"
    (pureVal (satExternal True))
    Current
    [ "Use an external SAT solver supporting CNF to prove the current"
    , "goal. The first argument is the executable name of the solver,"
    , "and the second is the list of arguments to pass to the solver."
    , "The string '%f' anywhere in the argument list will be replaced"
    , "with the name of the temporary file holding the CNF version of"
    , "the formula."
    ]

    ------------------------------------------------------------
    -- Cryptol

  , prim "eval_bool"           "Term -> Bool"
    (funVal1 eval_bool)
    Current
    [ "Evaluate a Cryptol term of type Bit to either 'true' or 'false'."
    ]

  , prim "eval_int"           "Term -> Int"
    (funVal1 eval_int)
    Current
    [ "Evaluate a Cryptol term of type [n] (a bitvector) and convert to"
    , "a SAWScript 'Int'."
    ]

  , prim "eval_size"          "Type -> Int"
    (funVal1 eval_size)
    Current
    [ "Convert a Cryptol size type to a SAWScript Int." ]

  , prim "eval_list"           "Term -> [Term]"
    (funVal1 eval_list)
    Current
    [ "Evaluate a Cryptol term of type [n]a to a list of terms." ]

  , prim "list_term"           "[Term] -> Term"
    (funVal1 list_term)
    Current
    [ "Make a Cryptol term of type [n]a from a list of terms of type a."
    , "'list_term' is the inverse of 'eval_list'."
    ]

  , prim "cryptol_load"        "String -> TopLevel CryptolModule"
    (pureVal (do_cryptol_load BS.readFile))
    Current
    [ "Load the given file as a Cryptol module." ]

  , prim "cryptol_extract"     "CryptolModule -> String -> TopLevel Term"
    (pureVal cryptol_extract)
    Current
    [ "Load a single definition from a Cryptol module and translate it"
    , "into a 'Term'."
    ]

  , prim "cryptol_prims"       "() -> CryptolModule"
    (funVal1 (\ () -> cryptol_prims))
    Current
    [ "Return a Cryptol module containing extra primitive operations,"
    , "including array updates, truncate/extend, and signed"
    , "comparisons."
    ]

  , prim "cryptol_add_path"    "String -> TopLevel ()"
    (pureVal do_cryptol_add_path)
    Current
    [ "Add a directory to the Cryptol search path. The Cryptol file"
    , "loader will look in this directory when following 'import'"
    , "statements in Cryptol source files."
    ]

  , prim "cryptol_add_prim"    "String -> String -> Term -> TopLevel ()"
    (pureVal cryptol_add_prim)
    Experimental
    [ "cryptol_add_prim <mod> <name> <term> trm sets the translation of"
    , "Cryptol primitive <name> in module <mod> to <term>."
    ]

  , prim "cryptol_add_prim_type"    "String -> String -> Term -> TopLevel ()"
    (pureVal cryptol_add_prim_type)
    Experimental
    [ "cryptol_add_prim_type <mod> <name> <type> sets the translation"
    , "of Cryptol primitive type <name> in module <mod> to <type>."
    ]

    ------------------------------------------------------------
    -- Verilog

  , prim "write_verilog"       "String -> Term -> TopLevel ()"
    (scVal do_write_verilog)
    Experimental
    [ "Write out a representation of a term in Verilog format." ]

  , prim "offline_verilog"        "String -> ProofScript ()"
    (pureVal do_offline_verilog)
    Experimental
    [ "Write the current goal to the given file in Verilog format." ]

    ------------------------------------------------------------
    -- Yosys

  , prim "yosys_import"  "String -> TopLevel Term"
    (pureVal do_yosys_import)
    Experimental
    [ "Produces a Term given the path to a JSON file produced by the"
    , "Yosys 'write_json' command. The resulting term is a Cryptol"
    , "record, where each field corresponds to one HDL module exported"
    , "by Yosys. Each HDL module is in turn represented by a function"
    , "from a record of input port values to a record of output port"
    , "values."
    ]

  , prim "yosys_verify"  ("Term -> [Term] -> Term -> [YosysTheorem] -> " <>
                          "ProofScript () -> TopLevel YosysTheorem")
    (pureVal yosys_verify)
    Experimental
    [ "Proves equality between a combinational HDL module and a"
    , "specification."
    , ""
    , "The first parameter is the HDL module - given a record m from"
    , "yosys_import, this will typically look something like '{{ m.foo"
    , "}}'. The second parameter is a list of preconditions for the"
    , "equality. The third parameter is the specification, a term of"
    , "the same type as the HDL module, which will typically be some"
    , "Cryptol function or another HDL module.  The fourth parameter is"
    , "a list of overrides, which witness the results of previous"
    , "yosys_verify proofs. These overrides can be used to simplify"
    , "terms by replacing use sites of submodules with their"
    , "specifications."
    , ""
    , "Note that terms derived from HDL modules are first class, and"
    , "are not restricted to yosys_verify: they may also be used with"
    , "SAW's typical Term infrastructure like 'sat', 'prove_print',"
    , "term rewriting, etc. yosys_verify simply provides a convenient"
    , "and familiar interface, similar to llvm_verify or jvm_verify."
    ]

  , prim "yosys_import_sequential"  ("String -> String -> " <>
                                     "TopLevel YosysSequential")
    (pureVal do_yosys_import_sequential)
    Experimental
    -- XXX isn't the remark about $dff not true any more?
    [ "Imports a sequential HDL module."
    , ""
    , "The first parameter is the module name; the second is the path"
    , "to the Yosys JSON file. The resulting value is an opaque"
    , "representation of the sequential circuit that can be extracted"
    , "to a Term or sent to solvers in various ways."
    , ""
    , "SAW expects the sequential module to exist entirely within a"
    , "single Yosys module - the Yosys 'flatten' command will collapse"
    , "the module hierarchy into a single module. The only supported"
    , "sequential element is the basic $dff cell. Memory cells and more"
    , "complex flip-flops can be translated into $dff using the"
    , "'memory' and 'dffunmap' Yosys commands."
    ]

  , prim "yosys_extract_sequential"  "YosysSequential -> Int -> TopLevel Term"
    (pureVal yosys_extract_sequential)
    Experimental
    [ "Extracts a term from the given sequential module with the state"
    , "eliminated by iterating the term over the given concrete number"
    , "of cycles."
    , ""
    , "The resulting term has no state field in the inputs or outputs,"
    , "and each input and output field is replaced with an array of"
    , "that field's type (array length being the number of cycles)."
    , "This term can be used like a normal SAW term -- it may be "
    , "embedded in Cryptol expressions, used in 'prove' and 'sat',"
    , "etc."
    ]

  , prim "yosys_extract_sequential_with_state"
    "YosysSequential -> Int -> TopLevel Term"
    (pureVal yosys_extract_sequential_with_state)
    Experimental
    [ "Like yosys_extract_sequential, but the resulting term has an"
    , "additional parameter to specify the initial state."
    ]

  , prim "yosys_extract_sequential_raw"  "YosysSequential -> TopLevel Term"
    (pureVal yosys_extract_sequential_raw)
    Experimental
    [ "Extracts a term from the given sequential module."
    , "This term has explicit fields for the state of the circuit in"
    , "the input and output record types."
    ]

  , prim "yosys_verify_sequential_offline_sally"
    "YosysSequential -> String -> Term -> [String] -> TopLevel ()"
    (pureVal do_yosys_verify_sequential_sally)
    Experimental
    [ "Export a query over the given sequential module to an input file"
    , "for the Sally model checker."
    , ""
    , " - The first parameter is the sequential module."
    , " - The second parameter is the path to write the resulting Sally"
    , "   input."
    , " - The third parameter is the query, which should be a boolean"
    , "   function of three parameters: an 8-bit cycle counter, a"
    , "   record of 'fixed' inputs, and a record of circuit outputs."
    , " - The fourth parameter is a list of strings specifying certain"
    , "   circuit inputs as fixed - these inputs are assumed to remain"
    , "   unchanged across cycles, and are therefore accesible from the"
    , "   query function."
    ]

    ------------------------------------------------------------
    -- Rocq / Coq export

  , prim "write_coq_term" ("String -> [(String, String)] -> [String] -> " <>
                           "String -> Term -> TopLevel ()")
    (pureVal do_write_coq_term)
    Experimental
    [ "Write out a representation of a term in Gallina syntax for Coq."
    , " - The first argument is the name to use in a Definition."
    , " - The second argument is a list of pairs of notation"
    , "   substitutions: the operator on the left will be replaced with"
    , "   the identifier on the right, as we do not support notations"
    , "   on the Coq side."
    , " - The third argument is a list of identifiers to skip"
    , "   translating."
    , " - The fourth argument is the name of the file to output into;"
    , "   use an empty string to output to standard output."
    , " - The fifth argument is the term to export."
    ]

  , prim "write_coq_cryptol_module" ("String -> String -> " <>
                                     "[(String, String)] -> [String] -> " <>
                                     "TopLevel ()")
    (pureVal do_write_coq_cryptol_module)
    Experimental
    [ "Write out a representation of a Cryptol module in Gallina syntax"
    , "for Coq."
    , " - The first argument is the file containing the module to"
    , "   export."
    , " - The second argument is the name of the file to output into;"
    , "   use an empty string to output to standard output."
    , " - The third argument is a list of pairs of notation"
    , "   substitutions: the operator on the left will be replaced with"
    , "   the identifier on the right, as we do not support notations"
    , "   on the Coq side."
    , " - The fourth argument is a list of identifiers to skip"
    , "   translating."
    ]

  , prim "write_coq_sawcore_prelude" ("String -> [(String, String)] -> " <>
                                      "[String] -> TopLevel ()")
    (pureVal do_write_coq_sawcore_prelude)
    Experimental
    [ "Write out a representation of the SAWCore prelude in Gallina"
    , "syntax for Coq."
    , " - The first argument is the name of the file to output into;"
    , "   use an empty string to output to standard output."
    , " - The second argument is a list of pairs of notation"
    , "   substitutions: the operator on the left will be replaced"
    , "   with the identifier on the right, as we do not support"
    , "   notations on the Coq side."
    , " - The third argument is a list of identifiers to skip"
    , "   translating."
    ]

  , prim "write_coq_cryptol_primitives_for_sawcore"
    "String -> [(String, String)] -> [String] -> TopLevel ()"
    (pureVal do_write_coq_cryptol_primitives_for_sawcore)
    Experimental
    [ "Write out a representation of cryptol-saw-core's Cryptol.sawcore"
    , "in Gallina syntax for Coq."
    , " - The first argument is the name of the output file for"
    , "   translating Cryptol.sawcore. Use an empty string to output to"
    , "   standard output."
    , " - The second argument is a list of pairs of notation"
    , "   substitutions: the operator on the left will be replaced"
    , "   with the identifier on the right, as we do not support"
    , "   notations on the Coq side."
    , " - The third argument is a list of identifiers to skip"
    , "   translating."
    ]

  , prim "offline_coq" "String -> ProofScript ()"
    (pureVal do_offline_coq)
    Experimental
    [ "Write out a representation of the current goal in Gallina syntax"
    , "(for Coq). The argument is a prefix to use for file names."
    ]

    ------------------------------------------------------------
    -- Additional output forms

  , prim "write_smtlib2"       "String -> Term -> TopLevel ()"
    (pureVal do_write_smtlib2)
    Current
    [ "Write the given term to the named file in SMT-Lib version 2"
    , "format."
    ]

  , prim "write_smtlib2_w4"    "String -> Term -> TopLevel ()"
    (pureVal do_write_smtlib2_w4)
    Current
    [ "Write the given term to the named file in SMT-Lib version 2"
    , "format, using the What4 backend instead of the SBV backend."
    ]

  , prim "offline_smtlib2"     "String -> ProofScript ()"
    (pureVal do_offline_smtlib2)
    Current
    [ "Write the current goal to the given file in SMT-Lib2 format." ]

  , prim "w4_offline_smtlib2"  "String -> ProofScript ()"
    (pureVal do_w4_offline_smtlib2)
    Current
    [ "Write the current goal to the given file in SMT-Lib2 format." ]

  , prim "offline_unint_smtlib2"  "[String] -> String -> ProofScript ()"
    (pureVal do_offline_unint_smtlib2)
    Current
    [ "Write the current goal to the given file in SMT-Lib2 format,"
    , "leaving the listed functions uninterpreted."
    ]

  , prim "codegen"         "String -> [String] -> String -> Term -> TopLevel ()"
    (scVal codegenSBV)
    Current
    [ "Generate straight-line C code for the given term using SBV."
    , ""
    , " - First argument is a directory name (\"\" for stdout) for"
    , "   the generated files."
    , " - Second argument is the list of function names to leave"
    , "   uninterpreted."
    , " - Third argument is the C function name."
    , " - Fourth argument is the term to generate code for. It must be"
    , "   a first-order function whose arguments and result are all of"
    , "   type Bit, [8], [16], [32], or [64]."
    ]

  ------------------------------------------------------------
  -- Crucible ghost state

  , prim "declare_ghost_state"
    "String -> TopLevel Ghost"
    (pureVal declare_ghost_state)
    Current
    [ "Allocates a unique ghost variable." ]

  , prim "llvm_declare_ghost_state"
    "String -> TopLevel Ghost"
    (pureVal declare_ghost_state)
    Current
    [ "Legacy alternative name for 'declare_ghost_state'." ]
  , prim "crucible_declare_ghost_state"
    "String -> TopLevel Ghost"
    (pureVal declare_ghost_state)
    Current
    [ "Legacy alternative name for 'declare_ghost_state'." ]

  , prim "llvm_ghost_value"
    "Ghost -> Term -> LLVMSetup ()"
    (pureVal llvm_ghost_value)
    Current
    [ "Specifies the value of a ghost variable. This can be used"
    , "in the pre- and post- conditions of a setup block."
    ]
  , prim "crucible_ghost_value"
    "Ghost -> Term -> LLVMSetup ()"
    (pureVal llvm_ghost_value)
    Current
    [ "Legacy alternative name for 'llvm_ghost_value'."]

  , prim "jvm_ghost_value"
    "Ghost -> Term -> JVMSetup ()"
    (pureVal jvm_ghost_value)
    Current
    [ "Specifies the value of a ghost variable. This can be used"
    , "in the pre- and post- conditions of a setup block."
    ]

  , prim "mir_ghost_value"
    "Ghost -> Term -> MIRSetup ()"
    (pureVal mir_ghost_value)
    Experimental
    [ "Specifies the value of a ghost variable. This can be used"
    , "in the pre- and post- conditions of a setup block."
    ]

    ------------------------------------------------------------
    -- LLVM types

  , prim "llvm_type"           "String -> LLVMType"
    (funVal1 llvm_type)
    Current
    [ "Parse the given string as LLVM type syntax." ]

  , prim "llvm_int"            "Int -> LLVMType"
    (pureVal llvm_int)
    Current
    [ "The type of LLVM integers, of the given bit width." ]

  , prim "llvm_float"          "LLVMType"
    (pureVal llvm_float)
    Current
    [ "The type of single-precision floating point numbers in LLVM." ]

  , prim "llvm_double"         "LLVMType"
    (pureVal llvm_double)
    Current
    [ "The type of double-precision floating point numbers in LLVM." ]

  , prim "llvm_array"          "Int -> LLVMType -> LLVMType"
    (pureVal llvm_array)
    Current
    [ "The type of LLVM arrays with the given number of elements of the"
    , "given type."
    ]

  , prim "llvm_alias"          "String -> LLVMType"
    (pureVal llvm_alias)
    Current
    [ "The type of an LLVM alias for the given name. This is often used"
    , "to alias a struct type."
    ]

  , prim "llvm_struct"         "String -> LLVMType"
    (pureVal llvm_alias)
    WarnDeprecated
    [ "Legacy alternative name for 'llvm_alias'."
    , "If you are trying to create a struct type from its contents, you"
    , "want llvm_struct_type."
    , ""
    , "Expected to be hidden by default in SAW 1.5."
    ]

  , prim "llvm_struct_type"
    "[LLVMType] -> LLVMType"
    (pureVal llvm_struct_type)
    Current
    [ "The type of an LLVM struct with elements of the given types." ]

  , prim "llvm_packed_struct_type"
    "[LLVMType] -> LLVMType"
    (pureVal llvm_packed_struct_type)
    Current
    [ "The type of a packed LLVM struct with elements of the given"
    , "types."
    ]

  , prim "llvm_pointer"        "LLVMType -> LLVMType"
    (pureVal llvm_pointer)
    Current
    [ "The type of an LLVM pointer that points to the given type." ]

    ------------------------------------------------------------
    -- LLVM values and terms

  , prim "llvm_null"
    "LLVMValue"
    (pureVal CIR.anySetupNull)
    Current
    [ "An LLVMValue representing a null pointer value." ]
  , prim "crucible_null"
    "LLVMValue"
    (pureVal CIR.anySetupNull)
    Current
    [ "Legacy alternative name for 'llvm_null'." ]

  , prim "llvm_term"
    "Term -> LLVMValue"
    (pureVal CIR.anySetupTerm)
    Current
    [ "Construct an 'LLVMValue' from a 'Term'." ]
  , prim "crucible_term"
    "Term -> LLVMValue"
    (pureVal CIR.anySetupTerm)
    Current
    [ "Legacy alternative name for 'llvm_term'." ]

  , prim "llvm_array_value"
    "[LLVMValue] -> LLVMValue"
    (pureVal CIR.anySetupArray)
    Current
    [ "Create an LLVMValue representing an array, with the given list"
    , "of values as elements. The list must be non-empty."
    ]
  , prim "crucible_array"
    "[LLVMValue] -> LLVMValue"
    (pureVal CIR.anySetupArray)
    Current
    [ "Legacy alternative name for 'llvm_array_value'." ]

  , prim "llvm_elem"
    "LLVMValue -> Int -> LLVMValue"
    (pureVal CIR.anySetupElem)
    Current
    [ "Turn an LLVMValue representing a struct or array pointer into"
    , "a pointer to an element of the struct or array by field index."
    ]
  , prim "crucible_elem"
    "LLVMValue -> Int -> LLVMValue"
    (pureVal CIR.anySetupElem)
    Current
    [ "Legacy alternative name for 'llvm_elem'." ]

  , prim "llvm_struct_value"
    "[LLVMValue] -> LLVMValue"
    (pureVal (CIR.anySetupStruct False))
    Current
    [ "Create an LLVMValue representing a struct, with the given list"
    , "of values as elements."
    ]
  , prim "crucible_struct"
    "[LLVMValue] -> LLVMValue"
    (pureVal (CIR.anySetupStruct False))
    Current
    [ "Legacy alternative name for 'llvm_struct_value'." ]

  , prim "llvm_packed_struct_value"
    "[LLVMValue] -> LLVMValue"
    (pureVal (CIR.anySetupStruct True))
    Current
    [ "Create an LLVMValue representing a packed struct, with the given"
    , "list of values as elements."
    ]
  , prim "crucible_packed_struct"
    "[LLVMValue] -> LLVMValue"
    (pureVal (CIR.anySetupStruct True))
    Current
    [ "Legacy alternative name for 'llvm_packed_struct_value'." ]

  , prim "llvm_field"
    "LLVMValue -> String -> LLVMValue"
    (pureVal CIR.anySetupField)
    Current
    [ "Turn an LLVMValue representing a struct pointer into a pointer"
    , "to an element of the struct by field name. Requires debug"
    , "to resolve struct field names."
    ]
  , prim "crucible_field"
    "LLVMValue -> String -> LLVMValue"
    (pureVal CIR.anySetupField)
    Current
    [ "Legacy alternative name for 'llvm_field'." ]

  , prim "llvm_union"
    "LLVMValue -> String -> LLVMValue"
    (pureVal CIR.anySetupUnion)
    Current
    [ "Turn an LLVMValue representing a union pointer into a pointer to"
    , "one of the branches of the union by field name. Requires debug"
    , "symbols to resolve union field names."
    ]

  , prim "llvm_global"
    "String -> LLVMValue"
    (pureVal CIR.anySetupGlobal)
    Current
    [ "Return an LLVMValue representing a pointer to the named global."
    , "The String may be either the name of a global value or a"
    , "function name."
    ]
  , prim "crucible_global"
    "String -> LLVMValue"
    (pureVal CIR.anySetupGlobal)
    Current
    [ "Legacy alternative name for 'llvm_global'." ]

  , prim "llvm_global_initializer"
    "String -> LLVMValue"
    (pureVal CIR.anySetupGlobalInitializer)
    Current
    [ "Return an LLVMValue representing the value of the initializer of"
    , "a named global. The String should be the name of a global value."
    ]
  , prim "crucible_global_initializer"
    "String -> LLVMValue"
    (pureVal CIR.anySetupGlobalInitializer)
    Current
    [ "Legacy alternative name for 'llvm_global_initializer'." ]

  , prim "llvm_cast_pointer" "LLVMValue -> LLVMType -> LLVMValue"
    (pureVal llvm_cast_pointer)
    Current
    [ "Cast the type of the given LLVM value, which must be a pointer."
    , "The resulting value will be a pointer to the same location,"
    , "treated as a pointer to the provided type."
    ]

  , prim "crucible_setup_val_to_term"
    " LLVMValue -> TopLevel Term"
    (pureVal crucible_setup_val_to_typed_term)
    HideDeprecated
    [ "Convert from a setup value to a typed term. This can only be"
    , "done for a subset of setup values. Fails if a setup value is a"
    , "global, variable, or null."
    , ""
    , "Expected to be removed in SAW 1.5."
    ]

    ------------------------------------------------------------
    -- LLVM fresh values

  , prim "llvm_fresh_var" "String -> LLVMType -> LLVMSetup Term"
    (pureVal llvm_fresh_var)
    Current
    [ "Create a fresh symbolic variable for use within an LLVM"
    , "specification. The name is used only for pretty-printing."
    ]
  , prim "crucible_fresh_var" "String -> LLVMType -> LLVMSetup Term"
    (pureVal llvm_fresh_var)
    Current
    [ "Legacy alternative name for 'llvm_fresh_var'." ]

  , prim "llvm_fresh_cryptol_var" "String -> Type -> LLVMSetup Term"
    (pureVal llvm_fresh_cryptol_var)
    Experimental
    [ "Create a fresh symbolic variable of the given Cryptol type for"
    , "use within a Crucible specification. The given name is used only"
    , "for pretty-printing. Unlike 'llvm_fresh_var', this can be used"
    , "when there isn't an appropriate LLVM type, such as for the"
    , "Cryptol Array type."
    ]
  , prim "crucible_fresh_cryptol_var" "String -> Type -> LLVMSetup Term"
    (pureVal llvm_fresh_cryptol_var)
    Experimental
    [ "Legacy alternative name for 'llvm_fresh_cryptol_var'." ]

  , prim "llvm_fresh_pointer" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_fresh_pointer)
    Current
    [ "Create a fresh pointer value for use in an LLVM specification."
    , "This works like 'llvm_alloc' except that the pointer is not"
    , "required to point to allocated memory."
    ]
  , prim "crucible_fresh_pointer" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_fresh_pointer)
    Current
    [ "Legacy alternative name for 'llvm_fresh_pointer'." ]

  , prim "llvm_fresh_expanded_val" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_fresh_expanded_val)
    Current
    [ "Create a compound type entirely populated with fresh symbolic"
    , "variables. Equivalent to allocating a new struct or array of the"
    , "given type and explicitly setting each field or element to"
    , "contain a fresh symbolic variable."
    ]
  , prim "crucible_fresh_expanded_val" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_fresh_expanded_val)
    Current
    [ "Legacy alternative name for 'llvm_fresh_expanded_val'." ]

    ------------------------------------------------------------
    -- LLVM allocation

  , prim "llvm_alloc" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc)
    Current
    [ "Declare that an object of the given type should be allocated in"
    , "an LLVM specification. Before 'llvm_execute_func', this states"
    , "that the function expects the object to be allocated before it"
    , "runs. After 'llvm_execute_func', it states that the function"
    , " being verified is expected to perform the allocation."
    ]
  , prim "crucible_alloc" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc)
    Current
    [ "Legacy alternative name for 'llvm_alloc'." ]

  , prim "llvm_alloc_aligned" "Int -> LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc_aligned)
    Current
    [ "Declare that a memory region of the given type should be"
    , "allocated in an LLVM specification, and also specify that the"
    , "start of the region should be aligned to a multiple of the"
    , "specified number of bytes (which must be a power of 2)."
    ]
  , prim "crucible_alloc_aligned" "Int -> LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc_aligned)
    Current
    [ "Legacy alternative name for 'llvm_alloc_aligned'." ]

  , prim "llvm_alloc_readonly" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc_readonly)
    Current
    [ "Declare that a read-only memory region of the given type should"
    , "be allocated in an LLVM specification. The function must not"
    , "attempt to write to this memory region. Unlike 'llvm_alloc',"
    , "regions allocated with 'llvm_alloc_readonly' are allowed to"
    , "alias other read-only regions."
    ]
  , prim "crucible_alloc_readonly" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc_readonly)
    Current
    [ "Legacy alternative name for 'llvm_alloc_readonly'." ]

  , prim "llvm_alloc_readonly_aligned" "Int -> LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc_readonly_aligned)
    Current
    [ "Declare that a read-only memory region of the given type should"
    , "be allocated in an LLVM specification, and also specify that the"
    , "start of the region should be aligned to a multiple of the"
    , "specified number of bytes (which must be a power of 2). The"
    , "function must not attempt to write to this memory region. Unlike"
    , "'llvm_alloc' and 'llvm_alloc_aligned', regions allocated with"
    , "'llvm_alloc_readonly_aligned' are allowed to alias other"
    , "read-only regions."
    ]
  , prim "crucible_alloc_readonly_aligned" ("Int -> LLVMType -> " <>
                                            "LLVMSetup LLVMValue")
    (pureVal llvm_alloc_readonly_aligned)
    Current
    [ "Legacy alternative name for 'llvm_alloc_readonly_aligned'." ]

  , prim "llvm_alloc_with_size" "Int -> LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc_with_size)
    Experimental
    [ "Like 'llvm_alloc', but with a user-specified size (given in"
    , "bytes). The specified size must be greater than the size of the"
    , "LLVM type."
    ]

  , prim "crucible_alloc_with_size" "Int -> LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc_with_size)
    Experimental
    [ "Legacy alternative name for 'llvm_alloc_with_size'." ]

  , prim "llvm_alloc_sym_init" "LLVMType -> LLVMSetup LLVMValue"
    (pureVal llvm_alloc_sym_init)
    Experimental
    [ "Like 'llvm_alloc', but assume that the allocation is initialized"
    , "with symbolic bytes."
    ]

  , prim "llvm_symbolic_alloc" "Bool -> Int -> Term -> LLVMSetup LLVMValue"
    (pureVal llvm_symbolic_alloc)
    Current
    [ "Like 'llvm_alloc', but with a (symbolic) size instead of an LLVM"
    , "type. The first argument specifies whether the allocation is"
    , "read-only. The second argument specifies the alignment in bytes"
    , "(which must be a power of 2). The third argument specifies the"
    , "size in bytes."
    ]
  , prim "crucible_symbolic_alloc" "Bool -> Int -> Term -> LLVMSetup LLVMValue"
    (pureVal llvm_symbolic_alloc)
    Current
    [ "Legacy alternative name for 'llvm_symbolic_alloc'." ]

  , prim "llvm_alloc_global" "String -> LLVMSetup ()"
    (pureVal llvm_alloc_global)
    Current
    [ "Declare that memory for the named global should be allocated in"
    , "an LLVM specification. This is done implicitly for immutable"
    , "globals. A pointer to the allocated memory may be obtained using"
    , "'llvm_global'."
    ]
  , prim "crucible_alloc_global" "String -> LLVMSetup ()"
    (pureVal llvm_alloc_global)
    Current
    [ "Legacy alternative name for 'llvm_alloc_global'." ]

    ------------------------------------------------------------
    -- LLVM assertions

  , prim "llvm_precond" "Term -> LLVMSetup ()"
    (pureVal llvm_precond)
    Current
    [ "State that the given predicate is a pre-condition of the"
    , "execution of the function being verified."
    ]
  , prim "crucible_precond" "Term -> LLVMSetup ()"
    (pureVal llvm_precond)
    Current
    [ "Legacy alternative name for 'llvm_precond'." ]

  , prim "llvm_postcond" "Term -> LLVMSetup ()"
    (pureVal llvm_postcond)
    Current
    [ "State that the given predicate is a post-condition of the"
    , "execution of the function being verified."
    ]
  , prim "crucible_postcond" "Term -> LLVMSetup ()"
    (pureVal llvm_postcond)
    Current
    [ "Legacy alternative name for 'llvm_postcond'." ]

  , prim "llvm_assert" "Term -> LLVMSetup ()"
    (pureVal llvm_assert)
    Current
    [ "State that the given predicate must hold. Acts as 'llvm_precond'"
    , "or 'llvm_postcond' depending on where it appears, that is,"
    , "before or after 'llvm_execute_func'."
    ]

  , prim "llvm_equal" "LLVMValue -> LLVMValue -> LLVMSetup ()"
    (pureVal llvm_equal)
    Current
    [ "State that two LLVM values should be equal. Can be used as"
    , "either a pre-condition or a post-condition. It is semantically"
    , "equivalent to an 'llvm_precond' or 'llvm_postcond' statement"
    , "that is an equality, but potentially more efficient."
    ]
  , prim "crucible_equal" "LLVMValue -> LLVMValue -> LLVMSetup ()"
    (pureVal llvm_equal)
    Current
    [ "Legacy alternative name for 'llvm_equal'." ]

  , prim "llvm_points_to" "LLVMValue -> LLVMValue -> LLVMSetup ()"
    (pureVal (llvm_points_to True))
    Current
    [ "Declare that the memory location indicated by the given pointer"
    , "(first argument) contains the given value (second argument)."
    , ""
    , "In the pre-state section (before 'llvm_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'llvm_execute_func'), this"
    , "specifies an assertion about the final memory state after"
    , "running the function."
    ]
    , prim "crucible_points_to" "LLVMValue -> LLVMValue -> LLVMSetup ()"
    (pureVal (llvm_points_to True))
    Current
    [ "Legacy alternative name for 'llvm_points_to'." ]

  , prim "llvm_conditional_points_to" ("Term -> LLVMValue -> LLVMValue -> " <>
                                       "LLVMSetup ()")
    (pureVal (llvm_conditional_points_to True))
    Current
    [ "Declare that the memory location indicated by a pointer (second"
    , "argument) contains a  value (third argument), but only when a"
    , "condition (first argument) holds."
    , ""
    , "In the pre-state section (before 'llvm_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'llvm_execute_func'), this"
    , "specifies an assertion about the final memory state after"
    , "running the function."
    ]
  , prim "crucible_conditional_points_to" ("Term -> LLVMValue -> " <>
                                           "LLVMValue -> LLVMSetup ()")
    (pureVal (llvm_conditional_points_to True))
    Current
    [ "Legacy alternative name for 'llvm_conditional_points_to'." ]

  , prim "llvm_points_to_at_type" ("LLVMValue -> LLVMType -> LLVMValue -> " <>
                                   "LLVMSetup ()")
    (pureVal llvm_points_to_at_type)
    Current
    [ "A variant of 'llvm_points_to' that casts the pointer to another"
    , "type. This may be useful, for example, when reading or writing a"
    , "prefix of a larger array."
    ]

  , prim "llvm_conditional_points_to_at_type" ("Term -> LLVMValue -> " <>
                                               "LLVMType -> LLVMValue -> " <>
                                               "LLVMSetup ()")
    (pureVal llvm_conditional_points_to_at_type)
    Current
    [ "A variant of 'llvm_conditional_points_to' that casts the pointer"
    , "to another type. This may be useful, for example, when reading"
    , "or writing a prefix of a larger array."
    ]

  , prim "llvm_points_to_untyped" "LLVMValue -> LLVMValue -> LLVMSetup ()"
    (pureVal (llvm_points_to False))
    Current
    [ "A variant of 'llvm_points_to' that does not check for"
    , "compatibility between the pointer type and the value type. This"
    , "may be useful, for example, when reading or writing a prefix of"
    , "a larger array."
    ]
  , prim "crucible_points_to_untyped" "LLVMValue -> LLVMValue -> LLVMSetup ()"
    (pureVal (llvm_points_to False))
    Current
    [ "Legacy alternative name for 'llvm_points_to'." ]

  , prim "llvm_conditional_points_to_untyped" ("Term -> LLVMValue -> " <>
                                               "LLVMValue -> LLVMSetup ()")
    (pureVal (llvm_conditional_points_to False))
    Current
    [ "A variant of 'llvm_conditional_points_to' that does not check"
    , "for compatibility between the pointer type and the value type."
    , "This may, for example, be useful when reading or writing a"
    , "prefix of larger array."
    ]
  , prim "crucible_conditional_points_to_untyped" ("Term -> LLVMValue -> " <>
                                                   "LLVMValue -> LLVMSetup ()")
    (pureVal (llvm_conditional_points_to False))
    Current
    [ "Legacy alternative name for 'llvm_conditional_points_to'." ]

  , prim "llvm_points_to_array_prefix" ("LLVMValue -> Term -> Term -> " <>
                                        "LLVMSetup ()")
    (pureVal llvm_points_to_array_prefix)
    Experimental
    [ "Declare that the memory location indicated by a pointer (first"
    , "argument) contains the prefix of an array (second argument)"
    , "whose size is given by the third argument."
    , ""
    , "In the pre-state section (before 'llvm_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'llvm_execute_func'), this"
    , "specifies an assertion about the final memory state after"
    , "running the function."
    ]
  , prim "crucible_points_to_array_prefix" ("LLVMValue -> Term -> Term -> " <>
                                            "LLVMSetup ()")
    (pureVal llvm_points_to_array_prefix)
    Experimental
    [ "Legacy alternative name for 'llvm_points_to_array_prefix'." ]

  , prim "llvm_points_to_bitfield" ("LLVMValue -> String -> LLVMValue -> " <>
                                    "LLVMSetup ()")
    (pureVal (llvm_points_to_bitfield))
    Experimental
    [ "A variant of 'llvm_points_to' that is meant to be used on struct"
    , "fields that reside within bitfields. Use"
    , "   llvm_points_to_bitfield <ptr> <field> <struct-val>"
    , "instead of"
    , "   llvm_points_to (llvm_field <ptr> <field>) <struct-val>,"
    , "as the latter will not behave as one would expect for technical"
    , "reasons."
    , ""
    , "This command should only be used in combination with"
    , "'enable_lax_loads_and_stores', as the memory model relaxations"
    , "controlled by that option are crucial to how"
    , "'llvm_points_to_bitfield' operates."
    ]

  , prim "llvm_execute_func" "[LLVMValue] -> LLVMSetup ()"
    (pureVal llvm_execute_func)
    Current
    [ "Specify the given list of values as the arguments of the"
    , "function."
    ,  ""
    , "The 'llvm_execute_func' command also serves to separate the"
    , "pre-state section of the spec (before it) from the post-state"
    , "section (after it). The effects of some LLVMSetup commands"
    , "depend on whether they occur in the pre-state or post-state"
    , "section."
    , ""
    , "Every LLVM specification must use this command to call its"
    , "function."
    ]
  , prim "crucible_execute_func" "[LLVMValue] -> LLVMSetup ()"
    (pureVal llvm_execute_func)
    Current
    [ "Legacy alternative name for 'llvm_execute_func'." ]

  , prim "llvm_return" "LLVMValue -> LLVMSetup ()"
    (pureVal llvm_return)
    Current
    [ "Specify the given value as the return value of the function. An"
    , "llvm_return statement is required if and only if the function"
    , "has a non-void return type."
    ]
  , prim "crucible_return" "LLVMValue -> LLVMSetup ()"
    (pureVal llvm_return)
    Current
    [ "Legacy alternative name for 'llvm_return'." ]

    ------------------------------------------------------------
    -- LLVM modules

  , prim "llvm_load_module"    "String -> TopLevel LLVMModule"
    (pureVal do_llvm_load_module)
    Current
    [ "Load an LLVM bitcode file and return a handle to it." ]

  , prim "llvm_sizeof"         "LLVMModule -> LLVMType -> Int"
    (funVal2 llvm_sizeof)
    Current
    [ "In the context of the given LLVM module, compute the size of the"
    , "given LLVM type in bytes. The module determines details of"
    , "struct layout and the meaning of type aliases."
    ]

  , prim "llvm_cfg"     "LLVMModule -> String -> TopLevel CFG"
    (pureVal llvm_cfg)
    Current
    [ "Load a function from the given LLVM module into a Crucible CFG." ]

  , prim "show_cfg"          "CFG -> String"
    (pureVal show_cfg)
    Current
    [ "Pretty-print a Crucible control-flow graph." ]

    ------------------------------------------------------------
    -- LLVM verification

  , prim "llvm_ffi_setup"  "Term -> LLVMSetup ()"
    (pureVal llvm_ffi_setup)
    Experimental
    [ "Generate a LLVMSetup spec that can be used to verify that the"
    , "given monomorphic Cryptol term, consisting of a Cryptol foreign"
    , "function fully applied to any type arguments, has a correct"
    , "foreign (LLVM) implementation with respect to its Cryptol"
    , "implementation."
    ]

  , prim "llvm_extract"  "LLVMModule -> String -> TopLevel Term"
    (pureVal llvm_extract)
    Current
    [ "Translate an LLVM function directly to a Term. The parameters of"
    , "the Term will be the parameters of the LLVM function, and the"
    , "return value will be the return value of the function. Only"
    , "functions with scalar argument and return types are currently"
    , "allowed. Use 'llvm_compositional_extract' for more flexibility."
    ]
  , prim "crucible_llvm_extract"  "LLVMModule -> String -> TopLevel Term"
    (pureVal llvm_extract)
    Current
    [ "Legacy alternative name for 'llvm_extract'." ]

  , prim "llvm_compositional_extract"
    ("LLVMModule -> String -> String -> [LLVMSpec] -> Bool -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal llvm_compositional_extract)
    Experimental
    [ "Translate an LLVM function directly to a Term. The parameters of"
    , "the Term are the input parameters of the LLVM function: the"
    , "parameters passed by value (in the order given by"
    , "'llvm_execute_func'), then the parameters passed by reference"
    , "(in the order given by 'llvm_points_to'). The Term is the tuple"
    , "consisting of the output parameters of the LLVM function: the"
    , "return parameter, then the parameters passed by reference (in"
    , "the order given by 'llvm_points_to')."
    , ""
    , "The arguments are:"
    , "   1. <mod>: The LLVM module containing the function to extract."
    , "   2. <fn>: The name of the function to extract."
    , "   3. <term-name>: The name of the Term to generate."
    , "   4. <ovs>: A list of overrides to use in the proof that the"
    , "      extracted function satisifies <spec>."
    , "   5. <check-path-sat>: Whether to perform path satisfiability"
    , "       checks."
    , "   6. <spec>: SAW specification for the extracted function."
    , "   7. <proof>: Proof script to use when verifying that the"
    , "      extracted function satisfies <spec>."
    , ""
    , "For more flexibility, see 'llvm_verify'."
    ]
  , prim "crucible_llvm_compositional_extract"
    ("LLVMModule -> String -> String -> [LLVMSpec] -> Bool -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal llvm_compositional_extract)
    Experimental
    [ "Legacy alternative name for 'llvm_compositional_extract'." ]

  , prim "llvm_verify"
    ("LLVMModule -> String -> [LLVMSpec] -> Bool -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal llvm_verify)
    Current
    [ "Verify the LLVM function named by the second parameter in the"
    , "module specified by the first. The third parameter lists the"
    , "LLVMSpec values returned by previous calls to use as overrides."
    , "The fourth (Bool) parameter enables or disables path "
    , "satisfiability checking. The fifth describes how to set up the"
    , "symbolic execution engine before verification. And the last"
    , "gives the script to use to prove the validity of the resulting"
    , "verification conditions."
    ]
  , prim "crucible_llvm_verify"
    ("LLVMModule -> String -> [LLVMSpec] -> Bool -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal llvm_verify)
    Current
    [ "Legacy alternative name for 'llvm_verify'." ]

  , prim "llvm_refine_spec"
    ("LLVMModule -> String -> [LLVMSpec] -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal llvm_refine_spec)
    Experimental
    [ "Verify that a given specification for a function is a refinement"
    , "of one or more specifications already proved for a function."
    , "This can be useful for situations where it is advantageous to"
    , "logically restate the specification in some way, or where a more"
    , "general specification can be constructed from a collection of"
    , "individual special cases."
    ]

  , prim "llvm_unsafe_assume_spec"
    "LLVMModule -> String -> LLVMSetup () -> TopLevel LLVMSpec"
    (pureVal llvm_unsafe_assume_spec)
    Current
    [ "Return an LLVMSpec corresponding to an LLVMSetup block, as would"
    , "be returned by 'crucible_llvm_verify' but without performing"
    , "any verification."
    ]
  , prim "crucible_llvm_unsafe_assume_spec"
    "LLVMModule -> String -> LLVMSetup () -> TopLevel LLVMSpec"
    (pureVal llvm_unsafe_assume_spec)
    Current
    [ "Legacy alternative name for 'llvm_unsafe_assume_spec'." ]

  , prim "llvm_array_size_profile"
    ("LLVMModule -> String -> [LLVMSpec] -> " <>
     "LLVMSetup () -> TopLevel [(String, [FunctionProfile])]")
    (pureVal $ llvm_array_size_profile assumeUnsat)
    Experimental
    [ "Symbolically execute the function named by the second parameter"
    , "in the module specified by the first. The fourth parameter may"
    , "be used to specify arguments. Returns profiles specifying the"
    , "sizes of buffers referred to by pointer arguments for the"
    , "function and all other functions it calls (recursively), to be"
    , "passed to 'llvm_boilerplate'."
    ]
  , prim "crucible_llvm_array_size_profile"
    ("LLVMModule -> String -> [LLVMSpec] -> " <>
     "LLVMSetup () -> TopLevel [(String, [FunctionProfile])]")
    (pureVal $ llvm_array_size_profile assumeUnsat)
    Experimental
    [ "Legacy alternative name for 'llvm_array_size_profile'." ]

  , prim "llvm_spec_solvers"  "LLVMSpec -> [String]"
    (pureVal llvm_spec_solvers)
    Current
    [ "Extract a list of all the solvers used when verifying the given"
    , "method spec."
    ]
  , prim "crucible_spec_solvers"  "LLVMSpec -> [String]"
    (pureVal llvm_spec_solvers)
    Current
    [ "Legacy alternative name for 'llvm_spec_solvers'." ]

  , prim "llvm_spec_size"  "LLVMSpec -> Int"
    (pureVal llvm_spec_size)
    Current
    [ "Return a count of the combined size of all verification goals"
    , "proved as part of the given method spec."
    ]
  , prim "crucible_spec_size"  "LLVMSpec -> Int"
    (pureVal llvm_spec_size)
    Current
    [ "Legacy alternative name for 'llvm_spec_size'." ]

    ------------------------------------------------------------
    -- LLVM x86 verification

  , prim "llvm_verify_x86"
    ("LLVMModule -> String -> String -> [(String, Int)] -> Bool -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal do_llvm_verify_x86)
    Experimental
    [ "Verify an x86 function from an ELF file for use as an override"
    , "in an LLVM verification. The first argument specifies the LLVM"
    , "module containing the _caller_. The second and third specify the"
    , "ELF file name and symbol name of the function to be verified."
    , "The fourth specifies the names and sizes (in bytes) of global"
    , "variables to initialize, and the fifth whether to perform path"
    , "satisfiability checking. The last argument is the LLVM"
    , "specification of the calling context against which to verify"
    , "the function. Returns a method spec that can be used as an"
    , "override when verifying other LLVM functions."
    ]
  , prim "crucible_llvm_verify_x86"
    ("LLVMModule -> String -> String -> [(String, Int)] -> Bool -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal do_llvm_verify_x86)
    Experimental
    [ "Legacy alternative name for 'llvm_verify_x86'." ]

  , prim "llvm_verify_fixpoint_x86"
    ("LLVMModule -> String -> String -> [(String, Int)] -> Bool -> Term -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal do_llvm_verify_fixpoint_x86)
    Experimental
    [ "An experimental variant of 'llvm_verify_x86'. This variant can"
    , "prove some properties involving simple loops with the help of a"
    , "user-provided term that describes how the live variables in the"
    , "loop evolve as the loop computes."
    ]

  , prim "llvm_verify_fixpoint_chc_x86"
    ("LLVMModule -> String -> String -> [(String, Int)] -> " <>
     "Bool -> Term -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal do_llvm_verify_fixpoint_chc_x86)
    Experimental
    [ "An experimental variant of 'llvm_verify_x86'. This variant can"
    , "prove some properties involving simple loops with the help of a"
    , "user-provided term that describes how the live variables in the"
    , "loop evolve as the loop computes."
    , ""
    , "This differs from 'llvm_verify_fixpoint_x86' in that it"
    , "leverages Z3's constrained horn-clause (CHC) functionality to"
    , "synthesize some of the loop's properties."
    ]

  , prim "llvm_verify_x86_with_invariant"
    ("LLVMModule -> String -> String -> [(String, Int)] -> " <>
     "Bool -> (String, Int, Term) -> " <>
     "LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec")
    (pureVal do_llvm_verify_x86_with_invariant)
    Experimental
    [ "An experimental variant of 'llvm_verify_x86'. This variant can"
    , "prove some properties involving simple loops with the help of a"
    , "user-provided term that describes how the live variables in the"
    , "loop evolve as the loop computes."
    , ""
    , "The loop invariant is provided by the tuple argument, which"
    , "indicates what symbol the loop appears in (which might differ"
    , "from the function the specification is for), which loop within"
    , "that function to reason about (starts counting from 0), and a"
    , "term that desribes the loop invariant itself. For success, the"
    , "loop in question must have a single entry-point, must have a"
    , "single back-edge, and must have a constant memory footprint."
    , ""
    , "The SAWCore type expected of the loop invariant will depend on"
    , "the results of an analysis done on the indicated loop, which"
    , "attempts to discover all the loop-carried dependencies. The"
    , "result of this analysis will be packaged into a tuple, and any"
    , "relevant top-level specification variables will be found. The"
    , "expected type of the loop invariant will then be a function"
    , "over all the implicit variables found, and two tuples consisting"
    , "of the initial values of the loop-carried dependencies, and the"
    , "current value of the loop-carried dependencies. The function"
    , "should return Bool. Some trial-and-error will generally be"
    , "required to match the results of the analysis with a suitable"
    , "function."
    , ""
    , "As part of the verification process, the loop invariant will be"
    , "used in several ways. First, a proof obligation will be issued"
    , "upon first entry to the loop, establishing the loop invariant"
    , "holds at the beginning of the loop. Second, the loop invariant"
    , "is used when starting execution from the loop head to make a"
    , "generic assumption that the invariant holds. Finally, the"
    , "invariant is used when execution once again reaches the loop"
    , "head to assert that the invariant holds inductively across the"
    , "execution of the loop body. The produced proof obligations will"
    , "be tagged with either the tag 'initial loop invariant' or"
    , "'inductive loop invariant'."
    , ""
    , "Provided all the generated verification conditions are"
    , "discharged, this results in a partial correctness proof for"
    , "the indicated function. Note that this procedure does not"
    , "prove termination."
    ]

    ------------------------------------------------------------
    -- x86 verification settings

  , prim "enable_x86_what4_hash_consing" "TopLevel ()"
    (pureVal enable_x86_what4_hash_consing)
    Experimental
    [ "Enable hash-consing for What4 expressions during x86"
    , "verification."
    ]

  , prim "disable_x86_what4_hash_consing" "TopLevel ()"
    (pureVal disable_x86_what4_hash_consing)
    Current
    [ "Disable hash-consing for What4 expressions during x86"
    , "verification."
    ]

  , prim "add_x86_preserved_reg" "String -> TopLevel ()"
    (pureVal add_x86_preserved_reg)
    Current
    [ "Treat the given register as callee-saved during x86"
    , "verification."
    ]

  , prim "default_x86_preserved_reg" "TopLevel ()"
    (pureVal default_x86_preserved_reg)
    Current
    [ "Use the default set of callee-saved registers during x86"
    , "verification."
    ]

  , prim "set_x86_stack_base_align" "Int -> TopLevel ()"
    (pureVal set_x86_stack_base_align)
    Experimental
    [ "Set the alignment of the stack allocation base to 2^n during x86"
    , "verification."
    ]

  , prim "default_x86_stack_base_align" "TopLevel ()"
    (pureVal default_x86_stack_base_align)
    Experimental
    [ "Use the default stack allocation base alignment during x86"
    , "verification."
    ]

    ------------------------------------------------------------
    -- LLVM skeletons

  , prim "module_skeleton" "LLVMModule -> TopLevel ModuleSkeleton"
    (pureVal module_skeleton)
    Experimental
    [ "Given a handle to an LLVM module, return a skeleton for that"
    , "module."
    ]

  , prim "function_skeleton" ("ModuleSkeleton -> String -> " <>
                              "TopLevel FunctionSkeleton")
    (pureVal function_skeleton)
    Experimental
    [ "Given a module skeleton and a function name, return the"
    , "corresponding function skeleton."
    ]

  , prim "skeleton_resize_arg_index" ("FunctionSkeleton -> Int -> Int -> " <>
                                      "Bool -> TopLevel FunctionSkeleton")
    (pureVal skeleton_resize_arg_index)
    Experimental
    [ "Given a function skeleton, argument index, array length, and"
    , "whether or not that argument is initialized, return a new"
    , "function skeleton where the assumed length/initialization of the"
    , "given argument is updated."
    ]

 , prim "skeleton_resize_arg" ("FunctionSkeleton -> String -> Int -> " <>
                               "Bool -> TopLevel FunctionSkeleton")
    (pureVal skeleton_resize_arg)
    Experimental
    [ "Given a function skeleton, argument name, array length, and"
    , "whether or not that argument is initialized, return a new"
    , "function skeleton where the assumed length/initialization of the"
    , "given argument is updated."
    ]

  , prim "skeleton_guess_arg_sizes" ("ModuleSkeleton -> LLVMModule -> " <>
                                     "[(String, [FunctionProfile])] -> " <>
                                     "TopLevel ModuleSkeleton")
    (pureVal skeleton_guess_arg_sizes)
    Experimental
    [ "Update the sizes of all arguments of the given module skeleton"
    , "using data obtained from 'crucible_llvm_array_size_profile'."
    ]

  , prim "skeleton_globals_pre" "ModuleSkeleton -> LLVMSetup ()"
    (pureVal skeleton_globals_pre)
    Experimental
    [ "Allocate and initialize mutable globals from the given module"
    , "skeleton."
    ]

  , prim "skeleton_globals_post" "ModuleSkeleton -> LLVMSetup ()"
    (pureVal skeleton_globals_post)
    Experimental
    [ "Assert that all mutable globals from the given module skeleton"
    , "are unchanged."
    ]

  , prim "skeleton_prestate" "FunctionSkeleton -> LLVMSetup SkeletonState"
    (pureVal skeleton_prestate)
    Experimental
    [ "Allocate and initialize the arguments of the given function"
    , "skeleton. Return a 'SkeletonState' from which those arguments can"
    , "be retrieved, so that preconditions can be imposed."
    ]

  , prim "skeleton_poststate"
    "FunctionSkeleton -> SkeletonState -> LLVMSetup SkeletonState"
    (pureVal skeleton_poststate)
    Experimental
    [ "Assert that pointer arguments of the given function skeleton remain"
    , "initialized. Return a 'SkeletonState' from which those arguments can"
    , "be retrieved, so that postconditions can be imposed."
    ]

  , prim "skeleton_arg_index" "SkeletonState -> Int -> LLVMSetup Term"
    (pureVal skeleton_arg_index)
    Experimental
    [ "Retrieve the argument value at the given index from the given"
    , "'SkeletonState'."
    ]

  , prim "skeleton_arg" "SkeletonState -> String -> LLVMSetup Term"
    (pureVal skeleton_arg)
    Experimental
    [ "Retrieve the argument value of the given name from the given"
    , "'SkeletonState'."
    ]

  , prim "skeleton_arg_index_pointer" ("SkeletonState -> Int -> " <>
                                       "LLVMSetup LLVMValue")
    (pureVal skeleton_arg_index_pointer)
    Experimental
    [ "Retrieve the argument pointer at the given index from the given"
    , "'SkeletonState'. Fails if the specified argument is not a"
    , "pointer."
    ]

  , prim "skeleton_arg_pointer" "SkeletonState -> String -> LLVMSetup LLVMValue"
    (pureVal skeleton_arg_pointer)
    Experimental
    [ "Retrieve the argument pointer of the given name from the given"
    , "'SkeletonState'. Fails if the specified argument is not a"
    , "pointer."
    ]

  , prim "skeleton_exec" "SkeletonState -> LLVMSetup ()"
    (pureVal skeleton_exec)
    Experimental
    [ "Wrapper around 'llvm_execute_func' that passes the arguments"
    , "initialized in 'skeleton_prestate'."
    ]

  , prim "llvm_boilerplate" "String -> ModuleSkeleton -> Bool -> TopLevel ()"
    (pureVal do_llvm_boilerplate)
    Experimental
    [ "Generate boilerplate for the definitions in the given LLVM"
    , "module skeleton. Output is written to the path passed as the"
    , "first argument. The third argument controls whether skeleton"
    , "builtins are emitted."
    ]

    ------------------------------------------------------------
    -- Java types

  , prim "java_bool"           "JavaType"
    (pureVal JavaBoolean)
    Current
    [ "The Java type of booleans." ]

  , prim "java_byte"           "JavaType"
    (pureVal JavaByte)
    Current
    [ "The Java type of bytes." ]

  , prim "java_char"           "JavaType"
    (pureVal JavaChar)
    Current
    [ "The Java type of characters." ]

  , prim "java_short"          "JavaType"
    (pureVal JavaShort)
    Current
    [ "The Java type of short integers." ]

  , prim "java_int"            "JavaType"
    (pureVal JavaInt)
    Current
    [ "The standard Java integer type." ]

  , prim "java_long"           "JavaType"
    (pureVal JavaLong)
    Current
    [ "The Java type of long integers." ]

  , prim "java_float"          "JavaType"
    (pureVal JavaFloat)
    Current
    [ "The Java type of single-precision floating point values." ]

  , prim "java_double"         "JavaType"
    (pureVal JavaDouble)
    Current
    [ "The Java type of double-precision floating point values." ]

  , prim "java_array"          "Int -> JavaType -> JavaType"
    (pureVal JavaArray)
    Current
    [ "The Java type of arrays of a fixed number of elements of the"
    , "given element type."
    ]

  , prim "java_class"          "String -> JavaType"
    (pureVal JavaClass)
    Current
    [ "The Java type corresponding to the named class." ]

    ------------------------------------------------------------
    -- Java values / terms

  , prim "jvm_null"
    "JVMValue"
    (pureVal (CMS.SetupNull () :: CMS.SetupValue CJ.JVM))
    Current
    [ "A JVMValue representing a null pointer value." ]

  , prim "jvm_term"
    "Term -> JVMValue"
    (pureVal (CMS.SetupTerm :: TypedTerm -> CMS.SetupValue CJ.JVM))
    Current
    [ "Construct a 'JVMValue' from a 'Term'." ]

    ------------------------------------------------------------
    -- Java fresh values

  , prim "jvm_fresh_var" "String -> JavaType -> JVMSetup Term"
    (pureVal jvm_fresh_var)
    Current
    [ "Create a fresh variable for use within a JVM specification. The"
    , "name is used only for pretty-printing."
    ]

    ------------------------------------------------------------
    -- Java allocation

  , prim "jvm_alloc_object" "String -> JVMSetup JVMValue"
    (pureVal jvm_alloc_object)
    Current
    [ "Declare that an instance of the given class should be allocated"
    , "in a JVM specification. Before 'jvm_execute_func', this states"
    , "that the method expects the object to be allocated before it"
    , "runs. After 'jvm_execute_func', it states that the method being"
    , "verified is expected to perform the allocation."
    ]

  , prim "jvm_alloc_array" "Int -> JavaType -> JVMSetup JVMValue"
    (pureVal jvm_alloc_array)
    Current
    [ "Declare that an array of the given size and element type should"
    , "be allocated in a JVM specification. Before 'jvm_execute_func',"
    , "this states that the method expects the array to be allocated"
    , "before it runs. After 'jvm_execute_func', it states that the"
    , "method being verified is expected to perform the allocation."
    ]

    -- TODO: jvm_alloc_multiarray

    ------------------------------------------------------------
    -- Java assertions

  , prim "jvm_precond" "Term -> JVMSetup ()"
    (pureVal jvm_precond)
    Current
    [ "State that the given predicate is a pre-condition for the"
    , "execution of the method being verified."
    ]

  , prim "jvm_postcond" "Term -> JVMSetup ()"
    (pureVal jvm_postcond)
    Current
    [ "State that the given predicate is a post-condition of the"
    , "execution of the method being verified."
    ]

  , prim "jvm_assert" "Term -> JVMSetup ()"
    (pureVal jvm_assert)
    Current
    [ "State that the given predicate must hold.  Acts as 'jvm_precond'"
    , "or 'jvm_postcond' depending on where it appears, that is, before"
    , "or after 'jvm_execute_func'."
    ]

  , prim "jvm_equal" "JVMValue -> JVMValue -> JVMSetup ()"
    (pureVal jvm_equal)
    Current
    [ "State that two JVM values should be equal. Can be used as either"
    , "a pre-condition or a post-condition. It is semantically"
    , "equivalent to a 'jvm_precond' or 'jvm_postcond' statement that"
    , "is an equality predicate, but potentially more efficient."
    ]

  , prim "jvm_modifies_field" "JVMValue -> String -> JVMSetup ()"
    (pureVal jvm_modifies_field)
    Current
    [ "Declare that the indicated object (first argument) has a field"
    , "(second argument) containing an unspecified value."
    , ""
    , "This lets users write partial specifications of JVM methods."
    , "In the post-state section (after 'jvm_execute_func'), this"
    , "states that the method may modify the field, but says nothing"
    , "about the new value."
    ]

  , prim "jvm_modifies_static_field" "String -> JVMSetup ()"
    (pureVal jvm_modifies_static_field)
    Current
    [ "Declare that the named static field contains an unspecified"
    , "value."
    , ""
    , "This lets users write partial specifications of JVM methods."
    , "In the post-state section (after 'jvm_execute_func'), it"
    , "states that the method may modify the static field, but says"
    , "nothing about the new value."
    ]

  , prim "jvm_modifies_elem" "JVMValue -> Int -> JVMSetup ()"
    (pureVal jvm_modifies_elem)
    Current
    [ "Declare that the indicated array (first argument) has an element"
    , "(second argument) containing an unspecified value."
    , ""
    , "This lets users write partial specifications of JVM methods."
    , "In the post-state section (after 'jvm_execute_func'), it"
    , "states that the method may modify the array element, but says"
    , "nothing about the new value."
    ]

  , prim "jvm_modifies_array" "JVMValue -> JVMSetup ()"
    (pureVal jvm_modifies_array)
    Current
    [ "Declare that the indicated array's elements contain unspecified"
    , "values."
    , ""
    , "This lets users write partial specifications of JVM methods."
    , "In the post-state section (after 'jvm_execute_func'), it"
    , "states that the method may modify the array elements, but says"
    , "nothing about the new values."
    ]

  , prim "jvm_field_is" "JVMValue -> String -> JVMValue -> JVMSetup ()"
    (pureVal jvm_field_is)
    Current
    [ "Declare that the indicated object (first argument) has a field"
    , "(second argument) containing the given value (third argument)."
    , ""
    , "In the pre-state section (before 'jvm_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'jvm_execute_func'), this"
    , "asserts the final memory state after running the function."
    ]

  , prim "jvm_static_field_is" "String -> JVMValue -> JVMSetup ()"
    (pureVal jvm_static_field_is)
    Current
    [ "Declare that the named static field contains the given value."
    , "By default the field name is assumed to belong to the same class"
    , "as the method being specified. Static fields belonging to other"
    , "classes can be selected using the \"<classname>.<fieldname>\""
    , "syntax in the string argument."
    , ""
    , "In the pre-state section (before 'jvm_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'jvm_execute_func'), this"
    , "asserts the final memory state after running the function."
    ]

  , prim "jvm_elem_is" "JVMValue -> Int -> JVMValue -> JVMSetup ()"
    (pureVal jvm_elem_is)
    Current
    [ "Declare that the indicated array (first argument) has an element"
    , "(second argument) containing the given value (third argument)."
    , ""
    , "In the pre-state section (before 'jvm_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'jvm_execute_func'), this"
    , "asserts the final memory state after running the function."
    ]

  , prim "jvm_array_is" "JVMValue -> Term -> JVMSetup ()"
    (pureVal jvm_array_is)
    Current
    [ "Declare that the indicated array reference (first argument)"
    , "contains the given sequence of values (second argument)."
    , ""
    , "In the pre-state section (before 'jvm_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'jvm_execute_func'), this"
    , "asserts the final memory state after running the function."
    ]

  , prim "jvm_execute_func" "[JVMValue] -> JVMSetup ()"
    (pureVal jvm_execute_func)
    Current
    [ "Specify the given list of values as the arguments of the method."
    ,  ""
    , "The 'jvm_execute_func' command also serves to separate the pre-"
    , "state section of the spec (before it) from the post-state"
    , "section (after it). The effects of some JVMSetup statements"
    , "depend on whether they occur in the pre-state or post-state"
    , "section."
    , ""
    , "Every JVM specification must use this command to call its"
    , "function."
    ]

  , prim "jvm_return" "JVMValue -> JVMSetup ()"
    (pureVal jvm_return)
    Current
    [ "Specify the given value as the return value of the method. A"
    , "'jvm_return' command is required if and only if the method has"
    , "a non-void return type."
    ]

    ------------------------------------------------------------
    -- Java class files / modules

  , prim "java_load_class"     "String -> TopLevel JavaClass"
    (pureVal CJ.loadJavaClass)
    Current
    [ "Load the named Java class and return a handle to it." ]

    ------------------------------------------------------------
    -- Java verification

  , prim "jvm_extract"  "JavaClass -> String -> TopLevel Term"
    (pureVal CJ.jvm_extract)
    Current
    [ "Translate a Java method directly to a Term. The parameters of"
    , "the Term will be the parameters of the Java method, and the"
    , "return value will be the return value of the method. Only"
    , "methods with scalar argument and return types are currently"
    , "supported."
    ]
  , prim "crucible_java_extract"  "JavaClass -> String -> TopLevel Term"
    (pureVal CJ.jvm_extract)
    Current
    [ "Legacy alternative name for 'jvm_extract'." ]

  , prim "jvm_verify"
    ("JavaClass -> String -> [JVMSpec] -> Bool -> " <>
     "JVMSetup () -> ProofScript () -> TopLevel JVMSpec")
    (pureVal jvm_verify)
    Current
    [ "Verify the JVM method named by the second parameter in the class"
    , "specified by the first. The third parameter lists the JVMSpec"
    , "values returned by previous calls to use as overrides. The"
    , "fourth (Bool) parameter enables or disables path satisfiability"
    , "checking. The fifth describes how to set up the symbolic"
    , "execution engine before verification. And the last gives the"
    , "script to use to prove the validity of the resulting"
    , "verification conditions."
    ]

  , prim "jvm_unsafe_assume_spec"
    "JavaClass -> String -> JVMSetup () -> TopLevel JVMSpec"
    (pureVal jvm_unsafe_assume_spec)
    Current
    [ "Return a JVMSpec corresponding to a JVMSetup block, as would be"
    , "returned by jvm_verify but without performing any verification."
    ]

    ------------------------------------------------------------
    -- MIR types

  , prim "mir_bool" "MIRType"
    (pureVal mir_bool)
    Experimental
    [ "The type of MIR booleans." ]

  , prim "mir_char" "MIRType"
    (pureVal mir_char)
    Experimental
    [ "The type of MIR characters." ]

  , prim "mir_i8" "MIRType"
    (pureVal mir_i8)
    Experimental
    [ "The type of MIR 8-bit signed integers." ]

  , prim "mir_i16" "MIRType"
    (pureVal mir_i16)
    Experimental
    [ "The type of MIR 16-bit signed integers." ]

  , prim "mir_i32" "MIRType"
    (pureVal mir_i32)
    Experimental
    [ "The type of MIR 32-bit signed integers." ]

  , prim "mir_i64" "MIRType"
    (pureVal mir_i64)
    Experimental
    [ "The type of MIR 64-bit signed integers." ]

  , prim "mir_i128" "MIRType"
    (pureVal mir_i128)
    Experimental
    [ "The type of MIR 128-bit signed integers." ]

  , prim "mir_isize" "MIRType"
    (pureVal mir_isize)
    Experimental
    [ "The type of MIR pointer-sized signed integers." ]

  , prim "mir_u8" "MIRType"
    (pureVal mir_u8)
    Experimental
    [ "The type of MIR 8-bit unsigned integers." ]

  , prim "mir_u16" "MIRType"
    (pureVal mir_u16)
    Experimental
    [ "The type of MIR 16-bit unsigned integers." ]

  , prim "mir_u32" "MIRType"
    (pureVal mir_u32)
    Experimental
    [ "The type of MIR 32-bit unsigned integers." ]

  , prim "mir_u64" "MIRType"
    (pureVal mir_u64)
    Experimental
    [ "The type of MIR 64-bit unsigned integers." ]

  , prim "mir_u128" "MIRType"
    (pureVal mir_u128)
    Experimental
    [ "The type of MIR 128-bit unsigned integers." ]

  , prim "mir_usize" "MIRType"
    (pureVal mir_usize)
    Experimental
    [ "The type of MIR pointer-sized unsigned integers." ]

  , prim "mir_f32" "MIRType"
    (pureVal mir_f32)
    Experimental
    [ "The type of MIR single-precision floating-point values." ]

  , prim "mir_f64" "MIRType"
    (pureVal mir_f64)
    Experimental
    [ "The type of MIR double-precision floating-point values." ]

  , prim "mir_tuple" "[MIRType] -> MIRType"
    (pureVal mir_tuple)
    Experimental
    [ "The type of MIR tuples of the given types." ]

  , prim "mir_adt" "MIRAdt -> MIRType"
    (pureVal mir_adt)
    Experimental
    [ "The type of a MIR algebraic data type (ADT), i.e., a struct or"
    , "enum, corresponding to the given MIRAdt. Use the 'mir_find_adt'"
    , "command to retrieve a MIRAdt value."
    ]

  , prim "mir_ref" "MIRType -> MIRType"
    (pureVal mir_ref)
    Experimental
    [ "The type of MIR immutable references." ]

  , prim "mir_ref_mut" "MIRType -> MIRType"
    (pureVal mir_ref_mut)
    Experimental
    [ "The type of MIR mutable references." ]

  , prim "mir_raw_ptr_const" "MIRType -> MIRType"
    (pureVal mir_raw_ptr_const)
    Experimental
    [ "The type of MIR immutable raw pointers." ]

  , prim "mir_raw_ptr_mut" "MIRType -> MIRType"
    (pureVal mir_raw_ptr_mut)
    Experimental
    [ "The type of MIR mutable raw pointers." ]

  , prim "mir_array" "Int -> MIRType -> MIRType"
    (pureVal mir_array)
    Experimental
    [ "The type of MIR arrays with the given number of elements of the"
    , "given type."
    ]

  , prim "mir_slice" "MIRType -> MIRType"
    (pureVal mir_slice)
    Experimental
    [ "The type of MIR slices, i.e., dynamically sized views into a"
    , "contiguous sequence of the given type. Currently, SAW can only"
    , "handle references to slices (&[T])."
    ]

  , prim "mir_str" "MIRType"
    (pureVal mir_str)
    Experimental
    [ "The type of MIR strings, which are a particular kind of slice."
    , "Currently, SAW can only handle references to strings (&str)."
    ]

  , prim "mir_const" "MIRType -> Term -> MIRType"
    (funVal2 mir_const)
    Experimental
    [ "A constant value used to instantiate a const generic parameter."
    , "This is intended to be used in conjunction with 'mir_find_adt'"
    , "to look up instantiations of const generic ADTs. This is never"
    , "used to represent the type of a value in its own right, so using"
    , "this in conjunction with 'mir_alloc', 'mir_fresh_var', etc. will"
    , "raise an error."
    , ""
    , "The MIRType argument represents the type of the constant, and"
    , "the Term argument represents the value of the constant. At"
    , "present, only a subset of MIR primitive types are supported in"
    , "'mir_const'. See the SAW manual for a more detailed description"
    , "of which types are supported, along with restrictions on what"
    , "forms the Terms can have."
    ]

  , prim "mir_lifetime" "MIRType"
    (pureVal mir_lifetime)
    Experimental
    [ "The type of MIR lifetimes." ]

  , prim "mir_find_adt" "MIRModule -> String -> [MIRType] -> MIRAdt"
    (funVal3 mir_find_adt)
    Experimental
    [ "Consult the given MIRModule to find an algebraic data type"
    , "(MIRAdt) with the given String as an identifier and the given"
    , "MIRTypes as the types used to instantiate the type parameters."
    , "Fails if such a MIRAdt cannot be found in the MIRModule."
    ]

  , prim "mir_find_mangled_adt" "MIRModule -> String -> MIRAdt"
    (funVal2 mir_find_mangled_adt)
    Experimental
    [ "Consult the given MIRModule to find an algebraic data type"
    , "(MIRAdt) with the given String as a mangled identifier. A"
    , "mangled identifier is one referring to an ADT that is already"
    , "instantiated with its type arguments (so foo::Bar::_adt123456789"
    , "is a mangled identifier, but foo::Bar is not). Fails if such a"
    , "MIRAdt cannot be found in the MIRModule."
    , ""
    , "Due to the fact that mangled identifiers can change easily when"
    , "recompiling Rust code, this function's use is discouraged in"
    , "favor of using 'mir_find_adt' whenever possible."
    ]

    ------------------------------------------------------------
    -- MIR values / terms

  , prim "mir_find_name" "MIRModule -> String -> [MIRType] -> String"
    (funVal3 mir_find_name)
    Experimental
    [ "Consult the given MIRModule to find an instantiation of a"
    , "function with the given String as an identifier and the given"
    , "MIRTypes as the types used to instantiate the type parameters."
    , "Fails if such an instantiation cannot be found in the MIRModule."
    ]

  , prim "mir_term"
    "Term -> MIRValue"
    (pureVal (CMS.SetupTerm :: TypedTerm -> CMS.SetupValue MIR))
    Experimental
    [ "Construct a 'MIRValue' from a 'Term'." ]

  , prim "mir_enum_value" "MIRAdt -> String -> [MIRValue] -> MIRValue"
    (funVal3 mir_enum_value)
    Experimental
    [ "Create a MIRValue representing a variant of a MIR enum with the"
    , "given list of values as elements. The MIRAdt argument determines"
    , "what enum type to create; use 'mir_find_adt' to retrieve a"
    , "MIRAdt value. The String argument represents the variant name."
    ]

  , prim "mir_tuple_value" "[MIRValue] -> MIRValue"
    (pureVal (CMS.SetupTuple () :: [CMS.SetupValue MIR] -> CMS.SetupValue MIR))
    Experimental
    [ "Create a MIRValue representing a MIR tuple with the given list"
    , "of values as elements."
    ]

  , prim "mir_array_value" "MIRType -> [MIRValue] -> MIRValue"
    (pureVal (CMS.SetupArray :: MIR.Ty -> [CMS.SetupValue MIR] ->
              CMS.SetupValue MIR))
    Experimental
    [ "Create a MIRValue representing an array of the given type, with"
    , "the given list of values as elements."
    ]

  , prim "mir_elem_value" "MIRValue -> Int -> MIRValue"
    (pureVal mir_elem_value)
    Experimental
    [ "Given a MIR array value and an index, return the MIR value in"
    , "the array at that index."
    ]

  , prim "mir_elem_ref" "MIRValue -> Int -> MIRValue"
    (pureVal mir_elem_ref)
    Experimental
    [ "Given a reference (or raw pointer) to a MIR array, and an index,"
    , "return a reference (resp. raw pointer) to the element in that"
    , "array at that index."
    , ""
    , "Note: If the given reference (or raw pointer) has been created"
    , "with 'mir_alloc' or 'mir_alloc_raw_ptr', the whole reference"
    , "(resp. raw pointer) must be initialized with 'mir_points_to'"
    , "before 'mir_elem_ref' can be used on it."
    ]

  , prim "mir_slice_value" "MIRValue -> MIRValue"
    (pureVal mir_slice_value)
    Experimental
    [ "Create a MIRValue representing a slice of type &[T]. The"
    , "argument must be a reference to an array value, whose overall"
    , "type must be &[T; N] for some length N."
    ]

  , prim "mir_slice_range_value" "MIRValue -> Int -> Int -> MIRValue"
    (pureVal mir_slice_range_value)
    Experimental
    [ "Create a MIRValue representing a slice of type &[T] over a given"
    , "range. The first argument must be a reference to an array value,"
    , "whose overall type must be &[T; N] for some length N. The second"
    , "and third arguments represent the start and end of the range."
    , "The start must not exceed the end, and the end must not exceed N."
    ]

  , prim "mir_str_slice_value" "MIRValue -> MIRValue"
    (pureVal mir_str_slice_value)
    Experimental
    [ "Create a MIRValue representing a slice of type &str. The"
    , "argument must be a reference to an array value, whose overall"
    , "type must be &[u8; N] for some length N. This array is expected"
    , "to be a UTF-8-encoded sequence of bytes."
    ]

  , prim "mir_str_slice_range_value" "MIRValue -> Int -> Int -> MIRValue"
    (pureVal mir_str_slice_range_value)
    Experimental
    [ "Create a MIRValue representing a slice of type &str over a given"
    , "range. The first argument must be a reference to an array value,"
    , "whose overall type must be &[u8; N] for some length N. This"
    , "array is expected to be a UTF-8-encoded sequence of bytes. The"
    , "second and third arguments represent the start and end of the"
    , "range. The start must not exceed the end, and the end must not"
    , "exceed N."
    ]

  , prim "mir_struct_value" "MIRAdt -> [MIRValue] -> MIRValue"
    (pureVal (CMS.SetupStruct :: MIR.Adt -> [CMS.SetupValue MIR] ->
              CMS.SetupValue MIR))
    Experimental
    [ "Create a MIRValue representing a MIR struct with the given list"
    , "of values as elements. The MIRAdt argument determines what"
    , "struct type to create; use 'mir_find_adt' to retrieve a MIRAdt"
    , "value."
    ]

  , prim "mir_mux_values" "Term -> MIRValue -> MIRValue -> MIRValue"
    (pureVal mir_mux_values)
    Experimental
    [ "Multiplex two MIRValues based on whether a (possibly symbolic)"
    , "Term predicate holds or not. The Term argument must have the"
    , "Cryptol type Bit, and the two MIRValue arguments must have the"
    , "same type."
    ]

  , prim "mir_static"
    "String -> MIRValue"
    (pureVal (CMS.SetupGlobal () :: Text -> CMS.SetupValue MIR))
    Experimental
    [ "Return a MIRValue representing a reference to the named static."
    , "The String should be the name of a static value."
    ]

  , prim "mir_static_initializer"
    "String -> MIRValue"
    (pureVal (CMS.SetupGlobalInitializer () :: Text -> CMS.SetupValue MIR))
    Experimental
    [ "Return a MIRValue representing the value of the initializer of a"
    , "named static. The String should be the name of a static value."
    ]

  , prim "mir_cast_raw_ptr" "MIRValue -> MIRType -> MIRValue"
    (pureVal mir_cast_raw_ptr)
    Experimental
    [ "Given a raw pointer, return a raw pointer to the same memory"
    , "location and with the same mutability, but with the given type"
    , "as the pointee type instead."
    , ""
    , "Note that this only changes the pointee type as statically"
    , "tracked by SAW. It does not allow you to reinterpret the value"
    , "pointed to as a type other than what it was originally allocated"
    , "as with 'mir_alloc_raw_ptr'. Therefore, it cannot be used in the"
    , "first argument to 'mir_points_to'."
    ]

    ------------------------------------------------------------
    -- MIR fresh values

  , prim "mir_fresh_cryptol_var" "String -> Type -> MIRSetup Term"
    (pureVal mir_fresh_cryptol_var)
    Experimental
    [ "Create a fresh symbolic variable of the given Cryptol type for"
    , "use within a MIR specification. The given name is used only for"
    , "pretty-printing. Unlike 'mir_fresh_var', this can be used when"
    , "there isn't an appropriate MIR type, such as the Cryptol Array"
    , "type."
    ]

  , prim "mir_fresh_expanded_value" "String -> MIRType -> MIRSetup MIRValue"
    (pureVal mir_fresh_expanded_value)
    Experimental
    [ "Create a MIR value entirely populated with fresh symbolic"
    , "variables. For compound types such as structs and arrays, this"
    , "will explicitly set each field or element to contain a fresh"
    , "symbolic variable. The String argument is used as a prefix in"
    , "each of the symbolic variables."
    ]

  , prim "mir_fresh_var" "String -> MIRType -> MIRSetup Term"
    (pureVal mir_fresh_var)
    Experimental
    [ "Create a fresh symbolic variable for use within a MIR"
    , "specification. The name is used only for pretty-printing."
    ]

    ------------------------------------------------------------
    -- MIR allocation

  , prim "mir_alloc" "MIRType -> MIRSetup MIRValue"
    (pureVal mir_alloc)
    Experimental
    [ "Declare that an immutable reference to the given type should be"
    , "allocated in a MIR specification. Before 'mir_execute_func',"
    , "this states that the function expects the object to be allocated"
    , "before it runs. After 'mir_execute_func', it states that the"
    , "function being verified is expected to perform the allocation."
    , ""
    , "This command will raise an error if a 'mir_slice' or 'mir_str'"
    , "type is passed as an argument. To create a slice reference, use"
    , "the 'mir_slice_value' or 'mir_slice_range_value' functions"
    , "instead."
    ]

  , prim "mir_alloc_mut" "MIRType -> MIRSetup MIRValue"
    (pureVal mir_alloc_mut)
    Experimental
    [ "Declare that a mutable reference to the given type should be"
    , "allocated in a MIR specification. Before 'mir_execute_func',"
    , "this states that the function expects the object to be allocated"
    , "before it runs. After 'mir_execute_func', it states that the"
    , "function being verified is expected to perform the allocation."
    , ""
    , "This command will raise an error if a 'mir_slice' or 'mir_str'"
    , "type is passed as an argument. To create a slice reference, use"
    , "the 'mir_slice_value' or 'mir_slice_range_value' functions"
    , "instead."
    ]

  , prim "mir_alloc_raw_ptr_const" "MIRType -> MIRSetup MIRValue"
    (pureVal mir_alloc_raw_ptr_const)
    Experimental
    [ "Declare that an immutable raw pointer to the given type should"
    , "be allocated in a MIR specification. Before 'mir_execute_func',"
    , "this states that the function expects the object to be allocated"
    , "before it runs. After 'mir_execute_func', it states that the"
    , "function being verified is expected to perform the allocation."
    ]

  , prim "mir_alloc_raw_ptr_const_multi" "Int -> MIRType -> MIRSetup MIRValue"
    (pureVal mir_alloc_raw_ptr_const_multi)
    Experimental
    [ "Declare that an immutable raw pointer to a contiguous sequence"
    , "of values should be allocated in a MIR specification. The first"
    , "argument specifies the number of values and the second argument"
    , "specifies a type for the values. Before 'mir_execute_func', this"
    , "states that the function expects the memory to be allocated"
    , "before it runs. After 'mir_execute_func', it states that the"
    , "function being verified is expected to perform the allocation."
    ]

  , prim "mir_alloc_raw_ptr_mut" "MIRType -> MIRSetup MIRValue"
    (pureVal mir_alloc_raw_ptr_mut)
    Experimental
    [ "Declare that a mutable raw pointer to the given type should be"
    , "allocated in a MIR specification. Before 'mir_execute_func',"
    , "this states that the function expects the object to be allocated"
    , "before it runs. After 'mir_execute_func', it states that the"
    , "function being verified is expected to perform the allocation."
    ]

  , prim "mir_alloc_raw_ptr_mut_multi" "Int -> MIRType -> MIRSetup MIRValue"
    (pureVal mir_alloc_raw_ptr_mut_multi)
    Experimental
    [ "Declare that a mutable raw pointer to a contiguous sequence of"
    , "values should be allocated in a MIR specification. The first"
    , "argument specifies the number of values and the second argument"
    , "specifies a type for the values. Before 'mir_execute_func', this"
    , "states that the function expects the memory to be allocated"
    , "before it runs. After 'mir_execute_func', it states that the"
    , "function being verified is expected to perform the allocation."
    ]

  , prim "mir_ref_of" "MIRValue -> MIRSetup MIRValue"
    (pureVal mir_ref_of)
    Experimental
    [ "Allocates an immutable reference and initializes it to point to"
    , "the given MIRValue."
    ]

  , prim "mir_ref_of_mut" "MIRValue -> MIRSetup MIRValue"
    (pureVal mir_ref_of_mut)
    Experimental
    [ "Allocates a mutable reference and initializes it to point to the"
    , "given MIRValue."
    ]

  , prim "mir_vec_of"
    "String -> MIRType -> MIRValue -> MIRSetup MIRValue"
    (pureVal mir_vec_of)
    Experimental
    [ "Create a MIR 'Vec' value. The String argument is used as a"
    , "prefix for naming the internal symbolic variables created as"
    , "part of the 'Vec' struct. The MIRType argument is the element"
    , "type of the 'Vec'. The MIRValue argument gives the contents of"
    , "the 'Vec', which must be a MIR array value whose element type"
    , "matches the MIRType argument."
    ]

    ------------------------------------------------------------
    -- MIR assertions

  , prim "mir_postcond" "Term -> MIRSetup ()"
    (pureVal mir_postcond)
    Experimental
    [ "State that the given predicate is a post-condition for the"
    , "execution of the method being verified."
    ]

  , prim "mir_precond" "Term -> MIRSetup ()"
    (pureVal mir_precond)
    Experimental
    [ "State that the given predicate is a pre-condition on the"
    , "execution of the method being verified."
    ]

  , prim "mir_assert" "Term -> MIRSetup ()"
    (pureVal mir_assert)
    Experimental
    [ "State that the given predicate must hold.  Acts as 'mir_precond'"
    , "or 'mir_postcond' depending on whether it appears before or"
    , "after 'mir_execute_func'."
    ]

  , prim "mir_equal" "MIRValue -> MIRValue -> MIRSetup ()"
    (pureVal mir_equal)
    Experimental
    [ "State that two MIR values should be equal. Can be used as either"
    , "a pre-condition or a post-condition. It is semantically"
    , "equivalent to a 'mir_precond' or 'mir_postcond' statement that"
    , "is an equality predicate, but potentially more efficient."
    ]

  , prim "mir_points_to" "MIRValue -> MIRValue -> MIRSetup ()"
    (pureVal mir_points_to)
    Experimental
    [ "Declare that the memory location indicated by the given"
    , "reference or raw pointer (first argument) contains the given"
    , "value (second argument)."
    , ""
    , "In the pre-state section (before 'mir_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'mir_execute_func'), this"
    , "asserts the final memory state after running the function."
    ]

  , prim "mir_points_to_multi" "MIRValue -> MIRValue -> MIRSetup ()"
    (pureVal mir_points_to_multi)
    Experimental
    [ "Declare that the memory location indicated by the given raw"
    , "pointer (first argument) contains the given contiguous sequence"
    , "of values (second argument, which must have MIR array type). If"
    , "the sequence has more than one element, then the raw pointer"
    , "must be allocated with 'mir_alloc_raw_ptr_{const,mut}_multi'"
    , "with at least as many elements as in the sequence."
    , ""
    , "Note that this is different from a raw pointer pointing to an"
    , "array of multiple values using 'mir_alloc_raw_ptr_{const,mut}'"
    , "and 'mir_points_to' commands. Here, the pointee type of the"
    , "pointer is the type of each individual element, not an array"
    , "type."
    , ""
    , "In the pre-state section (before 'mir_execute_func') this"
    , "specifies the initial memory layout before function execution."
    , "In the post-state section (after 'mir_execute_func'), this"
    , "asserts the final memory state after running the function."
    ]

  , prim "mir_execute_func" "[MIRValue] -> MIRSetup ()"
    (pureVal mir_execute_func)
    Experimental
    [ "Specify the given list of values as the arguments of the method."
    ,  ""
    , "The mir_execute_func statement also serves to separate the pre-"
    , "state section of the spec (before it) from the post-state"
    , "section (after it). The effects of some MIRSetup statements"
    , "depend on whether they occur in the pre-state or post-state"
    , "section."
    , ""
    , "Every MIR specification must use this command to call its"
    , "function."
    ]

  , prim "mir_return" "MIRValue -> MIRSetup ()"
    (pureVal mir_return)
    Experimental
    [ "Specify the given value as the return value of the method. A"
    , "mir_return statement is required if and only if the method has"
    , "a non-() return type."
    ]

    ------------------------------------------------------------
    -- MIR modules

  , prim "mir_load_module" "String -> TopLevel MIRModule"
    (pureVal do_mir_load_module)
    Experimental
    [ "Load a MIR JSON file and return a handle to it." ]

    ------------------------------------------------------------
    -- MIR verification

  , prim "mir_extract" "MIRModule -> String -> TopLevel Term"
    (pureVal mir_extract)
    Experimental
    [ "Translate a MIR function directly to a Term. The parameters of"
    , "the Term will be the parameters of the MIR function, and the"
    , "return value will be the return value of the function. Only"
    , "functions with the following argument and return types are"
    , "currently supported: primitive integer types (e.g., u8 or i8),"
    , "bool, char, arrays, and tuples."
    ]

  , prim "mir_verify"
    ("MIRModule -> String -> [MIRSpec] -> Bool -> " <>
     "MIRSetup () -> ProofScript () -> TopLevel MIRSpec")
    (pureVal mir_verify)
    Experimental
    [ "Verify the MIR function named by the second parameter in the"
    , "module specified by the first. The third parameter lists the"
    , "MIRSpec values returned by previous calls to use as overrides."
    , "The fourth (Bool) parameter enables or disables path"
    , "satisfiability checking. The fifth describes how to set up the"
    , "symbolic execution engine before verification. And the last"
    , "gives the script to use to prove the validity of the resulting"
    , "verification conditions."
    ]

  , prim "mir_unsafe_assume_spec"
    "MIRModule -> String -> MIRSetup () -> TopLevel MIRSpec"
    (pureVal mir_unsafe_assume_spec)
    Experimental
    [ "Return a MIRSpec corresponding to a MIRSetup block, as would be"
    , "returned by mir_verify but without performing any verification."
    ]

    ------------------------------------------------------------
    -- Additional Crucible-related bits

  , prim "llvm_setup_with_tag" "String -> LLVMSetup () -> LLVMSetup ()"
    (pureVal llvm_setup_with_tag)
    Experimental
    [ "All conditions (e.g., from points-to or assert statements)"
    , "executed in the scope of the given setup block will have the"
    , "first argument string attached as a tag that can later be"
    , "filtered by proof tactics."
    ]

  , prim "jvm_setup_with_tag" "String -> JVMSetup () -> JVMSetup ()"
    (pureVal jvm_setup_with_tag)
    Experimental
    [ "All conditions (e.g., from points-to or assert statements)"
    , "executed in the scope of the given setup block will have the"
    , "first argument string attached as a tag that can later be"
    , "filtered by proof tactics."
    ]

  ] ++
    let unint_help =
         [ "Keep the given Cryptol/SAWCore names opaque during symbolic"
         , "simulation. The command should be used before symbolic execution"
         , "begins (i.e., in the pre-condition of the specification). This"
         , "command does not affect the ProofScript---to keep names opaque"
         , "while discharging goals, you still need to provide them as"
         , "explicit arguments to the relevant proof tactics."
         ]
    in
  [ prim "llvm_unint" "[String] -> LLVMSetup ()"
    (pureVal llvm_unint) Current unint_help

  , prim "jvm_unint" "[String] -> JVMSetup ()"
    (pureVal jvm_unint) Current unint_help

  , prim "mir_unint" "[String] -> MIRSetup ()"
    (pureVal mir_unint) Current unint_help
  ]
  ++
  [
    ------------------------------------------------------------
    -- Other miscellaneous features

    prim "auto_match" "String -> String -> TopLevel ()"
    (pureVal do_auto_match)
    Current
    [ "Interactively decides how to align two modules of potentially"
    , "heterogeneous language and prints the result."
    ]
  ]

  where
    prim :: Text -> Text -> (Text -> Options -> BuiltinContext -> Value) -> PrimitiveLifecycle -> [Text]
         -> (SS.Name, Primitive)
    prim name ty fn lc doc = (name, Primitive
                                     { primitiveType = ty'
                                     , primitiveDoc  = doc
                                     , primitiveFn   = fn name
                                     , primitiveLife = lc
                                     })
      where
        -- Beware: errors in the type will only be detected when the
        -- type is actually looked at by something, like :env, :t,
        -- :search, or a direct use of the builtin.
        ty' = Loader.readSchemaPure fakeFileName lc primNamedTypeEnv ty
        fakeFileName = Text.unpack $ "<type of " <> name <> ">"

    pureVal :: forall t. IsValue t => t -> Text -> Options -> BuiltinContext -> Value
    pureVal x name _ _ = toValue name x

    -- pureVal can be used for anything with an IsValue instance,
    -- including functions. However, functions in TopLevel need to use
    -- funVal* instead; the IsValue instances capture incorrectly and
    -- you get a function that returns a VTopLevel instead of executing
    -- in TopLevel. (There isn't a special-case IsValue instance for
    -- a -> TopLevel t, because that would require overlapping instances;
    -- but there is an IsValue instance for TopLevel t by itself (that
    -- produces VTopLevel) so use of pureVal matches that and the
    -- generic IsValue instance for a -> t.)
    --
    -- XXX: rename these to e.g. monadVal1/2/3 so this is clearer?

    funVal1 :: forall a t. (FromValue a, IsValue t) => (a -> TopLevel t)
               -> Text -> Options -> BuiltinContext -> Value
    funVal1 f name _ _ =
      VBuiltin name Seq.empty $
        OneMoreArg $ \a ->
          toValue name <$> f (fromValue FromArgument a)

    funVal2 :: forall a b t. (FromValue a, FromValue b, IsValue t) => (a -> b -> TopLevel t)
               -> Text -> Options -> BuiltinContext -> Value
    funVal2 f name _ _ =
      VBuiltin name Seq.empty $
        ManyMoreArgs $ \a -> return $
        OneMoreArg $ \b ->
          toValue name <$> f (fromValue FromArgument a) (fromValue FromArgument b)

    funVal3 :: forall a b c t. (FromValue a, FromValue b, FromValue c, IsValue t) => (a -> b -> c -> TopLevel t)
               -> Text -> Options -> BuiltinContext -> Value
    funVal3 f name _ _ =
      VBuiltin name Seq.empty $
        ManyMoreArgs $ \a -> return $
        ManyMoreArgs $ \b -> return $
        OneMoreArg $ \c ->
          toValue name <$> f (fromValue FromArgument a) (fromValue FromArgument b) (fromValue FromArgument c)

    scVal :: forall t. IsValue t =>
             (SharedContext -> t) -> Text -> Options -> BuiltinContext -> Value
    scVal f name _ bic = toValue name (f (biSharedContext bic))

    scVal' :: forall t. IsValue t =>
             (SharedContext -> Options -> t) -> Text -> Options -> BuiltinContext -> Value
    scVal' f name opts bic = toValue name (f (biSharedContext bic) opts)

    bicVal :: forall t. IsValue t =>
              (BuiltinContext -> Options -> t) -> Text -> Options -> BuiltinContext -> Value
    bicVal f name opts bic = toValue name (f bic opts)



-- FUTURE: extract here is now functionally a nop, so if things don't
-- change going forward we should consider simplifying so primTypes
-- uses the same type as the interpreter environment this function
-- seeds, instead of its own.
primNamedTypeEnv :: Map SS.Name (PrimitiveLifecycle, SS.NamedType)
primNamedTypeEnv = fmap extract primTypes
   where extract pt = (primTypeLife pt, primTypeType pt)

-- | Initial value environment for the interpreter.
--
--   Contains the lifecycle state, the type, the value, and the
--   documentation for each builtin.
--
--   Note: all builtins have documentation; the environment type
--   includes a Maybe for the documentation so it can also be used for
--   user definitions.
--
--   FUTURE: extract here is now functionally a nop, so we should
--   consider simplifying so `primitives` uses the same type as the
--   interpreter environment this function seeds, instead of its own.
--
primValueEnv ::
   Options ->
   BuiltinContext ->
   Map SS.Name (SS.Pos, PrimitiveLifecycle, SS.Schema, Value, Maybe [Text])
primValueEnv opts bic = Map.mapWithKey extract primitives
  where
      header = [
          "Description",
          "-----------",
          ""
       ]
      tag p = case primitiveLife p of
          Current -> []
          WarnDeprecated -> ["DEPRECATED AND WILL WARN", ""]
          HideDeprecated -> ["DEPRECATED AND UNAVAILABLE BY DEFAULT", ""]
          Experimental -> ["EXPERIMENTAL", ""]
      name n p = [
          "    " <> n <> " : " <> PPS.pShowText (primitiveType p),
          ""
       ]
      doc n p =
          header <> tag p <> name n p <> primitiveDoc p
      extract n p =
          let pos = SS.PosInternal "<<builtin>>" in
          (pos, primitiveLife p, primitiveType p,
           (primitiveFn p) opts bic, Just $ doc n p)

primEnviron :: Options -> BuiltinContext -> CryptolEnvStack -> Environ
primEnviron opts bic cryenvs =

    -- Do a scope push so the builtins live by themselves in their own
    -- scope layer. This has the result of separating them from the
    -- user's variables in the :env output (which is now grouped by
    -- scope) and, because the builtin layer is readonly, might be
    -- marginally more efficient as the user's globals are added.

    let tyenv = ScopedMap.push $ ScopedMap.seed primNamedTypeEnv
        varenv = ScopedMap.push $ ScopedMap.seed $ primValueEnv opts bic
    in
    Environ varenv tyenv cryenvs

