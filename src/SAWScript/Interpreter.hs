{- |
Module      : SAWScript.Interpreter
Description : Interpreter for SAW-Script files and statements.
License     : BSD3
Maintainer  : huffman
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
#if !MIN_VERSION_base(4,8,0)
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NondecreasingIndentation #-}

module SAWScript.Interpreter
  ( interpretStmt
  , interpretFile
  , processFile
  , buildTopLevelEnv
  , primDocEnv
  , InteractiveMonad(..)
  )
  where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable hiding ( mapM )
#endif
import Control.Applicative ( (<|>) )
import qualified Control.Exception as X
import Control.Monad (unless, (>=>), when)
import Control.Monad.IO.Class (liftIO)
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import Data.Map ( Map )
import qualified Data.Set as Set
import Data.Set ( Set )
import qualified Data.Text as Text
import System.Directory (getCurrentDirectory, setCurrentDirectory, canonicalizePath)
import System.FilePath (takeDirectory)
import System.Process (readProcess)

import qualified SAWScript.AST as SS
import qualified SAWScript.Position as SS
import SAWScript.AST (Located(..),Import(..))
import SAWScript.Builtins
import SAWScript.Exceptions (failTypecheck)
import qualified SAWScript.Import
import SAWScript.HeapsterBuiltins
import SAWScript.JavaExpr
import SAWScript.LLVMBuiltins
import SAWScript.Options
import SAWScript.Lexer (lexSAW)
import SAWScript.MGU (checkDecl, checkDeclGroup)
import SAWScript.Parser (parseSchema)
import SAWScript.TopLevel
import SAWScript.Utils
import SAWScript.Value
import SAWScript.Proof (newTheoremDB)
import SAWScript.Prover.Rewrite(basic_ss)
import SAWScript.Prover.Exporter
import SAWScript.Prover.MRSolver (emptyMREnv)
import Verifier.SAW.Conversion
--import Verifier.SAW.PrettySExp
import Verifier.SAW.Prim (rethrowEvalError)
import Verifier.SAW.Rewriter (emptySimpset, rewritingSharedContext, scSimpset)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding (FlatTermF(..))
import Verifier.SAW.TypedTerm
import qualified Verifier.SAW.CryptolEnv as CEnv
import qualified Verifier.SAW.Cryptol.Monadify as Monadify

import qualified Lang.JVM.Codebase as JCB

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

-- Crucible
import qualified Lang.Crucible.JVM as CJ
import qualified SAWScript.Crucible.Common as CC
import qualified SAWScript.Crucible.Common.MethodSpec as CMS
import qualified SAWScript.Crucible.JVM.BuiltinsJVM as CJ
import           SAWScript.Crucible.LLVM.Builtins
import           SAWScript.Crucible.JVM.Builtins
import           SAWScript.Crucible.LLVM.X86
import           SAWScript.Crucible.LLVM.Boilerplate
import           SAWScript.Crucible.LLVM.Skeleton.Builtins
import qualified SAWScript.Crucible.LLVM.MethodSpecIR as CIR

-- Cryptol
import qualified Cryptol.Eval as V (PPOpts(..))
import qualified Cryptol.Backend.Monad as V (runEval)
import qualified Cryptol.Eval.Value as V (defaultPPOpts, ppValue)
import qualified Cryptol.Eval.Concrete as V (Concrete(..))

import qualified Prettyprinter.Render.Text as PP (putDoc)

import SAWScript.AutoMatch

import qualified Lang.Crucible.FunctionHandle as Crucible

-- Environment -----------------------------------------------------------------

bindPatternLocal :: SS.Pattern -> Maybe SS.Schema -> Value -> LocalEnv -> LocalEnv
bindPatternLocal pat ms v env =
  case pat of
    SS.PWild _   -> env
    SS.PVar x mt  -> extendLocal x (ms <|> (SS.tMono <$> mt)) Nothing v env
    SS.PTuple ps ->
      case v of
        VTuple vs -> foldr ($) env (zipWith3 bindPatternLocal ps mss vs)
          where mss = case ms of
                  Nothing -> repeat Nothing
                  Just (SS.Forall ks (SS.TyCon (SS.TupleCon _) ts))
                    -> [ Just (SS.Forall ks t) | t <- ts ]
                  Just t -> error ("bindPatternLocal: expected tuple type " ++ show t)
        _ -> error "bindPatternLocal: expected tuple value"
    SS.LPattern _ pat' -> bindPatternLocal pat' ms v env

bindPatternEnv :: SS.Pattern -> Maybe SS.Schema -> Value -> TopLevelRW -> TopLevel TopLevelRW
bindPatternEnv pat ms v env =
  case pat of
    SS.PWild _   -> pure env
    SS.PVar x mt ->
      do sc <- getSharedContext
         liftIO $ extendEnv sc x (ms <|> (SS.tMono <$> mt)) Nothing v env
    SS.PTuple ps ->
      case v of
        VTuple vs -> foldr (=<<) (pure env) (zipWith3 bindPatternEnv ps mss vs)
          where mss = case ms of
                  Nothing -> repeat Nothing
                  Just (SS.Forall ks (SS.TyCon (SS.TupleCon _) ts))
                    -> [ Just (SS.Forall ks t) | t <- ts ]
                  Just t -> error ("bindPatternEnv: expected tuple type " ++ show t)
        _ -> error "bindPatternEnv: expected tuple value"
    SS.LPattern _ pat' -> bindPatternEnv pat' ms v env

-- Interpretation of SAWScript -------------------------------------------------

interpret :: SS.Expr -> TopLevel Value
interpret expr =
    let ?fileReader = BS.readFile in
    case expr of
      SS.Bool b              -> return $ VBool b
      SS.String s            -> return $ VString (Text.pack s)
      SS.Int z               -> return $ VInteger z
      SS.Code str            -> do sc <- getSharedContext
                                   cenv <- fmap rwCryptol getMergedEnv
                                   --io $ putStrLn $ "Parsing code: " ++ show str
                                   --showCryptolEnv' cenv
                                   t <- io $ CEnv.parseTypedTerm sc cenv
                                           $ locToInput str
                                   return (toValue t)
      SS.CType str           -> do cenv <- fmap rwCryptol getMergedEnv
                                   s <- io $ CEnv.parseSchema cenv
                                           $ locToInput str
                                   return (toValue s)
      SS.Array es            -> VArray <$> traverse interpret es
      SS.Block stmts         -> interpretStmts stmts
      SS.Tuple es            -> VTuple <$> traverse interpret es
      SS.Record bs           -> VRecord <$> traverse interpret bs
      SS.Index e1 e2         -> do a <- interpret e1
                                   i <- interpret e2
                                   return (indexValue a i)
      SS.Lookup e n          -> do a <- interpret e
                                   return (lookupValue a n)
      SS.TLookup e i         -> do a <- interpret e
                                   return (tupleLookupValue a i)
      SS.Var x               -> do rw <- getMergedEnv
                                   case Map.lookup x (rwValues rw) of
                                     Nothing -> fail $ "unknown variable: " ++ SS.getVal x
                                     Just v -> return (addTrace (show x) v)
      SS.Function pat e      -> do env <- getLocalEnv
                                   let f v = withLocalEnv (bindPatternLocal pat Nothing v env) (interpret e)
                                   return $ VLambda f
      SS.Application e1 e2   -> do v1 <- interpret e1
                                   v2 <- interpret e2
                                   case v1 of
                                     VLambda f -> f v2
                                     _ -> fail $ "interpret Application: " ++ show v1
      SS.Let dg e            -> do env' <- interpretDeclGroup dg
                                   withLocalEnv env' (interpret e)
      SS.TSig e _            -> interpret e
      SS.IfThenElse e1 e2 e3 -> do v1 <- interpret e1
                                   case v1 of
                                     VBool b -> interpret (if b then e2 else e3)
                                     _ -> fail $ "interpret IfThenElse: " ++ show v1
      SS.LExpr _ e           -> interpret e

locToInput :: Located String -> CEnv.InputText
locToInput l = CEnv.InputText { CEnv.inpText = getVal l
                              , CEnv.inpFile = file
                              , CEnv.inpLine = ln
                              , CEnv.inpCol  = col + 2 -- for dropped }}
                              }
  where
  (file,ln,col) =
    case locatedPos l of
      SS.Range f sl sc _ _ -> (f,sl, sc)
      SS.PosInternal s -> (s,1,1)
      SS.PosREPL       -> ("<interactive>", 1, 1)
      SS.Unknown       -> ("Unknown", 1, 1)

interpretDecl :: LocalEnv -> SS.Decl -> TopLevel LocalEnv
interpretDecl env (SS.Decl _ pat mt expr) = do
  v <- interpret expr
  return (bindPatternLocal pat mt v env)

interpretFunction :: LocalEnv -> SS.Expr -> Value
interpretFunction env expr =
    case expr of
      SS.Function pat e -> VLambda f
        where f v = withLocalEnv (bindPatternLocal pat Nothing v env) (interpret e)
      SS.TSig e _ -> interpretFunction env e
      _ -> error "interpretFunction: not a function"

interpretDeclGroup :: SS.DeclGroup -> TopLevel LocalEnv
interpretDeclGroup (SS.NonRecursive d) =
    do env <- getLocalEnv
       interpretDecl env d
interpretDeclGroup (SS.Recursive ds) =
    do env <- getLocalEnv
       let addDecl (SS.Decl _ pat mty e) = bindPatternLocal pat mty (interpretFunction env' e)
           env' = foldr addDecl env ds
       return env'

interpretStmts :: [SS.Stmt] -> TopLevel Value
interpretStmts stmts =
    let ?fileReader = BS.readFile in
    case stmts of
      [] -> fail "empty block"
      [SS.StmtBind pos (SS.PWild _) _ e] -> withPosition pos (interpret e)
      SS.StmtBind pos pat _mcxt e : ss ->
          do env <- getLocalEnv
             v1 <- withPosition pos (interpret e)
             let f v = withLocalEnv (bindPatternLocal pat Nothing v env) (interpretStmts ss)
             bindValue pos v1 (VLambda f)
      SS.StmtLet _ bs : ss -> interpret (SS.Let bs (SS.Block ss))
      SS.StmtCode _ s : ss ->
          do sc <- getSharedContext
             rw <- getMergedEnv

             ce' <- io $ CEnv.parseDecls sc (rwCryptol rw) $ locToInput s
             -- FIXME: Local bindings get saved into the global cryptol environment here.
             -- We should change parseDecls to return only the new bindings instead.
             putTopLevelRW $ rw{rwCryptol = ce'}
             interpretStmts ss
      SS.StmtImport _ _ : _ ->
          do fail "block import unimplemented"
      SS.StmtTypedef _ name ty : ss ->
          do env <- getLocalEnv
             let env' = LocalTypedef (getVal name) ty : env
             withLocalEnv env' (interpretStmts ss)

stmtInterpreter :: StmtInterpreter
stmtInterpreter ro rw stmts =
  fst <$> runTopLevel (withLocalEnv emptyLocal (interpretStmts stmts)) ro rw

processStmtBind ::
  InteractiveMonad m =>
  Bool ->
  SS.Pattern ->
  Maybe SS.Type ->
  SS.Expr ->
  m ()
processStmtBind printBinds pat _mc expr = do -- mx mt
  let (mx, mt) = case pat of
        SS.PWild t -> (Nothing, t)
        SS.PVar x t -> (Just x, t)
        _ -> (Nothing, Nothing)
  let it = SS.Located "it" "it" SS.PosREPL
  let lname = maybe it id mx
  ctx <- SS.tContext <$> getMonadContext
  let expr' = case mt of
                Nothing -> expr
                Just t -> SS.TSig expr (SS.tBlock ctx t)
  let decl = SS.Decl (SS.getPos expr) pat Nothing expr'
  rw <- liftTopLevel getMergedEnv
  let opts = rwPPOpts rw

  ~(SS.Decl _ _ (Just schema) expr'') <- liftTopLevel $
    either failTypecheck return $ checkDecl (rwTypes rw) (rwTypedef rw) decl

  val <- liftTopLevel $ interpret expr''

  -- Run the resulting TopLevel action.
  (result, ty) <-
    case schema of
      SS.Forall [] t ->
        case t of
          SS.TyCon SS.BlockCon [c, t'] | c == ctx -> do
            result <- actionFromValue val
            return (result, t')
          _ -> return (val, t)
      _ -> fail $ "Not a monomorphic type: " ++ SS.pShow schema
  --io $ putStrLn $ "Top-level bind: " ++ show mx
  --showCryptolEnv

  -- Print non-unit result if it was not bound to a variable
  case pat of
    SS.PWild _ | printBinds && not (isVUnit result) ->
      liftTopLevel $
      do nenv <- io . scGetNamingEnv =<< getSharedContext
         printOutLnTop Info (showsPrecValue opts nenv 0 result "")
    _ -> return ()

  -- Print function type if result was a function
  case ty of
    SS.TyCon SS.FunCon _ ->
      liftTopLevel $ printOutLnTop Info $ getVal lname ++ " : " ++ SS.pShow ty
    _ -> return ()

  liftTopLevel $
   do rw' <- getTopLevelRW
      putTopLevelRW =<< bindPatternEnv pat (Just (SS.tMono ty)) result rw'


class (Monad m, MonadFail m) => InteractiveMonad m where
  liftTopLevel :: TopLevel a -> m a
  withTopLevel :: (forall b. TopLevel b -> TopLevel b) -> m a -> m a
  actionFromValue :: FromValue a => Value -> m a
  getMonadContext :: m SS.Context

instance InteractiveMonad TopLevel where
  liftTopLevel m = m
  withTopLevel f m = f m
  actionFromValue = fromValue
  getMonadContext = return SS.TopLevel

instance InteractiveMonad ProofScript where
  liftTopLevel m = scriptTopLevel m
  withTopLevel f (ProofScript m) = ProofScript (underExceptT (underStateT f) m)
  actionFromValue = fromValue
  getMonadContext = return SS.ProofScript

-- | Interpret a block-level statement in the TopLevel monad.
interpretStmt :: InteractiveMonad m =>
  Bool {-^ whether to print non-unit result values -} ->
  SS.Stmt ->
  m ()
interpretStmt printBinds stmt =
  let ?fileReader = BS.readFile in
  case stmt of

    SS.StmtBind pos pat mc expr ->
      withTopLevel (withPosition pos) (processStmtBind printBinds pat mc expr)

    SS.StmtLet _ dg           ->
      liftTopLevel $
      do rw <- getTopLevelRW
         dg' <- either failTypecheck return $
                checkDeclGroup (rwTypes rw) (rwTypedef rw) dg
         env <- interpretDeclGroup dg'
         withLocalEnv env getMergedEnv >>= putTopLevelRW

    SS.StmtCode _ lstr ->
      liftTopLevel $
      do rw <- getTopLevelRW
         sc <- getSharedContext
         --io $ putStrLn $ "Processing toplevel code: " ++ show lstr
         --showCryptolEnv
         cenv' <- io $ CEnv.parseDecls sc (rwCryptol rw) $ locToInput lstr
         putTopLevelRW $ rw { rwCryptol = cenv' }
         --showCryptolEnv

    SS.StmtImport _ imp ->
      liftTopLevel $
      do rw <- getTopLevelRW
         sc <- getSharedContext
         --showCryptolEnv
         let mLoc = iModule imp
             qual = iAs imp
             spec = iSpec imp
         cenv' <- io $ CEnv.importModule sc (rwCryptol rw) mLoc qual CEnv.PublicAndPrivate spec
         putTopLevelRW $ rw { rwCryptol = cenv' }
         --showCryptolEnv

    SS.StmtTypedef _ name ty ->
      liftTopLevel $
      do rw <- getTopLevelRW
         putTopLevelRW $ addTypedef (getVal name) ty rw

interpretFile :: FilePath -> Bool {- ^ run main? -} -> TopLevel ()
interpretFile file runMain = do
  opts <- getOptions
  stmts <- io $ SAWScript.Import.loadFile opts file
  mapM_ stmtWithPrint stmts
  when runMain interpretMain
  writeVerificationSummary
  where
    stmtWithPrint s = do let withPos str = unlines $
                                           ("[output] at " ++ show (SS.getPos s) ++ ": ") :
                                             map (\l -> "\t"  ++ l) (lines str)
                         showLoc <- printShowPos <$> getOptions
                         if showLoc
                           then localOptions (\o -> o { printOutFn = \lvl str ->
                                                          printOutFn o lvl (withPos str) })
                                  (interpretStmt False s)
                           else interpretStmt False s

-- | Evaluate the value called 'main' from the current environment.
interpretMain :: TopLevel ()
interpretMain = do
  rw <- getTopLevelRW
  let mainName = Located "main" "main" (SS.PosInternal "entry")
  case Map.lookup mainName (rwValues rw) of
    Nothing -> return () -- fail "No 'main' defined"
    Just v -> fromValue v

buildTopLevelEnv :: AIGProxy
                 -> Options
                 -> IO (BuiltinContext, TopLevelRO, TopLevelRW)
buildTopLevelEnv proxy opts =
    do let mn = mkModuleName ["SAWScript"]
       sc0 <- mkSharedContext
       let ?fileReader = BS.readFile
       CryptolSAW.scLoadPreludeModule sc0
       CryptolSAW.scLoadCryptolModule sc0
       scLoadModule sc0 (emptyModule mn)
       cryptol_mod <- scFindModule sc0 $ mkModuleName ["Cryptol"]
       let convs = natConversions
                   ++ bvConversions
                   ++ vecConversions
                   ++ [ tupleConversion
                      , recordConversion
                      , remove_ident_coerce
                      , remove_ident_unsafeCoerce
                      ]
           cryptolDefs = filter defPred $ moduleDefs cryptol_mod
           defPred d = defIdent d `Set.member` includedDefs
           includedDefs = Set.fromList
                          [ "Cryptol.ecDemote"
                          , "Cryptol.seq"
                          ]
       simps <- scSimpset sc0 cryptolDefs [] convs
       let sc = rewritingSharedContext sc0 simps
       ss <- basic_ss sc
       jcb <- JCB.loadCodebase (jarList opts) (classPath opts) (javaBinDirs opts)
       currDir <- getCurrentDirectory
       thmDB <- newTheoremDB
       Crucible.withHandleAllocator $ \halloc -> do
       let ro0 = TopLevelRO
                   { roJavaCodebase = jcb
                   , roOptions = opts
                   , roHandleAlloc = halloc
                   , roPosition = SS.Unknown
                   , roProxy = proxy
                   , roInitWorkDir = currDir
                   , roBasicSS = ss
                   , roStackTrace = []
                   , roSubshell = fail "Subshells not supported"
                   , roProofSubshell = fail "Proof subshells not supported"
                   , roLocalEnv = []
                   }
       let bic = BuiltinContext {
                   biSharedContext = sc
                 , biBasicSS = ss
                 }
           primsAvail = Set.fromList [Current]
       ce0 <- CEnv.initCryptolEnv sc

       jvmTrans <- CJ.mkInitialJVMContext halloc

       let rw0 = TopLevelRW
                   { rwValues     = valueEnv primsAvail opts bic
                   , rwTypes      = primTypeEnv primsAvail
                   , rwTypedef    = Map.empty
                   , rwDocs       = primDocEnv primsAvail
                   , rwCryptol    = ce0
                   , rwMonadify   = Monadify.defaultMonEnv
                   , rwMRSolverEnv = emptyMREnv
                   , rwProofs     = []
                   , rwPPOpts     = SAWScript.Value.defaultPPOpts
                   , rwSharedContext = sc
                   , rwTheoremDB = thmDB
                   , rwJVMTrans   = jvmTrans
                   , rwPrimsAvail = primsAvail
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
                   , rwCrucibleTimeout = CC.defaultSAWCoreBackendTimeout
                   , rwPathSatSolver = CC.PathSat_Z3
                   , rwSkipSafetyProofs = False
                   , rwSingleOverrideSpecialCase = False
                   , rwSequentGoals = False
                   }
       return (bic, ro0, rw0)

processFile ::
  AIGProxy ->
  Options ->
  FilePath ->
  Maybe (TopLevel ()) ->
  Maybe (ProofScript ()) ->
  IO ()
processFile proxy opts file mbSubshell mbProofSubshell = do
  (_, ro, rw) <- buildTopLevelEnv proxy opts
  let ro' = case mbSubshell of
              Nothing -> ro
              Just m  -> ro{ roSubshell = m }
  let ro'' = case mbProofSubshell of
              Nothing -> ro'
              Just m  -> ro'{ roProofSubshell = m }
  oldpath <- getCurrentDirectory
  file' <- canonicalizePath file
  setCurrentDirectory (takeDirectory file')
  _ <- runTopLevel (interpretFile file' True) ro'' rw
            `X.catch` (handleException opts)
  setCurrentDirectory oldpath
  return ()

-- Primitives ------------------------------------------------------------------

add_primitives :: PrimitiveLifecycle -> BuiltinContext -> Options -> TopLevel ()
add_primitives lc bic opts = do
  rw <- getTopLevelRW
  let lcs = Set.singleton lc
  putTopLevelRW rw {
    rwValues     = rwValues rw `Map.union` valueEnv lcs opts bic
  , rwTypes      = rwTypes rw `Map.union` primTypeEnv lcs
  , rwDocs       = rwDocs rw `Map.union` primDocEnv lcs
  , rwPrimsAvail = Set.insert lc (rwPrimsAvail rw)
  }

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


enable_crucible_profiling :: FilePath -> TopLevel ()
enable_crucible_profiling f = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwProfilingFile = Just f }

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

add_x86_preserved_reg :: String -> TopLevel ()
add_x86_preserved_reg r = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPreservedRegs = r:rwPreservedRegs rw }

default_x86_preserved_reg :: TopLevel ()
default_x86_preserved_reg = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPreservedRegs = [] }

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

set_crucible_timeout :: Integer -> TopLevel ()
set_crucible_timeout t = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwCrucibleTimeout = t }

include_value :: FilePath -> TopLevel ()
include_value file = do
  oldpath <- io $ getCurrentDirectory
  file' <- io $ canonicalizePath file
  io $ setCurrentDirectory (takeDirectory file')
  interpretFile file' False
  io $ setCurrentDirectory oldpath

set_ascii :: Bool -> TopLevel ()
set_ascii b = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { ppOptsAscii = b } }

set_base :: Int -> TopLevel ()
set_base b = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { ppOptsBase = b } }

set_color :: Bool -> TopLevel ()
set_color b = do
  rw <- getTopLevelRW
  opts <- getOptions
  -- Keep color disabled if `--no-color` command-line option is present
  let b' = b && useColor opts
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { ppOptsColor = b' } }

set_min_sharing :: Int -> TopLevel ()
set_min_sharing b = do
  rw <- getTopLevelRW
  putTopLevelRW rw { rwPPOpts = (rwPPOpts rw) { ppOptsMinSharing = b } }

print_value :: Value -> TopLevel ()
print_value (VString s) = printOutLnTop Info (Text.unpack s)
print_value (VTerm t) = do
  sc <- getSharedContext
  cenv <- fmap rwCryptol getTopLevelRW
  let cfg = CEnv.meSolverConfig (CEnv.eModuleEnv cenv)
  unless (null (getAllExts (ttTerm t))) $
    fail "term contains symbolic variables"
  sawopts <- getOptions
  t' <- io $ defaultTypedTerm sawopts sc cfg t
  opts <- fmap rwPPOpts getTopLevelRW
  let opts' = V.defaultPPOpts { V.useAscii = ppOptsAscii opts
                              , V.useBase = ppOptsBase opts
                              }
  evaled_t <- io $ evaluateTypedTerm sc t'
  doc <- io $ V.runEval mempty (V.ppValue V.Concrete opts' evaled_t)
  sawOpts <- getOptions
  io (rethrowEvalError $ printOutLn sawOpts Info $ show $ doc)

print_value v = do
  opts <- fmap rwPPOpts getTopLevelRW
  nenv <- io . scGetNamingEnv =<< getSharedContext
  printOutLnTop Info (showsPrecValue opts nenv 0 v "")

readSchema :: String -> SS.Schema
readSchema str =
  case parseSchema (lexSAW "internal" str) of
    Left err -> error (show err)
    Right schema -> schema

data Primitive
  = Primitive
    { primitiveName :: SS.LName
    , primitiveType :: SS.Schema
    , primitiveLife :: PrimitiveLifecycle
    , primitiveDoc  :: [String]
    , primitiveFn   :: Options -> BuiltinContext -> Value
    }

primitives :: Map SS.LName Primitive
primitives = Map.fromList
  [ prim "return"              "{m, a} a -> m a"
    (pureVal VReturn)
    Current
    [ "Yield a value in a command context. The command"
    , "    x <- return e"
    ,"will result in the same value being bound to 'x' as the command"
    , "    let x = e"
    ]

  , prim "true"                "Bool"
    (pureVal True)
    Current
    [ "A boolean value." ]

  , prim "false"               "Bool"
    (pureVal False)
    Current
    [ "A boolean value." ]

  , prim "for"                 "{m, a, b} [a] -> (a -> m b) -> m [b]"
    (pureVal (VLambda . forValue))
    Current
    [ "Apply the given command in sequence to the given list. Return"
    , "the list containing the result returned by the command at each"
    , "iteration."
    ]

  , prim "run"                 "{a} TopLevel a -> a"
    (funVal1 (id :: TopLevel Value -> TopLevel Value))
    Current
    [ "Evaluate a monadic TopLevel computation to produce a value." ]

  , prim "null"                "{a} [a] -> Bool"
    (pureVal (null :: [Value] -> Bool))
    Current
    [ "Test whether a list value is empty." ]

  , prim "nth"                 "{a} [a] -> Int -> a"
    (funVal2 (nthPrim :: [Value] -> Int -> TopLevel Value))
    Current
    [ "Look up the value at the given list position." ]

  , prim "head"                "{a} [a] -> a"
    (funVal1 (headPrim :: [Value] -> TopLevel Value))
    Current
    [ "Get the first element from the list." ]

  , prim "tail"                "{a} [a] -> [a]"
    (funVal1 (tailPrim :: [Value] -> TopLevel [Value]))
    Current
    [ "Drop the first element from a list." ]

  , prim "concat"              "{a} [a] -> [a] -> [a]"
    (pureVal ((++) :: [Value] -> [Value] -> [Value]))
    Current
    [ "Concatenate two lists to yield a third." ]

  , prim "length"              "{a} [a] -> Int"
    (pureVal (length :: [Value] -> Int))
    Current
    [ "Compute the length of a list." ]

  , prim "str_concat"          "String -> String -> String"
    (pureVal ((++) :: String -> String -> String))
    Current
    [ "Concatenate two strings to yield a third." ]

  , prim "callcc" "{a} ((a -> TopLevel ()) -> TopLevel a) -> TopLevel a"
    (\_ _ -> toplevelCallCC)
    Experimental
    [ "Call-with-current-continuation."
    , ""
    , "This is a highly experimental control operator that can be used"
    , "to capture the surrounding top-level computation as a continuation."
    , "The consequences of delaying and reentering the current continuation"
    , "may be somewhat unpredictable, so use this operator with great caution."
    ]

  , prim "checkpoint"          "TopLevel (() -> TopLevel ())"
    (pureVal checkpoint)
    Experimental
    [ "Capture the current state of the SAW interpreter, and return"
    , "A TopLevel monadic action that, if invoked, will reset the"
    , "state of the interpreter back to to what it was at the"
    , "moment checkpoint was invoked."
    , ""
    , "NOTE that this facility is highly experimental and may not"
    , "be entirely reliable.  It is intended only for proof development"
    , "where it can speed up the process of experimenting with"
    , "mid-proof changes. Finalized proofs should not use this facility."
    ]

  , prim "subshell"            "() -> TopLevel ()"
    (\_ _ -> toplevelSubshell)
    Experimental
    [ "Open an interactive subshell instance in the context where"
    , "'subshell' was called. This works either from within execution"
    , "of a outer shell instance, or from interpreting a file in batch"
    , "mode. Enter the end-of-file character in your terminal (Ctrl^D, usually)"
    , "to exit the subshell and resume execution."
    , ""
    , "This command is especially useful in conjunction with the 'checkpoint'"
    , "and 'callcc' commands, which allow state reset capabilities and the capturing"
    , "of the calling context."
    , ""
    , "Note that, due to the way the SAW script interpreter works, changes made"
    , "to a script file in which the 'subshell' command directly appears will"
    , "NOT affect subsequent execution following a 'checkpoint' or 'callcc' use."
    , "However, changes made in a file that executed via 'include' WILL affect"
    , "restarted executions, as the 'include' command will read and parse the"
    , "file from scratch."
    ]

  , prim "proof_subshell"      "() -> ProofScript ()"
    (\ _ _ -> proofScriptSubshell)
    Experimental
    [ "Open an interactive subshell instance in the context of the current proof."
    , "This allows the user to interactively execute 'ProofScript' tactic commands"
    , "directly on the command line an examine their effects using, e.g., 'print_goal'."
    , "In proof mode, the command prompt will change to 'proof (n)', where the 'n'"
    , "indicates the number of subgoals remaining to proof for the current overall goal."
    , "In this mode, tactic commands applied will only affect the current subgoal."
    , "When a particular subgoal is completed, the next subgoal will automatically become"
    , "the active subgoal. An overall goal is completed when all subgoals are proved"
    , "and the current number of subgoals is 0."
    , ""
    , "Enter the end-of-file character in your terminal (Ctrl^D, usually) to exit the proof"
    , "subshell and resume execution."
    ]

  , prim "proof_checkpoint"      "ProofScript (() -> ProofScript ())"
    (pureVal proof_checkpoint)
    Experimental
    [ "Capture the current state of the proof and return a"
    , "ProofScript monadic action that, if invoked, will reset the"
    , "state of the proof back to to what it was at the"
    , "moment checkpoint was invoked."
    , ""
    , "NOTE that this facility is highly experimental and may not"
    , "be entirely reliable.  It is intended only for proof development"
    , "where it can speed up the process of experimenting with"
    , "mid-proof changes. Finalized proofs should not use this facility."
    ]

  , prim "define"              "String -> Term -> TopLevel Term"
    (pureVal definePrim)
    Current
    [ "Wrap a term with a name that allows its body to be hidden or"
    , "revealed. This can allow any sub-term to be treated as an"
    , "uninterpreted function during proofs."
    ]

  , prim "include"             "String -> TopLevel ()"
    (pureVal include_value)
    Current
    [ "Execute the given SAWScript file." ]

  , prim "enable_deprecated"   "TopLevel ()"
    (bicVal (add_primitives Deprecated))
    Current
    [ "Enable the use of deprecated commands." ]

  , prim "enable_experimental" "TopLevel ()"
    (bicVal (add_primitives Experimental))
    Current
    [ "Enable the use of experimental commands." ]

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
    [ "When verifying proof obligations arising from `llvm_verify` and similar commands,"
    , "generate sequents for the proof obligations instead of a single boolean goal."
    ]

  , prim "disable_sequent_goals" "TopLevel ()"
    (pureVal disable_sequent_goals)
    Experimental
    [ "Restore the default behavior, which is to generate single boolean goals"
    , "for proof obligations arising from verification commands."
    ]

  , prim "enable_safety_proofs" "TopLevel ()"
    (pureVal enable_safety_proofs)
    Experimental
    [ "Restore the default state, where safety obligations"
    , "encountered during symbolic execution are proofed normally."
    ]

  , prim "disable_safety_proofs" "TopLevel ()"
    (pureVal disable_safety_proofs)
    Experimental
    [ "Disable checking of safety obligations encountered during symbolic"
    , "execution. This is unsound! However, it can be useful during"
    , "initial proof construction to focus only on the stated correcness"
    , "specifications."
    ]

  , prim "enable_single_override_special_case" "TopLevel ()"
    (pureVal enable_single_override_special_case)
    Experimental
    [ "Enable special-case handling when there is exactly one override"
    , "that appies at a given call site after structural matching."
    , "This special case handling asserts the override preconditions as separate"
    , "proof goals, instead of combining them into a single one.  In general,"
    , "this may produce more, but simpler, goals than when disabled."
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
    [ "Assume predicate after asserting it during Crucible symbolic simulation." ]

  , prim "disable_crucible_assert_then_assume" "TopLevel ()"
    (pureVal disable_crucible_assert_then_assume)
    Current
    [ "Do not assume predicate after asserting it during Crucible symbolic simulation." ]

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
    [ "Enable relaxed validity checking for memory loads and stores in Crucible." ]

  , prim "disable_lax_loads_and_stores" "TopLevel ()"
    (pureVal disable_lax_loads_and_stores)
    Current
    [ "Disable relaxed validity checking for memory loads and stores in Crucible." ]

  , prim "set_path_sat_solver" "String -> TopLevel ()"
    (pureVal set_path_sat_solver)
    Experimental
    [ "Set the path satisfiablity solver to use.  Accepted values"
    , "currently are 'z3' and 'yices'."
    ]

  , prim "enable_debug_intrinsics" "TopLevel ()"
    (pureVal enable_debug_intrinsics)
    Current
    [ "Enable translating statements using certain llvm.dbg intrinsic functions in Crucible." ]

  , prim "disable_debug_intrinsics" "TopLevel ()"
    (pureVal disable_debug_intrinsics)
    Current
    [ "Disable translating statements using certain llvm.dbg intrinsic functions in Crucible." ]

  , prim "enable_what4_hash_consing" "TopLevel ()"
    (pureVal enable_what4_hash_consing)
    Current
    [ "Enable hash consing for What4 expressions." ]

  , prim "disable_what4_hash_consing" "TopLevel ()"
    (pureVal disable_what4_hash_consing)
    Current
    [ "Disable hash consing for What4 expressions." ]

  , prim "env"                 "TopLevel ()"
    (pureVal envCmd)
    Current
    [ "Print all sawscript values in scope." ]

  , prim "set_ascii"           "Bool -> TopLevel ()"
    (pureVal set_ascii)
    Current
    [ "Select whether to pretty-print arrays of 8-bit numbers as ascii strings." ]

  , prim "set_base"            "Int -> TopLevel ()"
    (pureVal set_base)
    Current
    [ "Set the number base for pretty-printing numeric literals."
    , "Permissible values include 2, 8, 10, and 16." ]

  , prim "set_color"           "Bool -> TopLevel ()"
    (pureVal set_color)
    Current
    [ "Select whether to pretty-print SAWCore terms using color." ]

  , prim "set_min_sharing"     "Int -> TopLevel ()"
    (pureVal set_min_sharing)
    Current
    [ "Set the number times a subterm must be shared for it to be"
    ,  "let-bound in printer output." ]

  , prim "set_timeout"         "Int -> ProofScript ()"
    (pureVal set_timeout)
    Experimental
    [ "Set the timeout, in milliseconds, for any automated prover at the"
    , "end of this proof script. Not that this is simply ignored for provers"
    , "that don't support timeouts, for now."
    ]

  , prim "show"                "{a} a -> String"
    (funVal1 showPrim)
    Current
    [ "Convert the value of the given expression to a string." ]

  , prim "print"               "{a} a -> TopLevel ()"
    (pureVal print_value)
    Current
    [ "Print the value of the given expression." ]

  , prim "print_term"          "Term -> TopLevel ()"
    (pureVal print_term)
    Current
    [ "Pretty-print the given term in SAWCore syntax." ]

  , prim "print_term_depth"    "Int -> Term -> TopLevel ()"
    (pureVal print_term_depth)
    Current
    [ "Pretty-print the given term in SAWCore syntax up to a given depth." ]

  , prim "dump_file_AST"       "String -> TopLevel ()"
    (bicVal $ const $ \opts -> SAWScript.Import.loadFile opts >=> mapM_ print)
    Current
    [ "Dump a pretty representation of the SAWScript AST for a file." ]

  , prim "parser_printer_roundtrip"       "String -> TopLevel ()"
    (bicVal $ const $
      \opts -> SAWScript.Import.loadFile opts >=>
               PP.putDoc . SS.prettyWholeModule)
    Current
    [ "Parses the file as SAWScript and renders the resultant AST back to SAWScript concrete syntax." ]

  , prim "print_type"          "Term -> TopLevel ()"
    (pureVal print_type)
    Current
    [ "Print the type of the given term." ]

  , prim "type"                "Term -> Type"
    (funVal1 term_type)
    Current
    [ "Return the type of the given term." ]

  , prim "show_term"           "Term -> String"
    (funVal1 show_term)
    Current
    [ "Pretty-print the given term in SAWCore syntax, yielding a String." ]

  , prim "check_term"          "Term -> TopLevel ()"
    (pureVal check_term)
    Current
    [ "Type-check the given term, printing an error message if ill-typed." ]

  , prim "check_goal"          "ProofScript ()"
    (pureVal check_goal)
    Current
    [ "Type-check the current proof goal, printing an error message if ill-typed." ]

  , prim "term_size"           "Term -> Int"
    (pureVal scSharedSize)
    Current
    [ "Return the size of the given term in the number of DAG nodes." ]

  , prim "term_tree_size"      "Term -> Int"
    (pureVal scTreeSize)
    Current
    [ "Return the size of the given term in the number of nodes it would"
    , "have if treated as a tree instead of a DAG."
    ]

  , prim "abstract_symbolic"   "Term -> Term"
    (funVal1 abstractSymbolicPrim)
    Current
    [ "Take a term containing symbolic variables of the form returned"
    , "by 'fresh_symbolic' and return a new lambda term in which those"
    , "variables have been replaced by parameter references."
    ]

  , prim "fresh_symbolic"      "String -> Type -> TopLevel Term"
    (pureVal freshSymbolicPrim)
    Current
    [ "Create a fresh symbolic variable of the given type. The given name"
    , "is used only for pretty-printing."
    ]

  , prim "term_apply"          "Term -> [Term] -> Term"
    (funVal2 term_apply)
    Current
    [ "Build a term application node that applies the first term"
    , "(which much be a term representing a function) to given list of arguments."
    ]

  , prim "lambda"              "Term -> Term -> Term"
    (funVal2 lambda)
    Current
    [ "Take a 'fresh_symbolic' variable and another term containing that"
    , "variable, and return a new lambda abstraction over that variable."
    ]

  , prim "lambdas"             "[Term] -> Term -> Term"
    (funVal2 lambdas)
    Current
    [ "Take a list of 'fresh_symbolic' variable and another term containing"
    , "those variables, and return a new lambda abstraction over the list of"
    , "variables."
    ]

  , prim "generalize_term"   "[Term] -> Term -> Term"
    (funVal2 generalize_term)
    Experimental
    [ "Take a list of 'fresh_symbolic' variables and another term containing those"
    , "variables, and return a new Pi generalization over the list of variables."
    ]

  , prim "implies_term"      "Term -> Term -> Term"
    (funVal2 implies_term)
    Experimental
    [ "Given two terms, which must be Prop terms, construct the SAWCore implication"
    , "of those terms."
    ]

  , prim "size_to_term"      "Type -> Term"
    (funVal1 size_to_term)
    Current
    [ "Convert a Cryptol size type into a Term representation."
    ]

  , prim "int_to_term"      "Int -> Term"
    (funVal1 int_to_term)
    Current
    [ "Convert a concrete integer value into an integer term." ]

  , prim "nat_to_term"      "Int -> Term"
    (funVal1 nat_to_term)
    Current
    [ "Convert a non-negative integer value into a natural number term." ]

  , prim "term_theories" "[String] -> Term -> [String]"
    (funVal2 term_theories)
    Experimental
    [ "Given a term of type \'Bool\', compute the SMT theories required"
    , "to reason about this term. The functions (if any) given in the"
    , "first argument will be treated as uninterpreted."
    , ""
    , "If the returned list is empty, the given term represents a problem"
    , "that can be solved purely by boolean SAT reasoning."
    , ""
    , "Note: the given term will be simplified using the What4 backend"
    , "before evaluating what theories are required.  For simple problems,"
    , "this may simplify away some aspects of the problem altogether and may result"
    , "in requiring fewer theories than one might expect."
    ]

  , prim "default_term" "Term -> Term"
    (funVal1 default_typed_term)
    Experimental
    [ "Apply Cryptol defaulting rules to the given term." ]

  , prim "congruence_for" "Term -> TopLevel Term"
    (pureVal congruence_for)
    Experimental
    [ "Given a term representing a (nondependent) function, attempt"
    , "to automatically construct the statement of a congruence lemma"
    , "for the function."
    ]

  , prim "extract_uninterp" "[String] -> [String] -> Term -> TopLevel (Term, [(String,[(Term, Term)])])"
    (pureVal extract_uninterp)
    Experimental
    [ "Given a list of names of functions to treat as uninterpreted and a term, find all occurrences"
    , "of the named functions and extract them."
    , ""
    , "The first argument is the list of \'uninterpreted\' functions to extract."
    , "The second argument is a list of values to treat as opaque; they will not be unfolded during evaluation."
    , "The third argument is the term to extract from."
    , ""
    , "This operation will return a pair, consisting of a rewritten term and a list of replacements."
    , "The rewritten term will have each fully-applied occurrence of the named functions replaced"
    , "by a fresh constant of the return type of the function. The list of replacements consists"
    , "of pairs (one for each named function) giving the name of that function and the replacement"
    , "values for that function. The replacement values are a list of pairs of terms, one for each"
    , "occurence that was replaced.  The first term in each  pair gives the fresh constant appearing"
    , "in the rewritten term.  The second term will be a tuple containing the arguments to the"
    , "replaced function."
    ]

  , prim "sbv_uninterpreted"   "String -> Term -> TopLevel Uninterp"
    (pureVal sbvUninterpreted)
    Deprecated
    [ "Indicate that the given term should be used as the definition of the"
    , "named function when loading an SBV file. This command returns an"
    , "object that can be passed to 'read_sbv'."
    ]

  , prim "is_convertible"  "Term -> Term -> TopLevel Bool"
    (pureVal isConvertiblePrim)
    Current
    [ "Returns true iff the two terms are convertible." ]

  , prim "check_convertible"  "Term -> Term -> TopLevel ()"
    (pureVal checkConvertiblePrim)
    Current
    [ "Check if two terms are convertible and print the result." ]

  , prim "replace"             "Term -> Term -> Term -> TopLevel Term"
    (pureVal replacePrim)
    Current
    [ "'replace x y z' rewrites occurences of term x into y inside the"
    , "term z.  x and y must be closed terms."
    ]

  , prim "hoist_ifs"            "Term -> TopLevel Term"
    (pureVal hoistIfsPrim)
    Current
    [ "Hoist all if-then-else expressions as high as possible." ]

  , prim "read_bytes"          "String -> TopLevel Term"
    (pureVal readBytes)
    Current
    [ "Read binary file as a value of type [n][8]." ]

  , prim "read_sbv"            "String -> [Uninterp] -> TopLevel Term"
    (pureVal readSBV)
    Deprecated
    [ "Read an SBV file produced by Cryptol 1, using the given set of"
    , "overrides for any uninterpreted functions that appear in the file."
    ]

  , prim "load_aig"            "String -> TopLevel AIG"
    (pureVal loadAIGPrim)
    Current
    [ "Read an AIG file in binary AIGER format, yielding an AIG value." ]
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

  , prim "dsec_print"                "Term -> Term -> TopLevel ()"
    (pureVal dsecPrint)
    Current
    [ "Use ABC's 'dsec' command to compare two terms as SAIGs."
    , "The terms must have a type as described in ':help write_saig',"
    , "i.e. of the form '(i, s) -> (o, s)'. Note that nothing is returned:"
    , "you must read the output to see what happened."
    , ""
    , "You must have an 'abc' executable on your PATH to use this command."
    ]

  , prim "bitblast"            "Term -> TopLevel AIG"
    (pureVal bbPrim)
    Current
    [ "Translate a term into an AIG.  The term must be representable as a"
    , "function from a finite number of bits to a finite number of bits."
    ]

  , prim "read_aig"            "String -> TopLevel Term"
    (pureVal readAIGPrim)
    Current
    [ "Read an AIG file in AIGER format and translate to a term." ]

  , prim "read_core"           "String -> TopLevel Term"
    (pureVal readCore)
    Current
    [ "Read a term from a file in the SAWCore external format." ]

  , prim "write_aig"           "String -> Term -> TopLevel ()"
    (pureVal writeAIGPrim)
    Current
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits."
    ]

  , prim "write_aig_external"  "String -> Term -> TopLevel ()"
    (pureVal writeAIGviaVerilog)
    Current
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits. Uses ABC to convert an intermediate"
    , "Verilog file."
    ]

  , prim "write_saig"          "String -> Term -> TopLevel ()"
    (pureVal writeSAIGPrim)
    Current
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits. The type must be of the form"
    , "'(i, s) -> (o, s)' and is interpreted as an '[|i| + |s|] -> [|o| + |s|]'"
    , "AIG with '|s|' latches."
    , ""
    , "Arguments:"
    , "  file to translation to : String"
    , "  function to translate to sequential AIG : Term"
    ]

  , prim "write_saig'"         "String -> Term -> Int -> TopLevel ()"
    (pureVal writeSAIGComputedPrim)
    Current
    [ "Write out a representation of a term in binary AIGER format. The"
    , "term must be representable as a function from a finite number of"
    , "bits to a finite number of bits, '[m] -> [n]'. The int argument,"
    , "'k', must be at most 'min {m, n}', and specifies that the *last* 'k'"
    , "input and output bits are joined as latches."
    , ""
    , "Arguments:"
    , "  file to translation to : String"
    , "  function to translate to sequential AIG : Term"
    , "  number of latches : Int"
    ]

  , prim "write_cnf"           "String -> Term -> TopLevel ()"
    (pureVal write_cnf)
    Current
    [ "Write the given term to the named file in CNF format." ]

  , prim "write_cnf_external"  "String -> Term -> TopLevel ()"
    (pureVal write_cnf_external)
    Current
    [ "Write the given term to the named file in CNF format." ]

  , prim "write_smtlib2"       "String -> Term -> TopLevel ()"
    (pureVal write_smtlib2)
    Current
    [ "Write the given term to the named file in SMT-Lib version 2 format." ]

  , prim "write_smtlib2_w4"    "String -> Term -> TopLevel ()"
    (pureVal write_smtlib2_w4)
    Current
    [ "Write the given term to the named file in SMT-Lib version 2 format,"
    , "using the What4 backend instead of the SBV backend."
    ]

  , prim "write_core"          "String -> Term -> TopLevel ()"
    (pureVal writeCore)
    Current
    [ "Write out a representation of a term in SAWCore external format." ]

  , prim "write_verilog"       "String -> Term -> TopLevel ()"
    (scVal writeVerilog)
    Experimental
    [ "Write out a representation of a term in Verilog format." ]

  , prim "write_coq_term" "String -> [(String, String)] -> [String] -> String -> Term -> TopLevel ()"
    (pureVal writeCoqTerm)
    Experimental
    [ "Write out a representation of a term in Gallina syntax for Coq."
    , "The first argument is the name to use in a Definition."
    , "The second argument is a list of pairs of notation substitutions:"
    , "the operator on the left will be replaced with the identifier on"
    , "the right, as we do not support notations on the Coq side."
    , "The third argument is a list of identifiers to skip translating."
    , "The fourth argument is the name of the file to output into,"
    , "use an empty string to output to standard output."
    , "The fifth argument is the term to export."
    ]

  , prim "write_coq_cryptol_module" "String -> String -> [(String, String)] -> [String] -> TopLevel ()"
    (pureVal writeCoqCryptolModule)
    Experimental
    [ "Write out a representation of a Cryptol module in Gallina syntax for"
    , "Coq."
    , "The first argument is the file containing the module to export."
    , "The second argument is the name of the file to output into,"
    , "use an empty string to output to standard output."
    , "The third argument is a list of pairs of notation substitutions:"
    , "the operator on the left will be replaced with the identifier on"
    , "the right, as we do not support notations on the Coq side."
    , "The fourth argument is a list of identifiers to skip translating."
    ]

  , prim "write_coq_sawcore_prelude" "String -> [(String, String)] -> [String] -> TopLevel ()"
    (pureVal writeCoqSAWCorePrelude)
    Experimental
    [ "Write out a representation of the SAW Core prelude in Gallina syntax for"
    , "Coq."
    , "The first argument is the name of the file to output into,"
    , "use an empty string to output to standard output."
    , "The second argument is a list of pairs of notation substitutions:"
    , "the operator on the left will be replaced with the identifier on"
    , "the right, as we do not support notations on the Coq side."
    , "The third argument is a list of identifiers to skip translating."
    ]

  , prim "write_coq_cryptol_primitives_for_sawcore" "String -> [(String, String)] -> [String] -> TopLevel ()"
    (pureVal writeCoqCryptolPrimitivesForSAWCore)
    Experimental
    [ "Write out a representation of cryptol-saw-core's Cryptol.sawcore in"
    , "Gallina syntax for Coq."
    , "The first argument is the name of the file to output into,"
    , "use an empty string to output to standard output."
    , "The second argument is a list of pairs of notation substitutions:"
    , "the operator on the left will be replaced with the identifier on"
    , "the right, as we do not support notations on the Coq side."
    , "The third argument is a list of identifiers to skip translating."
    ]

  , prim "offline_coq" "String -> ProofScript ()"
    (pureVal offline_coq)
    Experimental
    [ "Write out a representation of the current goal in Gallina syntax"
    , "(for Coq). The argument is a prefix to use for file names."
    ]

  , prim "auto_match" "String -> String -> TopLevel ()"
    (pureVal (autoMatch stmtInterpreter :: FilePath -> FilePath -> TopLevel ()))
    Current
    [ "Interactively decides how to align two modules of potentially heterogeneous"
    , "language and prints the result."
    ]

  , prim "prove"               "ProofScript () -> Term -> TopLevel ProofResult"
    (pureVal provePrim)
    Current
    [ "Use the given proof script to attempt to prove that a term is valid"
    , "(true for all inputs). Returns a proof result that can be analyzed"
    , "with 'caseProofResult' to determine whether it represents a successful"
    , "proof or a counter-example."
    ]

  , prim "prove_print"         "ProofScript () -> Term -> TopLevel Theorem"
    (pureVal provePrintPrim)
    Current
    [ "Use the given proof script to attempt to prove that a term is valid"
    , "(true for all inputs). Returns a Theorem if successful, and aborts"
    , "if unsuccessful."
    ]

  , prim "prove_by_bv_induction"  "ProofScript () -> Term -> TopLevel Theorem"
    (pureVal proveByBVInduction)
    Experimental
    [ "Attempt to prove a fact by induction on the less-than order on bitvectors."
    , "The given term is expected to be a function of one or more arguments"
    , "which returns a tuple containing two values: first, a bitvector expression"
    , "(which will be the expression we perform induction on), and second, a boolean value"
    , "defining the theorem to prove."
    , ""
    , "This command will attempt to prove the theorem expressed in the second"
    , "element of the tuple by induction. The goal presented to the user-provided"
    , "tactic will ask to prove the stated goal and will be provided with an induction"
    , "hypothesis which states that the goal holds for all values of the varibles"
    , "where the expression given in the first element of the tuple has decreased."
    ]

  , prim "prove_extcore"         "ProofScript () -> Term -> TopLevel Theorem"
    (pureVal provePropPrim)
    Current
    [ "Use the given proof script to attempt to prove that a term representing"
    , "a proposition is valid. For example, this is useful for proving a goal"
    , "obtained with 'offline_extcore' or 'parse_core'. Returns a Theorem if"
    , "successful, and aborts if unsuccessful."
    ]

  , prim "sat"                 "ProofScript () -> Term -> TopLevel SatResult"
    (pureVal satPrim)
    Current
    [ "Use the given proof script to attempt to prove that a term is"
    , "satisfiable (is true for some input). Returns a proof result that can"
    , "be analyzed with 'caseSatResult' to determine whether it represents"
    , "a satisfying assignment or an indication of unsatisfiability."
    ]

  , prim "sat_print"           "ProofScript () -> Term -> TopLevel ()"
    (pureVal satPrintPrim)
    Current
    [ "Use the given proof script to attempt to prove that a term is"
    , "satisfiable (true for any input). Returns nothing if successful, and"
    , "aborts if unsuccessful."
    ]

  , prim "qc_print"            "Int -> Term -> TopLevel ()"
    (\a -> scVal (quickCheckPrintPrim a) a)
    Current
    [ "Quick Check a term by applying it to a sequence of random inputs"
    , "and print the results. The 'Int' arg specifies how many tests to run."
    ]

  , prim "codegen"             "String -> [String] -> String -> Term -> TopLevel ()"
    (scVal codegenSBV)
    Current
    [ "Generate straight-line C code for the given term using SBV."
    , ""
    , "First argument is directory path (\"\" for stdout) for generating files."
    , "Second argument is the list of function names to leave uninterpreted."
    , "Third argument is C function name."
    , "Fourth argument is the term to generate code for. It must be a"
    , "first-order function whose arguments and result are all of type"
    , "Bit, [8], [16], [32], or [64]."
    ]

  , prim "unfolding"           "[String] -> ProofScript ()"
    (pureVal unfoldGoal)
    Current
    [ "Unfold the named subterm(s) within the current goal." ]

  , prim "simplify"            "Simpset -> ProofScript ()"
    (pureVal simplifyGoal)
    Current
    [ "Apply the given simplifier rule set to the current goal." ]

  , prim "simplify_local"       "[Int] -> Simpset -> ProofScript ()"
    (pureVal simplifyGoalWithLocals)
    Current
    [ "Apply the given simplifier rule set to the current goal."
    , "Also, use the given numbered hypotheses as rewrites."
    ]

  , prim "unfocus"        "ProofScript ()"
    (pureVal unfocus)
    Experimental
    [ "Remove any sequent focus point." ]

  , prim "focus_concl"      "Int -> ProofScript ()"
    (pureVal focus_concl)
    Experimental
    [ "Focus on the numbered conclusion within a sequent. This will fail if there are"
    , "not enough conclusions."
    ]

  , prim "focus_hyp"       "Int -> ProofScript ()"
    (pureVal focus_hyp)
    Experimental
    [ "Focus on the numbered conclusion with a sequent.  This will fail if there are"
    , "enough hypotheses."
    ]

  , prim "normalize_sequent" "ProofScript ()"
    (pureVal normalize_sequent)
    Experimental
    [ "Normalize the current goal sequent by applying reversable sequent calculus rules."
    , "The resulting sequent will be unfocused."
    ]

  , prim "goal_cut" "Term -> ProofScript ()"
    (pureVal goal_cut)
    Experimental
    [ "Given a term provided by the user (which must be a boolean expression"
    , "or a Prop) the current goal is split into two subgoals. In the first subgoal,"
    , "the given proposition is assumed as a new hypothesis. In the second subgoal,"
    , "the given proposition is a new focused, conclusion. This implements the"
    , "usual cut rule of sequent calculus."
    ]

  , prim "retain_hyps" "[Int] -> ProofScript ()"
    (pureVal retain_hyps)
    Experimental
    [ "Remove all hypotheses from the current sequent other than the ones listed." ]

  , prim "delete_hyps" "[Int] -> ProofScript ()"
    (pureVal delete_hyps)
    Experimental
    [ "Remove the numbered hypotheses from the current sequent." ]

  , prim "retain_concl" "[Int] -> ProofScript ()"
    (pureVal retain_concl)
    Experimental
    [ "Remove all conclusions from the current sequent other than the ones listed." ]

  , prim "delete_concl" "[Int] -> ProofScript ()"
    (pureVal delete_concl)
    Experimental
    [ "Remove the numbered conclusions from the current sequent." ]

  , prim "hoist_ifs_in_goal"            "ProofScript ()"
    (pureVal hoistIfsInGoalPrim)
    Experimental
    [ "Hoist ifs in the current proof goal." ]

  , prim "normalize_term"      "Term -> Term"
    (funVal1 normalize_term)
    Experimental
    [ "Normalize the given term by performing evaluation in SAWCore." ]

  , prim "normalize_term_opaque" "[String] -> Term -> Term"
    (funVal2 normalize_term_opaque)
    Experimental
    [ "Normalize the given term by performing evaluation in SAWCore."
    , "The named values will be treated opaquely and not unfolded during evaluation."
    ]

  , prim "goal_normalize"  "[String] -> ProofScript ()"
    (pureVal goal_normalize)
    Experimental
    [ "Evaluate the current proof goal by performing evaluation in SAWCore."
    , "The currently-focused term will be evaluated.  If the sequent is unfocused"
    , "all terms will be evaluated. The given names will be treated as uninterpreted."
    ]

  , prim "goal_eval"           "ProofScript ()"
    (pureVal (goal_eval []))
    Current
    [ "Evaluate the proof goal to a first-order combination of primitives." ]

  , prim "goal_eval_unint"     "[String] -> ProofScript ()"
    (pureVal goal_eval)
    Current
    [ "Evaluate the proof goal to a first-order combination of primitives."
    , "Leave the given names as uninterpreted." ]

  , prim "beta_reduce_goal"    "ProofScript ()"
    (pureVal beta_reduce_goal)
    Current
    [ "Reduce the current goal to beta-normal form." ]

  , prim "goal_apply"          "Theorem -> ProofScript ()"
    (pureVal goal_apply)
    Experimental
    [ "Apply an introduction rule to the current goal. Depending on the"
    , "rule, this will result in zero or more new subgoals."
    ]

  , prim "goal_exact"          "Term -> ProofScript ()"
    (pureVal goal_exact)
    Experimental
    [ "Prove the current goal by giving an explicit proof term."
    , "This will succeed if the type of the given term matches the current goal."
    ]

  , prim "goal_intro_hyp"      "ProofScript ()"
    (pureVal goal_intro_hyp)
    Experimental
    [ "When focused on a conclusion that represents an implication,"
    , "simplify the conclusion by removing the implication and introducing"
    , "a new sequent hypothesis instead."
    ]

  , prim "goal_intro_hyps"     "Int -> ProofScript ()"
    (pureVal goal_intro_hyps)
    Experimental
    [ "When focused on a conclusion that represents an implication,"
    , "simplify the conclusion by removing the implication and introducing"
    , "a new sequent hypothesis instead. The given number indicates how many"
    , "hypotheses to introduce."
    ]

  , prim "goal_revert_hyp"     "Int -> ProofScript ()"
    (pureVal goal_revert_hyp)
    Experimental
    [ "When focused on a conclusion, weaken the focused conclusion"
    , "by introducing an implication using the numbered sequent hypothesis."
    , "This is essentially the reverse of 'gooal_intro_hyps'."
    ]

  , prim "goal_insert"         "Theorem -> ProofScript ()"
    (pureVal goal_insert)
    Experimental
    [ "Insert a Theorem as a new hypothesis in the current proof goal."
    ]

  , prim "goal_insert_and_specialize"  "Theorem -> [Term] -> ProofScript ()"
    (pureVal goal_insert_and_specialize)
    Experimental
    [ "Insert a Theorem as a new hypothesis in the current proof goal, after"
    , "specializing some of its universal quantifiers using the given terms."
    ]

  , prim "goal_apply_hyp"      "Int -> ProofScript ()"
    (pureVal goal_apply_hyp)
    Experimental
    [ "Apply the numbered local hypothesis to the focused conclusion." ]

  , prim "goal_specialize_hyp" "[Term] -> ProofScript ()"
    (pureVal goal_specialize_hyp)
    Experimental
    [ "Specialize the focused local hypothesis by supplying the values"
    , "for universal quantifiers. A new specialized hypothesis will be"
    , "added to the sequent."
    ]

  , prim "goal_intro"          "String -> ProofScript Term"
    (pureVal goal_intro)
    Experimental
    [ "Introduce a quantified variable in the current proof goal, returning"
    , "the variable as a Term."
    ]
  , prim "goal_when"           "String -> ProofScript () -> ProofScript ()"
    (pureVal goal_when)
    Experimental
    [ "Run the given proof script only when the goal name contains"
    , "the given string."
    ]
  , prim "goal_has_tags"      "[String] -> ProofScript Bool"
    (pureVal goal_has_tags)
    Experimental
    [ "Returns true if the current goal is tagged with all the tags"
    , "in the given list. This function returns true for all goals"
    , "when given an empty list. Tags may be added to goals using"
    , "'llvm_setup_with_tag' and similar operations in the specification"
    , "setup phase."
    ]
  , prim "goal_has_some_tag"  "[String] -> ProofScript Bool"
    (pureVal goal_has_some_tag)
    Experimental
    [ "Returns true if the current goal is tagged with any the tags"
    , "in the given list. This function returns false for all goals"
    , "when given an empty list. Tags may be added to goals using"
    , "'llvm_setup_with_tag' and similar operations in the specification"
    , "setup phase."
    ]
  , prim "goal_num_ite"       "{a} Int -> ProofScript a -> ProofScript a -> ProofScript a"
    (pureVal goal_num_ite)
    Experimental
    [ "If the goal number is the given number, runs the first script."
    , "Otherwise runs the second script" ]
  , prim "goal_num_when"       "Int -> ProofScript () -> ProofScript ()"
    (pureVal goal_num_when)
    Experimental
    [ "Run the given proof script only when the goal number is the"
    , "the given number."
    ]
  , prim "print_goal"          "ProofScript ()"
    (pureVal print_goal)
    Current
    [ "Print the current goal that a proof script is attempting to prove." ]
  , prim "write_goal" "String -> ProofScript ()"
    (pureVal write_goal)
    Current
    [ "Write the current goal that a proof script is attempting to prove"
    , "into the named file."
    ]
  , prim "print_goal_summary" "ProofScript ()"
    (pureVal print_goal_summary)
    Current
    [ "Print the number and description of the goal that a proof script"
    , "is attempting to prove."
    ]
  , prim "print_focus" "ProofScript ()"
    (pureVal print_focus)
    Experimental
    [ "Print just the focused part of the current goal."
    , "Prints a message without failing if there is no current focus."
    ]

  , prim "goal_num" "ProofScript Int"
    (pureVal goal_num)
    Current
    [ "Returns the number of the current proof goal."
    ]
  , prim "print_goal_depth"    "Int -> ProofScript ()"
    (pureVal print_goal_depth)
    Current
    [ "Print the current goal that a proof script is attempting to prove,"
    , "limited to a maximum depth."
    ]
  , prim "print_goal_consts"   "ProofScript ()"
    (pureVal printGoalConsts)
    Current
    [ "Print the list of unfoldable constants in the current proof goal."
    ]
  , prim "print_goal_size"     "ProofScript ()"
    (pureVal printGoalSize)
    Current
    [ "Print the size of the goal in terms of both the number of DAG nodes"
    , "and the number of nodes it would have if represented as a tree."
    ]

  , prim "assume_valid"        "ProofScript ()"
    (pureVal assumeValid)
    Current
    [ "Assume the current goal is valid, completing the proof."
    , "Prefer to use 'admit', this command will eventually be removed."
    ]

  , prim "assume_unsat"        "ProofScript ()"
    (pureVal assumeUnsat)
    Current
    [ "Assume the current goal is unsatisfiable, completing the proof."
    , "Prefer to use 'admit', this command will eventually be removed."
    ]

  , prim "admit"               "String -> ProofScript ()"
    (pureVal admitProof)
    Current
    [ "Admit the current goal, completing the proof by assumption."
    , "The string argument provides a description of why the user"
    , "had decided to admit this goal."
    ]

  , prim "quickcheck"          "Int -> ProofScript ()"
    (scVal quickcheckGoal)
    Current
    [ "Quick Check the current goal by applying it to a sequence of random"
    , "inputs. Fail the proof script if the goal returns 'False' for any"
    , "of these inputs."
    ]

  , prim "abc"                 "ProofScript ()"
    (pureVal w4_abc_aiger)
    Current
    [ "Use the ABC theorem prover to prove the current goal." ]

  , prim "sbv_abc"             "ProofScript ()"
    (pureVal proveABC_SBV)
    Current
    [ "Use the ABC theorem prover to prove the current goal." ]

  , prim "boolector"           "ProofScript ()"
    (pureVal proveBoolector)
    Current
    [ "Use the Boolector theorem prover to prove the current goal." ]

  , prim "cvc4"                "ProofScript ()"
    (pureVal proveCVC4)
    Current
    [ "Use the CVC4 theorem prover to prove the current goal." ]

  , prim "z3"                  "ProofScript ()"
    (pureVal proveZ3)
    Current
    [ "Use the Z3 theorem prover to prove the current goal." ]

  , prim "mathsat"             "ProofScript ()"
    (pureVal proveMathSAT)
    Current
    [ "Use the MathSAT theorem prover to prove the current goal." ]

  , prim "yices"               "ProofScript ()"
    (pureVal proveYices)
    Current
    [ "Use the Yices theorem prover to prove the current goal." ]

  , prim "unint_z3"            "[String] -> ProofScript ()"
    (pureVal proveUnintZ3)
    Current
    [ "Use the Z3 theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "unint_cvc4"            "[String] -> ProofScript ()"
    (pureVal proveUnintCVC4)
    Current
    [ "Use the CVC4 theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "unint_yices"           "[String] -> ProofScript ()"
    (pureVal proveUnintYices)
    Current
    [ "Use the Yices theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "sbv_boolector"       "ProofScript ()"
    (pureVal proveBoolector)
    Current
    [ "Use the Boolector theorem prover to prove the current goal." ]

  , prim "sbv_cvc4"            "ProofScript ()"
    (pureVal proveCVC4)
    Current
    [ "Use the CVC4 theorem prover to prove the current goal." ]

  , prim "sbv_z3"              "ProofScript ()"
    (pureVal proveZ3)
    Current
    [ "Use the Z3 theorem prover to prove the current goal." ]

  , prim "sbv_mathsat"         "ProofScript ()"
    (pureVal proveMathSAT)
    Current
    [ "Use the MathSAT theorem prover to prove the current goal." ]

  , prim "sbv_yices"           "ProofScript ()"
    (pureVal proveYices)
    Current
    [ "Use the Yices theorem prover to prove the current goal." ]

  , prim "sbv_unint_z3"        "[String] -> ProofScript ()"
    (pureVal proveUnintZ3)
    Current
    [ "Use the Z3 theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "sbv_unint_cvc4"        "[String] -> ProofScript ()"
    (pureVal proveUnintCVC4)
    Current
    [ "Use the CVC4 theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "sbv_unint_yices"       "[String] -> ProofScript ()"
    (pureVal proveUnintYices)
    Current
    [ "Use the Yices theorem prover to prove the current goal. Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "offline_aig"         "String -> ProofScript ()"
    (pureVal offline_aig)
    Current
    [ "Write the current goal to the given file in AIGER format." ]

  , prim "offline_aig_external" "String -> ProofScript ()"
    (pureVal offline_aig_external)
    Current
    [ "Write the current goal to the given file in AIGER format."
    , "Uses ABC and an intermediate Verilog file."
    ]

  , prim "offline_cnf"         "String -> ProofScript ()"
    (pureVal offline_cnf)
    Current
    [ "Write the current goal to the given file in CNF format." ]

  , prim "offline_cnf_external" "String -> ProofScript ()"
    (pureVal offline_cnf_external)
    Current
    [ "Write the current goal to the given file in CNF format."
    , "Uses ABC and an intermediate Verilog file."
    ]

  , prim "offline_extcore"     "String -> ProofScript ()"
    (pureVal offline_extcore)
    Current
    [ "Write the current goal to the given file in SAWCore format." ]

  , prim "offline_smtlib2"     "String -> ProofScript ()"
    (pureVal offline_smtlib2)
    Current
    [ "Write the current goal to the given file in SMT-Lib2 format." ]

  , prim "w4_offline_smtlib2"  "String -> ProofScript ()"
    (pureVal w4_offline_smtlib2)
    Current
    [ "Write the current goal to the given file in SMT-Lib2 format." ]

  , prim "offline_unint_smtlib2"  "[String] -> String -> ProofScript ()"
    (pureVal offline_unint_smtlib2)
    Current
    [ "Write the current goal to the given file in SMT-Lib2 format,"
    , "leaving the listed functions uninterpreted."
    ]

  , prim "offline_verilog"        "String -> ProofScript ()"
    (pureVal offline_verilog)
    Experimental
    [ "Write the current goal to the given file in Verilog format." ]

  , prim "external_cnf_solver" "String -> [String] -> ProofScript ()"
    (pureVal (satExternal True))
    Current
    [ "Use an external SAT solver supporting CNF to prove the current goal."
    , "The first argument is the executable name of the solver, and the"
    , "second is the list of arguments to pass to the solver. The string '%f'"
    , "anywhere in the argument list will be replaced with the name of the"
    , "temporary file holding the CNF version of the formula."]

  , prim "external_aig_solver" "String -> [String] -> ProofScript ()"
    (pureVal (satExternal False))
    Current
    [ "Use an external SAT solver supporting AIG to prove the current goal."
    , "The first argument is the executable name of the solver, and the"
    , "second is the list of arguments to pass to the solver. The string '%f'"
    , "anywhere in the argument list will be replaced with the name of the"
    , "temporary file holding the AIG version of the formula."]

  , prim "rme"                 "ProofScript ()"
    (pureVal proveRME)
    Current
    [ "Prove the current goal by expansion to Reed-Muller Normal Form." ]

  , prim "trivial"             "ProofScript ()"
    (pureVal trivial)
    Current
    [ "Succeeds if the goal is trivial. This tactic recognizes goals"
    , "that are instances of reflexivity, possibly with quantified variables."
    , "In particular, it will prove goals of the form 'EqTrue x' when 'x' reduces"
    , "to the constant value 'True'."
    ]

  , prim "w4"                  "ProofScript ()"
    (pureVal w4_z3)
    Current
    [ "Prove the current goal using What4 (Z3 backend)." ]

  , prim "w4_unint_z3"         "[String] -> ProofScript ()"
    (pureVal w4_unint_z3)
    Current
    [ "Prove the current goal using What4 (Z3 backend). Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "w4_unint_z3_using" "String -> [String] -> ProofScript ()"
    (pureVal w4_unint_z3_using)
    Current
    [ "Prove the current goal using What4 (Z3 backend) using the given"
    , "Z3 tactic. Leave the given list of names as uninterpreted."
    ]

  , prim "w4_unint_yices"         "[String] -> ProofScript ()"
    (pureVal w4_unint_yices)
    Current
    [ "Prove the current goal using What4 (Yices backend). Leave the"
    , "given list of names as uninterpreted."
    ]

  , prim "w4_unint_cvc4"         "[String] -> ProofScript ()"
    (pureVal w4_unint_cvc4)
    Current
    [ "Prove the current goal using What4 (CVC4 backend). Leave the"
    , "given list of names as uninterpreted."
    ]

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

  , prim "offline_w4_unint_z3"    "[String] -> String -> ProofScript ()"
    (pureVal offline_w4_unint_z3)
    Current
    [ "Write the current goal to the given file using What4 (Z3 backend) in"
    ," SMT-Lib2 format. Leave the given list of names as uninterpreted."
    ]

  , prim "offline_w4_unint_yices" "[String] -> String -> ProofScript ()"
    (pureVal offline_w4_unint_yices)
    Current
    [ "Write the current goal to the given file using What4 (Yices backend) in"
    ," SMT-Lib2 format. Leave the given list of names as uninterpreted."
    ]

  , prim "offline_w4_unint_cvc4"  "[String] -> String -> ProofScript ()"
    (pureVal offline_w4_unint_cvc4)
    Current
    [ "Write the current goal to the given file using What4 (CVC4 backend) in"
    ," SMT-Lib2 format. Leave the given list of names as uninterpreted."
    ]

  , prim "split_goal"          "ProofScript ()"
    (pureVal split_goal)
    Experimental
    [ "Split a goal of the form 'Prelude.and prop1 prop2' into two separate"
    ,  "goals 'prop1' and 'prop2'." ]

  , prim "empty_ss"            "Simpset"
    (pureVal (emptySimpset :: SAWSimpset))
    Current
    [ "The empty simplification rule set, containing no rules." ]

  , prim "cryptol_ss"          "() -> Simpset"
    (funVal1 (\() -> cryptolSimpset))
    Current
    [ "A set of simplification rules that will expand definitions from the"
    , "Cryptol module."
    ]

  , prim "add_prelude_eqs"     "[String] -> Simpset -> Simpset"
    (funVal2 addPreludeEqs)
    Current
    [ "Add the named equality rules from the Prelude module to the given"
    , "simplification rule set."
    ]

  , prim "add_cryptol_eqs"     "[String] -> Simpset -> Simpset"
    (funVal2 addCryptolEqs)
    Current
    [ "Add the named equality rules from the Cryptol module to the given"
    , "simplification rule set."
    ]

  , prim "add_prelude_defs"    "[String] -> Simpset -> Simpset"
    (funVal2 add_prelude_defs)
    Current
    [ "Add the named definitions from the Prelude module to the given"
    , "simplification rule set."
    ]

  , prim "add_cryptol_defs"    "[String] -> Simpset -> Simpset"
    (funVal2 add_cryptol_defs)
    Current
    [ "Add the named definitions from the Cryptol module to the given"
    , "simplification rule set."
    ]

  , prim "basic_ss"            "Simpset"
    (bicVal $ \bic _ -> toValue $ biBasicSS bic)
    Current
    [ "A basic rewriting simplification set containing some boolean identities"
    , "and conversions relating to bitvectors, natural numbers, and vectors."
    ]

  , prim "addsimp"             "Theorem -> Simpset -> Simpset"
    (funVal2 addsimp)
    Current
    [ "Add a proved equality theorem to a given simplification rule set." ]

  , prim "addsimp_shallow"    "Theorem -> Simpset -> Simpset"
    (funVal2 addsimp_shallow)
    Current
    [ "Add a proved equality theorem to a given simplification rule set."
    , "The rule is treated as a 'shallow' rewrite, which means that further"
    , "rewrite rules will not be applied to the result if this rule fires."
    ]

  , prim "addsimps"            "[Theorem] -> Simpset -> Simpset"
    (funVal2 addsimps)
    Current
    [ "Add proved equality theorems to a given simplification rule set." ]

  , prim "addsimp'"            "Term -> Simpset -> Simpset"
    (funVal2 addsimp')
    Deprecated
    [ "Add an arbitrary equality term to a given simplification rule set."
    , "Use `admit` or `core_axiom` and `addsimp` instead."
    ]

  , prim "addsimps'"           "[Term] -> Simpset -> Simpset"
    (funVal2 addsimps')
    Deprecated
    [ "Add arbitrary equality terms to a given simplification rule set."
    , "Use `admit` or `core_axiom` and `addsimps` instead."
    ]

  , prim "rewrite"             "Simpset -> Term -> Term"
    (funVal2 rewritePrim)
    Current
    [ "Rewrite a term using a specific simplification rule set, returning"
    , "the rewritten term."
    ]

  , prim "unfold_term"         "[String] -> Term -> Term"
    (funVal2 unfold_term)
    Current
    [ "Unfold the definitions of the specified constants in the given term." ]

  , prim "beta_reduce_term"    "Term -> Term"
    (funVal1 beta_reduce_term)
    Current
    [ "Reduce the given term to beta-normal form." ]

  , prim "cryptol_load"        "String -> TopLevel CryptolModule"
    (pureVal (cryptol_load BS.readFile))
    Current
    [ "Load the given file as a Cryptol module." ]

  , prim "cryptol_extract"     "CryptolModule -> String -> TopLevel Term"
    (pureVal CEnv.lookupCryptolModule)
    Current
    [ "Load a single definition from a Cryptol module and translate it into"
    , "a 'Term'."
    ]

  , prim "cryptol_prims"       "() -> CryptolModule"
    (funVal1 (\() -> cryptol_prims))
    Current
    [ "Return a Cryptol module containing extra primitive operations,"
    , "including array updates, truncate/extend, and signed comparisons."
    ]

  , prim "cryptol_add_path"    "String -> TopLevel ()"
    (pureVal cryptol_add_path)
    Current
    [ "Add a directory to the Cryptol search path. The Cryptol file loader"
    , "will look in this directory when following `import` statements in"
    , "Cryptol source files."
    ]

  , prim "cryptol_add_prim"    "String -> String -> Term -> TopLevel ()"
    (pureVal cryptol_add_prim)
    Experimental
    [ "cryptol_add_prim mod nm trm sets the translation of Cryptol primitive"
    , "nm in module mod to trm"
    ]

  , prim "cryptol_add_prim_type"    "String -> String -> Term -> TopLevel ()"
    (pureVal cryptol_add_prim_type)
    Experimental
    [ "cryptol_add_prim_type mod nm tp sets the translation of Cryptol"
    , "primitive type nm in module mod to tp"
    ]

  -- Java stuff

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
    [ "The Java type of arrays of a fixed number of elements of the given"
    , "type."
    ]

  , prim "java_class"          "String -> JavaType"
    (pureVal JavaClass)
    Current
    [ "The Java type corresponding to the named class." ]

  , prim "java_load_class"     "String -> TopLevel JavaClass"
    (pureVal CJ.loadJavaClass)
    Current
    [ "Load the named Java class and return a handle to it." ]

  , prim "jvm_extract"  "JavaClass -> String -> TopLevel Term"
    (pureVal CJ.jvm_extract)
    Current
    [ "Translate a Java method directly to a Term. The parameters of the"
    , "Term will be the parameters of the Java method, and the return"
    , "value will be the return value of the method. Only methods with"
    , "scalar argument and return types are currently supported."
    ]
  , prim "crucible_java_extract"  "JavaClass -> String -> TopLevel Term"
    (pureVal CJ.jvm_extract)
    Current
    [ "Legacy alternative name for `jvm_extract`."
    ]

  , prim "llvm_sizeof"         "LLVMModule -> LLVMType -> Int"
    (funVal2 llvm_sizeof)
    Current
    [ "In the context of the given LLVM module, compute the size of the"
    , "given LLVM type in bytes. The module determines details of struct"
    , "layout and the meaning of type aliases." ]

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
    [ "The type of an LLVM alias for the given name. Often times, this is used"
    , "to alias a struct type."
    ]
  , prim "llvm_struct"         "String -> LLVMType"
    (pureVal llvm_alias)
    Current
    [ "Legacy alternative name for `llvm_alias`."
    ]

  , prim "llvm_pointer"        "LLVMType -> LLVMType"
    (pureVal llvm_pointer)
    Current
    [ "The type of an LLVM pointer that points to the given type."
    ]

  , prim "llvm_load_module"    "String -> TopLevel LLVMModule"
    (pureVal llvm_load_module)
    Current
    [ "Load an LLVM bitcode file and return a handle to it." ]

  , prim "module_skeleton" "LLVMModule -> TopLevel ModuleSkeleton"
    (pureVal module_skeleton)
    Experimental
    [ "Given a handle to an LLVM module, return a skeleton for that module."
    ]

  , prim "function_skeleton" "ModuleSkeleton -> String -> TopLevel FunctionSkeleton"
    (pureVal function_skeleton)
    Experimental
    [ "Given a module skeleton and a function name, return the corresponding"
    , "function skeleton."
    ]

  , prim "skeleton_resize_arg_index" "FunctionSkeleton -> Int -> Int -> Bool -> TopLevel FunctionSkeleton"
    (pureVal skeleton_resize_arg_index)
    Experimental
    [ "Given a function skeleton, argument index, array length, and whether or"
    , "not that argument is initialized, return a new function skeleton where"
    , "the assumed length/initialization of the given argument is updated."
    ]

  , prim "skeleton_resize_arg" "FunctionSkeleton -> String -> Int -> Bool -> TopLevel FunctionSkeleton"
    (pureVal skeleton_resize_arg)
    Experimental
    [ "Given a function skeleton, argument name, array length, and whether or"
    , "not that argument is initialized, return a new function skeleton where"
    , "the assumed length/initialization of the given argument is updated."
    ]

  , prim "skeleton_guess_arg_sizes" "ModuleSkeleton -> LLVMModule -> [(String, [FunctionProfile])] -> TopLevel ModuleSkeleton"
    (pureVal skeleton_guess_arg_sizes)
    Experimental
    [ "Update the sizes of all arguments of the given module skeleton using"
    , "information obtained from 'crucible_llvm_array_size_profile'."
    ]

  , prim "skeleton_globals_pre" "ModuleSkeleton -> LLVMSetup ()"
    (pureVal skeleton_globals_pre)
    Experimental
    [ "Allocate and initialize mutable globals from the given module skeleton."
    ]

  , prim "skeleton_globals_post" "ModuleSkeleton -> LLVMSetup ()"
    (pureVal skeleton_globals_post)
    Experimental
    [ "Assert that all mutable globals from the given module skeleton are unchanged."
    ]

  , prim "skeleton_prestate" "FunctionSkeleton -> LLVMSetup SkeletonState"
    (pureVal skeleton_prestate)
    Experimental
    [ "Allocate and initialize the arguments of the given function skeleton."
    , "Return a 'SkeletonState' from which those arguments can be retrieved,"
    , "so that preconditions can be imposed."
    ]

  , prim "skeleton_poststate" "FunctionSkeleton -> SkeletonState -> LLVMSetup SkeletonState"
    (pureVal skeleton_poststate)
    Experimental
    [ "Assert that pointer arguments of the given function skeleton remain"
    , "initialized. Return a 'SkeletonState' from which those arguments can"
    , "be retrieved, so that postconditions can be imposed."
    ]

  , prim "skeleton_arg_index" "SkeletonState -> Int -> LLVMSetup Term"
    (pureVal skeleton_arg_index)
    Experimental
    [ "Retrieve the argument value at the given index from the given 'SkeletonState'."
    ]

  , prim "skeleton_arg" "SkeletonState -> String -> LLVMSetup Term"
    (pureVal skeleton_arg)
    Experimental
    [ "Retrieve the argument value of the given name from the given 'SkeletonState'."
    ]

  , prim "skeleton_arg_index_pointer" "SkeletonState -> Int -> LLVMSetup SetupValue"
    (pureVal skeleton_arg_index_pointer)
    Experimental
    [ "Retrieve the argument pointer at the given indexfrom the given 'SkeletonState'."
    , "Fails if the specified argument is not a pointer."
    ]

  , prim "skeleton_arg_pointer" "SkeletonState -> String -> LLVMSetup SetupValue"
    (pureVal skeleton_arg_pointer)
    Experimental
    [ "Retrieve the argument pointer of the given name from the given 'SkeletonState'."
    , "Fails if the specified argument is not a pointer."
    ]

  , prim "skeleton_exec" "SkeletonState -> LLVMSetup ()"
    (pureVal skeleton_exec)
    Experimental
    [ "Wrapper around 'crucible_execute_func' that passes the arguments initialized"
    , "in 'skeleton_prestate'."
    ]

  , prim "llvm_boilerplate" "String -> ModuleSkeleton -> Bool -> TopLevel ()"
    (pureVal llvm_boilerplate)
    Experimental
    [ "Generate boilerplate for the definitions in the given LLVM module skeleton."
    , "Output is written to the path passed as the first argument."
    , "The third argument controls whether skeleton builtins are emitted."
    ]

  , prim "caseSatResult"       "{b} SatResult -> b -> (Term -> b) -> b"
    (\_ _ -> toValueCase caseSatResultPrim)
    Current
    [ "Branch on the result of SAT solving."
    , ""
    , "Usage: caseSatResult <code to run if unsat> <code to run if sat>."
    , ""
    , "For example,"
    , ""
    , "  r <- sat abc <prop>"
    , "  caseSatResult r <unsat> <sat>"
    , ""
    , "will run '<unsat>' if '<prop>' is unSAT and will run '<sat> <example>'"
    , "if '<prop>' is SAT, where '<example>' is a satisfying assignment."
    , "If '<prop>' is a curried function, then '<example>' will be a tuple."
    , "If we could not determine the satisfiability of '<prop>', then"
    , "this will run '<sat> {{ () }}'."
    ]

  , prim "caseProofResult"     "{b} ProofResult -> (Theorem -> b) -> (Term -> b) -> b"
    (\_ _ -> toValueCase caseProofResultPrim)
    Current
    [ "Branch on the result of proving."
    , ""
    , "Usage: caseProofResult <result> <code to run if true> <code to run if false>."
    , ""
    , "For example,"
    , ""
    , "  r <- prove abc <prop>"
    , "  caseProofResult r <true> <false>"
    , ""
    , "will run '<true> <thm>' if '<prop>' is proved (where '<thm>' represents"
    , "the proved theorem) and will run '<false> <example>'"
    , "if '<prop>' is false, where '<example>' is a counter example."
    , "If '<prop>' is a curried function, then '<example>' will be a tuple."
    , "If the proof of <prop> was not finished, but we did not find a counterexample,"
    , "the example will run '<false> {{ () }}'"
    ]

  , prim "undefined"           "{a} a"
    (\_ _ -> error "interpret: undefined")
    Current
    [ "An undefined value of any type. Evaluating 'undefined' makes the"
    , "program crash."
    ]

  , prim "exit"                "Int -> TopLevel ()"
    (pureVal exitPrim)
    Current
    [ "Exit SAWScript, returning the supplied exit code to the parent"
    , "process."
    ]

  , prim "fail" "{a} String -> TopLevel a"
    (\_ _ -> toValue failPrim)
    Current
    [ "Throw an exception in the top level monad." ]

  , prim "fails"               "{a} TopLevel a -> TopLevel ()"
    (\_ _ -> toValue failsPrim)
    Current
    [ "Run the given inner action and convert failure into success.  Fail"
    , "if the inner action does NOT raise an exception. This is primarily used"
    , "for unit testing purposes, to ensure that we can elicit expected"
    , "failing behaviors."
    ]

  , prim "time"                "{a} TopLevel a -> TopLevel a"
    (\_ _ -> toValue timePrim)
    Current
    [ "Print the CPU time used by the given TopLevel command." ]

  , prim "with_time"           "{a} TopLevel a -> TopLevel (Int, a)"
    (\_ _ -> toValue withTimePrim)
    Current
    [ "Run the given toplevel command.  Return the number of milliseconds"
    , "elapsed during the execution of the command and its result."
    ]

  , prim "exec"               "String -> [String] -> String -> TopLevel String"
    (\_ _ -> toValue readProcess)
    Current
    [ "Execute an external process with the given executable"
    , "name, arguments, and standard input. Returns standard"
    , "output."
    ]

  , prim "eval_bool"           "Term -> Bool"
    (funVal1 eval_bool)
    Current
    [ "Evaluate a Cryptol term of type Bit to either 'true' or 'false'."
    ]

  , prim "eval_int"           "Term -> Int"
    (funVal1 eval_int)
    Current
    [ "Evaluate a Cryptol term of type [n] and convert to a SAWScript Int."
    ]

  , prim "eval_size"          "Type -> Int"
    (funVal1 eval_size)
    Current
    [ "Convert a Cryptol size type to a SAWScript Int."
    ]

  , prim "eval_list"           "Term -> [Term]"
    (funVal1 eval_list)
    Current
    [ "Evaluate a Cryptol term of type [n]a to a list of terms."
    ]

  , prim "list_term"           "[Term] -> Term"
    (funVal1 list_term)
    Current
    [ "Make a Cryptol term of type [n]a from a list of terms of type a."
    , "Function list_term is the inverse of function eval_list."
    ]

  , prim "parse_core"         "String -> Term"
    (funVal1 parse_core)
    Current
    [ "Parse a Term from a String in SAWCore syntax."
    ]

  , prim "parse_core_mod"      "String -> String -> Term"
    (funVal2 parse_core_mod)
    Current
    [ "Parse a Term from the second supplied String in SAWCore syntax,"
    , "relative to the module specified by the first String"
    ]

  , prim "prove_core"         "ProofScript () -> String -> TopLevel Theorem"
    (pureVal prove_core)
    Current
    [ "Use the given proof script to attempt to prove that a term is valid"
    , "(true for all inputs). The term is specified as a String containing"
    , "saw-core syntax. Returns a Theorem if successful, and aborts if"
    , "unsuccessful."
    ]

  , prim "core_axiom"         "String -> Theorem"
    (funVal1 core_axiom)
    Current
    [ "Declare the given core expression as an axiomatic rewrite rule."
    , "The input string contains a proof goal in saw-core syntax. The"
    , "return value is a Theorem that may be added to a Simpset."
    ]

  , prim "core_thm"           "String -> Theorem"
    (funVal1 core_thm)
    Current
    [ "Create a theorem from the type of the given core expression." ]

  , prim "specialize_theorem" "Theorem -> [Term] -> TopLevel Theorem"
    (pureVal specialize_theorem)
    Experimental
    [ "Specialize a theorem by instantiating universal quantifiers"
    , "with the given list of terms."
    ]

  , prim "get_opt"            "Int -> String"
    (funVal1 get_opt)
    Current
    [ "Get the nth command-line argument as a String. Index 0 returns"
    , "the program name; other parameters are numbered starting at 1."
    ]

  , prim "show_cfg"          "CFG -> String"
    (pureVal show_cfg)
    Current
    [ "Pretty-print a control-flow graph."
    ]

    ---------------------------------------------------------------------
    -- Crucible/LLVM interface

  , prim "llvm_cfg"     "LLVMModule -> String -> TopLevel CFG"
    (pureVal llvm_cfg)
    Current
    [ "Load a function from the given LLVM module into a Crucible CFG."
    ]

  , prim "llvm_extract"  "LLVMModule -> String -> TopLevel Term"
    (pureVal llvm_extract)
    Current
    [ "Translate an LLVM function directly to a Term. The parameters of the"
    , "Term will be the parameters of the LLVM function, and the return"
    , "value will be the return value of the functions. Only functions with"
    , "scalar argument and return types are currently supported. For more"
    , "flexibility, see 'llvm_verify'."
    ]
  , prim "crucible_llvm_extract"  "LLVMModule -> String -> TopLevel Term"
    (pureVal llvm_extract)
    Current
    [ "Legacy alternative name for `llvm_extract`." ]

  , prim "llvm_compositional_extract"
    "LLVMModule -> String -> String -> [LLVMSpec] -> Bool -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_compositional_extract)
    Experimental
    [ "Translate an LLVM function directly to a Term. The parameters of the"
    , "Term are the input parameters of the LLVM function: the parameters"
    , "passed by value (in the order given by `llvm_exec_func`), then"
    , "the parameters passed by reference (in the order given by"
    , "`llvm_points_to`). The Term is the tuple consisting of the"
    , "output parameters of the LLVM function: the return parameter, then"
    , "the parameters passed by reference (in the order given by"
    , "`llvm_points_to`). For more flexibility, see `llvm_verify`."
    ]
  , prim "crucible_llvm_compositional_extract"
    "LLVMModule -> String -> String -> [LLVMSpec] -> Bool -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_compositional_extract)
    Experimental
    [ "Legacy alternative name for `llvm_compositional_extract`." ]

  , prim "llvm_fresh_var" "String -> LLVMType -> LLVMSetup Term"
    (pureVal llvm_fresh_var)
    Current
    [ "Create a fresh symbolic variable for use within an LLVM"
    , "specification. The name is used only for pretty-printing."
    ]
  , prim "crucible_fresh_var" "String -> LLVMType -> LLVMSetup Term"
    (pureVal llvm_fresh_var)
    Current
    [ "Legacy alternative name for `llvm_fresh_var`." ]

  , prim "llvm_fresh_cryptol_var" "String -> Type -> LLVMSetup Term"
    (pureVal llvm_fresh_cryptol_var)
    Experimental
    [ "Create a fresh symbolic variable of the given Cryptol type for use"
    , "within a Crucible specification. The given name is used only for"
    , "pretty-printing. Unlike 'llvm_fresh_var', this can be used when"
    , "there isn't an appropriate LLVM type, such as the Cryptol Array type."
    ]
  , prim "crucible_fresh_cryptol_var" "String -> Type -> LLVMSetup Term"
    (pureVal llvm_fresh_cryptol_var)
    Experimental
    [ "Legacy alternative name for `llvm_fresh_cryptol_var`." ]

  , prim "llvm_alloc" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc)
    Current
    [ "Declare that an object of the given type should be allocated in an"
    , "LLVM specification. Before `llvm_execute_func`, this states that"
    , "the function expects the object to be allocated before it runs."
    , "After `llvm_execute_func`, it states that the function being"
    , "verified is expected to perform the allocation."
    ]
  , prim "crucible_alloc" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc)
    Current
    [ "Legacy alternative name for `llvm_alloc`." ]

  , prim "llvm_alloc_aligned" "Int -> LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_aligned)
    Current
    [ "Declare that a memory region of the given type should be allocated in"
    , "an LLVM specification, and also specify that the start of the region"
    , "should be aligned to a multiple of the specified number of bytes (which"
    , "must be a power of 2)."
    ]
  , prim "crucible_alloc_aligned" "Int -> LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_aligned)
    Current
    [ "Legacy alternative name for `llvm_alloc_aligned`." ]

  , prim "llvm_alloc_readonly" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_readonly)
    Current
    [ "Declare that a read-only memory region of the given type should be"
    , "allocated in an LLVM specification. The function must not attempt"
    , "to write to this memory region. Unlike `llvm_alloc`, regions"
    , "allocated with `llvm_alloc_readonly` are allowed to alias other"
    , "read-only regions."
    ]
  , prim "crucible_alloc_readonly" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_readonly)
    Current
    [ "Legacy alternative name for `llvm_alloc_readonly`." ]

  , prim "llvm_alloc_readonly_aligned" "Int -> LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_readonly_aligned)
    Current
    [ "Declare that a read-only memory region of the given type should be"
    , "allocated in an LLVM specification, and also specify that the start of"
    , "the region should be aligned to a multiple of the specified number of"
    , "bytes (which must be a power of 2). The function must not attempt to"
    , "write to this memory region. Unlike `llvm_alloc`/`llvm_alloc_aligned`,"
    , "regions allocated with `llvm_alloc_readonly_aligned` are allowed to"
    , "alias other read-only regions."
    ]
  , prim "crucible_alloc_readonly_aligned" "Int -> LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_readonly_aligned)
    Current
    [ "Legacy alternative name for `llvm_alloc_readonly_aligned`." ]

  , prim "llvm_alloc_with_size" "Int -> LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_with_size)
    Experimental
    [ "Like `llvm_alloc`, but with a user-specified size (given in bytes)."
    , "The specified size must be greater than the size of the LLVM type."
    ]
  , prim "crucible_alloc_with_size" "Int -> LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_with_size)
    Experimental
    [ "Legacy alternative name for `llvm_alloc_with_size`." ]

  , prim "llvm_alloc_sym_init" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_alloc_sym_init)
    Experimental
    [ "Like `llvm_alloc`, but assume that the allocation is initialized with"
    , "symbolic bytes."
    ]

  , prim "llvm_symbolic_alloc" "Bool -> Int -> Term -> LLVMSetup SetupValue"
    (pureVal llvm_symbolic_alloc)
    Current
    [ "Like `llvm_alloc`, but with a (symbolic) size instead of an LLVM type."
    , "The first argument specifies whether the allocation is read-only. The"
    , "second argument specifies the alignment in bytes (which must be a power"
    , "of 2). The third argument specifies the size in bytes."
    ]
  , prim "crucible_symbolic_alloc" "Bool -> Int -> Term -> LLVMSetup SetupValue"
    (pureVal llvm_symbolic_alloc)
    Current
    [ "Legacy alternative name for `llvm_symbolic_alloc`." ]

  , prim "llvm_alloc_global" "String -> LLVMSetup ()"
    (pureVal llvm_alloc_global)
    Current
    [ "Declare that memory for the named global should be allocated in an"
    , "LLVM specification. This is done implicitly for immutable globals."
    , "A pointer to the allocated memory may be obtained using `llvm_global`."
    ]
  , prim "crucible_alloc_global" "String -> LLVMSetup ()"
    (pureVal llvm_alloc_global)
    Current
    [ "Legacy alternative name for `llvm_alloc_global`." ]

  , prim "llvm_fresh_pointer" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_fresh_pointer)
    Current
    [ "Create a fresh pointer value for use in an LLVM specification."
    , "This works like `llvm_alloc` except that the pointer is not"
    , "required to point to allocated memory."
    ]
  , prim "crucible_fresh_pointer" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_fresh_pointer)
    Current
    [ "Legacy alternative name for `llvm_fresh_pointer`." ]

  , prim "llvm_fresh_expanded_val" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_fresh_expanded_val)
    Current
    [ "Create a compound type entirely populated with fresh symbolic variables."
    , "Equivalent to allocating a new struct or array of the given type and"
    , "explicitly setting each field or element to contain a fresh symbolic"
    , "variable."
    ]
  , prim "crucible_fresh_expanded_val" "LLVMType -> LLVMSetup SetupValue"
    (pureVal llvm_fresh_expanded_val)
    Current
    [ "Legacy alternative name for `llvm_fresh_expanded_val`." ]

  , prim "llvm_points_to" "SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_points_to True))
    Current
    [ "Declare that the memory location indicated by the given pointer (first"
    , "argument) contains the given value (second argument)."
    , ""
    , "In the pre-state section (before `llvm_execute_func`) this specifies"
    , "the initial memory layout before function execution. In the post-state"
    , "section (after `llvm_execute_func`), this specifies an assertion"
    , "about the final memory state after running the function."
    ]
    , prim "crucible_points_to" "SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_points_to True))
    Current
    [ "Legacy alternative name for `llvm_points_to`." ]

  , prim "llvm_conditional_points_to" "Term -> SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_conditional_points_to True))
    Current
    [ "Declare that the memory location indicated by the given pointer (second"
    , "argument) contains the given value (third argument) if the given"
    , "condition (first argument) holds."
    , ""
    , "In the pre-state section (before `llvm_execute_func`) this specifies"
    , "the initial memory layout before function execution. In the post-state"
    , "section (after `llvm_execute_func`), this specifies an assertion"
    , "about the final memory state after running the function."
    ]
  , prim "crucible_conditional_points_to" "Term -> SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_conditional_points_to True))
    Current
    [ "Legacy alternative name for `llvm_conditional_points_to`." ]

  , prim "llvm_points_to_at_type" "SetupValue -> LLVMType -> SetupValue -> LLVMSetup ()"
    (pureVal llvm_points_to_at_type)
    Current
    [ "A variant of `llvm_points_to` that casts the pointer to another type."
    , "This may be useful when reading or writing a prefix of larger array,"
    , "for example."
    ]

  , prim "llvm_conditional_points_to_at_type" "Term -> SetupValue -> LLVMType -> SetupValue -> LLVMSetup ()"
    (pureVal llvm_conditional_points_to_at_type)
    Current
    [ "A variant of `llvm_conditional_points_to` that casts the pointer to"
    , "another type. This may be useful when reading or writing a prefix"
    , "of larger array, for example."
    ]

  , prim "llvm_points_to_untyped" "SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_points_to False))
    Current
    [ "A variant of `llvm_points_to` that does not check for compatibility"
    , "between the pointer type and the value type. This may be useful when"
    , "reading or writing a prefix of larger array, for example."
    ]
  , prim "crucible_points_to_untyped" "SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_points_to False))
    Current
    [ "Legacy alternative name for `llvm_points_to`." ]

  , prim "llvm_conditional_points_to_untyped" "Term -> SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_conditional_points_to False))
    Current
    [ "A variant of `llvm_conditional_points_to` that does not check for"
    , "compatibility between the pointer type and the value type. This may"
    , "be useful when reading or writing a prefix of larger array, for example."
    ]
  , prim "crucible_conditional_points_to_untyped" "Term -> SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_conditional_points_to False))
    Current
    [ "Legacy alternative name for `llvm_conditional_points_to`." ]

  , prim "llvm_points_to_array_prefix" "SetupValue -> Term -> Term -> LLVMSetup ()"
    (pureVal llvm_points_to_array_prefix)
    Experimental
    [ "Declare that the memory location indicated by the given pointer (first"
    , "argument) contains the prefix of the given array (second argument) of"
    , "the given size (third argument)."
    , ""
    , "In the pre-state section (before `llvm_execute_func`) this specifies"
    , "the initial memory layout before function execution. In the post-state"
    , "section (after `llvm_execute_func`), this specifies an assertion"
    , "about the final memory state after running the function."
    ]
  , prim "crucible_points_to_array_prefix" "SetupValue -> Term -> Term -> LLVMSetup ()"
    (pureVal llvm_points_to_array_prefix)
    Experimental
    [ "Legacy alternative name for `llvm_points_to_array_prefix`." ]

  , prim "llvm_points_to_bitfield" "SetupValue -> String -> SetupValue -> LLVMSetup ()"
    (pureVal (llvm_points_to_bitfield))
    Experimental
    [ "A variant of `llvm_points_to` that is meant to be used on struct fields"
    , "that reside within bitfields. `llvm_points_to_bitfield ptr fieldName rhs`"
    , "should be used instead of `llvm_points_to (llvm_field ptr fieldName) rhs`,"
    , "as the latter will not behave as one would expect for technical reasons."
    , ""
    , "This command should only be used in combination with"
    , "`enable_lax_loads_and_stores`, as this option relaxes some assumptions"
    , "about the memory model that are crucial to how `llvm_points_to_bitfield`"
    , "operates."
    ]

  , prim "llvm_equal" "SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal llvm_equal)
    Current
    [ "State that two LLVM values should be equal. Can be used as either a"
    , "pre-condition or a post-condition. It is semantically equivalent to"
    , "an `llvm_precond` or `llvm_postcond` statement which is an equality"
    , "predicate, but potentially more efficient."
    ]
  , prim "crucible_equal" "SetupValue -> SetupValue -> LLVMSetup ()"
    (pureVal llvm_equal)
    Current
    [ "Legacy alternative name for `llvm_equal`." ]

  , prim "llvm_precond" "Term -> LLVMSetup ()"
    (pureVal llvm_precond)
    Current
    [ "State that the given predicate is a pre-condition on execution of the"
    , "function being verified."
    ]
  , prim "crucible_precond" "Term -> LLVMSetup ()"
    (pureVal llvm_precond)
    Current
    [ "Legacy alternative name for `llvm_precond`." ]

  , prim "llvm_assert" "Term -> LLVMSetup ()"
    (pureVal llvm_assert)
    Current
    [ "State that the given predicate must hold.  Acts as `llvm_precond`"
    , "or `llvm_postcond` depending on the phase of specification in which"
    , "it appears (i.e., before or after `llvm_execute_func`."
    ]

  , prim "llvm_setup_with_tag" "String -> LLVMSetup () -> LLVMSetup ()"
    (pureVal llvm_setup_with_tag)
    Experimental
    [ "All conditions (e.g., from points-to or assert statements) executed"
    , "in the scope of the given setup block will have the provieded string"
    , "attached as a tag that can later be filtered by proof tactics."
    ]

  , prim "llvm_postcond" "Term -> LLVMSetup ()"
    (pureVal llvm_postcond)
    Current
    [ "State that the given predicate is a post-condition of execution of the"
    , "function being verified."
    ]
  , prim "crucible_postcond" "Term -> LLVMSetup ()"
    (pureVal llvm_postcond)
    Current
    [ "Legacy alternative name for `llvm_postcond`." ]

  , prim "llvm_execute_func" "[SetupValue] -> LLVMSetup ()"
    (pureVal llvm_execute_func)
    Current
    [ "Specify the given list of values as the arguments of the function."
    ,  ""
    , "The `llvm_execute_func` statement also serves to separate the pre-state"
    , "section of the spec (before `llvm_execute_func`) from the post-state"
    , "section (after `llvm_execute_func`). The effects of some LLVMSetup"
    , "statements depend on whether they occur in the pre-state or post-state"
    , "section."
    ]
  , prim "crucible_execute_func" "[SetupValue] -> LLVMSetup ()"
    (pureVal llvm_execute_func)
    Current
    [ "Legacy alternative name for `llvm_execute_func`." ]

  , prim "llvm_return" "SetupValue -> LLVMSetup ()"
    (pureVal llvm_return)
    Current
    [ "Specify the given value as the return value of the function. A"
    , "crucible_return statement is required if and only if the function"
    , "has a non-void return type." ]
  , prim "crucible_return" "SetupValue -> LLVMSetup ()"
    (pureVal llvm_return)
    Current
    [ "Legacy alternative name for `llvm_return`." ]

  , prim "llvm_cast_pointer" "SetupValue -> LLVMType -> SetupValue"
    (pureVal llvm_cast_pointer)
    Current
    [ "Cast the type of the given setup value (which must be a pointer value)."
    , "The resulting setup value will be a pointer to the same location, treated"
    , "as a pointer to the provided type."
    ]

  , prim "llvm_verify"
    "LLVMModule -> String -> [LLVMSpec] -> Bool -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_verify)
    Current
    [ "Verify the LLVM function named by the second parameter in the module"
    , "specified by the first. The third parameter lists the LLVMSpec"
    , "values returned by previous calls to use as overrides. The fourth (Bool)"
    , "parameter enables or disables path satisfiability checking. The fifth"
    , "describes how to set up the symbolic execution engine before verification."
    , "And the last gives the script to use to prove the validity of the resulting"
    , "verification conditions."
    ]
  , prim "crucible_llvm_verify"
    "LLVMModule -> String -> [LLVMSpec] -> Bool -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_verify)
    Current
    [ "Legacy alternative name for `llvm_verify`." ]

  , prim "llvm_refine_spec"
    "LLVMModule -> String -> [LLVMSpec] -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_refine_spec)
    Experimental
    [ "Verify that a given specification for a function is a refinement of one or more"
    , "specifications already proved for a function. This can be useful for situations where"
    , "it is advantageous to logically restate the specification in some why, or where a more"
    , "general specification can be constructed from a collection of individual, more specific,"
    , "specifications."
    ]

  , prim "llvm_unsafe_assume_spec"
    "LLVMModule -> String -> LLVMSetup () -> TopLevel LLVMSpec"
    (pureVal llvm_unsafe_assume_spec)
    Current
    [ "Return an LLVMSpec corresponding to an LLVMSetup block,"
    , "as would be returned by crucible_llvm_verify but without performing"
    , "any verification."
    ]
  , prim "crucible_llvm_unsafe_assume_spec"
    "LLVMModule -> String -> LLVMSetup () -> TopLevel LLVMSpec"
    (pureVal llvm_unsafe_assume_spec)
    Current
    [ "Legacy alternative name for `llvm_unsafe_assume_spec`." ]

  , prim "llvm_array_size_profile"
    "LLVMModule -> String -> [LLVMSpec] -> LLVMSetup () -> TopLevel [(String, [FunctionProfile])]"
    (pureVal $ llvm_array_size_profile assumeUnsat)
    Experimental
    [ "Symbolically execute the function named by the second parameter in"
    , "the module specified by the first. The fourth parameter may be used"
    , "to specify arguments. Returns profiles specifying the sizes of buffers"
    , "referred to by pointer arguments for the function and all other functions"
    , "it calls (recursively), to be passed to llvm_boilerplate."
    ]
  , prim "crucible_llvm_array_size_profile"
    "LLVMModule -> String -> [LLVMSpec] -> LLVMSetup () -> TopLevel [(String, [FunctionProfile])]"
    (pureVal $ llvm_array_size_profile assumeUnsat)
    Experimental
    [ "Legacy alternative name for `llvm_array_size_profile`." ]

  , prim "llvm_verify_x86"
    "LLVMModule -> String -> String -> [(String, Int)] -> Bool -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_verify_x86)
    Experimental
    [ "Verify an x86 function from an ELF file for use as an override in an"
    , "LLVM verification. The first argument specifies the LLVM module"
    , "containing the _caller_. The second and third specify the ELF file"
    , "name and symbol name of the function to be verifier. The fourth"
    , "specifies the names and sizes (in bytes) of global variables to"
    , "initialize, and the fifth whether to perform path satisfiability"
    , "checking. The last argument is the LLVM specification of the calling"
    , "context against which to verify the function. Returns a method spec"
    , "that can be used as an override when verifying other LLVM functions."
    ]
  , prim "crucible_llvm_verify_x86"
    "LLVMModule -> String -> String -> [(String, Int)] -> Bool -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_verify_x86)
    Experimental
    [ "Legacy alternative name for `llvm_verify_x86`." ]

  , prim "llvm_verify_fixpoint_x86"
    "LLVMModule -> String -> String -> [(String, Int)] -> Bool -> Term -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_verify_fixpoint_x86)
    Experimental
    [ "An experimental variant of 'llvm_verify_x86'. This variant can prove some properties"
    , "involving simple loops with the help of a user-provided term that describes how"
    , "the live variables in the loop evolve as the loop computes."
    ]

  , prim "llvm_verify_x86_with_invariant"
    "LLVMModule -> String -> String -> [(String, Int)] -> Bool -> (String, Int, Term) -> LLVMSetup () -> ProofScript () -> TopLevel LLVMSpec"
    (pureVal llvm_verify_x86_with_invariant)
    Experimental
    [ "An experimental extension of 'llvm_verify_x86'. This extension can prove some properties"
    , "involving simple loops with the help of a user-provided loop invariant that describes"
    , "how the live variables in the loop evolve as the loop computes."
    , ""
    , "The loop invariant is provided by the tuple argument, which indicates what symbol the loop"
    , "appears in (which might differ from the function the specification is for), which loop within"
    , "that function to reason about (starts counting from 0), and a term that desribes the loop invariant"
    , "itself. For this verification command to succeed, the loop in question must have a single entry-point,"
    , "must have a single back-edge, and must have a constant memory footprint."
    , ""
    , "The SAWCore type expected of the loop invariant will depend on the results of an analysis done"
    , "on the indicated loop, which will attempt to discover what are all the loop-carried dependencies."
    , "The result of this analysis will be packaged into a tuple, and any relevant top-level specification"
    , "variables will be found. The expected type of the loop invariant will then be a function over all"
    , "the implicit variables found, and two tuples consisting of the initial values of the loop-carried"
    , "dependencies, and the current value of the loop-carried dependencies. The function should return Bool."
    , "Some trial-and-error will generally be required to match the results of the analysis with a sutiable"
    , "function."
    , ""
    , "As part of the verification process, the loop invariant will be used in several ways. First, a proof"
    , "obligation will be issued upon first entry to the loop, establishing the loop invariant holds at the"
    , "beginning of the loop. Second, the loop invariant is used when starting execution from the loop head"
    , "to make a generic assumption that the invariant holds. Finally, the invariant is used when execution"
    , "once again reaches the loop head to assert that the invariant holds inductively across the execution"
    , "of the loop body. The produced proof obligations will be tagged with either the tag"
    , "'initial loop invariant' or 'inductive loop invariant'."
    , ""
    , "Provided all the generated verification conditions are discharged, this results in a partial"
    , "correctness proof for the indicated function. Note that termination is not proved via this procedure."
    ]

  , prim "enable_x86_what4_hash_consing" "TopLevel ()"
    (pureVal enable_x86_what4_hash_consing)
    Experimental
    [ "Enable hash consing for What4 expressions during x86 verification." ]

  , prim "disable_x86_what4_hash_consing" "TopLevel ()"
    (pureVal disable_x86_what4_hash_consing)
    Current
    [ "Disable hash consing for What4 expressions during x86 verification." ]

  , prim "add_x86_preserved_reg" "String -> TopLevel ()"
    (pureVal add_x86_preserved_reg)
    Current
    [ "Treat the given register as callee-saved during x86 verification." ]

  , prim "default_x86_preserved_reg" "TopLevel ()"
    (pureVal default_x86_preserved_reg)
    Current
    [ "Use the default set of callee-saved registers during x86 verification." ]

  , prim "enable_what4_eval" "TopLevel ()"
    (pureVal enable_what4_eval)
    Experimental
    [ "Enable What4 translation for SAWCore expressions during Crucible symbolic execution." ]

  , prim "disable_what4_eval" "TopLevel ()"
    (pureVal disable_what4_eval)
    Current
    [ "Disable What4 translation for SAWCore expressions during Crucible symbolic execution." ]

  , prim "set_x86_stack_base_align" "Int -> TopLevel ()"
    (pureVal set_x86_stack_base_align)
    Experimental
    [ "Set the alignment of the stack allocation base to 2^n during x86 verification." ]

  , prim "default_x86_stack_base_align" "TopLevel ()"
    (pureVal default_x86_stack_base_align)
    Experimental
    [ "Use the default stack allocation base alignment during x86 verification." ]

  , prim "enable_alloc_sym_init_check" "TopLevel ()"
    (pureVal enable_alloc_sym_init_check)
    Experimental
    [ "Enable the allocation initialization check associated with alloc_sym_init during override application." ]

  , prim "disable_alloc_sym_init_check" "TopLevel ()"
    (pureVal disable_alloc_sym_init_check)
    Current
    [ "Disable the allocation initialization check associated with alloc_sym_init during override application."
    , "Disabling this check allows an override to apply when the memory region specified by the alloc_sym_init command"
    , "in the override specification is not written to in the calling context."
    , "This makes the implicit assumption that there is some unspecified byte at any valid memory address."
    ]

  , prim "set_crucible_timeout" "Int -> TopLevel ()"
    (pureVal set_crucible_timeout)
    Experimental
    [ "Set the timeout for the SMT solver during the LLVM and X86 Crucible symbolic execution,"
    ,"in milliseconds (0 is no timeout). The default is 10000ms (10s)."
    ,"This is used for path-sat checks, and sat checks when applying overrides."
    ]

  , prim "llvm_array_value"
    "[SetupValue] -> SetupValue"
    (pureVal CIR.anySetupArray)
    Current
    [ "Create a SetupValue representing an array, with the given list of"
    , "values as elements. The list must be non-empty." ]
  , prim "crucible_array"
    "[SetupValue] -> SetupValue"
    (pureVal CIR.anySetupArray)
    Current
    [ "Legacy alternative name for `llvm_array_value`." ]

  , prim "llvm_struct_type"
    "[LLVMType] -> LLVMType"
    (pureVal llvm_struct_type)
    Current
    [ "The type of an LLVM struct with elements of the given types." ]

  , prim "llvm_struct_value"
    "[SetupValue] -> SetupValue"
    (pureVal (CIR.anySetupStruct False))
    Current
    [ "Create a SetupValue representing a struct, with the given list of"
    , "values as elements." ]
  , prim "crucible_struct"
    "[SetupValue] -> SetupValue"
    (pureVal (CIR.anySetupStruct False))
    Current
    [ "Legacy alternative name for `llvm_struct_value`." ]

  , prim "llvm_packed_struct_type"
    "[LLVMType] -> LLVMType"
    (pureVal llvm_packed_struct_type)
    Current
    [ "The type of a packed LLVM struct with elements of the given types." ]

  , prim "llvm_packed_struct_value"
    "[SetupValue] -> SetupValue"
    (pureVal (CIR.anySetupStruct True))
    Current
    [ "Create a SetupValue representing a packed struct, with the given"
    , "list of values as elements." ]
  , prim "crucible_packed_struct"
    "[SetupValue] -> SetupValue"
    (pureVal (CIR.anySetupStruct True))
    Current
    [ "Legacy alternative name for `llvm_packed_struct_value`." ]

  , prim "llvm_elem"
    "SetupValue -> Int -> SetupValue"
    (pureVal CIR.anySetupElem)
    Current
    [ "Turn a SetupValue representing a struct or array pointer into"
    , "a pointer to an element of the struct or array by field index." ]
  , prim "crucible_elem"
    "SetupValue -> Int -> SetupValue"
    (pureVal CIR.anySetupElem)
    Current
    [ "Legacy alternative name for `llvm_elem`." ]

  , prim "llvm_union"
    "SetupValue -> String -> SetupValue"
    (pureVal CIR.anySetupUnion)
    Current
    [ "Turn a SetupValue representing a union pointer into"
    , "a pointer to one of the branches of the union by field name."
    , "Requires debug symbols to resolve union field names."
    ]

  , prim "llvm_field"
    "SetupValue -> String -> SetupValue"
    (pureVal CIR.anySetupField)
    Current
    [ "Turn a SetupValue representing a struct pointer into"
    , "a pointer to an element of the struct by field name."
    , "Requires debug symbols to resolve struct field names."
    ]
  , prim "crucible_field"
    "SetupValue -> String -> SetupValue"
    (pureVal CIR.anySetupField)
    Current
    [ "Legacy alternative name for `llvm_field`." ]

  , prim "llvm_null"
    "SetupValue"
    (pureVal CIR.anySetupNull)
    Current
    [ "A SetupValue representing a null pointer value." ]
  , prim "crucible_null"
    "SetupValue"
    (pureVal CIR.anySetupNull)
    Current
    [ "Legacy alternative name for `llvm_null`." ]

  , prim "llvm_global"
    "String -> SetupValue"
    (pureVal CIR.anySetupGlobal)
    Current
    [ "Return a SetupValue representing a pointer to the named global."
    , "The String may be either the name of a global value or a function name." ]
  , prim "crucible_global"
    "String -> SetupValue"
    (pureVal CIR.anySetupGlobal)
    Current
    [ "Legacy alternative name for `llvm_global`." ]

  , prim "llvm_global_initializer"
    "String -> SetupValue"
    (pureVal CIR.anySetupGlobalInitializer)
    Current
    [ "Return a SetupValue representing the value of the initializer of a named"
    , "global. The String should be the name of a global value."
    ]
  , prim "crucible_global_initializer"
    "String -> SetupValue"
    (pureVal CIR.anySetupGlobalInitializer)
    Current
    [ "Legacy alternative name for `llvm_global_initializer`." ]

  , prim "llvm_term"
    "Term -> SetupValue"
    (pureVal CIR.anySetupTerm)
    Current
    [ "Construct a `SetupValue` from a `Term`." ]
  , prim "crucible_term"
    "Term -> SetupValue"
    (pureVal CIR.anySetupTerm)
    Current
    [ "Legacy alternative name for `llvm_term`." ]

  , prim "crucible_setup_val_to_term"
    " SetupValue -> TopLevel Term"
    (pureVal crucible_setup_val_to_typed_term)
    Deprecated
    [ "Convert from a setup value to a typed term. This can only be done for a"
    , "subset of setup values. Fails if a setup value is a global, variable or null."
    ]

  -- Ghost state support
  , prim "llvm_declare_ghost_state"
    "String -> TopLevel Ghost"
    (pureVal llvm_declare_ghost_state)
    Current
    [ "Allocates a unique ghost variable." ]
  , prim "crucible_declare_ghost_state"
    "String -> TopLevel Ghost"
    (pureVal llvm_declare_ghost_state)
    Current
    [ "Legacy alternative name for `llvm_declare_ghost_state`." ]

  , prim "llvm_ghost_value"
    "Ghost -> Term -> LLVMSetup ()"
    (pureVal llvm_ghost_value)
    Current
    [ "Specifies the value of a ghost variable. This can be used"
    , "in the pre- and post- conditions of a setup block."]
  , prim "crucible_ghost_value"
    "Ghost -> Term -> LLVMSetup ()"
    (pureVal llvm_ghost_value)
    Current
    [ "Legacy alternative name for `llvm_ghost_value`."]

  , prim "llvm_spec_solvers"  "LLVMSpec -> [String]"
    (\_ _ -> toValue llvm_spec_solvers)
    Current
    [ "Extract a list of all the solvers used when verifying the given method spec."
    ]
  , prim "crucible_spec_solvers"  "LLVMSpec -> [String]"
    (\_ _ -> toValue llvm_spec_solvers)
    Current
    [ "Legacy alternative name for `llvm_spec_solvers`." ]

  , prim "llvm_spec_size"  "LLVMSpec -> Int"
    (\_ _ -> toValue llvm_spec_size)
    Current
    [ "Return a count of the combined size of all verification goals proved as part of"
    , "the given method spec."
    ]
  , prim "crucible_spec_size"  "LLVMSpec -> Int"
    (\_ _ -> toValue llvm_spec_size)
    Current
    [ "Legacy alternative name for `llvm_spec_size`." ]

    ---------------------------------------------------------------------
    -- Crucible/JVM commands

  , prim "jvm_fresh_var" "String -> JavaType -> JVMSetup Term"
    (pureVal jvm_fresh_var)
    Current
    [ "Create a fresh variable for use within a JVM specification. The"
    , "name is used only for pretty-printing."
    ]

  , prim "jvm_alloc_object" "String -> JVMSetup JVMValue"
    (pureVal jvm_alloc_object)
    Current
    [ "Declare that an instance of the given class should be allocated in a"
    , "JVM specification. Before `jvm_execute_func`, this states that the"
    , "method expects the object to be allocated before it runs. After"
    , "`jvm_execute_func`, it states that the method being verified is"
    , "expected to perform the allocation."
    ]

  , prim "jvm_alloc_array" "Int -> JavaType -> JVMSetup JVMValue"
    (pureVal jvm_alloc_array)
    Current
    [ "Declare that an array of the given size and element type should be"
    , "allocated in a JVM specification. Before `jvm_execute_func`, this"
    , "states that the method expects the array to be allocated before it"
    , "runs. After `jvm_execute_func`, it states that the method being"
    , "verified is expected to perform the allocation."
    ]

    -- TODO: jvm_alloc_multiarray

  , prim "jvm_modifies_field" "JVMValue -> String -> JVMSetup ()"
    (pureVal jvm_modifies_field)
    Current
    [ "Declare that the indicated object (first argument) has a field"
    , "(second argument) containing an unspecified value."
    , ""
    , "This lets users write partial specifications of JVM methods."
    , "In the post-state section (after `jvm_execute_func`), this"
    , "states that the method may modify the field, but says"
    , "nothing about the new value."
    ]

  , prim "jvm_modifies_static_field" "String -> JVMSetup ()"
    (pureVal jvm_modifies_static_field)
    Current
    [ "Declare that the named static field contains an unspecified"
    , "value."
    , ""
    , "This lets users write partial specifications of JVM methods."
    , "In the post-state section (after `jvm_execute_func`), it"
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
    , "In the post-state section (after `jvm_execute_func`), it"
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
    , "In the post-state section (after `jvm_execute_func`), it"
    , "states that the method may modify the array elements, but says"
    , "nothing about the new values."
    ]

  , prim "jvm_field_is" "JVMValue -> String -> JVMValue -> JVMSetup ()"
    (pureVal jvm_field_is)
    Current
    [ "Declare that the indicated object (first argument) has a field"
    , "(second argument) containing the given value (third argument)."
    , ""
    , "In the pre-state section (before jvm_execute_func) this specifies"
    , "the initial memory layout before function execution. In the post-state"
    , "section (after jvm_execute_func), this specifies an assertion"
    , "about the final memory state after running the function."
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
    , "In the pre-state section (before jvm_execute_func) this specifies"
    , "the initial memory layout before function execution. In the post-state"
    , "section (after jvm_execute_func), this specifies an assertion"
    , "about the final memory state after running the function."
    ]

  , prim "jvm_elem_is" "JVMValue -> Int -> JVMValue -> JVMSetup ()"
    (pureVal jvm_elem_is)
    Current
    [ "Declare that the indicated array (first argument) has an element"
    , "(second argument) containing the given value (third argument)."
    , ""
    , "In the pre-state section (before jvm_execute_func) this specifies"
    , "the initial memory layout before function execution. In the post-state"
    , "section (after jvm_execute_func), this specifies an assertion"
    , "about the final memory state after running the function."
    ]

  , prim "jvm_array_is" "JVMValue -> Term -> JVMSetup ()"
    (pureVal jvm_array_is)
    Current
    [ "Declare that the indicated array reference (first argument) contains"
    , "the given sequence of values (second argument)."
    , ""
    , "In the pre-state section (before jvm_execute_func) this specifies"
    , "the initial memory layout before function execution. In the post-state"
    , "section (after jvm_execute_func), this specifies an assertion"
    , "about the final memory state after running the function."
    ]

  , prim "jvm_precond" "Term -> JVMSetup ()"
    (pureVal jvm_precond)
    Current
    [ "State that the given predicate is a pre-condition on execution of the"
    , "method being verified."
    ]

  , prim "jvm_assert" "Term -> JVMSetup ()"
    (pureVal jvm_assert)
    Current
    [ "State that the given predicate must hold.  Acts as `jvm_precond`"
    , "or `jvm_postcond` depending on the phase of specification in which"
    , "it appears (i.e., before or after `jvm_execute_func`."
    ]

  , prim "jvm_postcond" "Term -> JVMSetup ()"
    (pureVal jvm_postcond)
    Current
    [ "State that the given predicate is a post-condition of execution of the"
    , "method being verified."
    ]

  , prim "jvm_execute_func" "[JVMValue] -> JVMSetup ()"
    (pureVal jvm_execute_func)
    Current
    [ "Specify the given list of values as the arguments of the method."
    ,  ""
    , "The jvm_execute_func statement also serves to separate the pre-state"
    , "section of the spec (before jvm_execute_func) from the post-state"
    , "section (after jvm_execute_func). The effects of some JVMSetup"
    , "statements depend on whether they occur in the pre-state or post-state"
    , "section."
    ]

  , prim "jvm_return" "JVMValue -> JVMSetup ()"
    (pureVal jvm_return)
    Current
    [ "Specify the given value as the return value of the method. A"
    , "jvm_return statement is required if and only if the method"
    , "has a non-void return type." ]

  , prim "jvm_setup_with_tag" "String -> JVMSetup () -> JVMSetup ()"
    (pureVal jvm_setup_with_tag)
    Experimental
    [ "All conditions (e.g., from points-to or assert statements) executed"
    , "in the scope of the given setup block will have the provieded string"
    , "attached as a tag that can later be filtered by proof tactics."
    ]

  , prim "jvm_verify"
    "JavaClass -> String -> [JVMSpec] -> Bool -> JVMSetup () -> ProofScript () -> TopLevel JVMSpec"
    (pureVal jvm_verify)
    Current
    [ "Verify the JVM method named by the second parameter in the class"
    , "specified by the first. The third parameter lists the JVMSpec values"
    , "returned by previous calls to use as overrides. The fourth (Bool)"
    , "parameter enables or disables path satisfiability checking. The fifth"
    , "describes how to set up the symbolic execution engine before verification."
    , "And the last gives the script to use to prove the validity of the resulting"
    , "verification conditions."
    ]

  , prim "jvm_unsafe_assume_spec"
    "JavaClass -> String -> JVMSetup () -> TopLevel JVMSpec"
    (pureVal jvm_unsafe_assume_spec)
    Current
    [ "Return a JVMSpec corresponding to a JVMSetup block, as would be"
    , "returned by jvm_verify but without performing any verification."
    ]

  , prim "jvm_null"
    "JVMValue"
    (pureVal (CMS.SetupNull () :: CMS.SetupValue CJ.JVM))
    Current
    [ "A JVMValue representing a null pointer value." ]

  , prim "jvm_term"
    "Term -> JVMValue"
    (pureVal (CMS.SetupTerm :: TypedTerm -> CMS.SetupValue CJ.JVM))
    Current
    [ "Construct a `JVMValue` from a `Term`." ]

    ---------------------------------------------------------------------

  , prim "mr_solver_prove" "Term -> Term -> TopLevel ()"
    (scVal (mrSolverProve True))
    Experimental
    [ "Call the monadic-recursive solver (that's MR. Solver to you)"
    , " to prove that one monadic term refines another. If this can"
    , " be done, this refinement will be used in future calls to"
    , " Mr. Solver, and if it cannot, the script will exit. See also:"
    , " mr_solver_test, mr_solver_query." ]

  , prim "mr_solver_test" "Term -> Term -> TopLevel ()"
    (scVal (mrSolverProve False))
    Experimental
    [ "Call the monadic-recursive solver (that's MR. Solver to you)"
    , " to prove that one monadic term refines another. If this cannot"
    , " be done, the script will exit. See also: mr_solver_prove,"
    , " mr_solver_query - unlike the former, this refinement will not"
    , " be used in future calls to Mr. Solver." ]

  , prim "mr_solver_query" "Term -> Term -> TopLevel Bool"
    (scVal mrSolverQuery)
    Experimental
    [ "Call the monadic-recursive solver (that's MR. Solver to you)"
    , " to prove that one monadic term refines another, returning"
    , " true iff this can be done. See also: mr_solver_prove,"
    , " mr_solver_test - unlike the former, this refinement will not"
    , " be considered in future calls to Mr. Solver, and unlike both,"
    , " this command will never fail." ]

  , prim "mr_solver_assume" "Term -> Term -> TopLevel Bool"
    (scVal mrSolverAssume)
    Experimental
    [ "Add the refinement of the two given expressions as an assumption"
    , " which will be used in future calls to Mr. Solver." ]

  , prim "mr_solver_set_debug_level" "Int -> TopLevel ()"
    (pureVal mrSolverSetDebug)
    Experimental
    [ "Set the debug level for Mr. Solver; 0 = no debug output,"
    , " 1 = basic debug output, 2 = verbose debug output,"
    , " 3 = all debug output" ]

    ---------------------------------------------------------------------

  , prim "monadify_term" "Term -> TopLevel Term"
    (scVal monadifyTypedTerm)
    Experimental
    [ "Monadify a Cryptol term, converting it to a form where all recursion"
    , " and errors are represented as monadic operators"]

  , prim "set_monadification" "String -> String -> TopLevel Term"
    (scVal setMonadification)
    Experimental
    [ "Set the monadification of a specific Cryptol identifer to a SAW core "
    , "identifier of monadic type" ]

  , prim "heapster_init_env"
    "String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_init_env)
    Experimental
    [ "Create a new Heapster environment with the given SAW module name"
    , " from the named LLVM bitcode file."
    ]

  , prim "heapster_init_env_debug"
    "String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_init_env)
    Experimental
    [ "Create a new Heapster environment with the given SAW module name"
    , " from the named LLVM bitcode file with debug tracing turned on"
    ]

  , prim "heapster_init_env_from_file"
    "String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_init_env_from_file)
    Experimental
    [ "Create a new Heapster environment from the named LLVM bitcode file,"
    , " initialized with the module in the given SAW core file."
    ]

  , prim "heapster_init_env_from_file_debug"
    "String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_init_env_from_file_debug)
    Experimental
    [ "Create a new Heapster environment from the named LLVM bitcode file,"
    , " initialized with the module in the given SAW core file, with debug"
    , " tracing turned on"
    ]

  , prim "load_sawcore_from_file"
    "String -> TopLevel ()"
    (bicVal load_sawcore_from_file)
    Experimental
    [ "Load a SAW core module from a file"
    ]

  , prim "heapster_init_env_for_files"
    "String -> [String] -> TopLevel HeapsterEnv"
    (bicVal heapster_init_env_for_files)
    Experimental
    [ "Create a new Heapster environment from the named LLVM bitcode files,"
    , " initialized with the module in the given SAW core file."
    ]

  , prim "heapster_init_env_for_files_debug"
    "String -> [String] -> TopLevel HeapsterEnv"
    (bicVal heapster_init_env_for_files_debug)
    Experimental
    [ "Create a new Heapster environment from the named LLVM bitcode files,"
    , " initialized with the module in the given SAW core file, with debug"
    , " tracing turned on"
    ]

  , prim "heapster_get_cfg"
    "HeapsterEnv -> String -> TopLevel CFG"
    (bicVal heapster_get_cfg)
    Experimental
    [ "Extract out the Crucible CFG associated with a symbol in a"
    , " Heapster environemnt"
    ]

  , prim "heapster_define_opaque_perm"
    "HeapsterEnv -> String -> String -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_opaque_perm)
    Experimental
    [ "heapster_define_opaque_perm nm args tp trans defines an opaque named"
    , " Heapster permission named nm with arguments parsed from args and type"
    , " parsed from tp that translates to the named type trans"
    ]

  , prim "heapster_define_recursive_perm"
    "HeapsterEnv -> String -> String -> String -> [String] -> String -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_recursive_perm)
    Experimental
    [ "heapster_define_recursive_perm env name arg_ctx value_type"
    , " [ p1, ..., pn ] trans_tp fold_fun unfold_fun defines an recursive named"
    , " Heapster permission named nm with arguments parsed from args_ctx and"
    , " type parsed from value_type that translates to the named type"
    , " trans_tp. The resulting permission is equivalent to the permission"
    , " p1 \\/ ... \\/ pn, where the pi can contain name."
    ]

  , prim "heapster_define_irt_recursive_perm"
    "HeapsterEnv -> String -> String -> String -> [String] -> TopLevel HeapsterEnv"
    (bicVal heapster_define_irt_recursive_perm)
    Experimental
    [ "heapster_define_irt_recursive_perm env name arg_ctx value_type"
    , " [ p1, ..., pn ] defines an recursive named Heapster permission named"
    , " nm with arguments parsed from args_ctx and type parsed from value_type"
    , " that translates to the appropriate IRT type. The resulting permission"
    , " is equivalent to the permission p1 \\/ ... \\/ pn, where the pi can"
    , " contain name."
    ]

  , prim "heapster_define_irt_recursive_shape"
    "HeapsterEnv -> String -> Int -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_irt_recursive_shape)
    Experimental
    [ "heapster_define_irt_recursive_shape env name w arg_ctx body_sh"
    , " defines a recursive named Heapser shape named nm with arguments"
    , " parsed from args_ctx and width w that translates to the appropriate"
    , " IRT type. The resulting shape is equivalent to the shape body_sh,"
    , " where body_sh can contain name."
    ]

  , prim "heapster_define_reachability_perm"
    "HeapsterEnv -> String -> String -> String -> String -> String -> String -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_reachability_perm)
    Experimental
    [ "heapster_define_recursive_perm env name arg_ctx value_type"
    , " [ p1, ..., pn ] trans_tp fold_fun unfold_fun defines an recursive named"
    , " Heapster permission named nm with arguments parsed from args_ctx and"
    , " type parsed from value_type that translates to the named type"
    , " trans_tp. The resulting permission is equivalent to he permission"
    , " p1 \\/ ... \\/ pn, where the pi can contain name."
    ]

  , prim "heapster_define_perm"
    "HeapsterEnv -> String -> String -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_perm)
    Experimental
    [ "heapster_define_perm nm args tp p defines a Heapster permission named"
    , " nm with arguments x1,...,xn parsed from args and type parsed from tp"
    , " such that nm<x1,...,xn> is equivalent to the permission p."
    ]

  , prim "heapster_define_llvmshape"
    "HeapsterEnv -> String -> Int -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_llvmshape)
    Experimental
    [ "heapster_define_llvmshape nm w args sh defines a Heapster LLVM shape"
    , " nm with type llvmshape w and arguments x1,...,xn parsed from args"
    , " such that nm<x1,...,xn> is equivalent to the permission p."
    ]

  , prim "heapster_define_opaque_llvmshape"
    "HeapsterEnv -> String -> Int -> String -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_opaque_llvmshape)
    Experimental
    [ "heapster_define_opaque_llvmshape henv nm w args len tp defines a Heapster"
    , " LLVM shape that is opaque, meaning it acts as a sort of shape axiom, where"
    , " Heapster does not know or care about the contents of memory of this shape"
    , " but instead treats that memory as an opaque object, defined only by its"
    , " length and its translation to a SAW core type."
    , ""
    , " The henv argument is the Heapster environment this new shape is added to,"
    , " nm is its name, args is a context of argument variables for this shape,"
    , " len is an expression for the length of the shape in terms of the arguments,"
    , " and tp gives the translation of the shape as a SAW core type over the"
    , " translation of the arguments to SAW core variables."
    ]

  , prim "heapster_define_rust_type"
    "HeapsterEnv -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_rust_type)
    Experimental
    [ "heapster_define_rust_type env tp defines a Heapster LLVM shape from tp,"
    , "a string representing a top-level struct or enum definition."
    ]

  , prim "heapster_define_rust_type_qual"
    "HeapsterEnv -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_define_rust_type_qual)
    Experimental
    [ "heapster_define_rust_type_qual env crate tp defines a Heapster LLVM"
    , " shape from tp, a string representing a top-level Rust struct or enum"
    , " definition. The type is qualified by crate, meaning that \"crate::\""
    , " is prepended to its name."
    ]

  , prim "heapster_block_entry_hint"
    "HeapsterEnv -> String -> Int -> String -> String -> String -> TopLevel ()"
    (bicVal heapster_block_entry_hint)
    Experimental
    [ "heapster_block_entry_hint env nm block top_args ghosts perms adds a hint"
    , " to the Heapster type-checker that Crucible block number block in nm"
    , " should have permissions perms on its inputs, assuming that top_args"
    , " lists the top-level ghost and normal arguments to function nm and"
    , " ghosts gives the ghost arguments to block"
    ]

  , prim "heapster_gen_block_perms_hint"
    "HeapsterEnv -> String -> [Int] -> TopLevel ()"
    (bicVal heapster_gen_block_perms_hint)
    Experimental
    [ "heapster_gen_block_perms_hint env nm blocks adds a hint to the Heapster"
    , " type-checker to *generalize* (recursively replace all instances of"
    , " eq(const) with (exists x. eq(x))) all permissions on the inputs of the"
    , " given Crucible blocks numbers. If the given list is empty, do so for"
    , " every block in the CFG."
    ]

  , prim "heapster_join_point_hint"
    "HeapsterEnv -> String -> [Int] -> TopLevel ()"
    (bicVal heapster_join_point_hint)
    Experimental
    [ "heapster_join_point_hint env nm blocks adds a hint to the Heapster"
    , " type-checker to make a join point at each of the given block numbers,"
    , " meaning that all entries to the given blocks are merged into a single"
    , " entrypoint, whose permissions are given by the first call to the block."
    , " If the given list is empty, do so for every block in the CFG."
    ]

  , prim "heapster_find_symbol"
    "HeapsterEnv -> String -> TopLevel String"
    (bicVal heapster_find_symbol)
    Experimental
    [ "Search for a symbol in any module contained in a HeapsterEnv that"
    , " contains the supplied string as a substring. Raise an error if there"
    , " is not exactly one such symbol"
    ]

  , prim "heapster_find_symbols"
    "HeapsterEnv -> String -> TopLevel [String]"
    (bicVal heapster_find_symbols)
    Experimental
    [ "Search for all symbols in any module contained in a HeapsterEnv that"
    , " contain the supplied string as a substring"
    ]

  , prim "heapster_find_symbol_with_type"
    "HeapsterEnv -> String -> String -> TopLevel String"
    (bicVal heapster_find_symbol_with_type)
    Experimental
    [ "Search for a symbol in any module contained in a HeapsterEnv that"
    , " contains the supplied string as a substring and that has the specified"
    , " LLVM type. Raise an error if there is not exactly one such symbol."
    ]

  , prim "heapster_find_symbols_with_type"
    "HeapsterEnv -> String -> String -> TopLevel [String]"
    (bicVal heapster_find_symbols_with_type)
    Experimental
    [ "Search for all symbols in any module contained in a HeapsterEnv that"
    , " contain the supplied string as a substring and that have the specified"
    , " LLVM type"
    ]

  , prim "heapster_find_symbol_commands"
    "HeapsterEnv -> String -> TopLevel [String]"
    (bicVal heapster_find_symbol_commands)
    Experimental
    [ "Map a search string str to a newline-separated sequence of SAW-script "
    , " commands \"heapster_find_symbol_with_type str tp\", one for each LLVM "
    , " type tp associated with a symbol whose name contains str" ]

  , prim "heapster_find_trait_method_symbol"
    "HeapsterEnv -> String -> TopLevel String"
    (bicVal heapster_find_trait_method_symbol)
    Experimental
    [ "Search for a symbol in any module contained in a HeapsterEnv that"
    , "corresponds to the given trait method implementation. The search"
    , "string should be of the form: trait::method<type>, e.g."
    , "core::fmt::Debug::fmt<Foo>"
    ]

  , prim "heapster_assume_fun"
    "HeapsterEnv -> String -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_assume_fun)
    Experimental
    [ "heapster_assume_fun nm perms trans assumes that function nm has"
    , " permissions perms and translates to the SAW core term trans"
    ]

  , prim "heapster_assume_fun_rename"
    "HeapsterEnv -> String -> String -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_assume_fun_rename)
    Experimental
    [ "heapster_assume_fun_rename nm nm_t perms trans assumes that function nm"
    , " has permissions perms and translates to the SAW core term trans. If"
    , " trans is not an identifier then it is bound to the defined name nm_to."
    ]

  , prim "heapster_assume_fun_rename_prim"
    "HeapsterEnv -> String -> String -> String -> TopLevel HeapsterEnv"
    (bicVal heapster_assume_fun_rename_prim)
    Experimental
    [
      "heapster_assume_fun_rename_prim nm nm_to perms assumes that function nm"
    , " has permissions perms as a primitive."
    ]

  , prim "heapster_assume_fun_multi"
    "HeapsterEnv -> String -> [(String, String)] -> TopLevel HeapsterEnv"
    (bicVal heapster_assume_fun_multi)
    Experimental
    [ "heapster_assume_fun_multi nm [(perm1, trans1), ...] assumes that function"
    , " nm can be typed with 0 or more permissions, each with the corresponding"
    , " translation to SAW core"
    ]

  , prim "heapster_typecheck_fun"
    "HeapsterEnv -> String -> String -> TopLevel ()"
    (bicVal heapster_typecheck_fun)
    Experimental
    [ "Translate an LLVM function to a SAW core term using Heapster"
    , " type-checking, and store the result in the current Heapster SAW module."
    ]

  , prim "heapster_typecheck_fun_rename"
    "HeapsterEnv -> String -> String -> String -> TopLevel ()"
    (bicVal heapster_typecheck_fun_rename)
    Experimental
    [ "Translate the LLVM function named by the first String to a SAW core term"
    , " using Heapster type-checking, and store the result in the current"
    , " Heapster SAW module as a definition named with the second string."
    ]

  , prim "heapster_typecheck_mut_funs"
    "HeapsterEnv -> [(String, String)] -> TopLevel ()"
    (bicVal heapster_typecheck_mut_funs)
    Experimental
    [ "Translate a set of mutually recursive LLVM function to a set of SAW "
    , "core terms using Heapster type-checking. Store the results in the "
    , "current Heapster SAW module."
    ]

  , prim "heapster_print_fun_trans"
    "HeapsterEnv -> String -> TopLevel ()"
    (bicVal heapster_print_fun_trans)
    Experimental
    [ "Print the translation to SAW of a function that has been type-checked."
    ]

  , prim "heapster_export_coq"
    "HeapsterEnv -> String -> TopLevel ()"
    (bicVal heapster_export_coq)
    Experimental
    [ "Export a Heapster environment to a Coq file" ]

  , prim "heapster_set_debug_level"
    "HeapsterEnv -> Int -> TopLevel ()"
    (bicVal heapster_set_debug_level)
    Experimental
    [ "Set the debug level for Heapster; 0 = no debug output, 1 = debug output" ]

  , prim "heapster_set_translation_checks"
    "HeapsterEnv -> Bool -> TopLevel ()"
    (bicVal heapster_set_translation_checks)
    Experimental
    [ "Tell Heapster whether to perform its translation-time checks of the "
    , "well-formedness of type-checking proofs" ]

  , prim "heapster_parse_test"
    "LLVMModule -> String -> String -> TopLevel ()"
    (bicVal heapster_parse_test)
    Experimental
    [ "Parse and print back a set of Heapster permissions for a function"
    ]

    ---------------------------------------------------------------------

  , prim "sharpSAT"  "Term -> TopLevel Integer"
    (pureVal sharpSAT)
    Current
    [ "Use the sharpSAT solver to count the number of solutions to the CNF"
    , "representation of the given Term."
    ]

  , prim "approxmc"  "Term -> TopLevel String"
    (pureVal approxmc)
    Current
    [ "Use the approxmc solver to approximate the number of solutions to the"
    , "CNF representation of the given Term."
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

  , prim "summarize_verification" "TopLevel ()"
    (pureVal summarize_verification)
    Experimental
    [ "Print a human-readable summary of all verifications performed"
    , "so far."
    ]

  , prim "summarize_verification_json" "String -> TopLevel ()"
    (pureVal summarize_verification_json)
    Experimental
    [ "Print a JSON summary of all verifications performed"
    , "so far into the named file."
    ]
  ]

  where
    prim :: String -> String -> (Options -> BuiltinContext -> Value) -> PrimitiveLifecycle -> [String]
         -> (SS.LName, Primitive)
    prim name ty fn lc doc = (qname, Primitive
                                     { primitiveName = qname
                                     , primitiveType = readSchema ty
                                     , primitiveDoc  = doc
                                     , primitiveFn   = fn
                                     , primitiveLife = lc
                                     })
      where qname = qualify name

    pureVal :: forall t. IsValue t => t -> Options -> BuiltinContext -> Value
    pureVal x _ _ = toValue x

    funVal1 :: forall a t. (FromValue a, IsValue t) => (a -> TopLevel t)
               -> Options -> BuiltinContext -> Value
    funVal1 f _ _ = VLambda $ \a -> fmap toValue (f (fromValue a))

    funVal2 :: forall a b t. (FromValue a, FromValue b, IsValue t) => (a -> b -> TopLevel t)
               -> Options -> BuiltinContext -> Value
    funVal2 f _ _ = VLambda $ \a -> return $ VLambda $ \b ->
      fmap toValue (f (fromValue a) (fromValue b))

    scVal :: forall t. IsValue t =>
             (SharedContext -> t) -> Options -> BuiltinContext -> Value
    scVal f _ bic = toValue (f (biSharedContext bic))

    bicVal :: forall t. IsValue t =>
              (BuiltinContext -> Options -> t) -> Options -> BuiltinContext -> Value
    bicVal f opts bic = toValue (f bic opts)


filterAvail ::
  Set PrimitiveLifecycle ->
  Map SS.LName Primitive ->
  Map SS.LName Primitive
filterAvail primsAvail =
  Map.filter (\p -> primitiveLife p `Set.member` primsAvail)

primTypeEnv :: Set PrimitiveLifecycle -> Map SS.LName SS.Schema
primTypeEnv primsAvail = fmap primitiveType (filterAvail primsAvail primitives)

valueEnv :: Set PrimitiveLifecycle -> Options -> BuiltinContext -> Map SS.LName Value
valueEnv primsAvail opts bic = fmap f (filterAvail primsAvail primitives)
  where f p = (primitiveFn p) opts bic

-- | Map containing the formatted documentation string for each
-- saw-script primitive.
primDocEnv :: Set PrimitiveLifecycle -> Map SS.Name String
primDocEnv primsAvail =
  Map.fromList [ (getVal n, doc n p) | (n, p) <- Map.toList prims ]
    where
      prims = filterAvail primsAvail primitives
      tag p = case primitiveLife p of
                Current -> []
                Deprecated -> ["DEPRECATED", ""]
                Experimental -> ["EXPERIMENTAL", ""]
      doc n p = unlines $
                [ "Description"
                , "-----------"
                , ""
                ] ++ tag p ++
                [ "    " ++ getVal n ++ " : " ++ SS.pShow (primitiveType p)
                , ""
                ] ++ primitiveDoc p

qualify :: String -> Located SS.Name
qualify s = Located s s (SS.PosInternal "coreEnv")
