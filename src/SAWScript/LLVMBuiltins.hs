{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.LLVMBuiltins where

import Control.Applicative
import Control.Monad.Error hiding (mapM)
import Control.Monad.State hiding (mapM)
import Data.List.Split
import qualified Data.Map as Map
import Data.String
import Text.PrettyPrint.HughesPJ
import Text.Read (readMaybe)

import qualified Verifier.SAW.Cryptol.Prelude as CryptolSAW

import Text.LLVM ( modTypes, modGlobals, modDeclares, modDefines, modDataLayout
                 , defName, defRetType, defVarArgs, defArgs, defAttrs
                 , funLinkage, funGC
                 , globalAttrs, globalSym, globalType
                 , ppType, ppGC, ppArgList,  ppLinkage, ppTyped,  ppTypeDecl
                 , ppDeclare, ppGlobalAttrs, ppMaybe, ppSymbol, ppIdent
                 )
import Verifier.LLVM.Backend
import Verifier.LLVM.Codebase hiding ( Global, ppSymbol, ppIdent
                                     , globalSym, globalType
                                     )
import qualified Verifier.LLVM.Codebase as CB
import Verifier.LLVM.Backend.SAW
import Verifier.LLVM.Simulator

import Verifier.SAW.FiniteValue
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST (Termlike)

import SAWScript.CongruenceClosure hiding (mapM)
import SAWScript.Builtins
import SAWScript.LLVMExpr
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMMethodSpec
import SAWScript.Options
import SAWScript.Proof
import SAWScript.Utils
import SAWScript.Value as SV
import qualified Verifier.SAW.Evaluator as SC

loadLLVMModule :: FilePath -> IO LLVMModule
loadLLVMModule file = LLVMModule file <$> loadModule file

browseLLVMModule :: LLVMModule -> IO ()
browseLLVMModule (LLVMModule name m) = do
  putStrLn ("Module: " ++ name)
  putStrLn "Types:"
  showParts ppTypeDecl (modTypes m)
  putStrLn ""
  putStrLn "Globals:"
  showParts ppGlobal' (modGlobals m)
  putStrLn ""
  putStrLn "External references:"
  showParts ppDeclare (modDeclares m)
  putStrLn ""
  putStrLn "Definitions:"
  showParts ppDefine' (modDefines m)
  putStrLn ""
    where
      showParts pp xs = mapM_ (print . nest 2 . pp) xs
      ppGlobal' g =
        ppSymbol (globalSym g) <+> char '=' <+>
        ppGlobalAttrs (globalAttrs g) <+>
        ppType (globalType g)
      ppDefine' d =
        ppMaybe ppLinkage (funLinkage (defAttrs d)) <+>
        ppType (defRetType d) <+>
        ppSymbol (defName d) <>
          ppArgList (defVarArgs d) (map (ppTyped ppIdent) (defArgs d)) <+>
        ppMaybe (\gc -> text "gc" <+> ppGC gc) (funGC (defAttrs d))

-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all
-- arguments and returns a term representing the return value. Some
-- verifications will require more complex execution contexts.
extractLLVM :: SharedContext SAWCtx -> LLVMModule -> String -> LLVMSetup ()
            -> IO (SV.TypedTerm SAWCtx)
extractLLVM sc (LLVMModule file mdl) func _setup = do
  let dl = parseDataLayout $ modDataLayout mdl
      sym = Symbol func
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- createSAWBackend' be dl []
    (_warnings, cb) <- mkCodebase sbe dl mdl
    -- TODO: Print warnings from codebase.
    case lookupDefine sym cb of
      Nothing -> fail $ "Bitcode file " ++ file ++
                        " does not contain symbol " ++ func ++ "."
      Just md -> runSimulator cb sbe mem Nothing $ do
        setVerbosity 0
        args <- mapM freshLLVMArg (sdArgs md)
        _ <- callDefine sym (sdRetType md) args
        mrv <- getProgramReturnValue
        case mrv of
          Nothing -> fail "No return value from simulated function."
          Just rv -> liftIO $ do
            lamTm <- bindExts scLLVM (map snd args) rv
            scImport sc lamTm >>= SV.mkTypedTerm sc

{-
extractLLVMBit :: FilePath -> String -> SC s (SharedTerm s')
extractLLVMBit file func = mkSC $ \_sc -> do
  mdl <- loadModule file
  let dl = parseDataLayout $ modDataLayout mdl
      sym = Symbol func
      mg = defaultMemGeom dl
  withBE $ \be -> do
    LBit.SBEPair sbe mem <- return $ LBit.createBuddyAll be dl mg
    cb <- mkCodebase sbe dl mdl
    case lookupDefine sym cb of
      Nothing -> fail $ "Bitcode file " ++ file ++
                        " does not contain symbol " ++ func ++ "."
      Just md -> runSimulator cb sbe mem defaultSEH Nothing $ do
        setVerbosity 0
        args <- mapM freshLLVMArg (sdArgs md)
        callDefine_ sym (sdRetType md) args
        mrv <- getProgramReturnValue
        case mrv of
          Nothing -> fail "No return value from simulated function."
          Just bt -> fail "extractLLVMBit: not yet implemented"
-}

freshLLVMArg :: Monad m =>
            (t, MemType) -> Simulator sbe m (MemType, SBETerm sbe)
freshLLVMArg (_, ty@(IntType bw)) = do
  sbe <- gets symBE
  tm <- liftSBE $ freshInt sbe bw
  return (ty, tm)
freshLLVMArg (_, _) = fail "Only integer arguments are supported for now."


verifyLLVM :: BuiltinContext -> Options -> LLVMModule -> String
           -> [LLVMMethodSpecIR]
           -> LLVMSetup ()
           -> IO LLVMMethodSpecIR
verifyLLVM bic opts (LLVMModule file mdl) func overrides setup = do
  let pos = fixPos -- TODO
      dl = parseDataLayout $ modDataLayout mdl
  withBE $ \be -> do
    (sbe, mem, scLLVM) <- createSAWBackend' be dl [CryptolSAW.cryptolModule]
    (_warnings, cb) <- mkCodebase sbe dl mdl
    let ms0 = initLLVMMethodSpec pos cb func
        lsctx0 = LLVMSetupState {
                    lsSpec = ms0
                  , lsTactic = Skip
                  , lsContext = scLLVM
                  }
    (_, lsctx) <- runStateT setup lsctx0
    let ms = lsSpec lsctx
    let vp = VerifyParams { vpCode = cb
                          , vpContext = scLLVM
                          , vpOpts = opts
                          , vpSpec = ms
                          , vpOver = overrides
                          }
    let verb = verbLevel (vpOpts vp)
    let overrideText =
          case overrides of
            [] -> ""
            irs -> " (overriding " ++ show (map specFunction irs) ++ ")"
    when (verb >= 2) $ putStrLn $ "Starting verification of " ++ show (specName ms)
    {-
    let configs = [ (bs, cl)
                  | bs <- {- concat $ Map.elems $ -} [specBehaviors ms]
                  , cl <- bsRefEquivClasses bs
                  ] -}
    let lopts = Nothing -- FIXME
    do
    -- forM_ configs $ \(bs,cl) -> do
      when (verb >= 3) $ do
        putStrLn $ "Executing " ++ show (specName ms)
      runSimulator cb sbe mem lopts $ do
        setVerbosity verb
        esd <- initializeVerification scLLVM ms
        res <- mkSpecVC scLLVM vp esd
        when (verb >= 3) $ liftIO $ do
          putStrLn "Verifying the following:"
          mapM_ (print . ppPathVC) res
        let prover :: ProofScript SAWCtx SV.SatResult
                   -> VerifyState
                   -> SharedTerm LSSCtx
                   -> IO ()
            prover script vs g = do
              glam <- bindAllExts scLLVM g
              let bsc = biSharedContext bic
              glam' <- scNegate bsc =<< scImport bsc glam
              (r, _) <- runStateT script (ProofGoal (vsVCName vs) glam')
              case r of
                SV.Unsat -> when (verb >= 3) $ putStrLn "Valid."
                SV.Sat val ->  showCexResults scLLVM ms vs [("x", val)] -- TODO: replace x with something
                SV.SatMulti vals -> showCexResults scLLVM ms vs vals
        case lsTactic lsctx of
          Skip -> liftIO $ putStrLn $
            "WARNING: skipping verification of " ++ show (specName ms)
          RunVerify script ->
            liftIO $ runValidation (prover script) vp scLLVM esd res
    putStrLn $ "Successfully verified " ++ show (specName ms) ++ overrideText
    return ms

showCexResults :: SharedContext LSSCtx
               -> LLVMMethodSpecIR
               -> VerifyState
               -> [(String, FiniteValue)]
               -> IO ()
showCexResults sc ms vs vals = do
  putStrLn $ "When verifying " ++ show (specName ms) ++ ":"
  putStrLn $ "Proof of " ++ vsVCName vs ++ " failed."
  putStrLn $ "Counterexample: "
  mapM_ (\(n, v) -> putStrLn ("  " ++ n ++ ": " ++ show v)) vals
  vsCounterexampleFn vs (cexEvalFn sc (map snd vals)) >>= print
  fail "Proof failed."

llvmPure :: LLVMSetup ()
llvmPure = return ()

parseLLVMExpr :: Codebase (SAWBackend LSSCtx)
              -> SymDefine (SharedTerm LSSCtx)
              -> String
              -> IO LLVMExpr
parseLLVMExpr cb fn = parseParts . reverse . splitOn "."
  where parseParts [] = fail "Empty LLVM expression"
        parseParts [s] =
          case s of
            ('*':rest) -> do
              e <- parseParts [rest]
              case lssTypeOfLLVMExpr e of
                PtrType (MemType ty) -> return (Term (Deref e ty))
                _ -> fail "Attempting to apply * operation to non-pointer"
            ('a':'r':'g':'s':'[':rest) -> do
              let num = fst (break (==']') rest)
              case readMaybe num of
                Just (n :: Int)
                  | n < length numArgs ->
                    let (i, ty) = args !! n in return (Term (Arg n i ty))
                  | otherwise ->
                    fail $ "Argument index too large: " ++ show n
                Nothing -> fail $ "Bad LLVM expression syntax: " ++ s
            _ -> do
              let nid = fromString s
              case lookup nid numArgs of
                Just (n, ty) -> return (Term (Arg n nid ty))
                Nothing ->
                  case lookupSym (Symbol s) cb of
                    Just (Left gb) ->
                      return (Term (Global (CB.globalSym gb) (CB.globalType gb)))
                    _ -> fail $ "Unknown variable: " ++ s
        parseParts (f:rest) = fail "struct fields not yet supported" {- do
          e <- parseParts rest
          let lt = lssTypeOfLLVMExpr e
              pos = fixPos -- TODO
          -}
        args = sdArgs fn
        numArgs = zipWith (\(i, ty) n -> (i, (n, ty))) args [0..]

getLLVMExpr :: Monad m =>
               LLVMMethodSpecIR -> String
            -> m (LLVMExpr, MemType)
getLLVMExpr ms name = do
  case Map.lookup name (specLLVMExprNames ms) of
    -- TODO: maybe compute type differently?
    Just (_, expr) -> return (expr, lssTypeOfLLVMExpr expr)
    Nothing -> fail $ "LLVM name " ++ name ++ " has not been declared."

exportLLVMType :: Value s -> MemType
exportLLVMType (VCtorApp "LLVM.IntType" [VInteger n]) =
  IntType (fromIntegral n)
exportLLVMType (VCtorApp "LLVM.ArrayType" [VInteger n, ety]) =
  ArrayType (fromIntegral n) (exportLLVMType ety)
exportLLVMType (VCtorApp "LLVM.PtrType" [VInteger n]) =
  PtrType (MemType (IntType 8)) -- Character pointer, to start.
exportLLVMType v =
  error $ "exportLLVMType: Can't translate to LLVM type: " ++ show v

llvmVar :: BuiltinContext -> Options -> String -> Value SAWCtx
        -> LLVMSetup (SharedTerm SAWCtx)
llvmVar bic _ name t = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
  funcDef <- case lookupDefine func cb of
               Just fd -> return fd
               Nothing -> fail $ "Function " ++ show func ++ " not found."
  expr <- liftIO $ parseLLVMExpr cb funcDef name
  let lty = exportLLVMType t
      expr' = updateLLVMExprType expr lty
  modify $ \st -> st { lsSpec = specAddVarDecl fixPos name expr' lty (lsSpec st) }
  let sc = biSharedContext bic
  Just ty <- liftIO $ logicTypeOfActual sc lty
  liftIO $ scLLVMValue sc ty name

llvmPtr :: BuiltinContext -> Options -> String -> Value SAWCtx
        -> LLVMSetup (SharedTerm SAWCtx)
llvmPtr bic _ name t = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
      Just funcDef = lookupDefine func cb
  expr <- liftIO $ parseLLVMExpr cb funcDef name
  let lty = exportLLVMType t
      pty = PtrType (MemType lty)
      expr' = updateLLVMExprType expr pty
      dexpr = Term (Deref expr' lty)
      dname = '*':name
  modify $ \st -> st { lsSpec = specAddVarDecl fixPos dname dexpr lty $
                                specAddVarDecl fixPos name expr' pty (lsSpec st) }
  let sc = biSharedContext bic
  Just dty <- liftIO $ logicTypeOfActual sc lty
  liftIO $ scLLVMValue sc dty dname

llvmDeref :: BuiltinContext -> Options -> Value SAWCtx
          -> LLVMSetup (SharedTerm SAWCtx)
llvmDeref _bic _ _t = fail "llvm_deref not yet implemented"

{-
llvmMayAlias :: BuiltinContext -> Options -> [String]
             -> LLVMSetup ()
llvmMayAlias bic _ exprs = do
  lsState <- get
  let ms = lsSpec lsState
      cb = specCodebase ms
      func = specFunction ms
  exprs <- liftIO $ mapM (parseLLVMExpr cb func) exprs
  modify $ \st -> st { lsSpec = specAddAliasSet exprs (lsSpec st) }
-}

llvmAssert :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmAssert _ _ v =
  modify $ \st ->
    st { lsSpec =
           specAddBehaviorCommand (AssertPred fixPos (mkLogicExpr v)) (lsSpec st) }

llvmAssertEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
             -> LLVMSetup ()
llvmAssertEq _bic _ name t = do
  ms <- gets lsSpec
  (expr, _) <- liftIO $ getLLVMExpr ms name
  modify $ \st ->
    st { lsSpec = specAddLogicAssignment fixPos expr (mkLogicExpr t) ms }

asLLVMValue :: (Monad f, Termlike t) => Recognizer f t String
asLLVMValue t =
  case asApplyAll t of
    (asGlobalDef -> Just "LLVM.mkValue", [_, st]) -> do
      s <- asStringLit st
      return s
    _ -> fail "not an instance of LLVM.mkValue"


llvmEnsureEq :: BuiltinContext -> Options -> String -> SharedTerm SAWCtx
             -> LLVMSetup ()
llvmEnsureEq _ _ name t = do
  ms <- gets lsSpec
  (expr, _) <- liftIO $ getLLVMExpr ms name
  modify $ \st ->
    st { lsSpec =
           specAddBehaviorCommand (Ensure fixPos expr (LogicE (mkLogicExpr t))) (lsSpec st) }

llvmModify :: BuiltinContext -> Options -> String
           -> LLVMSetup ()
llvmModify _ _ name = error "llvm_modify not implemented" {- do
  ms <- gets lsSpec
  (expr, ty) <- liftIO $ getLLVMExpr ms name
  modify $ \st ->
    st { lsSpec =
           specAddBehaviorCommand (Modify expr ty) (lsSpec st) } -}

llvmReturn :: BuiltinContext -> Options -> SharedTerm SAWCtx
           -> LLVMSetup ()
llvmReturn _ _ t =
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand (Return (LogicE (mkLogicExpr t))) (lsSpec st) }

llvmVerifyTactic :: BuiltinContext -> Options
                 -> ProofScript SAWCtx SV.SatResult
                 -> LLVMSetup ()
llvmVerifyTactic _ _ script =
  modify $ \st -> st { lsTactic = RunVerify script }
