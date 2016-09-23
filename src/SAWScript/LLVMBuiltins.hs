{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TupleSections #-}

{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.LLVMBuiltins where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (many)
#endif
import Control.Lens
import Control.Monad.State hiding (mapM)
import Control.Monad.Trans.Except
import Data.Function (on)
import Data.List (partition, sortBy, groupBy)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String
import qualified Data.Vector as V
import Text.Parsec as P

import Text.LLVM (modDataLayout)
import Verifier.LLVM.Backend
import Verifier.LLVM.Codebase hiding ( Global, ppSymbol, ppIdent
                                     , globalSym, globalType
                                     )
import qualified Verifier.LLVM.Codebase as CB
import Verifier.LLVM.Backend.SAW
import Verifier.LLVM.Simulator
import Verifier.LLVM.Simulator.Internals

import Verifier.SAW.Cryptol (exportFiniteValue)
import Verifier.SAW.FiniteValue
import Verifier.SAW.Recognizer (asExtCns)
import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.Builtins
import SAWScript.CryptolEnv (schemaNoUser)
import SAWScript.LLVMExpr
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMMethodSpec
import SAWScript.LLVMUtils
import SAWScript.Options
import SAWScript.Proof
import SAWScript.SolverStats
import SAWScript.TypedTerm
import SAWScript.Utils
import SAWScript.Value as SV

import qualified Cryptol.Eval.Monad as Cryptol (runEval)
import qualified Cryptol.Eval.Value as Cryptol (ppValue)
import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Utils.PP as Cryptol (pretty)

type Backend = SAWBackend
type SAWTerm = Term
type SAWDefine = SymDefine SAWTerm

loadLLVMModule :: FilePath -> IO LLVMModule
loadLLVMModule file = LLVMModule file <$> loadModule file

-- LLVM verification and model extraction commands

type Assign = (LLVMExpr, TypedTerm)

startSimulator :: SharedContext
               -> LSSOpts
               -> LLVMModule
               -> Symbol
               -> (SharedContext
                   -> SBE SAWBackend
                   -> Codebase SAWBackend
                   -> DataLayout
                   -> SymDefine Term
                   -> Simulator SAWBackend IO a)
               -> IO a
startSimulator sc lopts (LLVMModule file mdl) sym body = do
  let dl = parseDataLayout $ modDataLayout mdl
  (sbe, mem, scLLVM) <- createSAWBackend' sawProxy dl sc
  (warnings, cb) <- mkCodebase sbe dl mdl
  forM_ warnings $ putStrLn . ("WARNING: " ++) . show
  case lookupDefine sym cb of
    Nothing -> fail $ missingSymMsg file sym
    Just md -> runSimulator cb sbe mem (Just lopts) $
               body scLLVM sbe cb dl md

symexecLLVM :: BuiltinContext
            -> Options
            -> LLVMModule
            -> String
            -> [(String, Integer)]
            -> [(String, Term, Integer)]
            -> [(String, Integer)]
            -> Bool
            -> IO TypedTerm
symexecLLVM bic opts lmod fname allocs inputs outputs doSat =
  let sym = Symbol fname
      sc = biSharedContext bic
      lopts = LSSOpts { optsErrorPathDetails = True
                      , optsSatAtBranches = doSat
                      }
  in startSimulator sc lopts lmod sym $ \scLLVM sbe cb dl md -> do
        setVerbosity (simVerbose opts)
        let verb = simVerbose opts
        let mkAssign (s, tm, n) = do
              e <- failLeft $ runExceptT $ parseLLVMExpr cb sym s
              return (e, tm, n)
            mkAllocAssign (s, n) = do
              e <- failLeft $ runExceptT $ parseLLVMExpr cb sym s
              case resolveType cb (lssTypeOfLLVMExpr e) of
                PtrType (MemType ty) -> do
                  when (verb >= 2) $ liftIO $ putStrLn $
                    "Allocating " ++ show n ++ " elements of type " ++ show (ppActualType ty)
                  tm <- allocSome sbe dl n ty
                  when (verb >= 2) $ liftIO $ putStrLn $
                    "Allocated address: " ++ show tm
                  return (e, tm, 1)
                ty -> fail $ "Allocation parameter " ++ s ++
                             " does not have pointer type. Type is " ++
                             show (ppActualType ty)
            multDefErr i = error $ "Multiple terms given for " ++ ordinal (i + 1) ++
                                   " argument in function " ++ fname
            isArgAssign (e, _, _) = isArgLLVMExpr e
        allocAssigns <- mapM mkAllocAssign allocs
        assigns <- mapM mkAssign inputs
        let allAssigns = allocAssigns ++ assigns
            (argAssigns, otherAssigns) = partition isArgAssign allAssigns
            argMap =
              Map.fromListWithKey
              (\i _ _ -> multDefErr i)
              [ (idx, (tp, tm)) | (CC.Term (Arg idx _ tp), tm, _) <- argAssigns ]
        let rargs = [(i, resolveType cb ty) | (i, ty) <- sdArgs md]
        args <- forM (zip [0..] rargs) $ \(i, (_, ty)) ->
                  case (Map.lookup i argMap, ty) of
                    (Just v, _) -> return v
                    -- (Nothing, PtrType (MemType dty)) -> (ty,) <$> allocSome 1 dty
                    _ -> fail $ "No binding for " ++ ordinal (i + 1) ++
                                " argument in function " ++ fname
        let argVals = map snd args
            retReg = (,Ident "__SAWScript_rslt") <$> sdRetType md
        _ <- callDefine' False sym retReg args
        -- TODO: the following line is generating memory errors
        mapM_ (writeLLVMTerm argVals) otherAssigns
        when (verb >= 2) $ liftIO $ putStrLn $ "Running " ++ fname
        run
        when (verb >= 2) $ liftIO $ putStrLn $ "Finished running " ++ fname
        outtms <- forM outputs $ \(ostr, n) -> do
          case ostr of
            "$safety" -> do
              mp <- getPath
              case mp of
                Nothing -> fail "No final path for safety condition."
                Just p -> return (p ^. pathAssertions)
            _ -> do
              e <- failLeft $ runExceptT $ parseLLVMExpr cb sym ostr
              readLLVMTerm argVals e n
        let bundle tms = case tms of
                           [t] -> return t
                           _ -> scTuple scLLVM tms
        liftIO (mkTypedTerm scLLVM =<< bundle outtms)


-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all arguments and
-- returns a lambda term representing the return value as a function of the
-- arguments. Many verifications will require more complex execution contexts.
extractLLVM :: BuiltinContext
            -> Options
            -> LLVMModule
            -> String
            -> LLVMSetup ()
            -> IO TypedTerm
extractLLVM bic opts lmod func _setup =
  let sym = Symbol func
      sc = biSharedContext bic
      lopts = LSSOpts { optsErrorPathDetails = True
                      , optsSatAtBranches = True
                      }
  in startSimulator sc lopts lmod sym $ \scLLVM _sbe _cb _dl md -> do
    setVerbosity (simVerbose opts)
    args <- mapM freshLLVMArg (sdArgs md)
    exts <- mapM (asExtCns . snd) args
    _ <- callDefine sym (sdRetType md) args
    mrv <- getProgramReturnValue
    case mrv of
      Nothing -> fail "No return value from simulated function."
      Just rv -> liftIO $ do
        lamTm <- scAbstractExts scLLVM exts rv
        scImport sc lamTm >>= mkTypedTerm sc

verifyLLVM :: BuiltinContext
           -> Options
           -> LLVMModule
           -> String
           -> [LLVMMethodSpecIR]
           -> LLVMSetup ()
           -> TopLevel LLVMMethodSpecIR
verifyLLVM bic opts (LLVMModule file mdl) funcname overrides setup =
  let pos = fixPos -- TODO
      dl = parseDataLayout $ modDataLayout mdl
      sc = biSharedContext bic
  in do
    (sbe, mem, scLLVM) <- io $ createSAWBackend' sawProxy dl sc
    (warnings, cb) <- io $ mkCodebase sbe dl mdl
    io $ forM_ warnings $ putStrLn . ("WARNING: " ++) . show
    let ms0 = initLLVMMethodSpec pos sbe cb (fromString funcname)
        lsctx0 = LLVMSetupState {
                    lsSpec = ms0
                  , lsTactic = Skip
                  , lsContext = scLLVM
                  , lsSimulate = True
                  , lsSatBranches = False
                  }
    (_, lsctx) <- runStateT setup lsctx0
    let ms = lsSpec lsctx
    let vp = VerifyParams { vpCode = cb
                          , vpContext = scLLVM
                          , vpOpts = opts
                          , vpSpec = ms
                          , vpOver = overrides
                          }
    let verb = verbLevel opts
    let overrideText =
          case overrides of
            [] -> ""
            irs -> " (overriding " ++ show (map specFunction irs) ++ ")"
    when (verb >= 2) $ io $ putStrLn $ "Starting verification of " ++ show (specName ms)
    let lopts = LSSOpts { optsErrorPathDetails = True
                        , optsSatAtBranches = lsSatBranches lsctx
                        }
    ro <- getTopLevelRO
    rw <- getTopLevelRW
    if lsSimulate lsctx then io $ do
      when (verb >= 3) $ do
        putStrLn $ "Executing " ++ show (specName ms)
      ms' <- runSimulator cb sbe mem (Just lopts) $ do
        setVerbosity verb
        (initPS, otherPtrs, args) <- initializeVerification' scLLVM file ms
        dumpMem 4 "llvm_verify pre" Nothing
        let ovdsByFunction = groupBy ((==) `on` specFunction) $
                             sortBy (compare `on` specFunction) $
                             vpOver vp
        mapM_ (overrideFromSpec scLLVM (specPos ms)) ovdsByFunction
        run
        dumpMem 4 "llvm_verify post" Nothing
        res <- checkFinalState scLLVM ms initPS otherPtrs args
        when (verb >= 3) $ liftIO $ do
          putStrLn "Verifying the following:"
          print (ppPathVC res)
        case lsTactic lsctx of
             Skip -> do
                liftIO $ putStrLn $
                   "WARNING: skipping verification of " ++ show (specName ms)
                return ms
             RunVerify script -> do
                let prv = prover opts scLLVM ms script
                stats <- liftIO $ fmap fst $ runTopLevel (runValidation prv vp scLLVM [res]) ro rw
                return ms { specSolverStats = stats }
      putStrLn $ "Successfully verified " ++
                   show (specName ms) ++ overrideText
      return ms'
    else do
      io $ putStrLn $ "WARNING: skipping simulation of " ++ show (specName ms)
      return ms

prover :: Options
       -> SharedContext
       -> LLVMMethodSpecIR
       -> ProofScript SV.SatResult
       -> VerifyState
       -> Term
       -> TopLevel SolverStats
prover opts sc ms script vs g = do
  let exts = getAllExts g
      verb = verbLevel opts
  ppopts <- fmap rwPPOpts getTopLevelRW
  tt <- io (scAbstractExts sc exts g)
  r <- evalStateT script (startProof (ProofGoal Universal (vsVCName vs) tt))
  case r of
    SV.Unsat stats -> do
        when (verb >= 3) $ io $ putStrLn "Valid."
        return stats
    SV.SatMulti _stats vals -> do
        io $ showCexResults sc ppopts ms vs exts vals
        return mempty

showCexResults :: SharedContext
               -> SV.PPOpts
               -> LLVMMethodSpecIR
               -> VerifyState
               -> [ExtCns Term]
               -> [(String, FiniteValue)]
               -> IO ()
showCexResults sc opts ms vs exts vals = do
  putStrLn $ "When verifying " ++ show (specName ms) ++ ":"
  putStrLn $ "Proof of " ++ vsVCName vs ++ " failed."
  putStrLn $ "Counterexample:"
  let showVal v = show <$> (Cryptol.runEval (Cryptol.ppValue (cryptolPPOpts opts) (exportFiniteValue v)))
  mapM_ (\(n, v) -> do vdoc <- showVal v
                       putStrLn ("  " ++ n ++ ": " ++ vdoc)) vals
  if (length exts == length vals)
    then vsCounterexampleFn vs (cexEvalFn sc (zip exts (map snd vals))) >>= print
    else putStrLn "ERROR: Can't show result, wrong number of values"
  fail "Proof failed."

llvmPure :: LLVMSetup ()
llvmPure = return ()

type LLVMExprParser a = ParsecT String () IO a

failLeft :: (Monad m, Show s) => m (Either s a) -> m a
failLeft act = either (fail . show) return =<< act

checkProtoLLVMExpr :: (Monad m) =>
                      Codebase SAWBackend
                   -> FunDecl
                   -> Maybe [CB.Ident]
                   -> ProtoLLVMExpr
                   -> ExceptT String m LLVMExpr
checkProtoLLVMExpr cb fnDecl margs pe =
  case pe of
    PReturn ->
      case fdRetType fnDecl of
        Just ty -> return (CC.Term (ReturnValue ty))
        Nothing -> throwE "Function with void return type used with `return`."
    PVar x -> do
      let nid = fromString x
      case join (lookup nid <$> namedArgs) of
        Just (n, ty) -> return (CC.Term (Arg n nid ty))
        Nothing ->
          case lookupSym (Symbol x) cb of
            Just (Left gb) ->
              return (CC.Term (Global (CB.globalSym gb) (CB.globalType gb)))
            _ -> throwE $ "Unknown variable: " ++ x
    PArg n | n < length argTys ->
               return (CC.Term (Arg n (fromString ("args[" ++ show n ++ "]")) (argTys !! n)))
           | otherwise ->
               throwE $ "(Zero-based) argument index too large: " ++ show n
    PDeref de -> do
      e <- checkProtoLLVMExpr cb fnDecl margs de
      case lssTypeOfLLVMExpr e of
        PtrType (MemType ty) -> return (CC.Term (Deref e ty))
        ty -> throwE $
              "Attempting to apply * operation to non-pointer, of type " ++
              show (ppActualType ty)
    PField n se -> do
      e <- checkProtoLLVMExpr cb fnDecl margs se
      case resolveType cb (lssTypeOfLLVMExpr e) of
        PtrType (MemType (StructType si))
          | n < siFieldCount si -> do
            let ty = fiType (siFields si V.! n)
            return (CC.Term (StructField e si n ty))
          | otherwise -> throwE $ "Field out of range: " ++ show n
        ty ->
          throwE $ "Left side of -> is not a struct pointer: " ++
                   show (ppActualType ty)
    PDirectField n se -> do
      e <- checkProtoLLVMExpr cb fnDecl margs se
      case resolveType cb (lssTypeOfLLVMExpr e) of
        StructType si
          | n < siFieldCount si -> do
            let ty = fiType (siFields si V.! n)
            return (CC.Term (StructDirectField e si n ty))
          | otherwise -> throwE $ "Field out of range: " ++ show n
        ty ->
          throwE $ "Left side of . is not a struct: " ++
                   show (ppActualType ty)
  where
    argTys = map (resolveType cb) (fdArgTypes fnDecl)
    numArgs = zip [(0::Int)..] argTys
    namedArgs = flip zip numArgs <$> margs

parseLLVMExpr :: (Monad m) =>
                 Codebase SAWBackend
              -> Symbol
              -> String
              -> ExceptT String m LLVMExpr
parseLLVMExpr cb fn str = do
  fnDecl <- case lookupFunctionType fn cb of
              Just fd -> return fd
              Nothing -> fail $ "Function " ++ show fn ++ " neither declared nor defined."
  let margs = case lookupDefine fn cb of
                Just fd -> Just (map fst (sdArgs fd))
                Nothing -> Nothing
  case parseProtoLLVMExpr str of
    Left err -> throwE ("Parse error: " ++ show err)
    Right e -> checkProtoLLVMExpr cb fnDecl margs e

getLLVMExpr :: Monad m =>
               LLVMMethodSpecIR -> String
            -> m (LLVMExpr, MemType)
getLLVMExpr ms name = do
  case Map.lookup name (specLLVMExprNames ms) of
    -- TODO: maybe compute type differently?
    Just (_, expr) -> return (expr, lssTypeOfLLVMExpr expr)
    Nothing -> fail $ "LLVM name " ++ name ++ " has not been declared."

mkMixedExpr :: LLVMMethodSpecIR
            -> SharedContext
            -> Term
            -> LLVMSetup MixedExpr
mkMixedExpr ms _ (asLLVMExpr -> Just s) =
  (LLVME . fst) <$> getLLVMExpr ms s
mkMixedExpr ms sc t = LogicE <$> mkLogicExpr ms sc t


mkLogicExpr :: LLVMMethodSpecIR
            -> SharedContext
            -> Term
            -> LLVMSetup LogicExpr
mkLogicExpr ms sc t = do
  let exts = getAllExts t
      extNames = map ecName exts
  les <- mapM (getLLVMExpr ms) extNames
  fn <- liftIO $ scAbstractExts sc exts t
  return $ LogicExpr fn (map fst les)

llvmInt :: Int -> SymType
llvmInt n = MemType (IntType n)

llvmFloat :: SymType
llvmFloat = MemType FloatType

llvmDouble :: SymType
llvmDouble = MemType DoubleType

llvmArray :: Int -> SymType -> SymType
llvmArray n (MemType t) = MemType (ArrayType n t)
llvmArray _ t =
  error $ "Unsupported array element type: " ++ show (ppSymType t)

llvmStruct :: String -> SymType
llvmStruct n = Alias (fromString n)

llvmNoSimulate :: LLVMSetup ()
llvmNoSimulate = modify (\s -> s { lsSimulate = False })

llvmSatBranches :: Bool -> LLVMSetup ()
llvmSatBranches doSat = modify (\s -> s { lsSatBranches = doSat })

llvmVar :: BuiltinContext -> Options -> String -> SymType
        -> LLVMSetup TypedTerm
llvmVar bic _ name sty = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
  lty <- case resolveSymType cb sty of
           MemType mty -> return mty
           rty -> fail $ "Unsupported type in llvm_var: " ++ show (ppSymType rty)
  expr <- failLeft $ runExceptT $ parseLLVMExpr cb func name
  when (isPtrLLVMExpr expr) $ fail $
    "Used `llvm_var` for pointer expression `" ++ name ++
    "`. Use `llvm_ptr` instead."
  -- TODO: check compatibility before updating
  let expr' = updateLLVMExprType expr lty
  modify $ \st ->
    st { lsSpec = specAddVarDecl fixPos name expr' lty (lsSpec st) }
  let sc = biSharedContext bic
  mty <- liftIO $ logicTypeOfActual sc lty
  case mty of
    Just ty -> liftIO $ scLLVMValue sc ty name >>= mkTypedTerm sc
    Nothing -> fail $ "Unsupported type in llvm_var: " ++ show (ppMemType lty)

llvmPtr :: BuiltinContext -> Options -> String -> SymType
        -> LLVMSetup ()
llvmPtr _ _ name sty = do
  lsState <- get
  let ms = lsSpec lsState
      func = specFunction ms
      cb = specCodebase ms
  lty <- case resolveSymType cb sty of
           MemType mty -> return mty
           Alias i -> fail $ "Unexpected type alias in llvm_ptr: " ++ show i
           rty -> fail $ "Unsupported type in llvm_ptr: " ++ show (ppSymType rty)
  expr <- failLeft $ runExceptT $ parseLLVMExpr cb func name
  unless (isPtrLLVMExpr expr) $ fail $
    "Used `llvm_ptr` for non-pointer expression `" ++ name ++
    "`. Use `llvm_var` instead."
  let pty = PtrType (MemType lty)
      -- TODO: check compatibility before updating
      expr' = updateLLVMExprType expr pty
  modify $ \st ->
    st { lsSpec = specAddVarDecl fixPos name expr' pty (lsSpec st) }

checkCompatibleType :: String -> LLVMActualType -> Cryptol.Schema
                    -> LLVMSetup ()
checkCompatibleType msg aty schema = liftIO $ do
  case cryptolTypeOfActual aty of
    Nothing ->
      fail $ "Type is not translatable: " ++ show (ppMemType aty) ++
             " (" ++ msg ++ ")"
    Just lt -> do
      unless (Cryptol.Forall [] [] lt == schemaNoUser schema) $ fail $
        unlines [ "Incompatible type:"
                , "  Expected: " ++ Cryptol.pretty lt
                , "  Got: " ++ Cryptol.pretty schema
                , "  In context: " ++ msg
                ]

llvmAssert :: BuiltinContext -> Options -> Term
           -> LLVMSetup ()
llvmAssert bic _ v = do
  let sc = biSharedContext bic
  ms <- gets lsSpec
  liftIO $ checkBoolean sc v
  me <- mkMixedExpr ms sc v
  le <- case me of
          LogicE le -> return le
          _ -> fail "LLVM expressions not allowed on the right hand side of `llvm_assert`"
  modify $ \st ->
    st { lsSpec = specAddAssumption le (lsSpec st) }

llvmAssertEq :: BuiltinContext -> Options -> String -> TypedTerm -> LLVMSetup ()
llvmAssertEq bic _opts name (TypedTerm schema t) = do
  let sc = biSharedContext bic
  ms <- gets lsSpec
  (expr, mty) <- getLLVMExpr ms name
  me <- mkMixedExpr ms sc t
  le <- case me of
          LogicE le -> return le
          _ -> fail "LLVM expressions not allowed on the right hand side of `llvm_assert_eq`"
  checkCompatibleType "llvm_assert_eq" mty schema
  modify $ \st ->
    st { lsSpec = specAddLogicAssignment fixPos expr le ms }

llvmEnsureEq :: BuiltinContext -> Options -> String -> TypedTerm -> LLVMSetup ()
llvmEnsureEq bic _opts name (TypedTerm schema t) = do
  ms <- gets lsSpec
  let sc = biSharedContext bic
  (expr, mty) <- getLLVMExpr ms name
  checkCompatibleType "llvm_ensure_eq" mty schema
  me <- mkMixedExpr ms sc t
  let cmd = Ensure fixPos expr me
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }

llvmReturn :: BuiltinContext -> Options -> TypedTerm -> LLVMSetup ()
llvmReturn bic _opts (TypedTerm schema t) = do
  let sc = biSharedContext bic
  ms <- gets lsSpec
  let cb = specCodebase ms
  me <- mkMixedExpr ms sc t
  case fdRetType <$> lookupFunctionType (specFunction ms) cb of
    Just (Just mty) -> do
      checkCompatibleType "llvm_return" mty schema
      let cmd = Return me
      modify $ \st ->
        st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }
    Just Nothing -> fail "llvm_return called on void function"
    Nothing -> fail "llvm_return called inside non-existant function?"

llvmVerifyTactic :: BuiltinContext -> Options
                 -> ProofScript SV.SatResult
                 -> LLVMSetup ()
llvmVerifyTactic _ _ script =
  -- TODO: complain if tactic provided more than once
  modify $ \st -> st { lsTactic = RunVerify script }


llvmSpecSolvers :: LLVMMethodSpecIR -> [String]
llvmSpecSolvers = Set.toList . solverStatsSolvers . specSolverStats

llvmSpecSize :: LLVMMethodSpecIR -> Integer
llvmSpecSize = solverStatsGoalSize . specSolverStats
