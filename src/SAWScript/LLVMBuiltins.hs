{- |
Module      : SAWScript.LLVMBuiltins
Description : Implementations of LLVM-related SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
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
{-# LANGUAGE LambdaCase #-}

module SAWScript.LLVMBuiltins where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (many)
#endif
import Control.Lens
import Control.Monad.State hiding (mapM)
import Control.Monad.ST (stToIO)
import Control.Monad.Trans.Except
import Data.Function (on)
import Data.List (find, partition, sortBy, groupBy)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.String
import qualified Data.Vector as V
import Text.Parsec as P

import Text.LLVM (modDataLayout)
import qualified Text.LLVM.AST as LLVM
import qualified Data.LLVM.BitCode as LLVM
import qualified Text.LLVM.PP as LLVM
import qualified Text.LLVM.DebugUtils as DU
import qualified Text.LLVM.Parser as LLVM (parseType)
import Verifier.LLVM.Backend
import Verifier.LLVM.Codebase hiding ( Global, ppSymbol, ppIdent
                                     , globalSym, globalType
                                     )
import qualified Verifier.LLVM.Codebase as CB
import Verifier.LLVM.Codebase.LLVMContext (liftMemType)
import Verifier.LLVM.Backend.SAW
import Verifier.LLVM.Simulator
import Verifier.LLVM.Simulator.Internals

import Verifier.SAW.Cryptol (exportFirstOrderValue)
import Verifier.SAW.FiniteValue (FirstOrderValue)
import Verifier.SAW.Recognizer (asExtCns)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import Verifier.SAW.CryptolEnv (schemaNoUser)

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.Builtins
import SAWScript.LLVMExpr
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMMethodSpec
import SAWScript.LLVMUtils
import SAWScript.Options as Opt
import SAWScript.Proof
import SAWScript.Prover.SolverStats
import SAWScript.Utils
import SAWScript.Value as SV

import qualified SAWScript.CrucibleLLVM as Crucible (translateModule)
import qualified Cryptol.Eval.Monad as Cryptol (runEval)
import qualified Cryptol.Eval.Value as Cryptol (ppValue)
import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Utils.PP as Cryptol (pretty)

import qualified Data.AIG as AIG

type Backend = SAWBackend
type SAWTerm = Term
type SAWDefine = SymDefine SAWTerm

llvm_load_module :: FilePath -> TopLevel LLVMModule
llvm_load_module file =
  io (LLVM.parseBitCodeFromFile file) >>= \case
    Left err -> fail (LLVM.formatError err)
    Right llvm_mod -> do
      halloc <- getHandleAlloc
      mtrans <- io $ stToIO $ Crucible.translateModule halloc llvm_mod
      return (LLVMModule file llvm_mod mtrans)

-- LLVM verification and model extraction commands

type Assign = (LLVMExpr, TypedTerm)

startSimulator :: (AIG.IsAIG l g) =>
                  Options
               -> SharedContext
               -> LSSOpts
               -> LLVMModule
               -> Symbol
               -> AIG.Proxy l g
               -> (SharedContext
                   -> SBE SAWBackend
                   -> Codebase SAWBackend
                   -> DataLayout
                   -> SymDefine Term
                   -> Simulator SAWBackend IO a)
               -> IO a
startSimulator opts sc lopts (LLVMModule file mdl _) sym proxy body = do
  let dl = parseDataLayout $ modDataLayout mdl
  (sbe, mem, scLLVM) <- createSAWBackend' proxy dl sc
  (warnings, cb) <- mkCodebase sbe dl mdl
  forM_ warnings $ printOutLn opts Warn . ("WARNING: " ++) . show
  case lookupDefine sym cb of
    Nothing -> fail $ missingSymMsg file sym
    Just md -> runSimulator cb sbe mem (Just lopts) $
               body scLLVM sbe cb dl md

llvm_symexec :: BuiltinContext
             -> Options
             -> LLVMModule
             -> String
             -> [(String, Integer)]
             -> [(String, Term, Integer)]
             -> [(String, Integer)]
             -> Bool
             -> TopLevel TypedTerm
llvm_symexec bic opts lmod fname allocs inputs outputs doSat = do
  AIGProxy proxy <- getProxy
  let sym = Symbol fname
      sc = biSharedContext bic
      lopts = LSSOpts { optsErrorPathDetails = True
                      , optsSatAtBranches = doSat
                      , optsSimplifyAddrs = False
                      }
  liftIO $ startSimulator opts sc lopts lmod sym proxy $ \scLLVM sbe cb dl md -> do
        setVerbosity (simVerbose opts)
        let mkAssign (s, tm, n) = do
              e <- failLeft $ runExceptT $ parseLLVMExpr lmod cb sym s
              return (e, tm, n)
            mkAllocAssign (s, n) = do
              e <- failLeft $ runExceptT $ parseLLVMExpr lmod cb sym s
              case resolveType cb (lssTypeOfLLVMExpr e) of
                PtrType (MemType ty) -> do
                  liftIO $ printOutLn opts Debug $
                    "Allocating " ++ show n ++ " elements of type " ++ show (ppActualType ty)
                  tm <- allocSome sbe dl n ty
                  liftIO $ printOutLn opts Debug $
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
        mapM_ (writeLLVMTerm Nothing argVals) otherAssigns
        liftIO $ printOutLn opts Info $ "Running " ++ fname
        run
        liftIO $ printOutLn opts Info $ "Finished running " ++ fname
        outtms <- forM outputs $ \(ostr, n) -> do
          case ostr of
            "$safety" -> do
              mp <- getPath
              case mp of
                Nothing -> fail "No final path for safety condition."
                Just p -> return (p ^. pathAssertions)
            _ -> do
              e <- failLeft $ runExceptT $ parseLLVMExpr lmod cb sym ostr
              readLLVMTerm Nothing argVals e n
        let bundle tms = case tms of
                           [t] -> return t
                           _ -> scTuple scLLVM tms
        liftIO (mkTypedTerm scLLVM =<< bundle outtms)


-- | Extract a simple, pure model from the given symbol within the
-- given bitcode file. This code creates fresh inputs for all arguments and
-- returns a lambda term representing the return value as a function of the
-- arguments. Many verifications will require more complex execution contexts.
llvm_extract :: BuiltinContext
             -> Options
             -> LLVMModule
             -> String
             -> LLVMSetup ()
             -> TopLevel TypedTerm
llvm_extract bic opts lmod func _setup = do
  let sym = Symbol func
      sc = biSharedContext bic
      lopts = LSSOpts { optsErrorPathDetails = True
                      , optsSatAtBranches = True
                      , optsSimplifyAddrs = False
                      }
  AIGProxy proxy <- getProxy
  liftIO $ startSimulator opts sc lopts lmod sym proxy $ \scLLVM _sbe _cb _dl md -> do
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

llvm_verify :: BuiltinContext
            -> Options
            -> LLVMModule
            -> String
            -> [LLVMMethodSpecIR]
            -> LLVMSetup ()
            -> TopLevel LLVMMethodSpecIR
llvm_verify bic opts lmod@(LLVMModule file mdl _) funcname overrides setup = do
  let pos = fixPos -- TODO
      dl = parseDataLayout $ modDataLayout mdl
      sc = biSharedContext bic
  AIGProxy proxy <- getProxy
  (sbe, mem, scLLVM) <- io $ createSAWBackend' proxy dl sc
  (warnings, cb) <- io $ mkCodebase sbe dl mdl
  forM_ warnings $ printOutLnTop Warn . ("WARNING: " ++) . show
  let ms0 = initLLVMMethodSpec pos sbe cb (fromString funcname)
      lsctx0 = LLVMSetupState {
                    lsSpec = ms0
                  , lsTactic = Skip
                  , lsContext = scLLVM
                  , lsSimulate = True
                  , lsSatBranches = False
                  , lsSimplifyAddrs = False
                  , lsModule        = lmod
                  }
  (_, lsctx) <- runStateT setup lsctx0
  let ms = lsSpec lsctx
  let vp = VerifyParams { vpCode = cb
                        , vpContext = scLLVM
                        , vpOpts = opts
                        , vpSpec = ms
                        , vpOver = overrides
                        }
  let overrideText =
        case overrides of
          [] -> ""
          irs -> " (overriding " ++ show (map specFunction irs) ++ ")"
  printOutLnTop Info $ "Starting verification of " ++ show (specName ms)
  let lopts = LSSOpts { optsErrorPathDetails = True
                      , optsSatAtBranches = lsSatBranches lsctx
                      , optsSimplifyAddrs = lsSimplifyAddrs lsctx
                      }
  ro <- getTopLevelRO
  rw <- getTopLevelRW
  vpopts <- getOptions
  if lsSimulate lsctx then io $ do
      liftIO $ printOutLn vpopts Info $ "Executing " ++ show (specName ms)
      ms' <- runSimulator cb sbe mem (Just lopts) $ do
        setVerbosity (simVerbose opts)
        (initPS, otherPtrs, args) <- initializeVerification' scLLVM file ms
        dumpMem 4 "llvm_verify pre" Nothing
        let ovdsByFunction = groupBy ((==) `on` specFunction) $
                             sortBy (compare `on` specFunction) $
                             vpOver vp
        mapM_ (overrideFromSpec (vpOpts vp) scLLVM (specPos ms)) ovdsByFunction
        run
        dumpMem 4 "llvm_verify post" Nothing
        res <- checkFinalState scLLVM ms initPS otherPtrs args
        liftIO $ printOutFn vpopts Debug "Verifying the following:"
        liftIO $ printOutLn vpopts Debug $ show (ppPathVC res)
        case lsTactic lsctx of
             Skip -> do
                liftIO $ printOutLn vpopts Warn $
                   "WARNING: skipping verification of " ++ show (specName ms)
                return ms
             RunVerify script -> do
                let prv = prover opts scLLVM ms script
                stats <- liftIO $ fmap fst $ runTopLevel (runValidation prv vp scLLVM [res]) ro rw
                return ms { specSolverStats = stats }
      printOutLn vpopts Info $ "Successfully verified " ++
                   show (specName ms) ++ overrideText
      return ms'
    else do
      printOutLnTop Warn $ "WARNING: skipping simulation of " ++ show (specName ms)
      return ms

prover :: Options
       -> SharedContext
       -> LLVMMethodSpecIR
       -> ProofScript SV.SatResult
       -> VerifyState
       -> Int
       -> Term
       -> TopLevel SolverStats
prover vpopts sc ms script vs n g = do
  let exts = getAllExts g
  ppopts <- fmap rwPPOpts getTopLevelRW
  tt <- io $ scGeneralizeExts sc exts =<< scEqTrue sc g
  let goal = ProofGoal n "vc" (vsVCName vs) tt
  r <- evalStateT script (startProof goal)
  case r of
    SV.Unsat stats -> do
        printOutLnTop Info "Valid."
        return stats
    SV.SatMulti _stats vals -> do
        io $ showCexResults vpopts sc ppopts ms vs exts vals
        return mempty

showCexResults :: Options
               -> SharedContext
               -> SV.PPOpts
               -> LLVMMethodSpecIR
               -> VerifyState
               -> [ExtCns Term]
               -> [(String, FirstOrderValue)]
               -> IO ()
showCexResults vpopts sc opts ms vs exts vals = do
  printOutLn vpopts Info $ "When verifying " ++ show (specName ms) ++ ":"
  printOutLn vpopts Info $ "Proof of " ++ vsVCName vs ++ " failed."
  printOutLn vpopts OnlyCounterExamples $ "----------Counterexample----------"
  let showVal v = show <$> (Cryptol.runEval SV.quietEvalOpts (Cryptol.ppValue (cryptolPPOpts opts) (exportFirstOrderValue v)))
  mapM_ (\(n, v) -> do vdoc <- showVal v
                       printOutLn vpopts OnlyCounterExamples ("  " ++ n ++ ": " ++ vdoc)) vals
  if (length exts == length vals)
    then vsCounterexampleFn vs (cexEvalFn sc (zip exts (map snd vals))) >>= printOutLn vpopts OnlyCounterExamples . show
    else printOutLn vpopts Opt.Error "ERROR: Can't show result, wrong number of values"
  printOutLn vpopts Opt.Error "Proof failed."
  exitProofFalse

llvm_pure :: LLVMSetup ()
llvm_pure = return ()

type LLVMExprParser a = ParsecT String () IO a

failLeft :: (Monad m, Show s) => m (Either s a) -> m a
failLeft act = either (fail . show) return =<< act

checkProtoLLVMExpr ::
  Monad m =>
  Codebase SAWBackend         {- ^ current codebase                -} ->
  FunDecl                     {- ^ function declaration            -} ->
  Map.Map CB.Ident CB.Ident   {- ^ function argument map           -} ->
  DU.Info                     {- ^ return type information         -} ->
  Maybe [(CB.Ident, DU.Info)] {- ^ argument type information       -} ->
  ProtoLLVMExpr               {- ^ parsed expression               -} ->
  ExceptT String m (LLVMExpr, DU.Info)
checkProtoLLVMExpr cb fnDecl dbgArgNames retinfo margs pe =
  case pe of
    PReturn ->
      case fdRetType fnDecl of
        Just ty -> return (CC.Term (ReturnValue ty), retinfo)
        Nothing -> throwE "Function with void return type used with `return`."
    PVar x0 -> do
      let CB.Ident x = Map.findWithDefault (Ident x0) (Ident x0) dbgArgNames
      let nid = fromString x
      case lookup nid =<< namedArgs of
        Just (n,ty,info) ->
          return (CC.Term (Arg n nid ty),info)
        Nothing ->
          case lookupSym (Symbol x) cb of
            Just (Left gb) ->
              return (CC.Term (Global (CB.globalSym gb) (CB.globalType gb)), DU.Unknown) -- XXX: info missing for globals
            _ -> throwE $ "Unknown variable: " ++ x
    PArg n | n < length argTys ->
               return (CC.Term (Arg n (fromString ("args[" ++ show n ++ "]")) (argTys !! n)), DU.Unknown)
           | otherwise ->
               throwE $ "(Zero-based) argument index too large: " ++ show n
    PDeref de -> do
      (e,info) <- checkProtoLLVMExpr cb fnDecl dbgArgNames retinfo margs de
      case lssTypeOfLLVMExpr e of
        PtrType (MemType ty) -> return (CC.Term (Deref e ty), DU.derefInfo info)
        ty -> throwE $
              "Attempting to apply * operation to non-pointer, of type " ++
              show (ppActualType ty)
    PField n se -> do
      (e,info) <- checkProtoLLVMExpr cb fnDecl dbgArgNames retinfo margs se
      let info1 = DU.derefInfo info

      i <- resolveField info1 n

      case resolveType cb (lssTypeOfLLVMExpr e) of
        PtrType (MemType (StructType si))
          | i < siFieldCount si -> do
            let ty = fiType (siFields si V.! i)
            return (CC.Term (StructField e si i ty), DU.fieldIndexByPosition i info1)
          | otherwise -> throwE $ "Field out of range: " ++ show i
        ty ->
          throwE $ "Left side of -> is not a struct pointer: " ++
                   show (ppActualType ty)
    PDirectField n se -> do
      (e,info) <- checkProtoLLVMExpr cb fnDecl dbgArgNames retinfo margs se

      i <- resolveField info n

      case resolveType cb (lssTypeOfLLVMExpr e) of
        StructType si
          | i < siFieldCount si -> do
            let ty = fiType (siFields si V.! i)
            return (CC.Term (StructDirectField e si i ty), DU.fieldIndexByPosition i info)
          | otherwise -> throwE $ "Field out of range: " ++ show i
        ty ->
          throwE $ "Left side of . is not a struct: " ++
                   show (ppActualType ty)
  where
    argTys = map (resolveType cb) (fdArgTypes fnDecl)
    numArgs = zip [(0::Int)..] argTys
    namedArgs = (\xs -> [ (name, (i, ty, info)) | ((name,info),(i,ty)) <- zip xs numArgs]) <$> margs

    resolveField _ (FieldIndex i) = return i
    resolveField DU.Unknown (FieldName name) =
      throwE ("Field names not available for resolving: " ++ name)
    resolveField info (FieldName name) =
      case DU.fieldIndexByName name info of
        Nothing -> throwE ("Unknown field: " ++ name)
        Just i  -> return i


parseLLVMExpr ::
  Monad m =>
  LLVMModule          {- ^ current module   -} ->
  Codebase SAWBackend {- ^ current codebase -} ->
  Symbol              {- ^ function name    -} ->
  String              {- ^ expression       -} ->
  ExceptT String m LLVMExpr
parseLLVMExpr lmod cb fn str = do
  fnDecl <- case lookupFunctionType fn cb of
              Just fd -> return fd
              Nothing -> fail $ "Function " ++ show fn ++ " neither declared nor defined."

  let retInfo:argInfos = fromMaybe [] (DU.computeFunctionTypes (modMod lmod) fn)
                      ++ repeat DU.Unknown

  let margs = fmap (\fd -> zip (fst <$> sdArgs fd) argInfos)
                   (lookupDefine fn cb)

      argDbgNames = localVarMap (modMod lmod) fn

  case parseProtoLLVMExpr str of
    Left err -> throwE ("Parse error: " ++ show err)
    Right e -> fst <$> checkProtoLLVMExpr cb fnDecl argDbgNames retInfo margs e

localVarMap :: LLVM.Module -> Symbol -> Map.Map CB.Ident CB.Ident
localVarMap m fn =
  case find (\def -> LLVM.defName def == fn) (LLVM.modDefines m) of
    Nothing -> Map.empty
    Just def -> DU.localVariableNameDeclarations (DU.mkMdMap m) def


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

llvm_type :: String -> TopLevel LLVM.Type
llvm_type str =
  case LLVM.parseType str of
    Left e -> fail (show e)
    Right t -> return t

llvm_int :: Int -> LLVM.Type
llvm_int n = LLVM.PrimType (LLVM.Integer (fromIntegral n))

llvm_float :: LLVM.Type
llvm_float = LLVM.PrimType (LLVM.FloatType LLVM.Float)

llvm_double :: LLVM.Type
llvm_double = LLVM.PrimType (LLVM.FloatType LLVM.Double)

llvm_array :: Int -> LLVM.Type -> LLVM.Type
llvm_array n t = LLVM.Array (fromIntegral n) t

llvm_struct :: String -> LLVM.Type
llvm_struct n = LLVM.Alias (fromString n)

llvm_no_simulate :: LLVMSetup ()
llvm_no_simulate = modify (\s -> s { lsSimulate = False })

llvm_sat_branches :: Bool -> LLVMSetup ()
llvm_sat_branches doSat = modify (\s -> s { lsSatBranches = doSat })

llvm_simplify_addrs :: Bool -> LLVMSetup ()
llvm_simplify_addrs doSimp = modify (\s -> s { lsSimplifyAddrs = doSimp })

llvm_var :: BuiltinContext -> Options -> String -> LLVM.Type
         -> LLVMSetup TypedTerm
llvm_var bic _ name sty = do
  lsState <- get
  let lmod = lsModule lsState
      ms   = lsSpec lsState
      func = specFunction ms
      cb   = specCodebase ms
      dl   = cbDataLayout cb
  let ?lc  = cbLLVMContext cb
  lty <- case liftMemType sty of
           Just mty -> return mty
           Nothing -> fail $ "Unsupported type in llvm_var: " ++ show (LLVM.ppType sty)
  expr <- failLeft $ runExceptT $ parseLLVMExpr lmod cb func name
  when (isPtrLLVMExpr expr) $ fail $
    "Used `llvm_var` for pointer expression `" ++ name ++
    "`. Use `llvm_ptr` instead."
  -- TODO: check compatibility before updating
  let expr' = updateLLVMExprType expr lty
  modify $ \st ->
    st { lsSpec = specAddVarDecl fixPos name expr' lty (lsSpec st) }
  let sc = biSharedContext bic
  mty <- liftIO $ logicTypeOfActual dl sc lty
  case mty of
    Just ty -> liftIO $ scLLVMValue sc ty name >>= mkTypedTerm sc
    Nothing -> fail $ "Unsupported type in llvm_var: " ++ show (ppMemType lty)

llvm_ptr :: BuiltinContext -> Options -> String -> LLVM.Type
        -> LLVMSetup ()
llvm_ptr _ _ name sty = do
  lsState <- get
  let ms   = lsSpec lsState
      func = specFunction ms
      cb   = specCodebase ms
      lmod = lsModule lsState
  let ?lc  = cbLLVMContext cb
  lty <- case liftMemType sty of
           Just mty -> return mty
           Nothing -> fail $ "Unsupported type in llvm_ptr: " ++ show (LLVM.ppType sty)
  expr <- failLeft $ runExceptT $ parseLLVMExpr lmod cb func name
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

llvm_assert :: BuiltinContext -> Options -> Term
            -> LLVMSetup ()
llvm_assert bic _ v = do
  let sc = biSharedContext bic
  ms <- gets lsSpec
  me <- mkMixedExpr ms sc v
  le <- case me of
          LogicE le -> return le
          _ -> fail "LLVM expressions not allowed on the right hand side of `llvm_assert`"
  modify $ \st ->
    st { lsSpec = specAddAssumption le (lsSpec st) }

llvm_assert_eq :: BuiltinContext -> Options -> String -> TypedTerm -> LLVMSetup ()
llvm_assert_eq bic _opts name (TypedTerm schema t) = do
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

llvm_assert_null :: BuiltinContext -> Options -> String -> LLVMSetup ()
llvm_assert_null _bic _opts name = do
  ms <- gets lsSpec
  (expr, mty) <- getLLVMExpr ms name
  enull <- case mty of
             PtrType _ -> liftIO $ llvmNullPtr (specBackend ms) (MemType mty)
             _ -> fail $ unwords
                  [ "llvm_assert_null called with non-pointer expression"
                  , name
                  , "of type"
                  , show (ppMemType mty)
                  ]
  let le = LogicExpr enull []
  modify $ \st ->
    st { lsSpec = specAddLogicAssignment fixPos expr le ms }

llvm_ensure_eq :: Bool -> BuiltinContext -> Options -> String -> TypedTerm -> LLVMSetup ()
llvm_ensure_eq post bic _opts name (TypedTerm schema t) = do
  ms <- gets lsSpec
  let sc = biSharedContext bic
  (expr, mty) <- getLLVMExpr ms name
  checkCompatibleType "llvm_ensure_eq" mty schema
  me <- mkMixedExpr ms sc t
  let cmd = Ensure post fixPos expr me
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }

llvm_modify :: BuiltinContext -> Options -> String -> LLVMSetup ()
llvm_modify _bic _opts name = do
  ms <- gets lsSpec
  (expr, mty) <- getLLVMExpr ms name
  let cmd = Modify expr mty
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }

llvm_return :: BuiltinContext -> Options -> TypedTerm -> LLVMSetup ()
llvm_return bic _opts (TypedTerm schema t) = do
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

llvm_return_arbitrary :: LLVMSetup ()
llvm_return_arbitrary = do
  ms <- gets lsSpec
  let cb = specCodebase ms
  case fdRetType <$> lookupFunctionType (specFunction ms) cb of
    Just (Just mty) -> do
      let cmd = ReturnArbitrary mty
      modify $ \st ->
        st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }
    Just Nothing -> fail "llvm_return_arbitrary called on void function"
    Nothing -> fail "llvm_return_arbitrary called inside non-existant function?"

llvm_verify_tactic :: BuiltinContext -> Options
                 -> ProofScript SV.SatResult
                 -> LLVMSetup ()
llvm_verify_tactic _ _ script =
  -- TODO: complain if tactic provided more than once
  modify $ \st -> st { lsTactic = RunVerify script }


llvm_spec_solvers :: LLVMMethodSpecIR -> [String]
llvm_spec_solvers = Set.toList . solverStatsSolvers . specSolverStats

llvm_spec_size :: LLVMMethodSpecIR -> Integer
llvm_spec_size = solverStatsGoalSize . specSolverStats

llvm_allocates :: String -> LLVMSetup ()
llvm_allocates name = do
  ms <- gets lsSpec
  (expr, mty) <- getLLVMExpr ms name
  let cmd = Allocate expr mty
  modify $ \st ->
    st { lsSpec = specAddBehaviorCommand cmd (lsSpec st) }
