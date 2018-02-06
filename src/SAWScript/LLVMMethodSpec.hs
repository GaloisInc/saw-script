{- |
Module      : SAWScript.LLVMMethodSpec
Description : Interface to the LLVM symbolic simulator.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWScript.LLVMMethodSpec
  ( LLVMMethodSpecIR
  , specFunction
  , specName
  , SymbolicRunHandler
  , initializeVerification'
  , runValidation
  , checkFinalState
  , overrideFromSpec
  , ppPathVC
  , scLLVMValue
  , VerifyParams(..)
  , VerifyState(..)
  , EvalContext(..)
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (empty)
#endif
import Control.Lens
import Control.Monad
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.Foldable (traverse_)
import Data.List (sortBy)
import Data.Ord (comparing)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.LLVMExpr as TC
import SAWScript.Options hiding (Verbosity)
import qualified SAWScript.Options as Opts
import SAWScript.Utils
import Verifier.SAW.Prelude
import SAWScript.LLVMMethodSpecIR
import SAWScript.LLVMUtils
import SAWScript.PathVC
import SAWScript.SolverStats
import SAWScript.Value (TopLevel, TopLevelRW(rwPPOpts), getTopLevelRW, io, printOutLnTop)
import SAWScript.VerificationCheck

import Verifier.LLVM.Simulator hiding (State)
import Verifier.LLVM.Simulator.Internals hiding (State)
import Verifier.LLVM.Codebase
import Verifier.LLVM.Backend hiding (asBool)
import Verifier.LLVM.Backend.SAW

import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm hiding (Ident)

-- | Contextual information needed to evaluate expressions.
data EvalContext
  = EvalContext {
      ecContext :: SharedContext
    , ecOpts :: LSSOpts
    , ecDataLayout :: DataLayout
    , ecBackend :: SBE SpecBackend
    , ecGlobalMap :: GlobalMap SpecBackend
    , ecArgs :: [Term]
    , ecPathState :: SpecPathState
    , ecLLVMExprs :: Map String (TC.LLVMActualType, TC.LLVMExpr)
    , ecFunction :: Symbol
    }

type ExprEvaluator m a = ExceptT TC.LLVMExpr (Simulator SpecBackend m) a

runEval :: MonadIO m =>
           ExprEvaluator m b
        -> Simulator SpecBackend m (Either TC.LLVMExpr b)
runEval v = runExceptT v

-- | Evaluate an LLVM expression, and return its value (r-value) as an
-- internal term.
evalLLVMExpr :: (Functor m, MonadIO m) =>
                TC.LLVMExpr -> EvalContext
             -> ExprEvaluator m SpecLLVMValue
evalLLVMExpr expr ec = eval expr
  where eval (CC.Term app) =
          case app of
            TC.Arg n _ _
                | n < length (ecArgs ec) -> return (ecArgs ec !! n)
                | otherwise ->
                    fail $ "evalLLVMExpr: invalid argument index: " ++ show n
            TC.Global n tp -> lift $ do
              -- TODO: don't discard fst
              snd <$> (loadGlobal (ecGlobalMap ec) n tp ps)
            TC.Deref ae tp -> do
              addr <- evalLLVMExpr ae ec
              -- TODO: don't discard fst
              snd <$> (lift $ loadPathState addr tp ps)
            TC.StructField ae si idx tp ->
              case siFieldOffset si idx of
                Just off -> do
                  saddr <- evalLLVMExpr ae ec
                  addr <- liftIO $ addrPlusOffset sbe (ecDataLayout ec) saddr off
                  -- TODO: don't discard fst
                  snd <$> (lift $ loadPathState addr tp ps)
                Nothing ->
                  fail $ "Struct field index " ++ show idx ++ " out of bounds"
            TC.StructDirectField ve si idx tp -> do
              case siFieldOffset si idx of
                Just off -> do
                  saddr <- evalLLVMRefExpr ve ec
                  addr <- liftIO $ addrPlusOffset sbe (ecDataLayout ec) saddr off
                  -- TODO: don't discard fst
                  snd <$> (lift $ loadPathState addr tp ps)
                Nothing ->
                  fail $ "Struct field index " ++ show idx ++ " out of bounds"
            TC.ReturnValue _ -> fail "return values not yet supported" -- TODO
        sbe = ecBackend ec
        ps = ecPathState ec

-- | Evaluate an LLVM expression, and return the location it describes
-- (l-value) as an internal term.
evalLLVMRefExpr :: (Functor m, MonadIO m) =>
                   TC.LLVMExpr -> EvalContext
                -> ExprEvaluator m SpecLLVMValue
evalLLVMRefExpr expr ec = eval expr
  where eval (CC.Term app) =
          case app of
            TC.Arg _ _ _ -> fail "evalLLVMRefExpr: applied to argument"
            TC.Global n _ -> do
              case Map.lookup n gm of
                Just addr -> return addr
                Nothing ->
                  fail $ "evalLLVMRefExpr: global " ++ show n ++ " not found"
            TC.Deref ae _ -> evalLLVMExpr ae ec
            TC.StructField ae si idx _ ->
              case siFieldOffset si idx of
                Just off -> do
                  addr <- evalLLVMExpr ae ec
                  liftIO $ addrPlusOffset sbe (ecDataLayout ec) addr off
                Nothing ->
                  fail $ "Struct field index " ++ show idx ++ " out of bounds"
            TC.StructDirectField ve si idx _ -> do
              case siFieldOffset si idx of
                Just off -> do
                  addr <- evalLLVMRefExpr ve ec
                  liftIO $ addrPlusOffset sbe (ecDataLayout ec) addr off
                Nothing ->
                  fail $ "Struct field index " ++ show idx ++ " out of bounds"
            TC.ReturnValue _ -> fail "evalLLVMRefExpr: applied to return value"
        sbe = ecBackend ec
        gm = ecGlobalMap ec

-- | Evaluate a typed expression in the context of a particular state.
evalLogicExpr :: (Functor m, MonadIO m) =>
                 TC.LogicExpr -> EvalContext
              -> ExprEvaluator m SpecLLVMValue
evalLogicExpr initExpr ec = do
  let sc = ecContext ec
  args <- forM (TC.logicExprLLVMExprs initExpr) $ \expr ->
          evalLLVMExpr expr ec
  liftIO $ TC.useLogicExpr sc initExpr args

-- | Return Java value associated with mixed expression.
evalMixedExpr :: (Functor m, MonadIO m) =>
                 TC.MixedExpr -> EvalContext
              -> ExprEvaluator m SpecLLVMValue
evalMixedExpr (TC.LogicE expr) ec = evalLogicExpr expr ec
evalMixedExpr (TC.LLVME expr) ec = evalLLVMExpr expr ec

-- | State for running the behavior specifications in a method override.
data OCState = OCState {
         -- ocsLoc :: SymBlockID
         ocsEvalContext :: !EvalContext
       , ocsResultState :: !SpecPathState
       , ocsReturnValue :: !(Maybe Term)
       , ocsErrors :: [OverrideError]
       }

data OverrideError
   = UndefinedExpr TC.LLVMExpr
   | FalseAssertion Pos
   | AliasingInputs !TC.LLVMExpr !TC.LLVMExpr
   | SimException String
   | Misc String
   | Abort
   deriving (Show)

ppOverrideError :: OverrideError -> String
ppOverrideError (UndefinedExpr expr) =
  "Could not evaluate " ++ show (TC.ppLLVMExpr expr) ++ "."
ppOverrideError (FalseAssertion p)   = "Assertion at " ++ show p ++ " is false."
ppOverrideError (AliasingInputs x y) =
 "The expressions " ++ show (TC.ppLLVMExpr x) ++ " and " ++ show (TC.ppLLVMExpr y)
    ++ " point to the same memory location, but are not allowed to alias each other."
ppOverrideError (SimException s)     = "Simulation exception: " ++ s ++ "."
ppOverrideError (Misc s)             = "Other error: " ++ s ++ "."
ppOverrideError Abort                = "Path was aborted."

data OverrideResult
   = SuccessfulRun SpecPathState (Maybe SymBlockID) (Maybe SpecLLVMValue)
   | FailedRun SpecPathState (Maybe SymBlockID) [OverrideError]

type RunResult = ( SpecPathState
                 , Maybe SymBlockID
                 , Either [OverrideError] (Maybe SpecLLVMValue)
                 )

orParseResults :: [OverrideResult] -> [RunResult]
orParseResults l =
  [ (ps, block, Left  e) | FailedRun     ps block e <- l ] ++
  [ (ps, block, Right v) | SuccessfulRun ps block v <- l ]

type OverrideComputation m =
    ContT OverrideResult (StateT OCState (Simulator SpecBackend m))

ocError :: (Monad m, Functor m) =>
           OverrideError -> OverrideComputation m ()
ocError e = modify $ \ocs -> ocs { ocsErrors = e : ocsErrors ocs }

-- | Runs an evaluate within an override computation.
ocEval :: (MonadIO m, Functor m) =>
          (EvalContext -> ExprEvaluator m b)
       -> (b -> OverrideComputation m ())
       -> OverrideComputation m ()
ocEval fn m = do
  ec <- gets ocsEvalContext
  res <- lift $ lift $ runEval (fn ec)
  case res of
    Left expr -> ocError $ UndefinedExpr expr
    Right v   -> m v

ocSetExprValue :: (MonadIO m, Functor m) =>
                  TC.LLVMExpr
               -> SpecLLVMValue
               -> OverrideComputation m ()
ocSetExprValue expr@(CC.Term app) value = do
  case app of
    TC.Arg _ _ _ ->
      ocError $ Misc "Can't assign to argument in override."
    TC.ReturnValue _ ->
      modify $ \ocs -> ocs { ocsReturnValue = Just value }
    _ -> do
      ec <- gets ocsEvalContext
      mrv <- gets ocsReturnValue
      ps <- gets ocsResultState
      ps' <- lift $ lift $ do
        addr <- readLLVMTermAddrPS ps mrv (ecArgs ec) expr
        storePathState addr (TC.lssTypeOfLLVMExpr expr) value ps
      ocModifyResultState $ const $ return ps'

ocModifyResultStateIO :: (MonadIO m, Functor m) =>
                         (SpecPathState -> IO SpecPathState)
                      -> OverrideComputation m ()
ocModifyResultStateIO fn = do
  bcs <- get
  new <- liftIO $ fn $ ocsResultState bcs
  put $! bcs { ocsResultState = new }

ocModifyResultState :: (MonadIO m, Functor m) =>
                       (SpecPathState -> Simulator SpecBackend m SpecPathState)
                    -> OverrideComputation m ()
ocModifyResultState fn = do
  bcs <- get
  new <- lift $ lift $ fn $ ocsResultState bcs
  put $! bcs { ocsResultState = new }

-- | Add assumption for predicate.
ocAssert :: (MonadIO m, Functor m) =>
            Pos -> String -> Term -> OverrideComputation m ()
ocAssert p _nm x = do
  sbe <- (ecBackend . ocsEvalContext) <$> get
  sc <- gets (ecContext . ocsEvalContext)
  opts <- gets (ecOpts . ocsEvalContext)
  -- TODO: check statisfiability in context of current assumptions and assertions
  x' <- liftIO $ scWhnf sc x
  case asBool x' of
    Just True -> return ()
    Just False -> ocError (FalseAssertion p)
    _ | optsSatAtBranches opts -> do
          sr <- liftIO $ sbeRunIO sbe $ termSAT sbe x'
          case sr of
            Unsat -> ocError (FalseAssertion p)
            _ -> return ()
      | otherwise -> return ()
  ocModifyResultStateIO (addAssertion sbe x')

ocStep :: (MonadIO m, Functor m) =>
          BehaviorCommand -> OverrideComputation m ()
ocStep (Ensure _ _pos lhsExpr rhsExpr) = do
  ocEval (evalMixedExpr rhsExpr) $ \value -> do
    ocSetExprValue lhsExpr value
ocStep (Modify lhsExpr tp) = do
  sc <- gets (ecContext . ocsEvalContext)
  dl <- gets (ecDataLayout . ocsEvalContext)
  -- TODO: replace this pattern match with a check and possible error during setup
  Just lty <- liftIO $ TC.logicTypeOfActual dl sc tp
  value <- liftIO $ scFreshGlobal sc (show (TC.ppLLVMExpr lhsExpr)) lty
  ocSetExprValue lhsExpr value
ocStep (Allocate lhsExpr (PtrType (MemType tp))) = do
  ps <- gets ocsResultState
  (ptr, ps') <- lift $ lift $ allocPathState tp ps
  ocModifyResultState (const (return ps'))
  ocSetExprValue lhsExpr ptr
ocStep (Allocate _ tp) = do
  ocError $ Misc $ show $ "Unsupported allocation type:" <+> ppMemType tp
ocStep (Return expr) = do
  ocEval (evalMixedExpr expr) $ \val ->
    modify $ \ocs -> ocs { ocsReturnValue = Just val }
ocStep (ReturnArbitrary tp) = do
  sc <- gets (ecContext . ocsEvalContext)
  dl <- gets (ecDataLayout . ocsEvalContext)
  Symbol fname <- gets (ecFunction . ocsEvalContext)
  -- TODO: replace this pattern match with a check and possible error during setup
  Just lty <- liftIO $ TC.logicTypeOfActual dl sc tp
  value <- liftIO $ scFreshGlobal sc ("lss__return_" ++ fname) lty
  modify $ \ocs -> ocs { ocsReturnValue = Just value }

execBehavior :: (MonadIO m, Functor m) =>
                [BehaviorSpec] -> EvalContext -> SpecPathState
             -> Simulator SpecBackend m [RunResult]
execBehavior bsl ec ps = do
  -- Get state of current execution path in simulator.
  fmap orParseResults $ forM bsl $ \bs -> do
    let initOCS =
          OCState { -- ocsLoc = bsLoc bs
                    ocsEvalContext = ec
                  , ocsResultState = ps
                  , ocsReturnValue = Nothing
                  , ocsErrors = []
                  }
    let resCont () = do
          OCState { -- ocsLoc = loc
                    ocsResultState = resPS
                  , ocsReturnValue = v
                  , ocsErrors = l } <- get
          return $
            if null l then
              SuccessfulRun resPS Nothing v
            else
              FailedRun resPS Nothing l
    flip evalStateT initOCS $ flip runContT resCont $ do
       let sc = ecContext ec
       -- Verify the initial logic assignments
       forM_ (Map.toList (bsExprDecls bs)) $ \(lhs, (_ty, mrhs)) ->
         case mrhs of
           Just rhs -> do
             ocEval (evalLLVMExpr lhs) $ \lhsVal ->
               ocEval (evalLogicExpr rhs) $ \rhsVal ->
                 ocAssert (PosInternal "FIXME") "Override value assertion"
                    =<< liftIO (scEq sc lhsVal rhsVal)
           Nothing -> return ()
       -- Verify assumptions
       forM_ (bsAssumptions bs) $ \le -> do
         ocEval (evalLogicExpr le) $ \assumptions ->
           ocAssert (PosInternal "assumption") "Override assumption check" assumptions
       -- Execute statements.
       mapM_ ocStep (bsCommands bs)

execOverride :: (MonadIO m, Functor m)
             => Options
             -> SharedContext
             -> Pos
             -> [LLVMMethodSpecIR]
             -> [(MemType, SpecLLVMValue)]
             -> Simulator SpecBackend m (Maybe Term)
execOverride _ _ _ [] _ = fail "Empty list of overrides passed to execOverride."
execOverride vpopts sc _pos irs@(ir:_) args = do
  initPS <- fromMaybe (error "no path during override") <$> getPath
  let bsl = map specBehavior irs
      cb = specCodebase ir
  sbe <- gets symBE
  gm <- use globalTerms
  opts <- gets lssOpts
  let ec = EvalContext { ecContext = sc
                       , ecOpts = opts
                       , ecDataLayout = cbDataLayout cb
                       , ecBackend = sbe
                       , ecGlobalMap = gm
                       , ecArgs = map snd args
                       , ecPathState = initPS
                       , ecLLVMExprs = specLLVMExprNames ir
                       , ecFunction = specFunction ir
                       }
  liftIO $ printOutLn vpopts Debug $ "Executing behavior"
  res <- execBehavior bsl ec initPS
  case [ (ps, mval) | (ps, _, Right mval) <- res ] of
    -- One or more successful result: use the first.
    (ps, mval):rest -> do
      unless (null rest) $ liftIO $ printOutLn vpopts Warn $ show $ hcat
        [ text "WARNING: More than one successful path returned from override "
        , text "execution for " , specName ir
        ]
      currentPathOfState .= ps
      return mval
    -- No successful results. Are there any unsuccessful ones?
    [] -> case [ err | (_, _, Left err) <- res ] of
            [] -> fail $ show $ hcat
                  [ text "Zero paths returned from override execution for"
                  , specName ir
                  ]
            (el:_) -> fail $ show $ vcat
                      [ hcat [ text "Unsatisified assertions in "
                             , specName ir
                             , char ':'
                             ]
                      , vcat (map (text . ppOverrideError) el)
                      ]

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: (MonadIO m, Functor m) =>
                    Options
                 -> SharedContext
                 -> Pos
                 -> [LLVMMethodSpecIR]
                 -> Simulator SpecBackend m ()
overrideFromSpec _ _ _ [] =
  fail "Called overrideFromSpec with empty list."
overrideFromSpec vpopts sc pos irs@(ir:_) = do
  let ovd = Override (\_ _ -> execOverride vpopts sc pos irs)
  -- TODO: check argument types?
  tryRegisterOverride (specFunction ir) (const (Just ovd))

createLogicValue :: (MonadIO m, Monad m, Functor m) =>
                    Codebase SpecBackend
                 -> SBE SpecBackend
                 -> SharedContext
                 -> TC.LLVMExpr
                 -> SpecPathState
                 -> MemType
                 -> Maybe TC.LogicExpr
                 -> Simulator SpecBackend m (SpecLLVMValue, SpecPathState)
createLogicValue _ _ sc _ ps (PtrType _) (Just le) = do
  v <- useLogicExprPS sc ps Nothing [] le -- TODO: mrv, args?
  return (v, ps)
createLogicValue _ _ _ _ _ (StructType _) (Just _) =
  fail "Struct variables cannot be given initial values as a whole."
createLogicValue cb sbe sc _expr ps (PtrType (MemType mtp)) Nothing = liftIO $ do
  let dl = cbDataLayout cb
      sz = memTypeSize dl mtp
      w = ptrBitwidth dl
  let m = ps ^. pathMem
  szTm <- scBvConst sc (fromIntegral w) (fromIntegral sz)
  rslt <- sbeRunIO sbe (heapAlloc sbe m mtp w szTm 0)
  case rslt of
    AError msg -> fail msg
    AResult c addr m' -> do
      ps' <- addAssertion sbe c (ps & pathMem .~ m')
      return (addr, ps')
createLogicValue _ _ _ _ _ (PtrType ty) Nothing =
  fail $ "Pointer to weird type: " ++ show (ppSymType ty)
createLogicValue cb _ sc expr ps mtp mrhs = do
  mbltp <- liftIO $ TC.logicTypeOfActual (cbDataLayout cb) sc mtp
  -- Get value of rhs.
  tm <- case (mrhs, mbltp) of
          (Just v, _) -> useLogicExprPS sc ps Nothing [] v -- TODO: mrv, args?
          (Nothing, Just tp) -> liftIO $ scFreshGlobal sc (show (TC.ppLLVMExpr expr)) tp
          (Nothing, Nothing) -> fail "Can't calculate type for fresh input."
  return (tm, ps)

initializeVerification' :: (MonadIO m, Monad m, Functor m) =>
                           SharedContext
                        -> String
                        -> LLVMMethodSpecIR
                        -> Simulator SpecBackend m
                           (SpecPathState,
                            [(TC.LLVMExpr, (MemType, SpecLLVMValue))],
                            [(TC.LLVMExpr, (MemType, SpecLLVMValue))])
initializeVerification' sc file ir = do
  let bs = specBehavior ir
      fn = specFunction ir
      cb = specCodebase ir
      isArgAssgn (e, _) = TC.isArgLLVMExpr e
      isPtrAssgn (e, _) = TC.isPtrLLVMExpr e
      isRetAssgn (e, _) = TC.containsReturn e
      assignments = map getAssign $ Map.toList (bsExprDecls bs)
      getAssign (e, (_, v)) = (e, v)
      argAssignments = filter isArgAssgn assignments
      ptrAssignments = filter (\a -> isPtrAssgn a &&
                                     not (isArgAssgn a) &&
                                     not (isRetAssgn a)) assignments
      otherAssignments =
        filter (\a -> not (isArgAssgn a || isPtrAssgn a || isRetAssgn a)) assignments
      setPS ps = do
        Just cs <- use ctrlStk
        ctrlStk ?= (cs & currentPath .~ ps)

  fnDef <- case lookupDefine fn (specCodebase ir) of
             Just def -> return def
             Nothing -> fail $ missingSymMsg file (specFunction ir)
  sbe <- gets symBE
  -- Create argument list. For pointers, allocate enough space to
  -- store the pointed-to value. For scalar and array types,
  -- initialize this space to a fresh input. For structures, wait
  -- until later to initialize the fields.
  argAssignments' <- forM argAssignments $ \(expr, mle) ->
    case (expr, mle) of
      (CC.Term (TC.Arg _ _ _), Just le) -> do
        ps <- fromMaybe (error "initializeVerification: arg with value") <$> getPath
        tm <- useLogicExprPS sc ps Nothing [] le
        return (Just (expr, tm))
      (CC.Term (TC.Arg _ _ ty), Nothing) -> do
        ps <- fromMaybe (error "initializeVerification: arg w/o value") <$> getPath
        (tm, ps') <- createLogicValue cb sbe sc expr ps ty mle
        setPS ps'
        return (Just (expr, tm))
      _ -> return Nothing

  let argAssignments'' = catMaybes argAssignments'

  let args = flip map argAssignments'' $ \(expr, tm) ->
               case expr of
                 CC.Term (TC.Arg _ _ ty) -> Just (expr, (ty, tm))
                 _                       -> Nothing

  --gm <- use globalTerms
  let rreg =  (,Ident "__sawscript_result") <$> sdRetType fnDef
      cmpFst (CC.Term (TC.Arg i _ _), _) (CC.Term (TC.Arg i' _ _), _) =
        case i `compare` i' of
          EQ -> error $ "Argument " ++ show i ++ " declared multiple times."
          r -> r
      cmpFst _ _ = error "Comparing non-arguments?"
  let argVals = sortBy cmpFst (catMaybes args)
  callDefine' False fn rreg (map snd argVals)

  let doAlloc (expr, mle) = do
        let Just (ty, _) = Map.lookup expr (bsExprDecls bs)
        ps <- fromMaybe (error "initializeVerification") <$> getPath
        (v, ps') <- createLogicValue cb sbe sc expr ps ty mle
        setPS ps'
        writeLLVMTerm Nothing (map (snd . snd) argVals) (expr, v, 1)
        return (expr, (ty, v))

  -- Allocate space for all pointers that aren't directly parameters.
  otherPtrs <- traverse doAlloc
             $ sortBy (comparing (TC.exprDepth . fst)) ptrAssignments

  -- Set initial logic values for everything except arguments and
  -- pointers, including values pointed to by pointers from directly
  -- above, and fields of structures from anywhere.
  traverse_ doAlloc otherAssignments

  ps <- fromMaybe (error "initializeVerification") <$> getPath

  return (ps, otherPtrs, argVals)

nonNullAssumption :: DataLayout -> SharedContext -> SpecLLVMValue -> IO SpecLLVMValue
nonNullAssumption dl sc addr = do
  let aw = fromIntegral (ptrBitwidth dl)
  nullPtr <- scBvConst sc aw 0
  awTerm <- scNat sc aw
  nonNullTerm <- scNot sc =<< scBvEq sc awTerm addr nullPtr
  return nonNullTerm

checkFinalState :: (MonadIO m, Functor m, MonadException m) =>
                   SharedContext
                -> LLVMMethodSpecIR
                -> SpecPathState
                -> [(TC.LLVMExpr, (MemType, SpecLLVMValue))]
                -> [(TC.LLVMExpr, (MemType, SpecLLVMValue))]
                -> Simulator SpecBackend m (PathVC ())
checkFinalState sc ms initPS otherPtrs args = do
  let cmds = bsCommands (specBehavior ms)
      cb = specCodebase ms
      sbe = specBackend ms
      dl = cbDataLayout cb
      argVals = map (snd . snd) args
      initMem = initPS ^. pathMem
  mrv <- getProgramReturnValue
  finPS <- fromMaybe (error "no path in checkFinalState") <$> getPath
  let finMem = finPS ^. pathMem
  directAssumptions <- evalAssumptions sc initPS mrv argVals (specAssumptions ms)
  let ptrs = otherPtrs ++ [ a | a@(_, (ty, _)) <- args, TC.isActualPtr ty ]
  ptrAssumptions <- forM ptrs $ \(expr, (ty, ptr)) -> liftIO $ do
    case specGetLogicAssignment ms expr of
      Just _ -> return []
      Nothing -> do
        (minBoundTerm, maxBoundTerm) <- addrBounds sc sbe dl ptr (MemType ty)
        return [minBoundTerm, maxBoundTerm]
  allocAssumptions <- forM [ expr | Allocate expr _ <- cmds ] $ \expr -> do
    addr <- readLLVMTermPS finPS mrv argVals expr 1
    assm <- liftIO $ nonNullAssumption dl sc addr
    return [assm]
  allocAssertions <- forM [ (expr, mty) | Allocate expr mty <- cmds ] $ \(expr, mty) -> do
    addr <- readLLVMTermPS finPS mrv argVals expr 1
    let sz = memTypeSize dl mty
    szTm <- liftIO $ scBvConst sc (fromIntegral (ptrBitwidth dl)) (fromIntegral sz)
    initCond <- liftIO $ sbeRunIO sbe $ isAllocated sbe initMem addr szTm
    finCond <- liftIO $ sbeRunIO sbe $ isAllocated sbe finMem addr szTm
    initCond' <- liftIO $ scNot sc initCond
    liftIO $ scAnd sc initCond' finCond
  let allPtrAssumptions = concat (ptrAssumptions ++ allocAssumptions)
  assumptions <- liftIO $ foldM (scAnd sc) directAssumptions allPtrAssumptions
  msrv <- case [ e | Return e <- cmds ] of
            [e] -> Just <$> readLLVMMixedExprPS sc initPS Nothing argVals e
            [] -> return Nothing
            _  -> fail "more than one return value specified (multiple 'llvm_return's ?)"
  expectedValues <- forM [ (post, le, me) | Ensure post _ le me <- cmds ] $ \(post, le, me) -> do
    lhs <- readLLVMTermAddrPS (if post then finPS else initPS) mrv argVals le
    rhs <- readLLVMMixedExprPS sc initPS mrv argVals me
    let Just (tp, _) = Map.lookup le (bsExprDecls (specBehavior ms))
    return (le, lhs, tp, rhs)
  let initState  =
        PathVC { pvcStartLoc = ()
               , pvcEndLoc = Nothing
               , pvcAssumptions = assumptions
               , pvcStaticErrors = []
               , pvcChecks = []
               }
      allocReturn = not (null [ () | Allocate (CC.Term (TC.ReturnValue _)) _ <- cmds ])
  flip execStateT initState $ do
    case (mrv, msrv, [ () | ReturnArbitrary _ <- cmds ]) of
      (_, _, _ : _ : _) -> fail "More than one `llvm_return_arbitrary` statement."
      (Nothing, Nothing, []) -> return ()
      (Just rv, Just srv, []) -> pvcgAssertEq "return value" rv srv
      (Just _, Just _, [_]) -> fail "Both `llvm_return` and `llvm_return_arbitrary` specified."
      (Just _, Nothing, [_]) -> return () -- Arbitrary return value
      (Just _, Nothing, []) ->
        unless allocReturn $
          fail "simulator returned value when not expected (add an 'llvm_return' statement?)"
      (Nothing, Just _, _) -> fail "simulator did not return value when return value expected (remove an 'llvm_return' statement?)"
      (Nothing, _, [_]) -> fail "simulator did not return value when return value expected (remove an 'llvm_return' statement?)"

    forM_ allocAssertions $ pvcgAssert "allocation assertion"
    -- Check that expected state modifications have occurred.
    -- TODO: extend this to check that nothing else has changed.
    forM_ expectedValues $ \(e, lhs, tp, rhs) -> do
      when (memTypeSize dl tp > 0) $ do
        finalValue <- lift $ load tp lhs (memTypeAlign dl tp)
        pvcgAssertEq (show e) finalValue rhs
    -- Check assertions
    ps <- fromMaybe (error "no path in checkFinalState") <$> (lift $ getPath)
    pvcgAssert "final assertions" (ps ^. pathAssertions)


data VerifyParams = VerifyParams
  { vpCode    :: Codebase SAWBackend
  , vpContext :: SharedContext
  , vpOpts    :: Options
  , vpSpec    :: LLVMMethodSpecIR
  , vpOver    :: [LLVMMethodSpecIR]
  }

type SymbolicRunHandler =
  SharedContext -> [PathVC ()] -> TopLevel SolverStats
type Prover = VerifyState -> Int -> Term -> TopLevel SolverStats

runValidation :: Prover -> VerifyParams -> SymbolicRunHandler
runValidation prover params sc results = do
  let ir = vpSpec params
      verb = case Opts.verbLevel (vpOpts params) of
                Opts.Silent              -> 0
                Opts.OnlyCounterExamples -> 0
                Opts.Error               -> 1
                Opts.Warn                -> 2
                Opts.Info                -> 3
                _                        -> 5
  opts <- fmap rwPPOpts getTopLevelRW
  mconcat <$> (forM results $ \pvc -> do
    let mkVState nm cfn =
          VState { vsVCName = nm
                 , vsMethodSpec = ir
                 , vsVerbosity = verb
                 , vsCounterexampleFn = cfn
                 , vsStaticErrors = pvcStaticErrors pvc
                 }
    if null (pvcStaticErrors pvc) then
      mconcat <$> (forM (zip [0..] $ pvcChecks pvc) $ \(n, vc) -> do
        let vs = mkVState (vcName vc) (vcCounterexample sc opts vc)
        g <- io (scImplies sc (pvcAssumptions pvc) =<< vcGoal sc vc)
        io $ printOutLn (vpOpts params) Info $ "Checking " ++ vcName vc
        io $ printOutLn (vpOpts params) Debug $ " (" ++ show g ++ ")"
        io $ printOutLn (vpOpts params) Info "\n"
        prover vs n g)
    else do
      let vsName = "an invalid path"
      let vs = mkVState vsName (\_ -> return $ vcat (pvcStaticErrors pvc))
      false <- io $ scBool sc False
      g <- io $ scImplies sc (pvcAssumptions pvc) false
      printOutLnTop Info $ "Checking " ++ vsName
      printOutLnTop Info $ show (pvcStaticErrors pvc)
      printOutLnTop Info $ "Calling prover to disprove " ++
                 scPrettyTerm defaultPPOpts (pvcAssumptions pvc)
      prover vs 0 g)

data VerifyState = VState {
         vsVCName :: String
       , vsMethodSpec :: LLVMMethodSpecIR
       , vsVerbosity :: Verbosity
       , vsCounterexampleFn :: CounterexampleFn
       , vsStaticErrors :: [Doc]
       }

type Verbosity = Int

readLLVMMixedExprPS :: (Functor m, Monad m, MonadIO m) =>
                       SharedContext
                    -> SpecPathState
                    -> Maybe SpecLLVMValue
                    -> [SpecLLVMValue]
                    -> TC.MixedExpr
                    -> Simulator SpecBackend m SpecLLVMValue
readLLVMMixedExprPS sc ps mrv args (TC.LogicE le) = do
  useLogicExprPS sc ps mrv args le
readLLVMMixedExprPS _sc ps mrv args (TC.LLVME le) =
  readLLVMTermPS ps mrv args le 1

useLogicExprPS :: (Functor m, Monad m, MonadIO m) =>
                  SharedContext
               -> SpecPathState
               -> Maybe SpecLLVMValue
               -> [SpecLLVMValue]
               -> TC.LogicExpr
               -> Simulator SpecBackend m SpecLLVMValue
useLogicExprPS sc ps mrv args initExpr = do
  leArgs <- forM (TC.logicExprLLVMExprs initExpr) $ \expr ->
          readLLVMTermPS ps mrv args expr 1
  liftIO $ TC.useLogicExpr sc initExpr leArgs

evalAssumptions :: (Functor m, Monad m, MonadIO m) =>
                   SharedContext
                -> SpecPathState
                -> Maybe SpecLLVMValue
                -> [SpecLLVMValue]
                -> [TC.LogicExpr]
                -> Simulator SpecBackend m Term
evalAssumptions sc ps mrv args as = do
  assumptionList <- mapM (useLogicExprPS sc ps mrv args) as
  liftIO $ do
    true <- scBool sc True
    foldM (scAnd sc) true assumptionList
