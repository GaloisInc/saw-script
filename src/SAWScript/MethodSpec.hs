{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.MethodSpec
  ( VerifyCommand
  , ValidationPlan(..)
  , MethodSpecIR
  , specMethod
  , specName
  , specMethodClass
  --, specValidationPlan
  --, resolveMethodSpecIR
  , SymbolicRunHandler
  --, writeBlif
  --, runValidation
  --, validateMethodSpec
  , VerifyParams(..)
  ) where

-- Imports {{{1

import Control.Applicative hiding (empty)
import Control.Exception (finally)
import Control.Lens
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Error (ErrorT, runErrorT, throwError)
import Control.Monad.State
import Data.Int
import Data.List (foldl', intercalate, intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector.Storable as SV
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.HughesPJ as PP
import System.Directory(doesFileExist)
import System.FilePath (splitExtension, addExtension)
import System.IO

import qualified SAWScript.CongruenceClosure as CC
import qualified SAWScript.JavaExpr as TC
import SAWScript.Utils
import SAWScript.MethodSpecIR

import qualified Verifier.Java.Simulator as JSS
import Verifier.Java.SAWBackend
import Verinf.Symbolic
import qualified Verinf.Symbolic.BLIF as Blif
import qualified Verinf.Symbolic.QuickCheck as QuickCheck
import qualified Verinf.Symbolic.SmtLibTrans as SmtLib
import qualified Verinf.Symbolic.SmtLibTrans2 as SmtLib2
import qualified Verinf.Symbolic.Yices  as Yices
import Verinf.Utils.LogMonad

import Verifier.SAW.Evaluator
import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm

import qualified SMTLib1 as SmtLib
import qualified SMTLib2 as SmtLib2

-- Utilities {{{1

-- | Return first value satisfying predicate if any.
findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
findM _ [] = return Nothing
findM check (x:xs)  = do ok <- check x
                         if ok then return (Just x)
                               else findM check xs

-- Verinf Utilities {{{1

scEq :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scEq sc x y = undefined -- scApply?? sc x y -- FIXME

scImplies :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scImplies sc x y = do
  xNot <- scNot sc x
  orOp <- scApplyPreludeOr sc
  orOp xNot y

{-
typeBitCount :: DagType -> Int
typeBitCount SymBool = 1
typeBitCount (SymInt (widthConstant -> Just (Wx w))) = w
typeBitCount (SymArray (widthConstant -> Just (Wx l)) e) = l * typeBitCount e
typeBitCount (SymRec d s) = V.sum $ V.map typeBitCount $ recFieldTypes d s
typeBitCount _ = error "internal: typeBitCount called on polymorphic type."

mkInputEval :: DagType -> SV.Vector Bool -> CValue
mkInputEval (SymInt (widthConstant -> Just _)) lits = mkCIntFromLsbfV lits
mkInputEval (SymArray (widthConstant -> Just (Wx l)) e) lits =
  let w = typeBitCount e
   in CArray $ V.generate l $ (\i -> mkCIntFromLsbfV $ SV.slice (i*w) w lits)
mkInputEval _ _ = error "internal: Unsupported type given to mkInputEval"
-}

-- JSS Utilities {{{1

type SpecPathState s = JSS.Path (SharedContext s)
type SpecJavaValue s = JSS.Value (SharedTerm s)

-- | Set value of bound to instance field in path state.
setInstanceFieldValue :: JSS.Ref -> JSS.FieldId -> SpecJavaValue s
                      -> SpecPathState s -> SpecPathState s
setInstanceFieldValue r f v =
  JSS.pathMemory . JSS.memInstanceFields %~ Map.insert (r, f) v

-- | Set value bound to array in path state.
-- Assumes value is an array with a ground length.
setArrayValue :: JSS.Ref -> SharedTerm s
              -> SpecPathState s -> SpecPathState s
setArrayValue r v =
  JSS.pathMemory . JSS.memScalarArrays %~ Map.insert r (w, v)
    where w = undefined -- FIXME

-- | Returns value constructor from node.
mkJSSValue :: JSS.Type -> n -> JSS.Value n
mkJSSValue JSS.BooleanType n = JSS.IValue n
mkJSSValue JSS.ByteType    n = JSS.IValue n
mkJSSValue JSS.CharType    n = JSS.IValue n
mkJSSValue JSS.IntType     n = JSS.IValue n
mkJSSValue JSS.LongType    n = JSS.LValue n
mkJSSValue JSS.ShortType   n = JSS.IValue n
mkJSSValue _ _ = error "internal: illegal type"

-- | Add assumption for predicate to path state.
addAssumption :: SharedContext s -> SharedTerm s -> SpecPathState s -> IO (SpecPathState s)
addAssumption sc x ps = return ps -- FIXME
{- TODO: JSS
  do prop <- scApplyPreludeAnd sc (JSS.psAssumptions ps) x
     return ps { JSS.psAssumptions = prop }
-}

-- | Add assertion for predicate to path state.
addAssertion :: String -> SharedTerm s -> SpecPathState s -> SpecPathState s
addAssertion nm x ps = ps -- FIXME
  -- TODO: JSS
  -- ps { JSS.pathAssertions = (nm,x) : JSS.pathAssertions ps }

-- EvalContext {{{1

-- | Contextual information needed to evaluate expressions.
data EvalContext s = EvalContext {
         ecContext :: SharedContext s
       , ecLocals :: Map JSS.LocalVariableIndex (SpecJavaValue s)
       , ecPathState :: (SpecPathState s)
       }

evalContextFromPathState :: SharedContext s -> SpecPathState s -> EvalContext s
evalContextFromPathState sc ps =
  let Just f = JSS.currentCallFrame ps
      localMap = f ^. JSS.cfLocals
  in EvalContext {
          ecContext = sc
        , ecLocals = localMap
        , ecPathState = ps
        }

type ExprEvaluator a = ErrorT TC.JavaExpr IO a

runEval :: MonadIO m => ExprEvaluator b -> m (Either TC.JavaExpr b)
runEval v = liftIO (runErrorT v)

-- or undefined subexpression if not.
-- N.B. This method assumes that the Java path state is well-formed, the
-- the JavaExpression syntactically referes to the correct type of method
-- (static versus instance), and correct well-typed arguments.  It does
-- not assume that all the instanceFields in the JavaEvalContext are initialized.
evalJavaExpr :: TC.JavaExpr -> EvalContext s -> ExprEvaluator (SpecJavaValue s)
evalJavaExpr expr ec = eval expr
  where eval e@(CC.Term app) =
          case app of
            TC.Local _ idx _ ->
              case Map.lookup idx (ecLocals ec) of
                Just v -> return v
                Nothing -> throwError e
            TC.InstanceField r f -> do
              JSS.RValue ref <- eval r
              let ifields = (ecPathState ec) ^. JSS.pathMemory . JSS.memInstanceFields
              case Map.lookup (ref, f) ifields of
                Just v -> return v
                Nothing -> throwError e

evalJavaRefExpr :: TC.JavaExpr -> EvalContext s -> ExprEvaluator JSS.Ref
evalJavaRefExpr expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    JSS.RValue ref -> return ref
    _ -> error "internal: evalJavaRefExpr encountered illegal value."

evalJavaExprAsLogic :: TC.JavaExpr -> EvalContext s -> ExprEvaluator (SharedTerm s)
evalJavaExprAsLogic expr ec = do
  val <- evalJavaExpr expr ec
  case val of
    JSS.RValue r ->
      let arrs = (ecPathState ec) ^. JSS.pathMemory . JSS.memScalarArrays in
      case Map.lookup r arrs of
        Nothing    -> throwError expr
        Just (_,n) -> return n
    JSS.IValue n -> return n
    JSS.LValue n -> return n
    _ -> error "internal: evalJavaExprAsExpr encountered illegal value."

-- | Evaluates a typed expression.
evalLogicExpr :: TC.LogicExpr s -> EvalContext s -> ExprEvaluator (SharedTerm s)
evalLogicExpr initExpr ec = undefined -- eval initExpr
  where sc = ecContext ec
        -- FIXME: SAWCore
        {-
        eval (TC.Apply op exprs) =
          (liftIO . deApplyOp de op) =<< V.mapM eval (V.fromList exprs)
        eval (TC.Cns c tp) = return $ ConstTerm c tp
        eval (TC.IntLit i we@(widthConstant -> Just w)) =
          return $ ConstTerm (mkCInt w i) (SymInt we)
        eval TC.IntLit{} = error "internal: evalLogicExpr called with non-ground literal."
        eval (TC.Var _ _) = error "internal: evalLogicExpr called with var"
        eval (TC.JavaValue expr _ _) = evalJavaExprAsLogic expr ec
        -}

-- | Return Java value associated with mixed expression.
evalMixedExpr :: TC.MixedExpr s -> EvalContext s
              -> ExprEvaluator (SpecJavaValue s)
evalMixedExpr (TC.LE expr) ec = do
  n <- evalLogicExpr expr ec
  undefined -- FIXME: SAWCore
{-
  case termType n of
    SymInt (widthConstant -> Just 32) -> return (JSS.IValue n)
    SymInt (widthConstant -> Just 64) -> return (JSS.LValue n)
    _ -> error "internal: mixedExprValue called with malformed result type."
-}
evalMixedExpr (TC.JE expr) ec = evalJavaExpr expr ec


-- Method specification overrides {{{1
-- OverrideComputation definition {{{2

-- | State for running the behavior specifications in a method override.
data OCState s = OCState {
         ocsPC :: JSS.PC
       , ocsEvalContext :: !(EvalContext s)
       , ocsResultState :: !(SpecPathState s)
       , ocsReturnValue :: !(Maybe (SpecJavaValue s))
       , ocsErrors :: [OverrideError]
       }

data OverrideError
   = UndefinedExpr TC.JavaExpr
   | FalseAssertion Pos
   | AliasingInputs !TC.JavaExpr !TC.JavaExpr
   | JavaException JSS.Ref
   | SimException String
   | Abort
   deriving (Show)

ppOverrideError :: OverrideError -> String
ppOverrideError (UndefinedExpr expr) =
  "Could not evaluate " ++ show (TC.ppJavaExpr expr) ++ "."
ppOverrideError (FalseAssertion p)   = "Assertion at " ++ show p ++ " is false."
ppOverrideError (AliasingInputs x y) =
 "The expressions " ++ show (TC.ppJavaExpr x) ++ " and " ++ show (TC.ppJavaExpr y)
    ++ " point to the same reference, but are not allowed to alias each other."
ppOverrideError (JavaException _)    = "A Java exception was thrown."
ppOverrideError (SimException s)     = "Simulation exception: " ++ s ++ "."
ppOverrideError Abort                = "Path was aborted."

data OverrideResult s
   = SuccessfulRun (JSS.Memory (SharedTerm s)) (Maybe JSS.PC) (Maybe (SpecJavaValue s))
   | FalseAssumption
   | FailedRun (JSS.ErrorPath (SharedContext s)) (Maybe JSS.PC) [OverrideError]
   -- deriving (Show)

type RunResult s = ( Maybe (JSS.Path (SharedContext s))
                   , Maybe JSS.PC
                   , Either [OverrideError] (Maybe (SpecJavaValue s))
                   )

orParseResults :: [OverrideResult s] -> [RunResult s]
orParseResults l = undefined
{- TODO: design
  [ (ps, pc, Left  e) | FailedRun     ps pc e <- l ]
                ++ [ (ps, pc, Right v) | SuccessfulRun ps pc v <- l ]
-}

type OverrideComputation s = ContT (OverrideResult s) (StateT (OCState s) IO)

ocError :: OverrideError -> OverrideComputation s ()
ocError e = modify $ \ocs -> ocs { ocsErrors = e : ocsErrors ocs }

ocAssumeFailed :: OverrideComputation s a
ocAssumeFailed = ContT (\_ -> return FalseAssumption)

-- OverrideComputation utilities {{{2

-- | Runs an evaluate within an override computation.
ocEval :: (EvalContext s -> ExprEvaluator b)
       -> (b -> OverrideComputation s ())
       -> OverrideComputation s ()
ocEval fn m = do
  ec <- gets ocsEvalContext
  res <- runEval (fn ec)
  case res of
    Left expr -> ocError $ UndefinedExpr expr
    Right v   -> m v

-- Modify result state
ocModifyResultState :: (SpecPathState s -> SpecPathState s) -> OverrideComputation s ()
ocModifyResultState fn = do
  bcs <- get
  put $! bcs { ocsResultState = fn (ocsResultState bcs) }

ocModifyResultStateIO :: (SpecPathState s -> IO (SpecPathState s))
                      -> OverrideComputation s ()
ocModifyResultStateIO fn = do
  bcs <- get
  new <- liftIO $ fn $ ocsResultState bcs
  put $! bcs { ocsResultState = new }

-- | Add assumption for predicate.
ocAssert :: Pos -> String -> SharedTerm s -> OverrideComputation s ()
ocAssert p nm x = do
  case asBool x of
    Just True -> return ()
    Just False -> ocError (FalseAssertion p)
    _ -> ocModifyResultState $ addAssertion nm x

-- ocStep {{{2

ocStep :: BehaviorCommand s -> OverrideComputation s ()
ocStep (AssertPred pos expr) =
  ocEval (evalLogicExpr expr) $ \p ->
    ocAssert pos "Override predicate" p
ocStep (AssumePred expr) = do
  sc <- gets (ecContext . ocsEvalContext)
  ocEval (evalLogicExpr expr) $ \v ->
    case asBool v of
      Just True -> return ()
      Just False -> ocAssumeFailed
      _ -> ocModifyResultStateIO $ addAssumption sc v
ocStep (EnsureInstanceField _pos refExpr f rhsExpr) = do
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef ->
    ocEval (evalMixedExpr rhsExpr) $ \value ->
      ocModifyResultState $ setInstanceFieldValue lhsRef f value
ocStep (EnsureArray _pos lhsExpr rhsExpr) = do
  ocEval (evalJavaRefExpr lhsExpr) $ \lhsRef ->
    ocEval (evalLogicExpr   rhsExpr) $ \rhsVal ->
      ocModifyResultState $ setArrayValue lhsRef rhsVal
ocStep (ModifyInstanceField refExpr f) =
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef -> do
    sc <- gets (ecContext . ocsEvalContext)
    let tp = JSS.fieldIdType f
        w = fromIntegral $ JSS.stackWidth tp
    logicType <- liftIO $ scBitvector sc (fromInteger w)
    n <- liftIO $ scFreshGlobal sc "_" logicType
    ocModifyResultState $ setInstanceFieldValue lhsRef f (mkJSSValue tp n)
ocStep (ModifyArray refExpr tp) = do
  ocEval (evalJavaRefExpr refExpr) $ \ref -> do
    sc <- gets (ecContext . ocsEvalContext)
    rhsVal <- liftIO (scFreshGlobal sc "_" tp)
    ocModifyResultState $ setArrayValue ref rhsVal
ocStep (Return expr) = do
  ocEval (evalMixedExpr expr) $ \val ->
    modify $ \ocs -> ocs { ocsReturnValue = Just val }

-- Executing overrides {{{2

execBehavior :: [BehaviorSpec s] -> EvalContext s -> SpecPathState s -> IO [RunResult s]
execBehavior bsl ec ps = do
  -- Get state of current execution path in simulator.
  fmap orParseResults $ forM bsl $ \bs -> do
    let initOCS =
          OCState { ocsPC = bsPC bs
                  , ocsEvalContext = ec
                  , ocsResultState = ps
                  , ocsReturnValue = Nothing
                  , ocsErrors = []
                  }
    let resCont () = do
          OCState { ocsPC = pc
                  , ocsResultState = resPS
                  , ocsReturnValue = v
                  , ocsErrors = l } <- get
          return $ undefined -- FIXME
{- TODO: design
            if null l then
              SuccessfulRun resPS (Just pc) v
            else
              FailedRun resPS (Just pc) l
-}
    flip evalStateT initOCS $ flip runContT resCont $ do
       -- Check that all expressions that reference each other may do so.
       do -- Build map from references to expressions that map to them.
          let exprs = bsRefExprs bs
          ocEval (\_ -> mapM (flip evalJavaRefExpr ec) exprs) $ \refs -> do
            let refExprMap = Map.fromListWith (++) $ refs `zip` [[e] | e <- exprs]
            --- Get counterexamples.
            let mayAliasSet = bsMayAliasSet bs
            let badPairs = catMaybes
                         $ map (\cl -> CC.checkEquivalence cl mayAliasSet)
                         $ Map.elems refExprMap
            -- Throw error if counterexample is found.
            case badPairs of
              [] -> return ()
              (x,y):_ -> ocError (AliasingInputs x y)
       let sc = ecContext ec
       -- Verify the initial logic assignments
       forM_ (bsLogicAssignments bs) $ \(pos, lhs, rhs) -> do
         ocEval (evalJavaExprAsLogic lhs) $ \lhsVal ->
           ocEval (evalLogicExpr rhs) $ \rhsVal ->
             ocAssert pos "Override value assertion"
                =<< liftIO (scEq sc lhsVal rhsVal)
       -- Execute statements.
       mapM_ ocStep (bsCommands bs)

checkClassesInitialized :: JSS.MonadSim (SharedContext s) m => Pos -> String -> [String] -> JSS.Simulator (SharedContext s) m ()
checkClassesInitialized pos nm requiredClasses = do
  forM_ requiredClasses $ \c -> do
    status <- undefined -- JSS.getInitializationStatus c -- FIXME: JSS
    when (status /= Just JSS.Initialized) $
      let msg = "The method spec \'" ++ nm ++ "\' requires that the class "
                  ++ JSS.slashesToDots c ++ " is initialized.  SAWScript does not "
                  ++ "currently support methods that initialize new classes."
       in throwIOExecException pos (ftext msg) ""

execOverride :: JSS.MonadSim (SharedContext s) m
             => SharedContext s
             -> Pos
             -> MethodSpecIR s
             -> Maybe JSS.Ref
             -> [JSS.Value (SharedTerm s)]
             -> JSS.Simulator (SharedContext s) m ()
execOverride sc pos ir mbThis args = do
  -- Execute behaviors.
  initPS <- JSS.getPath (PP.text "MethodSpec override")
  let Just bsl = Map.lookup 0 (specBehaviors ir)
  let method = specMethod ir
      argLocals = map (JSS.localIndexOfParameter method) [0..] `zip` args
  let ec = EvalContext { ecContext = sc
                       , ecLocals =  Map.fromList $
                           case mbThis of
                             Just th -> (0, JSS.RValue th) : argLocals
                             Nothing -> argLocals
                       , ecPathState = initPS
                       }
  -- Check class initialization.
  checkClassesInitialized pos (specName ir) (specInitializedClasses ir)
  -- Execute behavior.
  res <- liftIO . execBehavior bsl ec =<< JSS.getPath (PP.text "MethodSpec behavior")
  when (null res) $ error "internal: execBehavior returned empty result list."
  -- Create function for generation resume actions.
  {- TODO: JSS
  let -- Failed run
      resAction (ps, _, Left el) = do
        let msg = "Unsatisified assertions in " ++ specName ir ++ ":\n"
                    ++ intercalate "\n" (map ppOverrideError el)
        JSS.CustomRA msg $ do
          verb <- getVerbosity
          let exc = JSS.SimExtErr { JSS.simExtErrMsg = msg
                                  , JSS.simExtErrVerbosity = verb
                                    -- TODO: Determine what to put instead of Map.empty
                                  , JSS.simExtErrResults = Map.empty
                                  }
          JSS.putPathState ps { JSS.finalResult = JSS.Exc exc }
          return $ JSS.NextInst
      resAction (ps, _, Right mval) =
        JSS.CustomRA ("Override execution") $ do
          --TODO: Investigate if this is right.
          JSS.putPathState $
            case (mval, JSS.frames ps) of
              (Just val, [])   -> ps { JSS.finalResult = JSS.ReturnVal val }
              (Just val, f:fr) -> ps { JSS.frames = f { JSS.frmOpds = val : JSS.frmOpds f } : fr }
              (Nothing,  [])   -> ps { JSS.finalResult = JSS.Terminated }
              (Nothing,  _:_)  -> ps
          return $ JSS.NextInst
  -- Split execution paths.
  let (firstRes:restRes) = res
  mapM_ (JSS.onNewPath . resAction) restRes
  JSS.onCurrPath (resAction firstRes)
  -}
  return ()

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: JSS.MonadSim (SharedContext s) m =>
                    SharedContext s
                 -> Pos
                 -> MethodSpecIR s
                 -> JSS.Simulator (SharedContext s) m ()
overrideFromSpec de pos ir
  | JSS.methodIsStatic method =
      JSS.overrideStaticMethod cName key $ \args ->
        execOverride de pos ir Nothing args
  | otherwise =
      JSS.overrideInstanceMethod cName key $ \thisVal args ->
        execOverride de pos ir (Just thisVal) args
 where cName = JSS.className (specMethodClass ir)
       method = specMethod ir
       key = JSS.methodKey method

-- ExpectedStateDef {{{1

-- | Describes expected result of computation.
data ExpectedStateDef s = ESD {
         -- | PC that we started from.
         esdStartPC :: JSS.PC
         -- | Initial path state (used for evaluating expressions in
         -- verification).
       , esdInitialPathState :: SpecPathState s
         -- | Stores initial assignments.
       , esdInitialAssignments :: [(TC.JavaExpr, SharedTerm s)]
         -- | Map from references back to Java expressions denoting them.
       , esdRefExprMap :: Map JSS.Ref [TC.JavaExpr]
         -- | Expected return value or Nothing if method returns void.
       , esdReturnValue :: Maybe (JSS.Value (SharedTerm s))
         -- | Maps instance fields to expected value, or Nothing if value may
         -- be arbitrary.
       , esdInstanceFields :: Map (JSS.Ref, JSS.FieldId) (Maybe (JSS.Value (SharedTerm s)))
         -- | Maps reference to expected node, or Nothing if value may be arbitrary.
       , esdArrays :: Map JSS.Ref (Maybe (Int32, SharedTerm s))
       }

esdRefName :: JSS.Ref -> ExpectedStateDef s -> String
esdRefName JSS.NullRef _ = "null"
esdRefName ref esd =
  case Map.lookup ref (esdRefExprMap esd) of
    Just cl -> ppJavaExprEquivClass cl
    Nothing -> "fresh allocation"

-- Initial state generation {{{1

-- | State for running the behavior specifications in a method override.
data ESGState s = ESGState {
         esContext :: SharedContext s
       , esMethod :: JSS.Method
       , esExprRefMap :: Map TC.JavaExpr JSS.Ref
       , esInitialAssignments :: [(TC.JavaExpr, SharedTerm s)]
       , esInitialPathState :: SpecPathState s
       , esReturnValue :: Maybe (SpecJavaValue s)
       , esInstanceFields :: Map (JSS.Ref, JSS.FieldId) (Maybe (SpecJavaValue s))
       , esArrays :: Map JSS.Ref (Maybe (Int32, SharedTerm s))
       }

-- | Monad used to execute statements in a behavior specification for a method
-- override.
type ExpectedStateGenerator s = StateT (ESGState s) IO

esEval :: (EvalContext s -> ExprEvaluator b) -> ExpectedStateGenerator s b
esEval fn = do
  sc <- gets esContext
  initPS <- gets esInitialPathState
  let ec = evalContextFromPathState sc initPS
  res <- runEval (fn ec)
  case res of
    Left expr -> fail $ "internal: esEval given " ++ show expr ++ "."
    Right v   -> return v

esGetInitialPathState :: ExpectedStateGenerator s (SpecPathState s)
esGetInitialPathState = gets esInitialPathState

esPutInitialPathState :: SpecPathState s -> ExpectedStateGenerator s ()
esPutInitialPathState ps = modify $ \es -> es { esInitialPathState = ps }

esModifyInitialPathState :: (SpecPathState s -> SpecPathState s)
                         -> ExpectedStateGenerator s ()
esModifyInitialPathState fn =
  modify $ \es -> es { esInitialPathState = fn (esInitialPathState es) }

esModifyInitialPathStateIO :: (SpecPathState s -> IO (SpecPathState s))
                         -> ExpectedStateGenerator s ()
esModifyInitialPathStateIO fn =
  do s0 <- esGetInitialPathState
     esPutInitialPathState =<< liftIO (fn s0)

esAddEqAssertion :: SharedContext s -> String -> SharedTerm s -> SharedTerm s
                 -> ExpectedStateGenerator s ()
esAddEqAssertion sc nm x y =
  do prop <- liftIO (scEq sc x y)
     esModifyInitialPathState (addAssertion nm prop)

-- | Assert that two terms are equal.
esAssertEq :: String -> SpecJavaValue s -> SpecJavaValue s
           -> ExpectedStateGenerator s ()
esAssertEq nm (JSS.RValue x) (JSS.RValue y) = do
  when (x /= y) $
    error $ "internal: Asserted different references for " ++ nm ++ " are equal."
esAssertEq nm (JSS.IValue x) (JSS.IValue y) = do
  sc <- gets esContext
  esAddEqAssertion sc nm x y
esAssertEq nm (JSS.LValue x) (JSS.LValue y) = do
  sc <- gets esContext
  esAddEqAssertion sc nm x y
esAssertEq _ _ _ = error "internal: esAssertEq given illegal arguments."

-- | Set value in initial state.
esSetJavaValue :: TC.JavaExpr -> SpecJavaValue s -> ExpectedStateGenerator s ()
esSetJavaValue e@(CC.Term exprF) v = do
  case exprF of
    -- FIXME: the following is ugly, and doesn't make good use of lenses
    TC.Local _ idx _ -> do
      ps <- esGetInitialPathState
      let ls = case JSS.currentCallFrame ps of
                 Just cf -> cf ^. JSS.cfLocals
                 Nothing -> Map.empty
          ls' = Map.insert idx v ls
          ps' = (JSS.pathStack %~ updateLocals) ps
          updateLocals (f:r) = (JSS.cfLocals %~ Map.insert idx v) f : r
          updateLocals [] = error "esSetJavaValue of local with empty call stack"
      case Map.lookup idx ls of
        Just oldValue -> esAssertEq (TC.ppJavaExpr e) oldValue v
        Nothing -> esPutInitialPathState ps'
    -- FIXME: the following is ugly, and doesn't make good use of lenses
    TC.InstanceField refExpr f -> do
      -- Lookup refrence associated to refExpr
      Just ref <- Map.lookup refExpr <$> gets esExprRefMap
      ps <- esGetInitialPathState
      case Map.lookup (ref,f) (ps ^. JSS.pathMemory . JSS.memInstanceFields) of
        Just oldValue -> esAssertEq (TC.ppJavaExpr e) oldValue v
        Nothing -> esPutInitialPathState $
          (JSS.pathMemory . JSS.memInstanceFields %~ Map.insert (ref,f) v) ps

esResolveLogicExprs :: SharedTerm s -> [TC.LogicExpr s]
                    -> ExpectedStateGenerator s (SharedTerm s)
esResolveLogicExprs tp [] = do
  sc <- gets esContext
  -- Create input variable.
  liftIO $ scFreshGlobal sc "_" tp
esResolveLogicExprs _ (hrhs:rrhs) = do
  sc <- gets esContext
  t <- esEval $ evalLogicExpr hrhs
  -- Add assumptions for other equivalent expressions.
  forM_ rrhs $ \rhsExpr -> do
    rhs <- esEval $ evalLogicExpr rhsExpr
    esModifyInitialPathStateIO $ \s0 -> do prop <- scEq sc t rhs
                                           addAssumption sc prop s0
  -- Return value.
  return t

esSetLogicValues :: [TC.JavaExpr] -> SharedTerm s -> [TC.LogicExpr s]
                 -> ExpectedStateGenerator s ()
esSetLogicValues cl tp lrhs = do
  -- Get value of rhs.
  value <- esResolveLogicExprs tp lrhs
  -- Update Initial assignments.
  modify $ \es -> es { esInitialAssignments =
                         map (\e -> (e,value)) cl ++  esInitialAssignments es }
{- TODO: JSS & SAWCore
  -- Update value.
  case termType value of
     SymArray (widthConstant -> Just (Wx l)) _ -> do
       refs <- forM cl $ \expr -> do
                 JSS.RValue ref <- esEval $ evalJavaExpr expr
                 return ref
       let len = mkCInt 32 (toInteger l) 
       let insertValue r m = Map.insert r (len, value) m
       esModifyInitialPathState $ \ps -> ps {
           JSS.arrays = foldr insertValue (JSS.arrays ps) refs
         }
     SymInt (widthConstant -> Just 32) ->
       mapM_ (flip esSetJavaValue (JSS.IValue value)) cl
     SymInt (widthConstant -> Just 64) ->
       mapM_ (flip esSetJavaValue (JSS.LValue value)) cl
     _ -> error "internal: initializing Java values given bad rhs."
-}
  return () -- FIXME

esStep :: BehaviorCommand s -> ExpectedStateGenerator s ()
esStep (AssertPred _ expr) = do
  sc <- gets esContext
  v <- esEval $ evalLogicExpr expr
  esModifyInitialPathStateIO $ addAssumption sc v
esStep (AssumePred expr) = do
  sc <- gets esContext
  v <- esEval $ evalLogicExpr expr
  esModifyInitialPathStateIO $ addAssumption sc v
esStep (Return expr) = do
  v <- esEval $ evalMixedExpr expr
  modify $ \es -> es { esReturnValue = Just v }
esStep (EnsureInstanceField _pos refExpr f rhsExpr) = do
  -- Evaluate expressions.
  ref <- esEval $ evalJavaRefExpr refExpr
  value <- esEval $ evalMixedExpr rhsExpr
  -- Get dag engine
  sc <- gets esContext
  -- Check that instance field is already defined, if so add an equality check for that.
  ifMap <- gets esInstanceFields
  case (Map.lookup (ref, f) ifMap, value) of
    (Nothing, _) -> return ()
    (Just Nothing, _) -> return ()
    (Just (Just (JSS.RValue prev)), JSS.RValue new)
      | prev == new -> return ()
    (Just (Just (JSS.IValue prev)), JSS.IValue new) ->
       esAddEqAssertion sc (show refExpr) prev new
    (Just (Just (JSS.LValue prev)), JSS.LValue new) ->
       esAddEqAssertion sc (show refExpr) prev new
    -- TODO: See if we can give better error message here.
    -- Perhaps this just ends up meaning that we need to verify the assumptions in this
    -- behavior are inconsistent.
    _ -> error "internal: Incompatible values assigned to instance field."
  -- Define instance field post condition.
  modify $ \es ->
    es { esInstanceFields = Map.insert (ref,f) (Just value) (esInstanceFields es) }
esStep (ModifyInstanceField refExpr f) = do
  -- Evaluate expressions.
  ref <- esEval $ evalJavaRefExpr refExpr
  es <- get
  -- Add postcondition if value has not been assigned.
  when (Map.notMember (ref, f) (esInstanceFields es)) $ do
    put es { esInstanceFields = Map.insert (ref,f) Nothing (esInstanceFields es) }
esStep (EnsureArray _pos lhsExpr rhsExpr) = do
  -- Evaluate expressions.
  ref    <- esEval $ evalJavaRefExpr lhsExpr
  value  <- esEval $ evalLogicExpr rhsExpr
  let l = undefined -- SymArray (widthConstant -> Just (Wx l)) _ = termType value -- FIXME
  -- Get dag engine
  sc <- gets esContext
  -- Check if array has already been assigned value.
  aMap <- gets esArrays
  case Map.lookup ref aMap of
    Just (Just (oldLen, prev))
      | l /= fromIntegral oldLen -> error "Array changed size."
      | otherwise -> esAddEqAssertion sc (show lhsExpr) prev value
    _ -> return ()
  -- Define instance field post condition.
  modify $ \es -> es { esArrays = Map.insert ref (Just (l, value)) (esArrays es) }
esStep (ModifyArray refExpr _) = do
  ref <- esEval $ evalJavaRefExpr refExpr
  es <- get
  -- Add postcondition if value has not been assigned.
  when (Map.notMember ref (esArrays es)) $ do
    put es { esArrays = Map.insert ref Nothing (esArrays es) }

initializeVerification :: JSS.MonadSim (SharedContext s) m =>
                          SharedContext s
                       -> MethodSpecIR s
                       -> BehaviorSpec s
                       -> RefEquivConfiguration
                       -> JSS.Simulator (SharedContext s) m (ExpectedStateDef s)
initializeVerification sc ir bs refConfig = do
  exprRefs <- undefined -- mapM (JSS.genRef . jssTypeOfActual . snd) refConfig -- FIXME
  let refAssignments = (map fst refConfig `zip` exprRefs)
  let clName = JSS.className (specThisClass ir)
      key = JSS.methodKey (specMethod ir)
{- TODO: JSS
      callFrame = JSS.Call { JSS.frmClass = clName
                           , JSS.frmMethod = specMethod ir
                           , JSS.frmPC = bsPC bs
                           , JSS.frmLocals = Map.empty
                           , JSS.frmOpds = []
                           }
  -- Push frame to create appropriate merge frames.
  JSS.pushFrame callFrame
  -- Get path state selector.
  initPSS <- JSS.pathStSel <$> JSS.getPathState
  -}
  -- Create initialize path state.
  let initPS = undefined
  {- TODO: JSS
        JSS.PathState {
            JSS.frames         = [callFrame]
          , JSS.finalResult    = JSS.Unassigned
          , JSS.initialization = Map.fromList $
                                   [ (cl, JSS.Initialized)
                                   | cl <- specInitializedClasses ir ]
          , JSS.staticFields   = Map.empty
          , JSS.instanceFields = Map.empty
          , JSS.arrays         = Map.empty
          , JSS.refArrays      = Map.empty
          , JSS.psAssumptions  = mkCBool True
          , JSS.psAssertions   = []
          , JSS.pathStSel      = initPSS
          , JSS.classObjects   = Map.empty
          , JSS.startingPC     = bsPC bs
          , JSS.breakpoints    = Set.fromList $
              map (\brpc -> (clName, key, brpc)) (Map.keys (specBehaviors ir))
          , JSS.insnCount      = 0
          }
-}
      initESG = ESGState { esContext = sc
                         , esMethod = specMethod ir
                         , esExprRefMap = Map.fromList
                             [ (e, r) | (cl,r) <- refAssignments, e <- cl ]
                         , esInitialAssignments = []
                         , esInitialPathState = initPS
                         , esReturnValue = Nothing
                         , esInstanceFields = Map.empty
                         , esArrays = Map.empty
                         }
  es <- liftIO $ flip execStateT initESG $ do
          -- Set references
          forM_ refAssignments $ \(cl,r) ->
            forM_ cl $ \e -> esSetJavaValue e (JSS.RValue r)
          -- Set initial logic values.
          case bsLogicClasses bs refConfig of
            Nothing ->
              let msg = "Unresolvable cyclic dependencies between assumptions."
               in throwIOExecException (specPos ir) (ftext msg) ""
            Just assignments -> mapM_ (\(l,t,r) -> esSetLogicValues l t r) assignments
          -- Process commands
          mapM esStep (bsCommands bs)
  let ps = esInitialPathState es
{- TODO: JSS
  JSS.putPathState ps
  -}
  return ESD { esdStartPC = bsPC bs
             , esdInitialPathState = esInitialPathState es
             , esdInitialAssignments = reverse (esInitialAssignments es)
             , esdRefExprMap =
                  Map.fromList [ (r, cl) | (cl,r) <- refAssignments ]
             , esdReturnValue = esReturnValue es
               -- Create esdArrays map while providing entry for unspecified
               -- expressions.
             , esdInstanceFields =
                 Map.union (esInstanceFields es)
                           (Map.map Just (ps ^. JSS.pathMemory . JSS.memInstanceFields))
               -- Create esdArrays map while providing entry for unspecified
               -- expressions.
             , esdArrays =
                 Map.union (esArrays es)
                           (Map.map Just (ps ^. JSS.pathMemory . JSS.memScalarArrays))
             }

-- MethodSpec verification {{{1

-- VerificationCheck {{{2

data VerificationCheck s
  = AssertionCheck String (SharedTerm s) -- ^ Name of assertion.
  -- | Check that equalitassertion is true.
  | EqualityCheck String -- ^ Name of value to compare
                  (SharedTerm s) -- ^ Value returned by JVM symbolic simulator.
                  (SharedTerm s) -- ^ Expected value in Spec.
  -- deriving (Eq, Ord, Show)

vcName :: VerificationCheck s -> String
vcName (AssertionCheck nm _) = nm
vcName (EqualityCheck nm _ _) = nm

-- | Returns goal that one needs to prove.
vcGoal :: SharedContext s -> VerificationCheck s -> IO (SharedTerm s)
vcGoal _ (AssertionCheck _ n) = return n
-- FIXME: want more polymorphic equality?
vcGoal sc (EqualityCheck _ x y) = do
  n <- scNat sc undefined -- FIXME: size of x and y
  scBvEq sc n x y

type CounterexampleFn s = (SharedTerm s -> IO Value) -> IO Doc

-- | Returns documentation for check that fails.
vcCounterexample :: VerificationCheck s -> CounterexampleFn s
vcCounterexample (AssertionCheck nm n) _ =
  return $ text ("Assertion " ++ nm ++ " is unsatisfied:") <+> scPrettyTermDoc n
vcCounterexample (EqualityCheck nm jvmNode specNode) evalFn =
  do jn <- evalFn jvmNode
     sn <- evalFn specNode
     return (text nm <$$>
        nest 2 (text $ "Encountered: " ++ show jn) <$$>
        nest 2 (text $ "Expected:    " ++ show sn))

-- PathVC {{{2

-- | Describes the verification result arising from one symbolic execution path.
data PathVC s = PathVC {
          pvcStartPC :: JSS.PC
        , pvcEndPC :: Maybe JSS.PC
        , pvcInitialAssignments :: [(TC.JavaExpr, SharedTerm s)]
          -- | Assumptions on inputs.
        , pvcAssumptions :: SharedTerm s
          -- | Static errors found in path.
        , pvcStaticErrors :: [Doc]
          -- | What to verify for this result.
        , pvcChecks :: [VerificationCheck s]
        }

type PathVCGenerator s = State (PathVC s)

-- | Add verification condition to list.
pvcgAssertEq :: String -> SharedTerm s -> SharedTerm s -> PathVCGenerator s ()
pvcgAssertEq name jv sv  =
  modify $ \pvc -> pvc { pvcChecks = EqualityCheck name jv sv : pvcChecks pvc }

pvcgAssert :: String -> SharedTerm s -> PathVCGenerator s ()
pvcgAssert nm v =
  modify $ \pvc -> pvc { pvcChecks = AssertionCheck nm v : pvcChecks pvc }

pvcgFail :: Doc -> PathVCGenerator s ()
pvcgFail msg =
  modify $ \pvc -> pvc { pvcStaticErrors = msg : pvcStaticErrors pvc }

-- generateVC {{{2

-- | Compare result with expected state.
generateVC :: MethodSpecIR s 
           -> ExpectedStateDef s -- ^ What is expected
           -> RunResult s -- ^ Results of symbolic execution.
           -> PathVC s -- ^ Proof oblications
generateVC ir esd (Nothing, _, _) = undefined -- TODO
generateVC ir esd (Just ps, endPC, res) = do
  let initState  =
        PathVC { pvcInitialAssignments = esdInitialAssignments esd
               , pvcStartPC = esdStartPC esd
               , pvcEndPC = endPC
               , pvcAssumptions = undefined -- JSS.psAssumptions ps -- FIXME
               , pvcStaticErrors = []
               , pvcChecks = []
               }
  flip execState initState $ do
    case res of
      Left oe -> pvcgFail (vcat (map (ftext . ppOverrideError) oe))
      Right maybeRetVal -> do
        -- Check return value
        case (maybeRetVal, esdReturnValue esd) of
          (Nothing,Nothing) -> return ()
          (Just (JSS.IValue rv), Just (JSS.IValue srv)) ->
            pvcgAssertEq "return value" rv srv
          (Just (JSS.LValue rv), Just (JSS.LValue srv)) ->
            pvcgAssertEq "return value" rv srv
          (Just (JSS.RValue rv), Just (JSS.RValue srv)) ->
            when (rv /= srv) $
              pvcgFail $ ftext $ "Assigns unexpected return value."
          _ ->  error "internal: The Java method has an unsupported return type."
        -- Check initialization
        do let sinits = Set.fromList (specInitializedClasses ir)
           forM_ (Map.keys (ps ^. JSS.pathMemory . JSS.memInitialization)) $ \cl -> do
             when (cl `Set.notMember` sinits) $ do
               pvcgFail $ ftext $
                 "Initializes extra class " ++ JSS.slashesToDots cl ++ "."
        -- Check static fields
        do forM_ (Map.toList $ ps ^. JSS.pathMemory . JSS.memStaticFields) $ \(f,_jvmVal) -> do
             let clName = JSS.slashesToDots (JSS.fieldIdClass f)
             let fName = clName ++ "." ++ JSS.fieldIdName f
             pvcgFail $ ftext $ "Modifies the static field " ++ fName ++ "."
        -- Check instance fields
        forM_ (Map.toList (ps ^. JSS.pathMemory . JSS.memInstanceFields)) $ \((ref,f), jval) -> do
          let fieldName = show (JSS.fieldIdName f)
                            ++ " of " ++ esdRefName ref esd
          case Map.lookup (ref,f) (esdInstanceFields esd) of
            Nothing ->
              pvcgFail $ ftext $ "Modifies the undefined field " ++ fieldName ++ "."
            Just sval -> do
              case (jval,sval) of
                (_,Nothing) -> return ()
                (jv, Just sv) | jv == sv -> return ()
                (JSS.RValue jref, Just (JSS.RValue _)) ->
                  pvcgFail $ ftext $
                    "Assigns an unexpected value " ++ esdRefName jref esd
                       ++ " to " ++ fieldName ++ "."
                (JSS.IValue jvmNode, Just (JSS.IValue specNode)) ->
                  pvcgAssertEq fieldName jvmNode specNode
                (JSS.LValue jvmNode, Just (JSS.LValue specNode)) ->
                  pvcgAssertEq fieldName jvmNode specNode
                (_, Just _) ->
                  error "internal: comparePathStates encountered illegal field type."
        -- Check value arrays
        forM_ (Map.toList (ps ^. JSS.pathMemory . JSS.memScalarArrays)) $ \(ref,(jlen,jval)) -> do
          case Map.lookup ref (esdArrays esd) of
            Nothing -> pvcgFail $ ftext $ "Allocates an array."
            Just Nothing -> return ()
            Just (Just (slen, sval))
              | jlen /= slen -> pvcgFail $ ftext $ "Array changes size."
              | otherwise -> pvcgAssertEq (esdRefName ref esd) jval sval
        -- Check ref arrays
        when (not (Map.null (ps ^. JSS.pathMemory . JSS.memRefArrays))) $ do
          pvcgFail $ ftext "Modifies references arrays."
{- TODO: JSS
        -- Check assertions
        forM_ (JSS.psAssertions ps) $ \(nm,n) -> do
          pvcgAssert nm n
        -- Check class objects
        forM_ (Map.keys (JSS.classObjects ps)) $ \clNm ->
          pvcgFail $ ftext $ "Allocated class object for " ++ JSS.slashesToDots clNm ++ "."
-}

-- verifyMethodSpec and friends {{{2

mkSpecVC :: JSS.MonadSim (SharedContext s) m =>
            SharedContext s
         -> VerifyParams s
         -> ExpectedStateDef s
         -> JSS.Simulator (SharedContext s) m [PathVC s]
mkSpecVC sc params esd = do
  let ir = vpSpec params
  -- Log execution.
  setVerbosity (simverbose (vpOpts params))
  -- Add method spec overrides.
  mapM_ (overrideFromSpec sc (specPos ir)) (vpOver params)
  -- Execute code.
  JSS.run
  returnVal <- JSS.getProgramReturnValue
  ps <- JSS.getPathMaybe
  errPaths <- JSS.getProgramErrorPaths
{-
  finalPathResults <-
    forM jssResults $ \(pd, fr) -> do
      finalPS <- JSS.getPathStateByName pd
      case fr of
        JSS.ReturnVal val -> return [(finalPS, Nothing, Right (Just val))]
        JSS.Terminated ->    return [(finalPS, Nothing, Right Nothing)]
        JSS.Breakpoint pc -> do
          -- Execute behavior specs at PC.
          let Just bsl = Map.lookup pc (specBehaviors ir)
          let ec = evalContextFromPathState de finalPS
          liftIO $ execBehavior bsl ec finalPS
        JSS.Exc JSS.SimExtErr { JSS.simExtErrMsg = msg } ->
          return [(finalPS, Nothing, Left [SimException msg]) ]
        JSS.Exc JSS.JavaException{ JSS.excRef = r } ->
          return [(finalPS, Nothing, Left [JavaException r])]
        JSS.Aborted ->
          return [(finalPS, Nothing, Left [Abort])]
        JSS.Unassigned -> error "internal: run terminated before completing."
-}
  -- TODO: include error paths
  return $ map (generateVC ir esd) [(ps, Nothing, Right returnVal)]

data VerifyParams s = VerifyParams
  { vpCode    :: JSS.Codebase
  , vpOpts    :: SSOpts
  , vpSpec    :: MethodSpecIR s
  , vpOver    :: [MethodSpecIR s]
  , vpRules   :: [Rule]
  , vpEnabledRules :: Set String
  }

writeToNewFile :: FilePath -- ^ Base file name
               -> String -- ^ Default extension
               -> (Handle -> IO ())
               -> IO FilePath
-- Warning: Contains race conition between checking if file exists and
-- writing.
writeToNewFile path defaultExt m =
  case splitExtension path of
    (base,"") -> impl base (0::Integer) defaultExt
    (base,ext) -> impl base (0::Integer) ext
 where impl base cnt ext = do
          let nm = addExtension (base ++ ('.' : show cnt)) ext
          b <- doesFileExist nm
          if b then
            impl base (cnt + 1) ext
          else
            withFile nm WriteMode m >> return nm

type SymbolicRunHandler s = SharedContext s -> ExpectedStateDef s -> [PathVC s] -> IO ()


{-
writeBlif :: FilePath -> Bool -> SymbolicRunHandler
writeBlif path compressed de _ results = do
  iTypes <- deInputTypes de
  let ext = if compressed then ".cblif" else ".blif"
  -- 1. Generate BLIF for each verification path.
  nm <-
    writeToNewFile path ext $ \h -> do
      Blif.writeBLIF h compressed $ do
        let joinModels ml inputs = do
              Blif.mkConjunction
                =<< mapM (\m -> Blif.mkSubckt m inputs) ml
        models <-
          forM ([(0::Integer)..] `zip` results) $ \(i,pvc) -> do
            let pathname = "path_" ++ show i ++ "_"
            --TOOD: Get path check name.
            condModel <-
              Blif.addModel (pathname ++ "cond") iTypes SymBool $
                Blif.mkTermCircuit (pvcAssumptions pvc)
            if null (pvcStaticErrors pvc) then do
              let addCheck (AssertionCheck nm t) = do
                    Blif.addModel (pathname ++ nm) iTypes SymBool $ \il -> do
                      condVal <- Blif.mkSubckt condModel il
                      predVal <- Blif.mkTermCircuit t il
                      Blif.mkImplication condVal predVal
                  addCheck (EqualityCheck nm simTerm expTerm) = do
                    let tp = termType simTerm
                    simModel <-
                      Blif.addModel (pathname ++ nm ++ "_lhs") iTypes tp $ \il ->
                        Blif.mkTermCircuit simTerm il
                    expModel <-
                      Blif.addModel (pathname ++ nm ++ "_rhs") iTypes tp $ \il ->
                        Blif.mkTermCircuit expTerm il
                    let goalName = pathname ++ nm ++ "_goal"
                    Blif.addModel goalName iTypes SymBool $ \il -> do
                      condVal <- Blif.mkSubckt condModel il
                      simVal <- Blif.mkSubckt simModel il
                      expVal <- Blif.mkSubckt expModel il
                      Blif.mkImplication condVal
                        =<< Blif.mkEquality tp simVal expVal
              checks <- mapM addCheck (pvcChecks pvc)
              Blif.addModel (pathname ++ "goal") iTypes SymBool $
                joinModels checks
            else do
              let goalName = pathname ++ "goal"
              Blif.addModel goalName iTypes SymBool $ \inputs -> do
                Blif.mkNegation <$> Blif.mkSubckt condModel inputs
        void $ Blif.addModel "all" iTypes SymBool $ \inputs ->
          Blif.mkNegation <$> joinModels models inputs
  putStrLn $ "Written to " ++ show nm ++ "."

runValidation :: VerifyParams -> SymbolicRunHandler
runValidation params de esd results = do
  let ir = vpSpec params
  let verb = verbose (vpOpts params)
  let ps = esdInitialPathState esd
  case specValidationPlan ir of
    Skip -> error "internal: Unexpected call to runValidation with Skip"
    GenBlif _ -> error "internal: Unexpected call to runValidation with GenBlif"
    QuickCheck n lim -> do
      forM_ results $ \pvc -> do
        testRandom de verb ir (fromInteger n) (fromInteger <$> lim) pvc
    RunVerify cmds -> do
      forM_ results $ \pvc -> do
        let mkVState nm cfn =
              VState { vsVCName = nm
                     , vsMethodSpec = ir
                     , vsVerbosity = verb
                     , vsRules = vpRules params
                     , vsEnabledRules = vpEnabledRules params
                     , vsEnabledOps = vpEnabledOps params
                     , vsFromPC = esdStartPC esd
                     , vsEvalContext = evalContextFromPathState de ps
                     , vsInitialAssignments = pvcInitialAssignments pvc
                     , vsCounterexampleFn = cfn
                     , vsStaticErrors = pvcStaticErrors pvc
                     }
        if null (pvcStaticErrors pvc) then
         forM_ (pvcChecks pvc) $ \vc -> do
           let vs = mkVState (vcName vc) (vcCounterexample vc)
           g <- scImplies sc (pvcAssumptions pvc) =<< vcGoal de vc
           when (verb >= 4) $ do
             putStrLn $ "Checking " ++ vcName vc
           runVerify vs g cmds
        else do
          let vsName = "an invalid path "
                         ++ (case esdStartPC esd of
                               0 -> ""
                               pc -> " from pc " ++ show pc)
                         ++ maybe "" (\pc -> " to pc " ++ show pc)
                                  (pvcEndPC pvc)
          let vs = mkVState vsName (\_ -> return $ vcat (pvcStaticErrors pvc))
          g <- scImplies sc (pvcAssumptions pvc) (mkCBool False)
          when (verb >= 4) $ do
            putStrLn $ "Checking " ++ vsName
            print $ pvcStaticErrors pvc
            putStrLn $ "Calling runVerify to disprove " ++ prettyTerm (pvcAssumptions pvc)
          runVerify vs g cmds


-- | Attempt to verify method spec using verification method specified.
validateMethodSpec :: VerifyParams -> SymbolicRunHandler -> IO ()
validateMethodSpec
    params@VerifyParams { vpCode = cb
                        , vpOpCache = oc
                        , vpSpec = ir
                        } 
    handler = do
  let verb = verbose (vpOpts params)
  when (verb >= 2) $ putStrLn $ "Starting verification of " ++ specName ir
  let configs = [ (bs, cl)
                | bs <- concat $ Map.elems $ specBehaviors ir
                , cl <- bsRefEquivClasses bs
                ]
  forM_ configs $ \(bs,cl) -> do
    when (verb >= 3) $
      putStrLn $ "Executing " ++ specName ir ++ " at PC " ++ show (bsPC bs) ++ "."
    withSymbolicMonadState oc $ \sms -> do
      let de = smsDagEngine sms
      let sbe = symbolicBackend sms
      JSS.runDefSimulator sbe cb $ do
        -- Create initial Java state and expected state definition.
        esd <- initializeVerification de ir bs cl
        -- Generate VC
        res <- mkSpecVC de params esd
        liftIO $ handler de esd res      
-}

data VerifyState s = VState {
         vsVCName :: String
       , vsMethodSpec :: MethodSpecIR s
       , vsVerbosity :: Verbosity
       -- , vsRules :: [Rule]
       , vsEnabledRules :: Set String
         -- | Starting PC is used for checking VerifyAt commands.
       , vsFromPC :: JSS.PC
         -- | Evaluation context used for parsing expressions during
         -- verification.
       , vsEvalContext :: EvalContext s
       , vsInitialAssignments :: [(TC.JavaExpr, SharedTerm s)]
       , vsCounterexampleFn :: CounterexampleFn s
       , vsStaticErrors :: [Doc]
       }

vsSharedContext :: VerifyState s -> SharedContext s
vsSharedContext = ecContext . vsEvalContext

type VerifyExecutor s = StateT (VerifyState s) IO

--runVerify :: VerifyState s -> SharedTerm s -> [VerifyCommand s] -> IO ()
--runVerify vs g cmds = evalStateT (applyTactics cmds g) vs

-- runABC {{{2

runABC :: SharedTerm s -> VerifyExecutor s ()
runABC goal = do
  sc <- gets vsSharedContext
  v <- gets vsVerbosity
  ir <- gets vsMethodSpec
  ia <- gets vsInitialAssignments
  cfn <- gets vsCounterexampleFn

  liftIO $ do
    when (v >= 3) $ do
      putStrLn $ "Running ABC on " ++ specName ir
      putStrLn $ "Goal is:"
      putStrLn $ scPrettyTerm goal
    be <- createBitEngine
    flip finally (beFree be) $ do
      inputTypes <- undefined -- deInputTypes de -- FIXME
      inputPairs <- V.forM inputTypes $ \tp -> do
        -- Get number of literals.
        lc <- beInputLitCount be
        -- Create input variable.
        l <- undefined -- let ?be = be in lMkInputLitResult tp -- FIXME
        let evalFn bits = undefined -- mkInputEval tp $ SV.slice lc (typeBitCount tp) bits -- FIXME
        return (l,evalFn)
      let (iLits,inputs) = V.unzip inputPairs
      let inputFn i _ = return (iLits V.! i)
      lEval <- undefined -- evalDagTermFn inputFn (mkBitBlastTermSemantics be) -- FIXME
      LV value <- lEval goal
      unless (SV.length value == 1) $
        error "internal: Unexpected number of in verification condition"
      case beCheckSat be of
        Nothing -> error "internal: Bit engine does not support SAT checking."
        Just checkSat -> do
          b <- checkSat (beNeg be (value SV.! 0))
          case b of
            UnSat -> when (v >= 3) $ putStrLn "Verification succeeded."
            Unknown -> do
              let msg = "ABC has returned a status code indicating that it "
                        ++ "could not determine whether the specification is "
                        ++ "correct.  This result is not expected for "
                        ++ "sequential circuits, and could indicate an internal"
                        ++ "error in ABC or SAWScript's connection to ABC."
               in throwIOExecException (specPos ir) (ftext msg) ""
            Sat lits -> do
              evalFn <- undefined -- concreteEvalFn (V.map (\fn -> fn lits) inputs) -- FIXME
              -- Get doc showing inputs
              let docInput (e,n) =
                    do vn <- evalFn n
                       return $ text (TC.ppJavaExpr e) <+> equals
                                                       <+> (text (show vn))
              inputDocs <- mapM docInput ia

              -- Get differences between two.
              val <- cfn evalFn
              let msg = ftext ("ABC failed to verify " ++ specName ir ++ ".\n\n") <$$>
                        ftext ("The inputs that generated the failure are:") <$$>
                        nest 2 (vcat inputDocs) <$$>
                         ftext ("Counterexample:") <$$> nest 2 val
              throwIOExecException (specPos ir) msg ""

-- testRandom {{{2

type Verbosity = Int

{-
testRandom :: DagEngine -> Verbosity
           -> MethodSpecIR -> Int -> Maybe Int -> PathVC -> IO ()
testRandom de v ir test_num lim pvc =
    do when (v >= 3) $
         putStrLn $ "Generating random tests: " ++ specName ir
       (passed,run) <- loop 0 0
       when (passed < test_num) $
         let m = text "Quickcheck: Failed to generate enough good inputs."
                $$ nest 2 (vcat [ text "Attempts:" <+> int run
                                , text "Passed:" <+> int passed
                                , text "Goal:" <+> int test_num
                                ])
         in throwIOExecException (specPos ir) m ""
  where
  loop run passed | passed >= test_num      = return (passed,run)
  loop run passed | Just l <- lim, run >= l = return (passed,run)
  loop run passed = loop (run + 1) =<< testOne passed

  testOne passed = do
    vs   <- V.mapM QuickCheck.pickRandom =<< deInputTypes de
    eval <- concreteEvalFn vs
    badAsmp <- isViolated eval (pvcAssumptions pvc)
    if badAsmp then do
      return passed
    else do 
      when (v >= 4) $
        JSS.dbugM $ "Begin concrete DAG eval on random test case for all goals ("
                            ++ show (length $ pvcChecks pvc) ++ ")."
      forM_ (pvcChecks pvc) $ \goal -> do
        bad_goal <- isInvalid eval goal
        when (v >= 4) $ JSS.dbugM "End concrete DAG eval for one VC check."
        when bad_goal $ do
          (_vs1,goal1) <- QuickCheck.minimizeCounterExample
                            isCounterExample (V.toList vs) goal
          txt <- msg eval goal1
          throwIOExecException (specPos ir) txt ""
      return $! passed + 1

  isCounterExample vs =
    do eval    <- concreteEvalFn (V.fromList vs)
       badAsmps <- isViolated eval (pvcAssumptions pvc)
       if badAsmps
         then return Nothing
         else findM (isInvalid eval) (pvcChecks pvc)

  isViolated eval goal = (not . toBool) <$> (eval goal)
  isInvalid eval vcc   = isViolated eval =<< vcGoal de vcc

  msg eval g =
    do what_happened <-
         case g of
           EqualityCheck n x y ->
              do val_y <- eval y
                 val_x <- eval x
                 return (text "Unexpected value for:" <+> text n
                         $$ nest 2 (text "Expected:" <+> ppCValueD Mixfix val_y)
                         $$ text "Found:"    <+> ppCValueD Mixfix val_x)
           AssertionCheck nm _ -> return (text ("Invalid " ++ nm))

       args <- mapM (ppInput eval) (pvcInitialAssignments pvc)

       return (
         text "Random testing found a counter example:"
         $$ nest 2 (vcat
            [ text "Method:" <+> text (specName ir)
            , what_happened
            , text "Arguments:" $$ nest 2 (vcat args)
            ])
         )

  ppInput eval (expr, n) =
    do val <- eval n
       return $ text (ppJavaExpr expr) <+> text "=" <+> ppCValueD Mixfix val

  toBool (CBool b) = b
  toBool value = error $ unlines [ "Internal error in 'testRandom':"
                                 , "  Expected: boolean value"
                                 , "  Result:   " ++ ppCValue Mixfix value ""
                                 ]
-}

-- useSMTLIB {{{2

announce :: String -> VerifyExecutor s ()
announce msg = do
  v <- gets vsVerbosity
  when (v >= 3) $ liftIO (putStrLn msg)

{-
useSMTLIB :: Maybe Int -> Maybe String -> DagTerm -> VerifyExecutor ()
useSMTLIB mbVer mbNm g = do
  de <- gets vsDagEngine
  ir <- gets vsMethodSpec
  enabledOps <- gets vsEnabledOps
  inputTypes <- liftIO $ deInputTypes de
  announce ("Translating to SMTLIB (version " ++ show version ++"): " ++ specName ir)
  let name = case mbNm of
               Just x  -> x
               Nothing -> specName ir
  liftIO $ do
    let params = SmtLib.TransParams
                   { SmtLib.transName = name
                   , SmtLib.transInputs = V.toList inputTypes
                   , SmtLib.transAssume = mkCBool True
                   , SmtLib.transCheck = [g]
                   , SmtLib.transEnabled = enabledOps
                   , SmtLib.transExtArr = True
                   }
    doc <-
      case version of
        1 -> do (script,_) <- SmtLib.translate params
                return (SmtLib.pp script)

        2 -> do (script,_) <- SmtLib2.translate params
                return (SmtLib2.pp script)
        _ -> error "Unexpected version"

    -- XXX: THERE IS A RACE CONDITION HERE!
    let pickName n = do let cand = name ++ (if n == 0 then "" else show n)
                                        ++ ".smt" ++ ver_exr
                        b <- doesFileExist cand
                        if b then pickName (n + 1) else return cand

    fileName <- pickName (0 :: Integer)
    writeFile fileName (show doc)

  where
  version :: Int
  (version, ver_exr) = case mbVer of
                         Just n | n /= 1 -> (n, show n)
                         _      -> (1, "")   -- For now, we use 1 by default.

-- useYices {{{2

useYices :: Maybe Int -> DagTerm -> VerifyExecutor ()
useYices mbTime g = do
  de <- gets vsDagEngine
  ir <- gets vsMethodSpec
  enabledOps <- gets vsEnabledOps
  inputTypes <- liftIO $ deInputTypes de
  ia <- gets vsInitialAssignments
  announce ("Using Yices2: " ++ specName ir)
  liftIO $ do
    (script,info) <- SmtLib.translate SmtLib.TransParams
        { SmtLib.transName = "CheckYices"
        , SmtLib.transInputs = V.toList inputTypes
        , SmtLib.transAssume = mkCBool True
        , SmtLib.transCheck = [g]
        , SmtLib.transEnabled = enabledOps
        , SmtLib.transExtArr = True
        }

    res <- Yices.yices mbTime script
    case res of
      Yices.YUnsat   -> return ()
      Yices.YUnknown -> yiFail ir (text "Failed to decide property.")
      Yices.YSat m   ->
        yiFail ir ( text "Found a counter example:"
              -- TODO: Fix counterexample generation.
              -- $$ nest 2 (vcat $ intersperse (text " ") $
              --     zipWith ppIn ia (map (Yices.getIdent m) (SmtLib.trInputs info)))
              $$ text " "
              $$ ppUninterp m (SmtLib.trUninterp info)

              $$ ppArgHist ia info m
              $$ text " "

              $$ text "Assumptions:"
              $$ nest 2 (SmtLib.pp (SmtLib.trAsmp info))
              $$ text " "
              $$ text "Goals:"
              $$ nest 2 (vcat $ intersperse (text " ")
                              $ map SmtLib.pp (SmtLib.trGoals info))
              $$ text " "
              $$ text "Full model:"
              $$ nest 2 (vcat $ map Yices.ppVal (Map.toList m))
               )
  where
  yiFail ir xs = fail $ show $ vcat $
                   [ text "Yices: Verification failed."
                   , text "*** Method:" <+> text (specName ir)
                   , text "*** Location:" <+> text (show (specPos ir))
                   , text "*** Details:"
                   , nest 2 xs
                   ]

  _ppIn expr val = Yices.ppVal (TC.ppJavaExpr expr, val)

  ppUninterp _ [] = empty
  ppUninterp m us =
    text "Uninterpreted functions:"
    $$ nest 2 (vcat $
      [ Yices.ppVal (s, Yices.getIdent m i) $$ text " " | (i,s) <- us ]
    )

  varSuccessors m time i = (i,time) :
    case Map.lookup i m of
      Nothing -> []
      Just js -> concatMap (varSuccessors m $! (time + 1)) js

  ppHist model upds nm arg = vcat $ intersperse (text " ")
    [ Yices.ppVal (nm, Yices.getIdent model i)
         -- This is written in this weird way, so that we can easily
         -- switch between the whole update-history for a variable
         -- and just the last value.
         | (i,time) <- [ last $ varSuccessors upds (0::Integer) arg ],
                                                              time /= 0 ]

  ppArgHist ia info model =
    case zipWith (ppHist model (SmtLib.trArrays info))
                 (map (ppJavaExpr . fst) ia)
                 (SmtLib.trInputs info) of
      [] -> empty
      ds -> text ("trInputs = " ++ show (SmtLib.trInputs info))
         $$ text ("trArrays = " ++ show (SmtLib.trArrays info))
         $$ text ("ia = " ++ show ia)
         $$ text ("ia asexpr = " ++ show (map (ppJavaExpr . fst) ia))
         $$ text ("Final values for array arguments:")
         $$ nest 2 (vcat (intersperse (text " ") ds))
-- applyTactics {{{2

applyTactics :: [VerifyCommand] -> DagTerm -> VerifyExecutor ()
applyTactics (Rewrite:r) g = do
  de <- gets vsDagEngine
  rules <- gets vsRules
  enRules <- gets vsEnabledRules
  let isEnabled rl = Set.member (ruleName rl) enRules 
      pgm = foldl' addRule emptyProgram
          $ filter isEnabled rules
  g' <- liftIO $ do
          rew <- mkRewriter pgm de
          reduce rew g
  case getBool g' of
    Just True -> return ()
    _ -> applyTactics r g'
applyTactics (ABC:_) goal = runABC goal
-- SmtLib always succeeds.
applyTactics (SmtLib ver file :_) g = useSMTLIB ver file g
-- Yices always succeeds.
applyTactics (Yices v :_) g = useYices v g
applyTactics (Expand _ expandOp argExprs rhs:r) g = do
  ec <- gets vsEvalContext
  mterms <- runEval $ V.mapM (flip evalLogicExpr ec) (V.fromList argExprs)
  case mterms of
    Left expr ->
      error $ "internal: Unexpected expression " ++ ppJavaExpr expr
    Right terms -> do
      let de = ecDagEngine ec
      let applyFn op lazyArgs = do
            args <- V.sequence lazyArgs
            if op == expandOp && args == terms then
              let argFn i _ = return (terms V.! i)
               in evalDagTerm argFn (deTermSemantics de) rhs
            else
              deApplyOp de op args
      let ts = mkTermSemantics (\i tp -> return (ConstTerm i tp)) applyFn
      g' <- liftIO $ do
        inputs <- deInputTerms de
        evalDagTerm (\i _ -> return (inputs V.! i)) ts g
      applyTactics r g'
applyTactics (VerifyEnable nm :r) g = do
  modify (\s -> s { vsEnabledRules = Set.insert nm (vsEnabledRules s) })
  applyTactics r g
applyTactics (VerifyDisable nm :r) g = do
  modify (\s -> s { vsEnabledRules = Set.delete nm (vsEnabledRules s) })
  applyTactics r g
applyTactics (VerifyAt pc cmds :r) g = do
  fromPC <- gets vsFromPC
  let newCmds | fromPC == pc = cmds ++ r
              | otherwise = r
  applyTactics newCmds g
applyTactics [] g = do
  nm <- gets vsVCName
  ir <- gets vsMethodSpec
  se <- gets vsStaticErrors
  if null se then
    let msg = ftext ("Failed to discharge the verification of " ++ nm
                       ++ " in " ++ specName ir ++ " .\n\n") $$
              ftext ("The remaining goal is:") $$
              nest 2 (prettyTermD g)
     in throwIOExecException (specPos ir) msg ""
  else
    let msg = ftext ("A potentially satisfiable error path was found when verifying "
                       ++ nm ++ " in " ++ specName ir ++ " .\n\n") $$
              ftext ("Path errors:") $$ nest 2 (vcat se) $$
              ftext ("The remaining goal is:") $$ nest 2 (prettyTermD g)
     in throwIOExecException (specPos ir) msg ""
-}
