{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.CommandExec(runProofs) where

-- Imports {{{1
import Control.Exception
import Control.Monad
import Data.Int
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Prelude hiding (catch)
import System.Directory (makeRelativeToCurrentDirectory)
import System.Exit
import System.FilePath
import System.IO (hFlush, stdout)
import Text.PrettyPrint.HughesPJ

import qualified Execution.Codebase as JSS
import SAWScript.Utils
import qualified SAWScript.MethodAST as AST
import qualified SAWScript.MethodSpec as TC
import qualified SAWScript.TypeChecker as TC
import qualified SBVModel.SBV as SBV
import qualified SBVParser as SBV
import qualified Simulation as JSS
import Symbolic
import Utils.IOStateT
import Utils.LogMonad

-- Executor primitives {{{1

data ExecutorState = ES {
    -- | Java codebase
    codebase :: JSS.Codebase
  , execOptions :: SSOpts
    -- | Maps SAWScript function names to corresponding operator definition.
  , sawOpMap :: Map String OpDef
    -- | Map from names to constant value bound to name.
  , globalLetBindings :: Map String (CValue,DagType)
    -- | Maps file paths to verifier commands.
  , parsedFiles :: Map FilePath [AST.VerifierCommand]
    -- | Flag that indicates if verification commands should be executed.
  , runVerification :: Bool
    -- | Maps rule and let binding names to location where it was introduced.
    -- Contains names in sawOpMap
  , definedNames :: Map String Pos
    -- | Maps function names read in from SBV file into corresponding
    -- operator definition and position where operator was introduced.
  , sbvOpMap :: Map String (Pos,OpDef)
    -- | List of method specs added to state.
  , methodSpecs :: [TC.MethodSpecIR]
    -- | Maps rule names to corresponding rule.
  , rules :: Map String Rule
    -- | Set of currently enabled rules.
  , enabledRules :: Set String
  } deriving (Show)

newtype MExecutor m a = Ex (StateT ExecutorState m a)
  deriving ( CatchMIO
           , Functor
           , Monad
           , MonadIO
           , MonadState ExecutorState
           , MonadTrans
           )

type Executor = MExecutor OpSession

instance JSS.HasCodebase Executor where
  getCodebase = gets codebase

-- | Given a file path, this returns the verifier commands in the file,
-- or throws an exception.
parseFile :: FilePath -> Executor [AST.VerifierCommand]
parseFile path = do
  m <- gets parsedFiles
  case Map.lookup path m of
    Nothing -> error $ "internal: Could not find file " ++ path
    Just cmds -> return cmds

getGlobalBindings :: Executor TC.GlobalBindings
getGlobalBindings = do
  cb <- gets codebase
  opts <- gets execOptions
  opBindings <- gets sawOpMap
  constBindings <- gets globalLetBindings
  return $ TC.GlobalBindings { TC.codeBase = cb
                             , TC.ssOpts = opts
                             , TC.opBindings
                             , TC.constBindings
                             }

-- verbosity {{{2

instance LogMonad Executor where
  getVerbosity = fmap verbose $ gets execOptions
  setVerbosity v = modify $ \s -> s { execOptions = (execOptions s) { verbose = v } }

-- | Write messages to standard IO.
whenVerbosityWrite :: (Int -> Bool) -> String -> Executor ()
whenVerbosityWrite cond msg = whenVerbosity cond $ liftIO $ putStrLn msg

-- | Write messages to standard IO without printing a line.
whenVerbosityWriteNoLn :: (Int -> Bool) -> String -> Executor ()
whenVerbosityWriteNoLn cond msg =
  whenVerbosity cond $ liftIO $ do
    putStr msg
    hFlush stdout
          
-- | Write debug message to standard IO.
debugWrite :: String -> Executor ()
debugWrite = whenVerbosityWrite (>=6)

-- Rule functions {{{2

-- | Throw exception indicating a rule already exists.
checkNameIsUndefined :: Pos -> String -> Executor ()
checkNameIsUndefined pos name = do
  m <- gets definedNames
  case Map.lookup name m of
    Nothing -> return ()
    Just absPos -> do
      relPos <- liftIO $ posRelativeToCurrentDirectory absPos
      throwIOExecException pos
                           (ftext "The name " <+> quotes (text name)
                              <+> ftext "has already been defined at "
                              <+> text (show relPos) <> char '.')
                           ("Please ensure all names are distinct.")

checkNameIsDefined :: Pos -> String -> Executor ()
checkNameIsDefined pos name = do
  m <- gets rules
  unless (Map.member name m) $ do
    throwIOExecException pos
                         (text "No operator or rule named " <+> quotes (text name)
                           <+> text "has been defined.")
                         ("Please check that the name is correct.")

-- idRecordsInIRType {{{1

-- | Identify recors in IRType and register them with Executor.
idRecordsInIRType :: Pos -> Doc -> Maybe String -> SBV.IRType -> Executor ()
idRecordsInIRType pos relativePath uninterpName tp =
   case tp of
     SBV.TApp "->" [(SBV.TApp op irTypes), irResult]
        | SBV.isTuple op (length irTypes) -> mapM_ parseType (irResult:irTypes)
     SBV.TApp "->" [irType, irResult] -> mapM_ parseType [irType, irResult]
     _ -> parseType tp -- Contant
  where -- Parse single IRType to get records out of it and verify function names.
        parseType :: SBV.IRType -> Executor ()
        parseType (SBV.TVar _i) = return ()
        parseType (SBV.TInt _i) = return ()
        parseType (SBV.TApp fnName args)
          | SBV.isTuple fnName (length args) =
             case uninterpName of
               Just name ->
                throwIOExecException pos
                  (text "The SBV file" <+> relativePath
                    <+> ftext "references an uninterpreted function" <+> text name
                    <+> ftext "with a tuple type, however this is not currently supported by SAWScript.")
                  ("Please ensure that the SBV file was correctly generated.")
               Nothing ->
                throwIOExecException pos
                  (text "The SBV file" <+> relativePath
                    <+> ftext "has a tuple in its signature.  This is not currently supported by SAWScript.")
                  ("Please rewrite the Cryptol function to use a record rather than a tuple.")
          | otherwise = mapM_ parseType args
        parseType (SBV.TRecord (unzip -> (names,schemes))) = do
          -- Lookup record def for files to ensure it is known to executor.
          _ <- lift $ getStructuralRecord (Set.fromList names)
          mapM_ (parseType . SBV.schemeType) schemes

-- Operations for extracting DagType from AST expression types {{{1

-- | Returns argument types and result type.
opDefType :: OpDef -> ([DagType], DagType)
opDefType def = (V.toList (opDefArgTypes def), opDefResultType def)

-- | Parse the FnType returned by the parser into symbolic dag types.
parseFnType :: AST.FnType -> Executor ([DagType], DagType)
parseFnType (AST.FnType args res) = do
  globalBindings <- getGlobalBindings
  let config = TC.mkGlobalTCConfig globalBindings Map.empty
  lift $ do
    parsedArgs <- mapM (TC.tcType config) args
    parsedRes <- TC.tcType config res
    return (parsedArgs, parsedRes)

-- Operations used for SBV Parsing {{{1

-- | Create record def map using currently known records.
getRecordDefMap :: OpSession SBV.RecordDefMap
getRecordDefMap = do
  curRecDefs <- listStructuralRecords
  let recordFn :: [(String, DagType)] -> Maybe DagType
      recordFn fields =
        let fieldNames = Set.fromList (map fst fields)
            sub = emptySubst { shapeSubst = Map.fromList fields }
         in fmap (flip SymRec sub) $ Map.lookup fieldNames curRecDefs
  return recordFn

-- | Check uninterpreted functions expected in SBV are already defined.
checkSBVUninterpretedFunctions :: Pos -> Doc -> SBV.SBVPgm -> Executor ()
checkSBVUninterpretedFunctions pos relativePath sbv = do
  let SBV.SBVPgm (_ver, _, _cmds, _vc, _warn, sbvUninterpFns) = sbv
  curSbvOps <- gets sbvOpMap
  recordFn <- lift $ getRecordDefMap
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) -> do
    case Map.lookup name curSbvOps of
      Nothing -> do
        let msg = text "The extern SBV file"
                    <+> relativePath
                    <+> text "calls an undefined uninterpreted function named"
                    <+> quotes (text name)
                    <> char '.'
            res = "Please load this extern SBV file before attempting to load \'"
                    ++ name ++ "\'."
        throwIOExecException pos msg res
      Just (_,def) ->
        unless (opDefType def == SBV.inferFunctionType recordFn irType) $ do
          let msg = text "The type of the uninterpreted function"
                     <+> quotes (text name)
                     <+> text "does not match the type expected in the extern SBV file"
                     <+> relativePath <> char '.'
              res = "Please check that the correct SBV files match the Cryptol source."
          throwIOExecException pos msg res

-- | Throw ExecException if SBVException is thrown.
throwSBVParseError :: MonadIO m => Pos -> Doc -> SBV.SBVException -> m a
throwSBVParseError pos relativePath e =
  let msg = text "An internal error occurred when loading the SBV"
              <+> relativePath <> colon $$
              text (SBV.ppSBVException e)
      res = "Please reconfirm that the SBV filename is a valid SBV file from Cryptol."
   in throwIOExecException pos msg res

-- Verifier command execution {{{1

-- | Execute command
execute :: AST.VerifierCommand -> Executor ()
-- Execute commands from file.
execute (AST.ImportCommand _pos path) = do
  mapM_ execute =<< parseFile path
execute (AST.ExternSBV pos nm absolutePath astFnType) = do
  -- Get relative path as Doc for error messages.
  relativePath <- liftIO $ fmap (doubleQuotes . text) $
                    makeRelativeToCurrentDirectory absolutePath
  -- Get name of op in Cryptol from filename.
  let sbvOpName = dropExtension (takeFileName absolutePath)
  -- Get current uninterpreted function map.
  curSbvOps <- gets sbvOpMap
  -- Check if rule for operator definition is undefined.
  checkNameIsUndefined pos nm
  -- Check SBV Op name is undefined.
  case Map.lookup sbvOpName curSbvOps of
    Nothing -> return ()
    Just (absPos,_) -> do
      relPos <- liftIO $ posRelativeToCurrentDirectory absPos
      let msg = (text "The Cryptol function"
                  <+> text sbvOpName
                  <+> ftext "has already been defined at"
                  <+> text (show relPos)
                  <> char '.')
          res = "Please check that each exported function is only loaded once."
       in throwIOExecException pos msg res
  -- Load SBV file
  sbv <- liftIO $ SBV.loadSBV absolutePath
  --- Parse SBV type to add recordDefs as needed.
  debugWrite $ "Parsing SBV type for " ++ nm
  let SBV.SBVPgm (_ver, sbvExprType, _cmds, _vc, _warn, sbvUninterpFns) = sbv
  idRecordsInIRType pos relativePath Nothing sbvExprType
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) ->
    idRecordsInIRType pos relativePath (Just name) irType
  -- Define recordDefFn
  debugWrite $ "Defining recordDefFn for " ++ nm
  recordFn <- lift $ getRecordDefMap
  -- Check that op type matches expected type.
  debugWrite $ "Checking expected type matches inferred type for " ++ nm
  fnType <- parseFnType astFnType
  unless (fnType == SBV.inferFunctionType recordFn sbvExprType) $
    let msg = (ftext "The type of the function in the imported SBV file"
                 $$ relativePath
                 $$ ftext "differs from the type provided to the extern command.")
        res = "Please check that the function exported from Cryptol via SBV "
               ++ "matches the type in the SAWScript file."
     in throwIOExecException pos msg res
  -- Check uninterpreted functions are defined.
  debugWrite $ "Checking uninterpreted inputs for " ++ nm
  checkSBVUninterpretedFunctions pos relativePath sbv
  -- Define uninterpreted function map.
  let uninterpFns :: String -> [DagType] -> Maybe Op
      uninterpFns name _ = fmap (groundOp . snd) $ Map.lookup name curSbvOps
  -- Parse SBV file.
  debugWrite $ "Parsing SBV inport for " ++ nm
  (op, SBV.WEF opFn) <-
    flip catchMIO (throwSBVParseError pos relativePath) $ lift $
      SBV.parseSBVOp recordFn uninterpFns nm sbv
  -- Create rule for definition.
  debugWrite $ "Creating rule definition for for " ++ nm
  let (argTypes,_) = fnType
  let lhsArgs = map (uncurry mkVar) $ (map show ([0..] :: [Int]) `zip` argTypes)
  let lhs = evalTerm $ appTerm (groundOp op) lhsArgs
  rhs <- lift $ runSymSession $ do
    inputVars <- V.mapM freshUninterpretedVar (V.fromList argTypes)
    res <- opFn inputVars :: SymbolicMonad Node
    return $ nodeToTermCtor (fmap show . termInputId) res
  -- Update state with op and rules.
  modify $ \s -> s { sbvOpMap = Map.insert sbvOpName (pos,op) (sbvOpMap s)
                   , definedNames = Map.insert nm pos (definedNames s)
                   , sawOpMap = Map.insert nm op (sawOpMap s)
                   , rules = Map.insert nm (Rule nm lhs rhs) (rules s)
                   --, enabledRules = Set.insert nm (enabledRules s)
                   }
  debugWrite $ "Finished process extern SBV " ++ nm
execute (AST.GlobalLet pos name astExpr) = do
  debugWrite $ "Start defining let " ++ name
  checkNameIsUndefined pos name
  valueExpr <- do
    bindings <- getGlobalBindings
    let config = TC.mkGlobalTCConfig bindings Map.empty
    lift $ TC.tcExpr config astExpr
  val <- lift $ TC.globalEval valueExpr
  let tp = TC.getTypeOfExpr valueExpr
  modify $ \s -> s { definedNames = Map.insert name pos (definedNames s)
                   , globalLetBindings = Map.insert name (val, tp) (globalLetBindings s) }
  debugWrite $ "Finished defining let " ++ name
execute (AST.SetVerification _pos val) = do
  modify $ \s -> s { runVerification = val }
execute (AST.DeclareMethodSpec pos methodId cmds) = do
  let mName:revClasspath = reverse methodId
  when (null revClasspath) $
    throwIOExecException pos (ftext "Missing class in method declaration.") ""
  let jvmClassName = intercalate "/" $ reverse revClasspath
  -- Get class
  thisClass <- JSS.lookupClass jvmClassName
  -- Resolve method spec IR
  ir <- do
    bindings <- getGlobalBindings
    lift $ TC.resolveMethodSpecIR bindings pos thisClass mName cmds
  v <- gets runVerification
  ts <- getTimeStamp
  whenVerbosityWriteNoLn (==1) $
    "[" ++ ts ++ "] Verifying \"" ++ TC.methodSpecName ir ++ "\"... "
  if v && (TC.methodSpecVerificationTactic ir /= AST.Skip)
    then do
      whenVerbosityWrite (>1) $
        "[" ++ ts ++ "] Starting verification of \"" ++ TC.methodSpecName ir ++ "\"."
      ((), elapsedTime) <- timeIt $ do
        cb <- gets codebase
        opts <- gets execOptions
        overrides <- gets methodSpecs
        allRules <- gets rules
        enRules <- gets enabledRules
        let activeRules = map (allRules Map.!) $ Set.toList enRules
        lift $ TC.verifyMethodSpec pos cb opts ir overrides activeRules
      whenVerbosityWrite (==1) $ "Done. [Time: " ++ elapsedTime ++ "]"
      whenVerbosityWrite (>1) $
        "Completed verification of \"" ++ TC.methodSpecName ir ++ "\". [Time: " ++ elapsedTime ++ "]"
    else do
      whenVerbosityWrite (==1) $ "Skipped."
      whenVerbosityWrite (>1) $
        "Skipped verification of \"" ++ TC.methodSpecName ir ++ "\"."
  -- Add methodIR to state for use in later verifications.
  modify $ \s -> s { methodSpecs = ir : methodSpecs s }
execute (AST.Rule pos ruleName params astLhsExpr astRhsExpr) = do
  debugWrite $ "Start defining rule " ++ ruleName
  checkNameIsUndefined pos ruleName
  bindings <- getGlobalBindings
  -- | Get map from variable names to typed expressions.
  nameTypeMap <- lift $ flip execStateT Map.empty $ do
    forM_ params $ \(fieldPos, fieldNm, astType) -> do
      m <- get
      case Map.lookup fieldNm m of
        Just _ ->
          let msg = "Rule contains multiple declarations of the variable \'"
                     ++ fieldNm ++ "\'."
           in throwIOExecException fieldPos (ftext msg) ""
        Nothing -> do
          let config = TC.mkGlobalTCConfig bindings Map.empty
          tp <- lift $ TC.tcType config astType
          modify $ Map.insert fieldNm (TC.Var fieldNm tp)
  let config = TC.mkGlobalTCConfig bindings nameTypeMap
  lhsExpr <- lift $ TC.tcExpr config astLhsExpr
  rhsExpr <- lift $ TC.tcExpr config astRhsExpr
  -- Check types are equivalence
  let lhsTp = TC.getTypeOfExpr lhsExpr
      rhsTp = TC.getTypeOfExpr rhsExpr
  unless (lhsTp == rhsTp) $ do
    let msg = "In the rule " ++ ruleName
                ++ ", the left hand and right hand sides of the rule have distinct types "
                ++ ppType lhsTp ++ " and " ++ ppType rhsTp ++ "."
        res = "Please ensure the left and right-hand side of the rule have equivalent types."
     in throwIOExecException pos (ftext msg) res
  -- Check all vars in quantifier are used.
  let paramVars = Set.fromList $ map (\(_,nm,_) -> nm) params
      lhsVars = TC.typedExprVarNames lhsExpr
  unless (lhsVars == paramVars) $ do
    let msg = "In the rule '" ++ ruleName ++ "', the left hand side term does"
               ++ " not refer to all of the variables in the quantifier."
        res = "Please ensure that all variables are referred to in the"
               ++ " left-hand side of the rule, ensure the right-hand side"
               ++ " does not refer to variables unbound in the left-hand side."
     in throwIOExecException pos (ftext msg) res
  -- TODO: Parse lhsExpr and rhsExpr and add rule.
  let mkRuleTerm :: TC.Expr -> Term
      mkRuleTerm (TC.Apply op args) = appTerm op (map mkRuleTerm args)
      mkRuleTerm (TC.Cns cns tp) = mkConst cns tp
      mkRuleTerm (TC.JavaValue _ _) = error "internal: Java value given to mkRuleTerm"
      mkRuleTerm (TC.Var name tp) = mkVar name tp
  let rl = Rule ruleName (evalTerm (mkRuleTerm lhsExpr)) (evalTerm (mkRuleTerm rhsExpr))
  modify $ \s -> s { rules = Map.insert ruleName rl (rules s)
                   , enabledRules = Set.insert ruleName (enabledRules s) }
  debugWrite $ "Finished defining rule " ++ ruleName
execute (AST.Disable pos name) = do
  checkNameIsDefined pos name
  modify $ \s -> s { enabledRules = Set.delete name (enabledRules s) }
execute (AST.Enable pos name) = do
  checkNameIsDefined pos name
  modify $ \s -> s { enabledRules = Set.insert name (enabledRules s) }

-- | This is the entry point from the front-end
-- The implicit assumption is that you can either return back with an exitCode;
-- or never come back with a proper call to exitWith..
runProofs :: JSS.Codebase
          -> SSOpts
          -> AST.SSPgm
          -> IO ExitCode
runProofs cb ssOpts files = do
  let initialPath = entryPoint ssOpts
  let initState = ES {
          codebase = cb
        , execOptions = ssOpts
        , parsedFiles = files
        , runVerification = True
        , definedNames = Map.empty
        , sawOpMap     = Map.fromList [ ("aget", getArrayValueOpDef)
                                      , ("aset", setArrayValueOpDef)]
        , sbvOpMap     = Map.empty
        , methodSpecs  = []
        , rules        = Map.empty
        , enabledRules = Set.empty
        , globalLetBindings = Map.empty
        }
      Ex action = do cmds <- parseFile initialPath
                     mapM_ execute cmds
                     liftIO $ putStrLn "Verification complete!"
                     return ExitSuccess
  catch (runOpSession (evalStateT action initState))
    (\(ExecException absPos errorMsg resolution) -> do
        relPos <- posRelativeToCurrentDirectory absPos
        ts <- getTimeStamp
        putStrLn $ "\n[" ++ ts ++ "] Verification failed!\n"
        putStrLn $ show relPos
        let rend = renderStyle style { lineLength = 100 }
        putStrLn $ rend $ nest 2 errorMsg
        when (resolution /= "") $ do
          putStrLn ""
          putStrLn $ rend $ nest 2 $ ftext resolution
        return $ ExitFailure (-1))
