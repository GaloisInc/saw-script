{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.CommandExec(runProofs) where

import Control.Exception
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import qualified Data.Vector as V
import Prelude hiding (catch)
import System.Directory (makeRelativeToCurrentDirectory)
import Text.PrettyPrint.HughesPJ


import qualified Execution.Codebase as JSS
import qualified Simulation as JSS

import MethodSpec
import SAWScript.Utils (Pos(..), SSOpts(..))
import qualified SAWScript.MethodAST as AST
import qualified SBVModel.SBV as SBV
import qualified SBVParser as SBV
import Symbolic
import Utils.IOStateT
import System.Exit

data ExecutorState = ES {
    -- | Java codebase
    codeBase :: JSS.Codebase 
    -- | Flag that indicates if verification commands should be executed.
  , runVerification :: Bool
    -- | Maps file paths to verifier commands.
  , parsedFiles :: Map FilePath [AST.VerifierCommand]
    -- | Maps field names to corresponding record definition.
  , recordDefs :: Map (Set String) SymRecDef
    -- | Maps function names read in from SBV file into corresponding
    -- operator definition.
  , sbvOps :: Map String OpDef
    -- | Maps rule names to corresponding rule and location where it was introduced.
  , rules :: Map String (Pos,Rule)
    -- | Set of currently enabled rules.
  , enabledRules :: Set String
  } deriving (Show)

-- | Class of exceptions thrown by SBV parser.
data ExecException = ExecException Pos -- ^ Position
                                   Doc -- ^ Error message
                                   String -- ^ Resolution tip
  deriving (Show, Typeable)
 
instance Exception ExecException

type Executor a = StateT ExecutorState (OpSession IO) a

-- | Given a file path, this returns the verifier commands in the file,
-- or throws an exception.
parseFile :: FilePath -> Executor [AST.VerifierCommand]
parseFile path = do
  m <- gets parsedFiles
  case Map.lookup path m of
    Nothing -> error $ "internal: Could not find file " ++ path
    Just cmds -> return cmds

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> Doc -> String -> m a
throwIOExecException pos errorMsg resolution =
  liftIO $ throwIO (ExecException pos errorMsg resolution)

-- Rule functions {{{2

-- | Return true if rule with given name is enabled.
ruleEnabled :: String -> Executor Bool
ruleEnabled name = fmap (Set.member name) $ gets enabledRules

-- | Throw exception indicating a rule already exists.
checkRuleIsUndefined :: Pos -> String -> Executor ()
checkRuleIsUndefined pos name = do
  m <- gets rules
  case Map.lookup name m of
    Nothing -> return ()
    Just (Pos prevFile prevLine _,_) -> do
      throwIOExecException pos 
                           (text "The name " <+> quotes (text name)
                              <+> text "has already been defined at "
                              <+> text prevFile <> colon <> int prevLine)
                           ("Please ensure all names are distinct.")

checkRuleIsDefined :: Pos -> String -> Executor ()
checkRuleIsDefined pos name = do
  m <- gets rules
  if Map.member name m
    then return ()
    else throwIOExecException pos 
                              (text "No operator or rule named " <+> quotes (text name)
                                <+> text "has been defined.")
                              ("Please check that the name is correct.")

addRule :: String -> TermCtor -> TermCtor -> Executor ()
addRule _nm _lhs _rhs = undefined

-- }}}2

-- This is the entry point from the front-end
-- The implicit assumption is that you can either return back with an exitCode;
-- or never come back with a proper call to exitWith..
runProofs :: JSS.Codebase
          -> SSOpts
          -> AST.SSPgm
          -> IO ExitCode
runProofs cb ssOpts parsedFiles = do
  let initialPath = entryPoint ssOpts
  let initState = ES {
          codeBase = cb
        , runVerification = True
        , parsedFiles  = parsedFiles
        , recordDefs   = Map.empty
        , sbvOps       = Map.empty
        , rules        = Map.empty
        , enabledRules = Set.empty
        }
      action = do cmds <- parseFile initialPath
                  mapM_ execute cmds
                  liftIO $ putStrLn "Verification succeeded!"
                  return ExitSuccess
  catch (runOpSession (evalStateT action initState))
    (\(ExecException pos errorMsg resolution) -> do
        let Pos path line col = pos
        relativePath <- makeRelativeToCurrentDirectory path
        putStrLn $ "Verification Failed!\n"
        putStrLn $ relativePath ++ ":" ++ show line ++ ":" ++ show col ++ ":"
        putStrLn $ render errorMsg
        when (resolution /= "") $ putStrLn $ resolution
        return $ ExitFailure (-1))

-- | Returns record definition for given set of field names
lookupRecordDef :: Set String -> Executor SymRecDef
lookupRecordDef names = do
  rm <- gets recordDefs 
  case Map.lookup names rm of
    Just def -> return def
    Nothing -> do -- Create new record
      let fields = V.map (\name -> (name, defaultPrec, SymShapeVar name))
                 $ V.fromList $ Set.toList names
      rec <- lift $ defineRecord (show names) fields
      modify $ \s -> s { recordDefs = Map.insert names rec (recordDefs s) }
      return rec

-- Parse the given IRType to look for records.
parseFnIRType :: Pos -> Doc -> Maybe String -> SBV.IRType -> Executor ()
parseFnIRType pos relativePath uninterpName tp = 
   case tp of
     SBV.TApp "->" [(SBV.TApp op irTypes), irResult]
        | SBV.isTuple op (length irTypes) -> mapM_ parseType (irResult:irTypes)
     SBV.TApp "->" [irType, irResult] -> mapM_ parseType [irType, irResult]
     _ -> parseType tp -- Contant
  where -- Parse single IRType.
        parseType :: SBV.IRType -> Executor ()
        parseType (SBV.TVar i) = return ()
        parseType (SBV.TInt i) = return ()
        parseType (SBV.TApp fnName args)
          | SBV.isTuple fnName (length args) =
             case uninterpName of
               Just name -> 
                throwIOExecException pos
                  (text "The SBV file" <+> relativePath
                    <+> text "references an uninterpreted function" <+> text name
                    <+> text "with a tuple type, however this is not currently supported by SAWScript.")
                  ("Please ensure that the SBV file was correctly generated.")
               Nothing -> 
                throwIOExecException pos
                  (text "The SBV file" <+> relativePath
                    <+> text "has a tuple in its signature.  This is not currently supported by SAWScript.")
                  ("Please rewrite the Cryptol function to use a record rather than a tuple.")
          | otherwise = mapM_ parseType args
        parseType (SBV.TRecord (unzip -> (names,schemes))) = do
          -- Lookup record def for files to ensure it is known to executor.
          _ <- lookupRecordDef (Set.fromList names)
          mapM_ (parseType . SBV.schemeType) schemes

-- | Throw undeclared uninterpreted function message.
throwUndeclaredFn :: MonadIO m => Pos -> Doc -> String -> m a
throwUndeclaredFn pos relativePath name =
  let msg = text "The extern SBV file"
              <+> relativePath 
              <+> text "calls an undefined uninterpreted function named"
              <+> quotes (text name)
              <> char '.'
      res = "Please load this extern SBV file before attempting to load \'"
              ++ name ++ "\'."
   in throwIOExecException pos msg res

-- | Throw unexpected function type.
throwUnexpectedFnType :: MonadIO m => Pos -> Doc -> String -> m a
throwUnexpectedFnType pos relativePath name =
  let msg = text "The type of the uninterpreted function"
              <+> quotes (text name)
              <+> text "does not match the type expected in the extern SBV file"
              <+> relativePath <> char '.'
      res = "Please check that the correct SBV files match the Cryptol source."
   in throwIOExecException pos msg res

-- | Throw ExecException if SBVException is thrown.
throwSBVParseError :: MonadIO m => Pos -> Doc -> SBV.SBVException -> m a
throwSBVParseError pos relativePath e =
  let msg = text "An internal error occurred when loading the SBV" 
              <+> relativePath <> colon $$
              text (SBV.ppSBVException e)
      res = "Please reconfirm that the SBV filename is a valid SBV file from Cryptol."
   in throwIOExecException pos msg res

-- | Returns argument types and result type.
opDefType :: OpDef -> ([DagType], DagType)
opDefType def = (V.toList (opDefArgTypes def), opDefResultType def)

-- | Convert expression type from AST into WidthExpr
parseExprWidth :: AST.ExprWidth -> WidthExpr
parseExprWidth (AST.WidthConst i) = constantWidth (Wx i)
parseExprWidth (AST.WidthVar nm) = varWidth nm
parseExprWidth (AST.WidthAdd u v) = addWidth (parseExprWidth u) (parseExprWidth v)

-- | Convert expression type from AST into DagType.
-- Uses Executor monad for parsing record types.
parseExprType :: AST.ExprType -> Executor DagType
parseExprType AST.BitType = return SymBool
parseExprType (AST.BitvectorType w) = return (SymInt (parseExprWidth w))
parseExprType (AST.Array l tp) =
  fmap (SymArray (constantWidth (Wx l))) $ parseExprType tp
parseExprType (AST.Record fields) = undefined
parseExprType (AST.ShapeVar v) = return (SymShapeVar v)

-- | Parse the FnType returned by the parser into symbolic dag types.
parseFnType :: AST.FnType -> Executor ([DagType], DagType)
parseFnType (AST.FnType args res) = do
  parsedArgs <- V.mapM parseExprType (V.fromList args)
  parsedRes <- parseExprType res
  return (V.toList parsedArgs, parsedRes)

-- | Execute command 
execute :: AST.VerifierCommand -> Executor ()
-- Execute commands from file.
execute (AST.ImportCommand pos path) = do
  mapM_ execute =<< parseFile path
execute (AST.ExternSBV pos opName absolutePath astFnType) = do
  -- Get relative path as Doc for error messages.
  relativePath <- liftIO $ fmap (doubleQuotes . text) $
                    makeRelativeToCurrentDirectory absolutePath
  -- Check if rule is already defined.
  checkRuleIsUndefined pos opName
  -- Load SBV file
  sbv <- liftIO $ SBV.loadSBV absolutePath
  --- Parse SBV type to add recordDefs as needed.
  let SBV.SBVPgm (_ver, sbvExprType, _cmds, _vc, _warn, sbvUninterpFns) = sbv
  parseFnIRType pos relativePath Nothing sbvExprType
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) ->
    parseFnIRType pos relativePath (Just name) irType
  -- Define recordDefMap
  curRecDefs <- gets recordDefs
  let recordFn :: [(String, DagType)] -> Maybe DagType
      recordFn fields = 
        let fieldNames = Set.fromList (map fst fields)
            sub = emptySubst { shapeSubst = Map.fromList fields }
         in fmap (flip SymRec sub) $ Map.lookup fieldNames curRecDefs
  -- Check that op type matches expected type.
  fnType <- parseFnType astFnType
  unless (fnType == SBV.inferFunctionType recordFn sbvExprType) $ 
    let msg = (text "The type of the function in the imported SBV file"
                 <+> relativePath
                 <+> text "differs from the type provided to the extern command")
        res = "Please check that the function exported from Cryptol via SBV matches the expected type."
     in throwIOExecException pos msg res
  -- Check function types are correct.
  curOps <- gets sbvOps
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) -> do
    case Map.lookup name curOps of
      Nothing -> throwUndeclaredFn pos relativePath name
      Just def -> do
        unless (opDefType def == SBV.inferFunctionType recordFn irType) $
          throwUnexpectedFnType pos relativePath name
  -- Define uninterpreted function map.
  let uninterpFns :: String -> [DagType] -> Maybe Op
      uninterpFns name _ = fmap groundOp $ Map.lookup name curOps
  -- Parse SBV file.
  (op, SBV.WEF opFn) <- 
    flip catchMIO (throwSBVParseError pos relativePath) $ lift $
      SBV.parseSBVOp recordFn uninterpFns opName opName defaultPrec sbv
  -- Create rule for definition.
  let (argTypes,_) = fnType
  let lhsArgs = map (uncurry mkVar) $ (map show ([0..] :: [Int]) `zip` argTypes)
  let lhs = evalTerm $ appTerm (groundOp op) lhsArgs
  rhs <- lift $ runSymSession $ do
    inputVars <- V.mapM freshUninterpretedVar (V.fromList argTypes)
    res <- opFn inputVars :: SymbolicMonad Node
    return $ nodeToTermCtor (fmap show . termInputId) res
  case mkRuleFromCtor opName lhs rhs of
    Left _msg -> error "internal: Unexpected failure when creating rule"
    Right rl -> 
      -- Update state with op and rules.
      modify $ \s -> s { sbvOps = Map.insert opName op (sbvOps s)
                       , rules = Map.insert opName (pos,rl) (rules s)
                       , enabledRules = Set.insert opName (enabledRules s) }
execute (AST.GlobalLet _pos _name _expr) = do
  undefined
execute (AST.SetVerification _pos _val) = do
  undefined
execute (AST.DeclareMethodSpec _pos _method _cmds) = do
  undefined
execute (AST.Rule _pos _name _lhs _rhs) = do
  undefined
  {-
  -- Check rule does not exist.
  re <- ruleExists name
  when re $ do
    throwIOExecException pos $ "The rule " ++ name ++ " has previously been defined."
  -- Parse terms.
  let parseASTTerm :: RewriteTerm -> TermCtor
      parseASTTerm _ = undefined
  let tlhs = parseASTTerm lhs
      trhs = parseASTTerm rhs
  -- TODO: Check that types are equal, and check that right-hand side variables
  -- are contained in left-hand side.
  let rl = mkRuleFromCtor name tlhs trhs
  modify $ \s -> s { rules = Map.insert name rl (rules s)
                   , enabledRules = Set.insert name (enabledRules s) }
                   -}
execute (AST.Disable pos name) = do
  checkRuleIsDefined pos name
  modify $ \s -> s { enabledRules = Set.delete name (enabledRules s) }
execute (AST.Enable pos name) = do
  checkRuleIsDefined pos name
  modify $ \s -> s { enabledRules = Set.insert name (enabledRules s) }
{-
execute (BlastJavaMethodSpec pos specName) = do
  rv <- gets runVerification
  when rv $ do
    cb <- gets codeBase
    let spec :: MethodSpec SymbolicMonad
        spec = undefined
    lift $ blastMethodSpec cb spec
execute (ReduceJavaMethodSpec pos specName) = do
  rv <- gets runVerification
  when rv $ do
    cb <- gets codeBase
    let spec :: MethodSpec SymbolicMonad
        spec = undefined
        installOverrides :: JSS.Simulator SymbolicMonad ()
        installOverrides = do
          -- TODO: Get list of overrides to install.
          -- Install overrides.
          undefined
    lift $ redMethodSpec cb spec installOverrides $ \t -> do
      --TODO: Attempt to reduce term t.
      throwIOExecException pos $ 
        "Verification of " ++ specName ++ " failed!\n" ++
        "The remaining proof obligation is:\n  " ++ prettyTerm t
        -}
