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
    -- | Maps rule names to corresponding rule.
  , rules :: Map String Rule
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

-- | Return true if rule with given name already exists.
ruleExists :: String -> Executor Bool
ruleExists name = fmap (Map.member name) $ gets rules

-- | Return true if rule with given name is enabled.
ruleEnabled :: String -> Executor Bool
ruleEnabled name = fmap (Set.member name) $ gets enabledRules

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

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> Doc -> String -> m a
throwIOExecException pos errorMsg resolution =
  liftIO $ throwIO (ExecException pos errorMsg resolution)

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
          let nameSet = Set.fromList names
          rm <- gets recordDefs 
          if Map.member nameSet rm
            then return ()
            else do -- Create new record
             let fields = V.map (\name -> (name, defaultPrec, SymShapeVar name))
                        $ V.fromList $ Set.toList nameSet
             rec <- lift $ defineRecord (show nameSet) fields
             modify $ \s -> s { recordDefs = Map.insert nameSet rec (recordDefs s) }

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
opDefType :: OpDef -> (V.Vector DagType, DagType)
opDefType def = (opDefArgTypes def, opDefResultType def)

-- | Convert expression type from AST into WidthExpr
parseExprWidth :: AST.ExprWidth -> WidthExpr
parseExprWidth (AST.WidthVar nm) = undefined
parseExprWidth (AST.WidthConst i) = undefined
parseExprWidth (AST.WidthAdd u v) = undefined

-- | Convert expression type from AST into DagType.
-- Uses Executor monad for parsing record types.
parseExprType :: AST.ExprType -> Executor DagType
parseExprType AST.BitType = return SymBool
parseExprType (AST.BitvectorType w) = return $ SymInt (parseExprWidth w)
parseExprType (AST.Array l tp) = undefined
parseExprType (AST.Record fields) = undefined
parseExprType (AST.ShapeVar v) = undefined

-- | Parse the FnType returned by the parser into symbolic dag types.
parseFnType :: AST.FnType -> Executor (V.Vector DagType, DagType)
parseFnType (AST.FnType args res) = do
  parsedArgs <- V.mapM parseExprType (V.fromList args)
  parsedRes <- parseExprType res
  return (parsedArgs, parsedRes)

-- | Execute command 
execute :: AST.VerifierCommand -> Executor ()
-- Execute commands from file.
execute (AST.ImportCommand pos path) = do
  mapM_ execute =<< parseFile path
execute (AST.ExternSBV pos opName absolutePath fnType) = do
  -- Get relative path for error messages.
  relativePath <- liftIO $ fmap (doubleQuotes . text) $
                    makeRelativeToCurrentDirectory absolutePath
  -- Load SBV file
  sbv <- liftIO $ SBV.loadSBV absolutePath
  --- Parse SBV type to add recordDefs as needed.
  let SBV.SBVPgm (_ver, exprType, _cmds, _vc, _warn, sbvUninterpFns) = sbv
  parseFnIRType pos relativePath Nothing exprType
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) ->
    parseFnIRType pos relativePath (Just name) irType
  -- Define recordDefMap
  curRecDefs <- gets recordDefs
  let recordFn :: [(String, DagType)] -> Maybe DagType
      recordFn fields = 
        let fieldNames = Set.fromList (map fst fields)
            sub = emptySubst { shapeSubst = Map.fromList fields }
         in fmap (flip SymRec sub) $ Map.lookup fieldNames curRecDefs
  -- Check function types are correct.
  curOps <- gets sbvOps
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) -> do
    case Map.lookup name curOps of
      Nothing -> throwUndeclaredFn pos relativePath name
      Just def -> do
        unless (opDefType def == undefined) $ --inferTypeList recordFn irType) $
          throwUnexpectedFnType pos relativePath name
  -- Define uninterpreted function map.
  let uninterpFns :: String -> [DagType] -> Maybe Op
      uninterpFns name _ = fmap groundOp $ Map.lookup name curOps
  -- Parse SBV file.
  (op, SBV.WEF opFn) <- 
    flip catchMIO (throwSBVParseError pos relativePath) $ lift $
      SBV.parseSBVOp recordFn uninterpFns opName opName defaultPrec sbv
  --TODO: Check that op type matches expected type.
  undefined
  -- Add op to SBV ops
  modify $ \s -> s { sbvOps = Map.insert opName op (sbvOps s) }
  -- TODO: Add rule to list of rules.
  undefined
execute (AST.GlobalLet _pos _name _expr) = do
  undefined
execute (AST.SetVerification _pos _val) = do
  undefined
execute (AST.DeclareMethodSpec _pos _method _cmds) = do
  undefined
execute (AST.Rule pos name lhs rhs) = do
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
  -- Check rule exists.
  re <- ruleExists name
  when (not re) $ do
    throwIOExecException pos 
                         (text "No operator or rule named " <+> quotes (text name)
                            <+> text "has been defined.")
                         ("Please check that the name is correct.")
  -- Check rule is enabled.
  en <- ruleEnabled name
  when (not en) $ do
    throwIOExecException pos 
                         (quotes (text name) <+> text "is already disabled.")
                         ""
  -- Disable rule
  modify $ \s -> s { enabledRules = Set.delete name (enabledRules s) }
execute (AST.Enable pos name) = do
  -- Check rule exists.
  re <- ruleExists name
  when (not re) $ do
    throwIOExecException pos 
                         (text "No operator or rule named " <+> quotes (text name)
                            <+> text "has been defined.")
                         ("Please check that the name is correct.")
  -- Check rule is disabled.
  en <- ruleEnabled name
  when en $ do
  when (not en) $ do
    throwIOExecException pos (quotes (text name) <+> text "is already enabled.") ""
  -- Enable rule
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
