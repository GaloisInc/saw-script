{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.CommandExec(runProofs) where

-- Imports {{{1
import Control.Exception
import Control.Monad
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import qualified Data.Vector as V
import Prelude hiding (catch)
import System.Directory (makeRelativeToCurrentDirectory)
import System.Exit
import System.FilePath
import Text.PrettyPrint.HughesPJ

import qualified Execution.Codebase as JSS
import JavaParser as JSS
import SAWScript.Utils (Pos(..)
                       , SSOpts(..)
                       , posRelativeToCurrentDirectory)
import qualified SAWScript.MethodAST as AST
import qualified SBVModel.SBV as SBV
import qualified SBVParser as SBV
import qualified Simulation as JSS
import Symbolic
import Utils.Common
import Utils.IOStateT

-- Utility functions {{{1

-- | Convert a string to a paragraph formatted document.
ftext :: String -> Doc
ftext msg = fsep (map text $ words msg)

-- ExecException {{{1

-- | Class of exceptions thrown by SBV parser.
data ExecException = ExecException Pos -- ^ Position
                                   Doc -- ^ Error message
                                   String -- ^ Resolution tip
  deriving (Show, Typeable)
 
instance Exception ExecException

-- | Throw exec exception in a MonadIO.
throwIOExecException :: MonadIO m => Pos -> Doc -> String -> m a
throwIOExecException pos errorMsg resolution =
  liftIO $ throwIO (ExecException pos errorMsg resolution)

-- Executor primitives {{{1

data ExecutorState = ES {
    -- | Java codebase
    codebase :: JSS.Codebase 
    -- | Flag that indicates if verification commands should be executed.
  , runVerification :: Bool
    -- | Maps file paths to verifier commands.
  , parsedFiles :: Map FilePath [AST.VerifierCommand]
    -- | Maps field names to corresponding record definition.
  , recordDefs :: Map (Set String) SymRecDef
    -- | Maps function names read in from SBV file into corresponding
    -- operator definition and position where operator was introduced.
  , sbvOpMap :: Map String (Pos,OpDef)
    -- | Maps rule and let binding names to location where it was introduced.
  , definedNames :: Map String Pos
    -- | Maps SAWScript function names to corresponding operator definition.
  , sawOpMap :: Map String OpDef
    -- | Maps rule names to corresponding rule.
  , rules :: Map String Rule
    -- | Set of currently enabled rules.
  , enabledRules :: Set String
    -- | Map from names to constant value bound to name.
  , globalLetBindings :: Map String CValue
    -- | Flag used to control how much logging to print out.
  , verbosity :: Int
  } deriving (Show)

type Executor = StateT ExecutorState (OpSession IO)

instance JSS.HasCodebase Executor where
  getCodebase = gets codebase
  putCodebase cb = modify $ \s -> s { codebase = cb }

-- | Given a file path, this returns the verifier commands in the file,
-- or throws an exception.
parseFile :: FilePath -> Executor [AST.VerifierCommand]
parseFile path = do
  m <- gets parsedFiles
  case Map.lookup path m of
    Nothing -> error $ "internal: Could not find file " ++ path
    Just cmds -> return cmds

-- | Define a polymorphic record from a set of field names.
defineRecFromFields :: Set String -> OpSession IO SymRecDef
defineRecFromFields names =
  defineRecord (show names) $
    V.map (\name -> (name, defaultPrec, SymShapeVar name)) $
          V.fromList (Set.toList names)

-- | Returns record definition for given set of field names
lookupRecordDef :: Set String -> Executor SymRecDef
lookupRecordDef names = do
  rm <- gets recordDefs 
  case Map.lookup names rm of
    Just def -> return def
    Nothing -> do -- Create new record
      rec <- lift $ defineRecFromFields names
      modify $ \s -> s { recordDefs = Map.insert names rec (recordDefs s) }
      return rec

-- verbosity {{{2

-- | Execute command when verbosity exceeds given minimum value.
whenVerbosity :: Int -> Executor () -> Executor ()
whenVerbosity minVerb action = do
  cur <- gets verbosity
  when (minVerb <= cur) action

-- | Write debug message to standard IO.
execDebugLog :: String -> Executor ()
execDebugLog msg = whenVerbosity 6 $ liftIO $ putStrLn msg

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

checkRuleIsDefined :: Pos -> String -> Executor ()
checkRuleIsDefined pos name = do
  m <- gets rules
  unless (Map.member name m) $ do
    throwIOExecException pos 
                         (text "No operator or rule named " <+> quotes (text name)
                           <+> text "has been defined.")
                         ("Please check that the name is correct.")

-- }}}2

--}}}1

-- Parse the given IRType to look for records.
parseFnIRType :: Pos -> Doc -> Maybe String -> SBV.IRType -> Executor ()
parseFnIRType pos relativePath uninterpName tp = 
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
          _ <- lookupRecordDef (Set.fromList names)
          mapM_ (parseType . SBV.schemeType) schemes

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

type FieldRecordMap = Map (Set String) SymRecDef

-- | Convert expression type from AST into DagType.
-- Uses Executor monad for parsing record types.
parseExprType :: AST.ExprType -> Executor DagType
parseExprType (AST.BitType _) = return SymBool
parseExprType (AST.BitvectorType _ w) = return $ SymInt (parseExprWidth w)
parseExprType (AST.Array _ l tp) =
  fmap (SymArray (constantWidth (Wx l))) $ parseExprType tp
parseExprType (AST.Record _ fields) = do
  let names = [ nm | (_,nm,_) <- fields ]
  def <- lookupRecordDef (Set.fromList names)
  tps <- mapM parseExprType [ tp | (_,_,tp) <- fields ]
  let sub = emptySubst { shapeSubst = Map.fromList $ names `zip` tps }
  return $ SymRec def sub
parseExprType (AST.ShapeVar _ v) = return (SymShapeVar v)

-- | Parse the FnType returned by the parser into symbolic dag types.
parseFnType :: AST.FnType -> Executor ([DagType], DagType)
parseFnType (AST.FnType args res) = do
  parsedArgs <- V.mapM parseExprType (V.fromList args)
  parsedRes <- parseExprType res
  return (V.toList parsedArgs, parsedRes)

data TypedExpr 
  = TypedVar String DagType
  | TypedCns CValue DagType
  | TypedApply Op [TypedExpr]
  deriving (Show)

-- | Evaluate a ground typed expression to a constant value.
globalEval :: TypedExpr -> Executor CValue
globalEval exp = do
  let mkNode :: TypedExpr -> SymbolicMonad Node
      mkNode (TypedVar _nm _tp) =
        error "internal: globalEval called with non-ground expression"
      mkNode (TypedCns c tp) = makeConstant c tp
      mkNode (TypedApply op args) = do
        argNodes <- mapM mkNode args
        applyOp op argNodes
  -- | Create rewrite program that contains all the operator definition rules.
  sawOpNames <- fmap Map.keys $ gets sawOpMap
  rls <- gets rules
  let opRls = map (rls Map.!) sawOpNames
      pgm = foldl addRule emptyProgram opRls
  lift $ runSymSession $ do
    n <- mkNode exp
    -- Simplify definition.
    rew <- liftIO $ mkRewriter pgm
    nr <- reduce rew n
    case termConst nr of
      Nothing -> error "internal: globalEval called with an expression that could not be evaluated."
      Just c -> return c

-- | Convert an AST expression from parser into a typed expression.
typecheckGlobalExpr :: AST.Expr -> Executor TypedExpr
typecheckGlobalExpr (AST.TypeExpr pos (AST.ConstantInt _ i) astTp) = do
  tp <- parseExprType astTp
  let throwNonGround =
        let msg = text "The type" <+> text (ppType tp)
                    <+> ftext "bound to literals must be a ground type."
         in throwIOExecException pos msg ""
  case tp of
    SymInt (widthConstant -> Just (Wx w)) ->
      return $ TypedCns (mkCInt (Wx w) i) tp
    SymInt _ -> throwNonGround
    SymShapeVar _ -> throwNonGround
    _ ->
      let msg = text "Incompatible type" <+> text (ppType tp)
                  <+> ftext "assigned to integer literal."
       in throwIOExecException pos msg ""
typecheckGlobalExpr e =
  error $ "internal: typecheckExpr given illegal type " ++ show e

-- | Create record def map using currently known records.
getRecordDefMap :: Executor SBV.RecordDefMap
getRecordDefMap = do
  curRecDefs <- gets recordDefs
  let recordFn :: [(String, DagType)] -> Maybe DagType
      recordFn fields = 
        let fieldNames = Set.fromList (map fst fields)
            sub = emptySubst { shapeSubst = Map.fromList fields }
         in fmap (flip SymRec sub) $ Map.lookup fieldNames curRecDefs
  return recordFn

-- | Check uninterpreted functions expected in SBV are already defined.
checkSBVUninterpretedFunctions :: Pos -> Doc -> SBV.SBVPgm -> Executor ()
checkSBVUninterpretedFunctions pos relativePath sbv = do
  let SBV.SBVPgm (_ver, sbvExprType, _cmds, _vc, _warn, sbvUninterpFns) = sbv
  curSbvOps <- gets sbvOpMap
  recordFn <- getRecordDefMap
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

{-
parseGlobalLetExpr :: AST.RewriteTerm -> Executor CValue
parseGlobalLetExpr initTerm = do
  let parse :: MixExpr RewriteTerm -> SymbolicMonad Node
      parse t = undefined
  undefined

parseMethodLetExpr :: AST.JavaExpr -> Executor (SpecExpr SymbolicMonad)
parseMethodLetExpr = undefined

extractSpecJavaExprs :: AST.JavaExpr -> Set SpecJavaExpr
extractSpecJavaExprs = undefined

parseJavaRef :: AST.JavaRef -> SpecJavaExpr 
parseJavaRef = undefined

parseRewriteExpr :: AST.RewriteTerm -> TermCtor
parseRewriteExpr = undefined
-}


{-
impl (Extern (RewriteVar p v)) = 
  --TODO: Check to see if value for variable is already defined.
impl (ConstantBool p b) = undefined

impl (ConstantInt p i) =
  error "An explicit type must be given for the literal integer " ++ show i


impl (MkArray p []) = error "Explicit type for empty arrays."
impl (MkRecord p fields) = undefined
impl (DerefField p r f) = undefined

impl (ApplyExpr p opName args) = undefined
impl (NotExpr p e) = undefined
impl (MulExpr p x y) = undefined
impl (SDivExpr p x y) = undefined
impl (SRemExpr p x y) = undefined
impl (PlusExpr p x y) = undefined
impl (SubExpr p x y) = undefined
impl (ShlExpr p x y) = undefined
impl (SShrExpr p x y) = undefined
impl (UShrExpr p x y) = undefined
impl (BitAndExpr p x y) = undefined
impl (BitXorExpr p x y) = undefined
impl (BitOrExpr p x y) = undefined
impl (AppendExpr p x y) = undefined
impl (EqExpr p x y) = undefined
impl (IneqExpr p x y) = undefined
impl (SGeqExpr p x y) = undefined
impl (UGeqExpr p x y) = undefined
impl (SGtExpr p x y) = undefined
impl (UGtExpr p x y) = undefined
impl (SLeqExpr p x y) = undefined
impl (ULeqExpr p x y) = undefined
impl (SLtExpr p x y) = undefined
impl (ULtExpr p x y) = undefined
impl (AndExpr p x y) = undefined
impl (OrExpr p x y) = undefined
impl (IteExpr p x y) = undefined


--TODO: Handle special ops (trunc, sext, read, and write).

-}

-- | Atempt to find class with given name, or throw ExecException if no class
-- with that name exists.
lookupClass :: Pos -> String -> Executor JSS.Class
lookupClass pos nm = do 
  maybeCl <- JSS.tryLookupClass nm
  case maybeCl of
    Nothing -> do
     let msg = ftext ("The Java class " ++ slashesToDots nm ++ " could not be found.")
         res = "Please check the class name and class path to ensure that they are correct."
      in throwIOExecException pos msg res
    Just cl -> return cl

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findMethod :: Pos -> String -> JSS.Class -> Executor JSS.Method
findMethod pos nm cl = do
  let javaClassName = slashesToDots (className cl)
  let methodMatches m = methodName m == nm && not (JSS.methodIsAbstract m)
  case filter methodMatches (classMethods cl) of
    [] -> do
      case superClass cl of
        Nothing ->
          let msg = ftext $ "Could not find method " ++ nm
                      ++ " in class " ++ javaClassName ++ "."
              res = "Please check that the class and method are correct."
           in throwIOExecException pos msg res
        Just superName -> 
          findMethod pos nm =<< lookupClass pos superName
    [method] -> return method
    _ -> let msg = ftext $ "The method " ++ nm
                     ++ " in class " ++ javaClassName ++ " is ambiguous."
                     ++ "SAWScript currently requires that method names are unique."
             res = "Please rename the Java method so that it is unique."
          in throwIOExecException pos msg res

-- SpecJavaRefType {{{1

-- | A parsed type from AST.JavaType
data SpecJavaRefType
  = SpecRefClass !(JSS.Class) -- ^ Specific class for a reference.
  | SpecIntArray !Int32
  | SpecLongArray !Int32
  deriving (Eq, Ord, Show)

-- | Converts an int into a Java array length.
checkedGetArrayLength :: Pos -> Int -> Executor Int32
checkedGetArrayLength pos l = do
  unless (0 <= l && toInteger l < toInteger (maxBound :: Int32)) $
    let msg  = "Array length " ++ show l ++ " is invalid."
    throwIOExecException pos (ftext msg) ""
  return $ fromIntegral l

-- | Parse AST Type.
parseASTType :: AST.JavaType -> Executor SpecJavaRefType
parseASTType (AST.RefType pos names) = do
  let nm = intercalate "." names
  fmap SpecRefClass $ lookupClass pos nm
parseASTType (IntArray pos l) =
  fmap SpecIntArray $ checkedGetArrayLength pos l
parseASTType (IntArray pos l) =
  fmap SpecLongArray $ checkedGetArrayLength pos l

-- SpecJavaRef {{{1

data SpecJavaRef 
  = SpecThis
  | SpecArg Int
  | SpecField SpecJavaRef Field
 deriving (Eq, Ord, Show)

-- | Pretty print SpecJavaRef
ppSpecJavaRef :: SpecJavaRef -> String
ppSpecJavaRef SpecThis = "this"
ppSpecJavaRef (SpecArg i) = "args[" ++ show i ++ "]"
ppSpecJavaRef (SpecField r f) = ppSpecJavaRef r ++ ('.' : f)

-- | Return Java ref type from spec reference.
getSpecRefType :: JSS.Class -> JSS.Method -> SpecJavaRef -> Executor SpecJavaRefType
getSpecRefType cl m SpecThis = 
  assert (not (methodIsStatic m)) $ SpecRefClass cl
getSpecRefType cl m (SpecArg i) =
  let params = methodParameterTypes method
  unless (0 <= i && i < length params) $
    throwIOExecException pos (ftext "Invalid argument index for method.") ""

-- }}}1


data SpecParserState = SPS {
          refTypeMap :: Map SpecJavaRef SpecJavaRefType
        }

type SpecParser = StateT SpecParserState Executor

-- | Parse AST Java reference to get specification ref.
parseASTRef :: JSS.Method 
            -> AST.JavaRef
            -> SpecParser (SpecJavaRef, SpecJavaRefType)
parseASTRef method (AST.This pos) = 
  when (methodIsStatic method) $
    throwIOExecException pos (ftext "\'this\' is not defined on static methods.") ""
  return SpecThis
parseASTRef method (AST.Arg pos i) = do
  let params = methodParameterTypes method
  -- Check that arg index is valid.
  unless (0 <= i && i < length params) $
    throwIOExecException pos (ftext "Invalid argument index for method.") ""
  -- Check that arg is a reference.
  case params !! i of
    ArrayType IntType -> return ()
    ArrayType LongType -> return ()
    ArrayType eltType -> 
      let msg = "SAWScript currently only supports arrays of int and long, "
                "and does yet support arrays with type " ++ show eltType ++ "."
          res = "Please modify the Java code to only use int or long array types."
       in throwIOExecException pos (ftext msg) res
    ClassType nm -> return ()
    tp ->
      let msg = "SAWScript only requires reference types to be annotated "
                ++ "with type information, and currently only supports "
                ++ "methods with array and reference values as arguments.  "
                ++ "The type " ++ show tp ++ " is not a reference type."
          res = "Please modify the Java code to only use int or long array "
                ++ "types."
       in throwIOExecException pos (ftext msg) res
  return $ SpecArg i
parseASTRef method (AST.InstanceField pos astLhs fName) = do
  lhs <- parseASTRef method astLhs
  m <- gets regTypeMap
  let throwFieldUndefined =
        let msg = "Could not find a field named " ++ fName ++ " in " 
                    ++ ppSpecJavaRef lhs ++ "."
            res = "Please check to make sure the field name is correct."
         in throwIOExecException pos (ftext msg) res
  case Map.lookup lhs m of
    Nothing -> 
      let msg = "The type of " ++ ppSpecJavaRef lhs 
                   ++ "must be specified before specifying the type of its fields."
          res = "SAWScript requires that the type of an object is specified before the type of its fields."
       in throwIOExecException pos (ftext msg) res
    Just (SpecRefClass cl) -> do
      case filter (\f -> fieldName f == fName) $ classFields cl of
        [] -> throwFieldUndefined
        [f] -> do
          --TODO: Check that field is a reference
          return $ SpecField lhs f
        _ -> error "internal: Found multiple fields with the same name."
    Just _ -> throwFieldUndefined


-- | Returns map from Java references to type.
parseMethodSpecDecl :: String
                    -> JSS.Method
                    -> [MethodSpecDecl]
                    -> Executor SpecParserState
parseMethodSpecDecl methodClass method cmds =
  let impl :: MethodSpecDecl -> SpecParser ()
      impl (Type pos astRefs astTp) = do
        tp <- lift $ parseAstType astTp
        forM_ astRefs $ \astRef -> do
          ref <- parseASTRef method astRef
          m <- gets refTypeMap 
          when (Map.member ref m) $
            let msg = "The type of " ++ ppSpecJavaRef ref ++ " is already defined."
             in throwIOExecException pos (ftext msg) ""
          -- TODO: Check that type of ref and the type of tp are compatible.
          case tp of 
            SpecRefClass cl ->
            SpecIntArray l ->
            SpecLongArray l ->
          -- Add ref to type map.
          modify $ \s -> s { refTypeMap = Map.insert ref 
          undefined
      impl (MayAlias _pos _refs) = undefined
      impl (Const _pos _ref _expr) = undefined
      impl (MethodLet _pos _ref _expr) = undefined
      impl (Assume _pos _expr) = undefined
      impl (Ensures _pos _ref _Expr) = undefined
      impl (Arbitrary _pos _refs) = undefined
      impl (VerifyUsing _pos _method) = undefined
      
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
  -- Check if rule is undefined.
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
  execDebugLog $ "Parsing SBV type for " ++ nm
  let SBV.SBVPgm (_ver, sbvExprType, _cmds, _vc, _warn, sbvUninterpFns) = sbv
  parseFnIRType pos relativePath Nothing sbvExprType
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) ->
    parseFnIRType pos relativePath (Just name) irType
  -- Define recordDefFn
  execDebugLog $ "Defining recordDefFn for " ++ nm
  recordFn <- getRecordDefMap
  -- Check that op type matches expected type.
  execDebugLog $ "Checking expected type matches inferred type for " ++ nm
  fnType <- parseFnType astFnType
  unless (fnType == SBV.inferFunctionType recordFn sbvExprType) $ 
    let msg = (ftext "The type of the function in the imported SBV file"
                 $$ relativePath
                 $$ ftext "differs from the type provided to the extern command.")
        res = "Please check that the function exported from Cryptol via SBV matches the type in the SAWScript file."
     in throwIOExecException pos msg res
  -- Check uninterpreted functions are defined.
  execDebugLog $ "Checking uninterpreted inputs for " ++ nm
  checkSBVUninterpretedFunctions pos relativePath sbv 
  -- Define uninterpreted function map.
  let uninterpFns :: String -> [DagType] -> Maybe Op
      uninterpFns name _ = fmap (groundOp . snd) $ Map.lookup name curSbvOps
  -- Parse SBV file.
  execDebugLog $ "Parsing SBV inport for " ++ nm
  (op, SBV.WEF opFn) <- 
    flip catchMIO (throwSBVParseError pos relativePath) $ lift $
      SBV.parseSBVOp recordFn uninterpFns nm nm defaultPrec sbv
  -- Create rule for definition.
  execDebugLog $ "Creating rule definition for for " ++ nm
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
                   , enabledRules = Set.insert nm (enabledRules s) }
  execDebugLog $ "Finished process extern SBV " ++ nm
execute (AST.GlobalLet pos name astExpr) = do
  execDebugLog $ "Start defining let " ++ name
  checkNameIsUndefined pos name
  expr <- typecheckGlobalExpr astExpr
  val <- globalEval expr
  modify $ \s -> s { definedNames = Map.insert name pos (definedNames s)
                   , globalLetBindings = Map.insert name val (globalLetBindings s) }
  execDebugLog $ "Finished defining let " ++ name
execute (AST.SetVerification _pos val) = do
  modify $ \s -> s { runVerification = val }
execute (AST.DeclareMethodSpec pos methodId cmds) = do
  let mName:revClassPath = reverse methodId
  when (null revClassPath) $
    throwIOExecException pos (ftext "Missing class in method declaration.") ""
  let jvmClassName = intercalate "/" $ reverse revClassPath
  let javaClassName = intercalate "." $ reverse revClassPath
  -- Get class 
  thisClass <- JSS.lookupClass jvmClassName
  -- Find code for method.
  method <- findMethod pos mName thisClass
  -- Get a list of all distinct references in method spec commands.
  -- For each possible aliasing configuration.
  

  error $ "AST.DeclareMethodSpec" ++ show method
execute (AST.Rule _pos _name _params _lhs _rhs) = do
  error "AST.Rule"
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
    cb <- gets codebase
    let spec :: MethodSpec SymbolicMonad
        spec = undefined
    lift $ blastMethodSpec cb spec
execute (ReduceJavaMethodSpec pos specName) = do
  rv <- gets runVerification
  when rv $ do
    cb <- gets codebase
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
        , runVerification = True
        , parsedFiles = files
        , recordDefs   = Map.empty
        , sbvOpMap     = Map.empty
        , definedNames = Map.empty
        , sawOpMap     = Map.empty
        , rules        = Map.empty
        , enabledRules = Set.empty
        , globalLetBindings = Map.empty
        , verbosity = verbose ssOpts
        }
      action = do cmds <- parseFile initialPath
                  mapM_ execute cmds
                  liftIO $ putStrLn "Verification succeeded!"
                  return ExitSuccess
  catch (runOpSession (evalStateT action initState))
    (\(ExecException absPos errorMsg resolution) -> do
        relPos <- posRelativeToCurrentDirectory absPos
        putStrLn $ "Verification Failed!\n"
        putStrLn $ show relPos
        let rend = renderStyle style { lineLength = 100 }
        putStrLn $ rend $ nest 2 errorMsg
        when (resolution /= "") $ do
          putStrLn ""
          putStrLn $ rend $ nest 2 $ ftext resolution
        return $ ExitFailure (-1))
