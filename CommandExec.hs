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
import qualified Data.Vector.Storable as SV
import qualified Data.Vector as V
import Prelude hiding (catch)
import System.Directory (makeRelativeToCurrentDirectory)
import System.Exit
import System.FilePath
import Text.PrettyPrint.HughesPJ

import qualified Execution.Codebase as JSS
import JavaParser as JSS
import MethodSpec as JSS(partitions)
import SAWScript.Utils
import qualified SAWScript.MethodAST as AST
import SAWScript.TypeChecker 
import qualified SBVModel.SBV as SBV
import qualified SBVParser as SBV
import qualified Simulation as JSS
import Symbolic
import Utils.Common
import Utils.IOStateT

import Debug.Trace

-- Utilities {{{1

-- | Insert multiple keys that map to the same value in a map.
mapInsertKeys :: Ord k => [k] -> a -> Map k a -> Map k a
mapInsertKeys keys val m = foldr (\i -> Map.insert i val) m keys

-- Executor primitives {{{1

data ExecutorState = ES {
    -- | Java codebase
    codebase :: JSS.Codebase 
  , execOptions :: SSOpts
    -- | Maps file paths to verifier commands.
  , parsedFiles :: Map FilePath [AST.VerifierCommand]
    -- | Flag that indicates if verification commands should be executed.
  , runVerification :: Bool
    -- | Maps rule and let binding names to location where it was introduced.
  , definedNames :: Map String Pos
    -- | Maps SAWScript function names to corresponding operator definition.
  , sawOpMap :: Map String OpDef
    -- | Maps function names read in from SBV file into corresponding
    -- operator definition and position where operator was introduced.
  , sbvOpMap :: Map String (Pos,OpDef)
    -- | Maps rule names to corresponding rule.
  , rules :: Map String Rule
    -- | Set of currently enabled rules.
  , enabledRules :: Set String
    -- | Map from names to constant value bound to name.
  , globalLetBindings :: Map String (CValue,DagType)
  } deriving (Show)

type Executor = StateT ExecutorState OpSession

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

globalParserConfig :: Map String TypedExpr -> Executor TCConfig
globalParserConfig localBindings = do
  globalCnsBindings <- gets globalLetBindings
  opBindings <- gets sawOpMap
  cb <- gets codebase
  opts <- gets execOptions
  return TCC { localBindings
             , globalCnsBindings
             , opBindings 
             , codeBase = cb
             , methodInfo = Nothing
             , toJavaExprType = \_ _ -> Nothing
             , sawOptions = opts }

-- verbosity {{{2

-- | Execute command when verbosity exceeds given minimum value.
whenVerbosity :: (Int -> Bool) -> Executor () -> Executor ()
whenVerbosity cond action = do
  opts <- gets execOptions
  when (cond (verbose opts)) action

-- | Write debug message to standard IO.
execDebugLog :: String -> Executor ()
execDebugLog msg = whenVerbosity (>=6) $ liftIO $ putStrLn msg

-- Rule functions {{{2

-- | Throw IO exception indicating name was previously defined.
throwNameAlreadyDefined :: MonadIO m => Pos -> Pos -> String -> m ()
throwNameAlreadyDefined pos absPrevPos name = do
  relPos <- liftIO $ posRelativeToCurrentDirectory absPrevPos
  throwIOExecException pos 
                       (ftext "The name " <+> quotes (text name)
                          <+> ftext "has already been defined at "
                          <+> text (show relPos) <> char '.')
                       ("Please ensure all names are distinct.")

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
  config <- globalParserConfig Map.empty
  lift $ do
    parsedArgs <- mapM (tcType config) args
    parsedRes <- tcType config res
    return (parsedArgs, parsedRes)

-- TypedExpr {{{1

-- | Evaluate a ground typed expression to a constant value.
globalEval :: TypedExpr -> Executor CValue
globalEval expr = do
  let mkNode :: TypedExpr -> SymbolicMonad Node
      mkNode (TypedVar _nm _tp) =
        error "internal: globalEval called with non-ground expression"
      mkNode (TypedJavaValue _nm _tp) =
        error "internal: globalEval called with expression containing Java references."
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
    n <- mkNode expr
    -- Simplify definition.
    rew <- liftIO $ mkRewriter pgm
    nr <- reduce rew n
    case termConst nr of
      Nothing -> error "internal: globalEval called with an expression that could not be evaluated."
      Just c -> return c

-- typecheckExpr{{{2

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


-- SpecJavaType {{{1

-- | A parsed type from AST.JavaType
data SpecJavaType
  = SpecRefClass !(JSS.Class) -- ^ Specific class for a reference.
  | SpecIntArray !Int
  | SpecLongArray !Int
  | SpecBool
  | SpecInt
  | SpecLong

-- | Pretty print SpecJavaType
ppSpecJavaType :: SpecJavaType -> String
ppSpecJavaType (SpecRefClass cl) = className cl
ppSpecJavaType (SpecIntArray l)  = "int[" ++ show l ++ "]"
ppSpecJavaType (SpecLongArray l) = "long[" ++ show l ++ "]"
ppSpecJavaType SpecBool = "bool"
ppSpecJavaType SpecInt  = "int"
ppSpecJavaType SpecLong = "long"

-- | Returns JSS Type of SpecJavaType
getJSSTypeOfSpecJavaType :: SpecJavaType -- ^ Spec Java reference to get type of.
                        -> JSS.Type -- ^ Java type
getJSSTypeOfSpecJavaType (SpecRefClass cl) = JSS.ClassType (className cl)
getJSSTypeOfSpecJavaType (SpecIntArray _) = JSS.ArrayType JSS.IntType
getJSSTypeOfSpecJavaType (SpecLongArray _) = JSS.ArrayType JSS.LongType
getJSSTypeOfSpecJavaType SpecBool = JSS.BooleanType
getJSSTypeOfSpecJavaType SpecInt  = JSS.IntType
getJSSTypeOfSpecJavaType SpecLong = JSS.LongType

-- | Converts an int into a Java array length.
checkedGetArrayLength :: Pos -> Int -> Executor Int
checkedGetArrayLength pos l = do
  unless (0 <= l && toInteger l < toInteger (maxBound :: Int32)) $
    let msg  = "Array length " ++ show l ++ " is invalid."
     in throwIOExecException pos (ftext msg) ""
  return $ fromIntegral l

-- | Parse AST Type to SpecJavaType.
parseASTType :: AST.JavaType -> Executor SpecJavaType
parseASTType (AST.RefType pos names) = do
  let nm = intercalate "/" names
  fmap SpecRefClass $ lookupClass pos nm
parseASTType (AST.IntArray pos l) =
  fmap SpecIntArray $ checkedGetArrayLength pos l
parseASTType (AST.LongArray pos l) =
  fmap SpecLongArray $ checkedGetArrayLength pos l
parseASTType (AST.BoolScalar  _) = return SpecBool
parseASTType (AST.IntScalar  _) = return SpecInt
parseASTType (AST.LongScalar  _) = return SpecLong

-- MethodSpecIR Translation {{{1

-- MethodSpec translation common defines {{{2

-- | Java expression initial value.
data SpecJavaRefInitialValue
  = RIVArrayConst JSS.Type -- ^ Java symbolic simulator type.
                  CValue -- ^ Value of array as const.
                  DagType -- ^ Type of array at symbolic level.
  | RIVClass JSS.Class
  | RIVIntArray !Int
  | RIVLongArray !Int

instance Eq SpecJavaRefInitialValue where
  RIVArrayConst tp1 c1 _ == RIVArrayConst tp2 c2 _ = tp1 == tp2 && c1 == c2
  RIVClass c1 == RIVClass c2 = className c1 == className c2
  RIVIntArray l1 == RIVIntArray l2 = l1 == l2
  RIVLongArray l1 == RIVLongArray l2 = l1 == l2
  _ == _ = False

data SpecPostcondition 
  = PostUnchanged
  | PostArbitrary
  | PostResult TypedExpr

type SpecJavaRefEquivClass = [SpecJavaExpr]

-- MethodSpecTranslation immediate state {{{2

-- | Method spec translator state
-- N.B. keys in nonRefTypes, refTypeMap and constExprMap are disjoint.
data MethodSpecTranslatorState = MSTS {
         -- | Class we are currently parsing.
         specClass :: JSS.Class
       , specMethod :: JSS.Method
       -- | List of non-ref types found in type expressions.
       , nonRefTypes :: Set SpecJavaExpr
         -- | Maps Java expressions referenced in type expressions
         -- to their associated type.
       , refTypeMap :: Map SpecJavaExpr SpecJavaRefInitialValue
         -- | Maps Java references to to associated constant expression.
       , constExprMap :: Map SpecJavaExpr (CValue,DagType)
       -- | Maps Java ref expression to associated equivalence class.
       , mayAliasRefs :: Map SpecJavaExpr SpecJavaRefEquivClass
       -- | List of mayAlias classes in reverse order that they were created.
       , revAliasSets :: [(SpecJavaRefEquivClass, SpecJavaRefInitialValue)]
       -- | Map let bindings local to expression.
       , currentLetBindingMap :: Map String (Pos,TypedExpr)
       -- | List of let bindings encountered in reverse order.
       , reversedLetBindings :: [(String, TypedExpr)]
       -- | Lift of assumptions parsed so far in reverse order.
       , currentAssumptions :: [TypedExpr]
       -- | Set of expressions that have had ensures expressions declared.
       , ensuredExprs :: Set SpecJavaExpr
       -- | Map from Java expressions to typed expression in ensures clause.
       -- or nothing if an arbitrary expression for term has been given.
       , scalarEnsures :: Map SpecJavaExpr (Pos,SpecPostcondition)
       -- | Map from Java expressions to typed expression in ensures clause.
       -- or nothing if an arbitrary expression for term has been given.
       , arrayEnsures :: Map SpecJavaRefEquivClass (Pos, SpecPostcondition)
       -- | Return value found during resolution.
       , currentReturnValue :: Maybe (Pos, TypedExpr)
       -- Verification method chosen.
       , chosenVerificationMethod :: Maybe (Pos, AST.VerificationMethod)
       }

type MethodSpecTranslator = StateT MethodSpecTranslatorState Executor

checkJSSTypeIsRef :: Pos -> JSS.Type -> Executor ()
checkJSSTypeIsRef _ (ArrayType _) = return ()
checkJSSTypeIsRef _ (ClassType _) = return ()
checkJSSTypeIsRef pos tp =
  let msg = "SAWScript only requires reference types to be annotated "
            ++ "with type information, and currently only supports "
            ++ "methods with array and reference values as arguments.  "
            ++ "The type " ++ show tp ++ " is not a reference type."
      res = "Please modify the Java code to only use int or long array "
            ++ "types."
   in throwIOExecException pos (ftext msg) res

-- | Check that the reference type is not mentioned in a constant declaration.
checkRefIsNotConst pos ref note = do
  m <- gets constExprMap
  when (Map.member ref m) $
    let msg = "The Java expression \'" ++ show ref
              ++ "\' was previously used in a const declaration.  "  ++ note
     in throwIOExecException pos (ftext msg) ""

-- | Check that the Java expression type is undefined.
checkTypeIsUndefined :: Pos -> SpecJavaExpr -> String -> MethodSpecTranslator ()
checkTypeIsUndefined pos ref note = do
  s <- gets nonRefTypes
  when (Set.member ref s) $
    let msg = "The type of the Java expresssion \'" ++ show ref
                ++ "\' has been already defined.  " ++ note
     in throwIOExecException pos (ftext msg) ""
  m <- gets refTypeMap 
  when (Map.member ref m) $
    let msg = "The type of the Java expresssion \'" ++ show ref
                ++ "\' has been already defined.  " ++ note
     in throwIOExecException pos (ftext msg) ""

-- | Check that a type declaration has been provided for this expression.
checkJavaTypeIsDefined :: Pos -> SpecJavaExpr -> MethodSpecTranslator ()
checkJavaTypeIsDefined pos javaExpr = do
  m <- gets refTypeMap 
  s <- gets nonRefTypes
  unless (Map.member javaExpr m || Set.member javaExpr s) $
    let msg = "The type of " ++ show javaExpr ++ " has not been defined."
        res = "Please add a \'type\' declaration to indicate the concrete type of this Java expression."
     in throwIOExecException pos (ftext msg) res

-- | Throw io exception indicating that a reference type is incompatible with
-- an expression type.
throwIncompatibleExprType :: MonadIO m => Pos -> String -> JSS.Type -> String -> m ()
throwIncompatibleExprType pos lhsExpr refType specTypeName =
  let msg = "The type of " ++ lhsExpr ++ " is " ++ show refType
             ++ ", which is incompatible with the specification type "
             ++ specTypeName ++ "."
   in throwIOExecException pos (ftext msg) ""

-- | Typecheck expression at global level.
methodParserConfig :: MethodSpecTranslator TCConfig
methodParserConfig = do
  locals <- gets currentLetBindingMap
  cl <- gets specClass
  m <- gets specMethod
  rtm <- gets refTypeMap
  cem <- gets constExprMap
  lift $ do
    globalCnsBindings <- gets globalLetBindings
    opBindings <- gets sawOpMap
    opts <- gets execOptions
    cb <- JSS.getCodebase
    let exprTypeFn :: Pos -> SpecJavaExpr -> Maybe DagType
        exprTypeFn pos e = 
          case Map.lookup e rtm of
            Just (RIVArrayConst _ _ tp) -> Just tp
            Just (RIVClass _) ->
              let msg = "The expression " ++ show e ++ " denotes a Java reference,"
                        ++ " and cannot be directly used in a SAWScript expression."
                  res = "Please alter the expression, perhaps by referring to "
                        ++ "an field in the reference."
               in throw $ ExecException pos (ftext msg) res
            Just (RIVIntArray l) ->
              Just $ SymArray (constantWidth (Wx l)) (SymInt (constantWidth 32))
            Just (RIVLongArray l) ->
              Just $ SymArray (constantWidth (Wx l)) (SymInt (constantWidth 64))
            Nothing ->               
              case Map.lookup e cem of
                Nothing -> Nothing
                Just (_,tp) -> Just tp
    return TCC { localBindings = Map.map snd locals
               , globalCnsBindings
               , opBindings
               , codeBase = cb
               , methodInfo = Just (m, cl)
               , toJavaExprType = exprTypeFn
               , sawOptions = opts }

-- | Typecheck expression at global level.
typecheckJavaExpr :: AST.JavaRef -> MethodSpecTranslator SpecJavaExpr
typecheckJavaExpr astExpr = do
  config <- methodParserConfig
  lift $ lift $ tcJavaExpr config astExpr

-- | Typecheck expression at global level.
typecheckMethodExpr :: AST.Expr -> MethodSpecTranslator TypedExpr
typecheckMethodExpr astExpr = do
  config <- methodParserConfig
  lift $ lift $ tcExpr config astExpr

-- Check that the Java spec reference has a type compatible with typedExpr.
checkSpecJavaExprCompat :: Pos -> String -> JSS.Type -> DagType -> MethodSpecTranslator ()
checkSpecJavaExprCompat pos exprName exprType dagType = do
  case (exprType, dagType) of
    (BooleanType, SymBool) -> return ()
    (IntType, SymInt (widthConstant -> Just 32)) -> return ()
    (LongType, SymInt (widthConstant -> Just 64)) -> return ()
    (  ArrayType IntType
     , SymArray (widthConstant -> Just _) (SymInt (widthConstant -> Just 32))) ->
       return ()
    (  ArrayType LongType
     , SymArray (widthConstant -> Just _) (SymInt (widthConstant -> Just 64))) ->
       return ()
    (_, specType) -> throwIncompatibleExprType pos exprName exprType (ppType specType)

-- | Check that no 'ensures' or 'arbitrary' statement has been added for the
-- given reference is undefined.
checkEnsuresUndefined :: Pos -> SpecJavaExpr -> String -> MethodSpecTranslator ()
checkEnsuresUndefined pos ref msg = do
  exprs <- gets ensuredExprs
  when (Set.member ref exprs) $ 
    throwIOExecException pos (ftext msg) ""

-- | Get type assigned to SpecJavaRef, or throw exception if it is not assigned.
lookupRefType :: Pos -> SpecJavaExpr -> MethodSpecTranslator SpecJavaRefInitialValue
lookupRefType pos ref = do
  m <- gets refTypeMap
  case Map.lookup ref m of
    Just tp -> return tp
    Nothing -> 
      let msg = "The type of " ++ show ref ++ "must be specified "
                  ++ "before referring to it or one of its fields."
          res = "Please add a \'type\' declaration for this expression before this refence."
       in throwIOExecException pos (ftext msg) res

-- | Check that a reference is unaliased.
checkRefIsUnaliased :: Pos -> SpecJavaExpr -> String -> MethodSpecTranslator ()
checkRefIsUnaliased pos ref res = do
  s <- gets mayAliasRefs
  when (Map.member ref s) $ do
    let msg = "\'" ++ show ref ++ "\'was previously mentioned in a mayAlias"
              ++ " declaration."
    throwIOExecException pos (ftext msg) res

-- | Check that Java expression is of a type that can be assigned.
checkJavaExprIsModifiable :: Pos -> SpecJavaExpr -> String -> MethodSpecTranslator ()
checkJavaExprIsModifiable pos expr declName =
  case getJSSTypeOfSpecRef expr of
    JSS.ClassType _ ->
      let msg = declName ++ " declaration given a constant value " ++ show expr
                ++ "SAWScript currently requires constant values are unmodified by method calls."
          res = "Please modify the spec and/or Java code so that it does not "
                ++ "modify a reference value."
       in throwIOExecException pos (ftext msg) res
    _ -> return ()

-- | Add ensures statement mappping Java expr to given postcondition.
addEnsures :: Pos
           -> SpecJavaExpr
           -> SpecPostcondition
           -> MethodSpecTranslator ()
addEnsures pos javaExpr post = do
  aliasClasses <- gets mayAliasRefs
  case getJSSTypeOfSpecRef javaExpr of
    JSS.ArrayType _ -> do
      let equivCl = Map.findWithDefault [javaExpr] javaExpr aliasClasses
      modify $ \s -> 
        s { ensuredExprs = foldr Set.insert (ensuredExprs s) equivCl
          , arrayEnsures = Map.insert equivCl (pos, post) (arrayEnsures s) 
          }
    _ -> do
      modify $ \s -> 
        s { ensuredExprs = Set.insert javaExpr (ensuredExprs s)
          , scalarEnsures = Map.insert javaExpr (pos, post) (scalarEnsures s)
          }

-- | Code for parsing a method spec declaration.
resolveDecl :: AST.MethodSpecDecl -> MethodSpecTranslator ()
resolveDecl (AST.Type pos astExprs astTp) = do
  clName <- fmap className $ gets specClass
  method <- gets specMethod
  let params = V.fromList (methodParameterTypes method)
  specType <- lift $ parseASTType astTp
  forM_ astExprs $ \astExpr -> do
    javaExpr <- typecheckJavaExpr astExpr
    -- Check type has not already been assigned.
    checkTypeIsUndefined pos javaExpr $
      "Multiple type declarations on the same Java expression " 
        ++ "are not allowed."
    -- Check type is not a const.
    checkRefIsNotConst pos javaExpr $
       "Type declarations and const declarations on the same Java expression " 
         ++ "are not allowed."
    let javaExprType = getJSSTypeOfSpecRef javaExpr
        tgtType = getJSSTypeOfSpecJavaType specType
    -- Check that type of ref and the type of tp are compatible.
    b <- lift $ JSS.isSubtype tgtType javaExprType
    unless b $
      throwIncompatibleExprType pos (show javaExpr) javaExprType (ppSpecJavaType specType)
    modify $ \s -> 
      case specType of
        SpecRefClass cl -> s { refTypeMap = Map.insert javaExpr (RIVClass cl)    (refTypeMap s) }
        SpecIntArray l  -> s { refTypeMap = Map.insert javaExpr (RIVIntArray l)  (refTypeMap s) }
        SpecLongArray l -> s { refTypeMap = Map.insert javaExpr (RIVLongArray l) (refTypeMap s) }
        _ -> s { nonRefTypes = Set.insert javaExpr (nonRefTypes s) }
resolveDecl (AST.MayAlias _ []) = error "internal: mayAlias set is empty"
resolveDecl (AST.MayAlias pos astRefs) = do
  let tcASTJavaRef astRef = do
        ref <- typecheckJavaExpr astRef
        lift $ checkJSSTypeIsRef pos (getJSSTypeOfSpecRef ref)
        checkEnsuresUndefined pos ref $
          "An ensures declaration has been added for " ++ show ref
            ++ " prior to this 'mayAlias' declaration.  Please declare "
            ++ " 'mayAlias' declarations before 'ensures' declarations."
        return ref
  refs@(firstRef:restRefs) <- mapM tcASTJavaRef astRefs
  -- Check types of references are the same. are the same.
  firstType <- lookupRefType pos firstRef 
  forM_ restRefs $ \r -> do
    restType <- lookupRefType pos r
    unless (firstType  == restType) $
      let msg = "The type assigned to " ++ show r 
                  ++ " differs from the type assigned "
                  ++ show r ++ "."
          res = "All references that may alias must be assigned the same type."
       in throwIOExecException pos (ftext msg) res
  -- Check refs have not already appeared in a mayAlias set.
  do forM_ refs $ \ref -> do
       checkRefIsUnaliased pos ref $
         "Please merge mayAlias declarations as needed so that each "
           ++ "reference is mentioned at most once."
       checkRefIsNotConst pos ref $
         "Java expressions appearing in const declarations may not be aliased."
  -- Add mayAlias to state.
  modify $ \s -> 
     s { mayAliasRefs = mapInsertKeys refs refs (mayAliasRefs s)
       , revAliasSets = (refs,firstType) : revAliasSets s }
resolveDecl (AST.Const pos astJavaExpr astValueExpr) = do
  -- Typecheck and validate javaExpr.
  javaExpr <- typecheckJavaExpr astJavaExpr
  checkTypeIsUndefined pos javaExpr $
    "Type declarations and const declarations on the same Java expression are not allowed."
  checkRefIsNotConst pos javaExpr $
    "Multiple const declarations on the same Java expression are not allowed."
  -- Parse expression (must be global since this is a constant.
  valueExpr <- lift $ do
    config <- globalParserConfig Map.empty
    lift $ tcExpr config astValueExpr
  val <- lift $ globalEval valueExpr
  let tp = getTypeOfTypedExpr valueExpr
  -- Check ref and expr have compatible types.
  checkSpecJavaExprCompat pos (show javaExpr) (getJSSTypeOfSpecRef javaExpr) tp
  -- Add ref to refTypeMap
  modify $ \s -> s { constExprMap = Map.insert javaExpr (val,tp) (constExprMap s) }
resolveDecl (AST.MethodLet pos name astExpr) = do
  -- Check var is not already bound.
  do lift $ checkNameIsUndefined pos name
     locals <- gets currentLetBindingMap
     case Map.lookup name locals of
       Nothing -> return ()
       Just (prevPos,_) -> throwNameAlreadyDefined pos prevPos name
  expr <- typecheckMethodExpr astExpr
  -- Add binding to let bindings
  modify $ \s ->
    s { currentLetBindingMap = Map.insert name (pos,expr) (currentLetBindingMap s)
      , reversedLetBindings = (name,expr) : reversedLetBindings s }
resolveDecl (AST.Assume _pos astExpr) = do
  expr <- typecheckMethodExpr astExpr
  modify $ \s -> s { currentAssumptions = expr : currentAssumptions s }
resolveDecl (AST.Ensures pos astJavaExpr astValueExpr) = do
  -- Resolve and check astJavaExpr.
  javaExpr <- typecheckJavaExpr astJavaExpr
  checkJavaTypeIsDefined pos javaExpr
  checkJavaExprIsModifiable pos javaExpr "\'ensures\'"
  checkEnsuresUndefined pos javaExpr $
    "Multiple ensures and arbitrary statements have been added for " ++ show javaExpr ++ "."
  -- Resolve astValueExpr
  valueExpr <- typecheckMethodExpr astValueExpr
  -- Check javaExpr and valueExpr have compatible types.
  let javaExprType = getJSSTypeOfSpecRef javaExpr
      valueExprType = getTypeOfTypedExpr valueExpr
  checkSpecJavaExprCompat pos (show javaExpr) javaExprType valueExprType
  addEnsures pos javaExpr (PostResult valueExpr)
resolveDecl (AST.Arbitrary pos astJavaExprs) = do 
  forM_ astJavaExprs $ \astJavaExpr -> do
    -- Resolve and check astJavaExpr.
    javaExpr <- typecheckJavaExpr astJavaExpr
    checkJavaTypeIsDefined pos javaExpr
    checkJavaExprIsModifiable pos javaExpr "\'arbitrary\'"
    checkEnsuresUndefined pos javaExpr $
      "Multiple ensures and arbitrary statements have been added for " ++ show javaExpr ++ "."
    addEnsures pos javaExpr PostArbitrary
resolveDecl (AST.Returns pos astValueExpr) = do
  -- Check return value is undefined.
  do rv <- gets currentReturnValue
     case rv of
       Nothing -> return ()
       Just (absPrevPos, _) -> do
         relPos <- liftIO $ posRelativeToCurrentDirectory absPrevPos
         let msg = "Multiple return values specified in a single method spec.  The "
                   ++ "previous return value was given at " ++ show relPos ++ "."
         throwIOExecException pos (ftext msg) ""
  -- Resolve astValueExpr
  valueExpr <- typecheckMethodExpr astValueExpr
  -- Check javaExpr and valueExpr have compatible types.
  method <- gets specMethod
  case JSS.methodReturnType method of
    Nothing ->
      let msg = "Return value specified for \'" ++ JSS.methodName method ++ "\', but "
                 ++ "method returns \'void\'."
       in throwIOExecException pos (ftext msg) ""
    Just returnType ->
      let valueExprType = getTypeOfTypedExpr valueExpr
       in checkSpecJavaExprCompat pos "the return value" returnType valueExprType
  -- Update state with return value.
  modify $ \s -> s { currentReturnValue = Just (pos, valueExpr) }
resolveDecl (AST.VerifyUsing pos method) = do
  -- Check verification method has not been assigned.
  vm <- gets chosenVerificationMethod
  case vm of
   Nothing -> return ()
   Just (_oldPos,_) ->
     let msg = "The verification tactic is set multiple times in the same "
                ++ "method specification."
         res = "Please include at most one verification tactic in a single specification."
      in throwIOExecException pos (ftext msg) res
  -- Assign verification method.
  modify $ \s -> s { chosenVerificationMethod = Just (pos,method) }

-- MethodSpecIR {{{2

data MethodSpecIR = MSIR {
    methodSpecPos :: Pos
  , methodSpecIRClass :: JSS.Class
  , methodSpecIRMethod :: JSS.Method
    -- | Class names expected to be initialized using JVM "/" separators.
    -- (as opposed to Java "." path separators).
  , initializedClasses :: [String]
    -- | References in specification with alias information and reference info.
  , specReferences :: [(SpecJavaRefEquivClass, SpecJavaRefInitialValue)]
    -- | List of non-reference input variables that must be available.
  , specScalarInputs :: [SpecJavaExpr]
    -- | List of constants expected in input.
  , specConstants :: [(SpecJavaExpr,CValue,DagType)]
    -- | Let bindings
  , methodLetBindings :: [(String,TypedExpr)]
  -- | Preconditions that must be true before method executes.
  , assumptions :: [TypedExpr]
  -- | Maps expressions for scalar values to their expected value after execution.
  -- This map should include results both inputs and constants.
  , scalarPostconditions :: Map SpecJavaExpr SpecPostcondition
  -- | Maps expressions ot the expected value after execution.
  -- This map should include results both inputs and constants.
  -- The keys may include arrays and class references, but only arrays may be mapped to unchanged.
  , arrayPostconditions :: Map SpecJavaRefEquivClass SpecPostcondition
  -- | Return value if any (is guaranteed to be compatible with method spec.
  , returnValue :: Maybe TypedExpr
  -- | Verification method for method. 
  , verificationMethod :: AST.VerificationMethod
  }

-- | Interprets AST method spec commands to construct an intermediate
-- representation that 
resolveMethodSpecIR :: Pos
                    -> JSS.Class
                    -> JSS.Method
                    -> [AST.MethodSpecDecl]
                    -> Executor MethodSpecIR
resolveMethodSpecIR pos cl method cmds = do
  let st = MSTS { specClass = cl
                , specMethod = method
                , nonRefTypes = Set.empty
                , refTypeMap = Map.singleton (SpecThis (className cl)) (RIVClass cl)
                , constExprMap = Map.empty
                , mayAliasRefs = Map.empty
                , revAliasSets = [] 
                , currentLetBindingMap = Map.empty
                , reversedLetBindings = []
                , currentAssumptions = []
                , ensuredExprs = Set.empty
                , scalarEnsures = Map.empty
                , arrayEnsures = Map.empty
                , chosenVerificationMethod = Nothing
                }
  st' <- fmap snd $ runStateT (mapM_ resolveDecl cmds) st
  -- Get list of initial superclasses.
  superClasses <- JSS.supers cl
  -- Check that each declaration of a field does not have the base
  -- object in the mayAlias class.
  let allRefs = Map.keysSet (refTypeMap st') `Set.union` Map.keysSet (constExprMap st')
  let checkRef (SpecThis _) = return ()
      checkRef (SpecArg _ _) = return ()
      checkRef (SpecField lhs f) = do
        when (Map.member lhs (mayAliasRefs st')) $
          let msg = "This specification contains a mayAlias declaration "
                   ++ "containing \'" ++ show lhs ++ "\' and an additional "
                   ++ "declaration that references its field \'"
                   ++ JSS.fieldName f ++ "\'.  The current SAWScript "
                   ++ "implementation does not support this."
              res = "Please remove the mayAlias declaration of \'" ++ show lhs
                   ++ "\' and alter the Java code as needed."
           in throwIOExecException pos (ftext msg) res
        checkRef lhs
  mapM_ checkRef (Set.toList allRefs)
  -- Define specReferences
  let unaliasedRefs
        = map (\(r,tp) -> ([r], tp))
        $ filter (\(r,_) -> Map.notMember r (mayAliasRefs st'))
        $ Map.toList (refTypeMap st')
  let constRefs
        = catMaybes
        $ map (\(r,(c,tp)) ->
                 let javaTp = getJSSTypeOfSpecRef r
                  in case javaTp of
                       ArrayType _ -> Just ([r], RIVArrayConst javaTp c tp)
                       _ -> Nothing)
        $ Map.toList (constExprMap st')
  let specReferences = revAliasSets st' ++ unaliasedRefs ++ constRefs
  --TODO: Validate that types or constants for all arguments have been provided.
  -- Get specConstants
  let specConstants
        = catMaybes
        $ map (\(r,(c,tp)) ->
                 case tp of
                   SymInt _ -> Just (r, c, tp)
                   _ -> Nothing)
        $ Map.toList (constExprMap st')
  -- returnValue
  returnValue <-
    case JSS.methodReturnType method of
      Nothing -> return Nothing
      Just cl -> do
        let throwUndefinedReturnValue =
              let msg = "The Java method \'" ++ methodName method 
                        ++ "\' has a return value, but the spec does not define it."
               in throwIOExecException pos (ftext msg) ""
        maybe throwUndefinedReturnValue (return . Just . snd) $
              (currentReturnValue st')
  -- Get post conditions
  let allExprs = (nonRefTypes st') `Set.union` (Map.keysSet (constExprMap st'))
  let scalarPostconditions =
        let getScalarPostCondition expr =
             case Map.lookup expr (scalarEnsures st') of
               Nothing -> (expr, PostUnchanged)
               Just (pos,cond) -> (expr, cond)
     
         in Map.fromList $ map getScalarPostCondition
                         $ Set.toList (nonRefTypes st')
  let arrayPostconditions = 
        let getArrayPostCondition (refEqClass,_) =
             case Map.lookup refEqClass (arrayEnsures st') of
               Nothing -> (refEqClass, PostUnchanged)
               Just (_,cond) -> (refEqClass, cond)
            isArrayClass (_, RIVClass _) = False
            isArrayClass _ = True
         in Map.fromList $ map getArrayPostCondition
                         $ filter isArrayClass
                         $ specReferences
  -- Get verification method.
  let throwUndefinedVerification =
        let msg = "The verification method for \'" ++ methodName method 
                  ++ "\' is undefined."
            res = "Please specify a verification method.  Use \'skip\' to skip verification."
         in throwIOExecException pos (ftext msg) res
  verificationMethod
    <- maybe throwUndefinedVerification (return . snd) $
         chosenVerificationMethod st'
  -- Return IR.
  return MSIR { methodSpecPos = pos
              , methodSpecIRClass = cl
              , methodSpecIRMethod = method
              , initializedClasses = map className superClasses
              , specReferences
              , specScalarInputs = Set.toList (nonRefTypes st')
              , specConstants
              , methodLetBindings = reverse (reversedLetBindings st')
              , assumptions = currentAssumptions st'
              , scalarPostconditions
              , arrayPostconditions
              , returnValue
              , verificationMethod
              }

-- MethodSpec verification {{{1
-- EquivClassMap {{{2
type EquivClassMap = (Int, Map Int [SpecJavaExpr], Map Int SpecJavaRefInitialValue)

-- | Return list of class indices to initial values.
equivClassMapEntries :: EquivClassMap -> V.Vector (Int,[SpecJavaExpr],SpecJavaRefInitialValue)
equivClassMapEntries (_,em,vm) 
  = V.map (\(i,v) -> (i,em Map.! i,v))
  $ V.fromList $ Map.toList vm

-- JavaEvalState {{{2
type InputEvaluator = SV.Vector Bool -> CValue

data JavaEvalState = JES {
        -- | Name of class in printable form.
        jesClassName :: String   
        -- | Name of method in printable form.
      , jesMethodName :: String
        -- | Maps Java expression to associated node.
      , jesExprNodeMap :: Map SpecJavaExpr Node
        -- | Contains functions that translate from counterexample
        -- returned by ABC back to constant values, along with the
        -- Java expression associated with that evaluator.
      , jesInputEvaluators :: [(SpecJavaExpr,InputEvaluator)]
        -- | Maps Spec Java expression to value for that expression.
      , jesExprValueMap :: Map SpecJavaExpr (JSS.Value Node)
        -- | Maps JSS refs to name for that ref.
      , jesRefNameMap :: Map JSS.Ref String
        -- | List of array references, the associated equivalence class, and the initial value.
      , jesArrayNodeList :: [(JSS.Ref,SpecJavaRefEquivClass,Node)]
      , jesLetNodeBindings :: Map String Node
      }

-- | Returns name of reference in a state.
getRefName :: MonadIO m => Pos -> JSS.Ref -> JavaEvalState -> m String
getRefName pos r jem = do
  case Map.lookup r (jesRefNameMap jem) of
    Nothing ->
      let msg = "The JVM method \'" ++ jesMethodName jem ++ "\' has allocated "
                ++ "a new reference.  JavaVerifier does not currently support "
                ++ "methods that allocate new references."
       in throwIOExecException pos (ftext msg) ""
    Just e -> return (show e)

-- | Returns value associated to Java expression in initial state associated with mapping.
jesExprValue :: MonadIO m => JavaEvalState -> SpecJavaExpr -> m (JSS.Value Node)
jesExprValue jem expr = do
  case Map.lookup expr (jesExprValueMap jem) of
    Nothing -> error $ "internal: jesExprValue given undefined expression " ++ show expr
    Just v -> return v

-- | Returns information about value of instance fields at initial state.
initialInstanceFieldValues :: JavaEvalState
                           -> [(SpecJavaExpr, JSS.Ref, JSS.FieldId, JSS.Value Node)]
initialInstanceFieldValues JES { jesClassName = clName, jesExprValueMap = m } =
  [ (expr, ref, fid, v)
    | (expr@(SpecField refExpr f), v) <- Map.toList m
    , let Just (JSS.RValue ref) = Map.lookup refExpr m
    , let fid = FieldId clName (fieldName f) (fieldType f) ]

-- | Evaluates a typed expression.
evalTypedExpr :: JavaEvalState -> TypedExpr -> SymbolicMonad Node
evalTypedExpr jes (TypedApply op exprs) = do
  applyOp op =<< mapM (evalTypedExpr jes) exprs
evalTypedExpr _ (TypedCns c tp) = 
  makeConstant c tp
evalTypedExpr jes (TypedJavaValue javaExpr tp) = do
  case Map.lookup javaExpr (jesExprNodeMap jes) of
    Nothing -> error $ "internal: evalTypedExpr given invalid Java expression."
    Just n -> return n
evalTypedExpr jes (TypedVar name tp) = do
  case Map.lookup name (jesLetNodeBindings jes) of
    Nothing -> error $ "internal: evalTypedExpr given invalid variable " ++ name
    Just n -> return n

type JavaEvaluator = StateT JavaEvalState (JSS.Simulator SymbolicMonad)

-- createJavaEvalState {{{3

-- | Initialize JavaEvalState components involving references,
-- and create them in simulator.
createJavaEvalReferences :: EquivClassMap -> JavaEvaluator ()
createJavaEvalReferences cm = do
  let liftAig = lift . JSS.liftSymbolic . liftAigMonad
      liftSym = lift . JSS.liftSymbolic
  V.forM_ (equivClassMapEntries cm) $ \(idx, exprClass, initValue) -> do
    litCount <- liftAig $ getInputLitCount
    let refName = show (head exprClass)
    let -- create array input node with length and int width.
        createInputArrayNode l w = do
          let arrType = SymArray (constantWidth (Wx l)) (SymInt (constantWidth (Wx w)))
          lv <- liftAig $ V.replicateM l $ fmap LV $ SV.replicateM w makeInputLit
          n <- liftSym $ freshVar arrType (LVN lv)
          let inputEval lits =
                CArray $ V.map (\j -> mkCIntFromLsbfV $ SV.slice j w lits)
                       $ V.enumFromStepN litCount w (fromIntegral l)
          ref <- lift $ JSS.newSymbolicArray (JSS.ArrayType JSS.IntType) (fromIntegral l) n
          modify $ \s -> 
            s { jesExprNodeMap =  mapInsertKeys exprClass n (jesExprNodeMap s)
              , jesInputEvaluators = map (\expr -> (expr,inputEval)) exprClass
                                      ++ jesInputEvaluators s
              , jesExprValueMap = mapInsertKeys exprClass (JSS.RValue ref) (jesExprValueMap s)
              , jesRefNameMap = Map.insert ref refName (jesRefNameMap s)
              , jesArrayNodeList = (ref,exprClass,n):(jesArrayNodeList s) }
    case initValue of
      RIVArrayConst javaTp c@(CArray v) tp -> do
        n <- liftSym $ makeConstant c tp
        let l = V.length v
        ref <- lift $ JSS.newSymbolicArray javaTp (fromIntegral l) n
        modify $ \s -> s 
          { jesExprNodeMap =  mapInsertKeys exprClass n (jesExprNodeMap s)
          , jesExprValueMap = mapInsertKeys exprClass (JSS.RValue ref) (jesExprValueMap s)
          , jesRefNameMap = Map.insert ref refName (jesRefNameMap s)
          , jesArrayNodeList = (ref,exprClass,n):(jesArrayNodeList s)
          }
      RIVArrayConst _ _ _ -> error "internal: Illegal RIVArrayConst to runMethodVerification"
      RIVClass cl -> do
        ref <- lift $ JSS.genRef (ClassType (className cl))
        modify $ \s -> s 
          { jesExprValueMap = mapInsertKeys exprClass (JSS.RValue ref) (jesExprValueMap s)
          , jesRefNameMap = Map.insert ref refName (jesRefNameMap s)
          }
      RIVIntArray l ->  createInputArrayNode l 32
      RIVLongArray l -> createInputArrayNode l 64

createJavaEvalScalars :: MethodSpecIR -> JavaEvaluator ()
createJavaEvalScalars ir = do
  let liftAig = lift . JSS.liftSymbolic . liftAigMonad
      liftSym = lift . JSS.liftSymbolic
  -- Create symbolic inputs from specScalarInputs.
  forM_ (specScalarInputs ir) $ \expr -> do
    litCount <- liftAig $ getInputLitCount
    let addScalarNode node inputEval value = 
          modify $ \s ->
            s { jesExprNodeMap = Map.insert expr node (jesExprNodeMap s)
              , jesInputEvaluators = (expr,inputEval) : jesInputEvaluators s
              , jesExprValueMap = Map.insert expr value (jesExprValueMap s) }
    case getJSSTypeOfSpecRef expr of
      JSS.BooleanType -> 
        --TODO: Figure out what to do.
        error "internal: Boolean not supported until value problem figured out."
      JSS.IntType -> do
        lv <- liftAig $ SV.replicateM 32 makeInputLit
        n <- liftSym $ freshVar (SymInt (constantWidth 32)) (LV lv)
        let inputEval lits = mkCIntFromLsbfV $ SV.slice litCount 32 lits
        addScalarNode n inputEval (JSS.IValue n)
      JSS.LongType -> do
        lv <- liftAig $ SV.replicateM 64 makeInputLit
        n <- liftSym $ freshVar (SymInt (constantWidth 64)) (LV lv)
        let inputEval lits = mkCIntFromLsbfV $ SV.slice litCount 64 lits
        addScalarNode n inputEval (JSS.LValue n)
      _ -> error "internal: createSpecSymbolicInputs Illegal spectype."

-- | Create an evaluator state with the initial JVM state form the IR and
-- equivalence class map.
createJavaEvalState :: MethodSpecIR
                    -> EquivClassMap
                    -> JSS.Simulator SymbolicMonad JavaEvalState
createJavaEvalState ir cm = do
  let clName = slashesToDots $ JSS.className $ methodSpecIRClass ir
      initialEvalState = JES
        { jesClassName = clName
        , jesMethodName = clName ++ "." ++ JSS.methodName (methodSpecIRMethod ir)
        , jesExprNodeMap = Map.empty
        , jesInputEvaluators = []
        , jesExprValueMap = Map.empty
        , jesRefNameMap = Map.empty
        , jesArrayNodeList = []
        , jesLetNodeBindings = Map.empty
        }
  flip execStateT initialEvalState $ do
    createJavaEvalReferences cm
    createJavaEvalScalars ir
    -- createMethodLetBindings
    forM_ (methodLetBindings ir) $ \(name,expr) -> do
      jes <- get
      n <- lift $ JSS.liftSymbolic $ evalTypedExpr jes expr
      modify $ \s -> s { jesLetNodeBindings = Map.insert name n (jesLetNodeBindings s) }

-- Java execution {{{2

addInitializedClasses :: MethodSpecIR -> JSS.Simulator SymbolicMonad ()
addInitializedClasses ir = do
  forM_ (initializedClasses ir) $ \c -> do
    JSS.setInitializationStatus c JSS.Initialized

-- | Update initial instance field values.
setInstanceFields :: MethodSpecIR 
                  -> JavaEvalState
                  -> JSS.Simulator SymbolicMonad ()
setInstanceFields ir jem = do
  forM_ (initialInstanceFieldValues jem) $ \(_,r,f,v) -> do
    JSS.setInstanceFieldValue r f v

-- Run method and get final path state
runMethod :: MethodSpecIR
          -> JavaEvalState
          -> JSS.Simulator SymbolicMonad ()
runMethod ir jem = do
  let clName = className (methodSpecIRClass ir)
  let method = methodSpecIRMethod ir
  args <- mapM (jesExprValue jem)
        $ map (uncurry SpecArg)
        $ [0..] `zip` methodParameterTypes method
  if methodIsStatic method
    then JSS.invokeStaticMethod clName (methodKey method) args
    else do
      JSS.RValue thisRef <- jesExprValue jem (SpecThis clName)
      JSS.invokeInstanceMethod clName (methodKey method) thisRef args

-- ExpectedStateDef {{{2

-- | Stores expected values in symbolic state after execution.
data ExpectedStateDef = ESD {
       -- | Maps instance fields to expected values.
       esdInstanceFields :: Map (JSS.Ref, JSS.FieldId) (Maybe (JSS.Value Node))
     , esdArrays :: Map JSS.Ref (Maybe Node)
     }

-- | Create a expected state definition from method spec and eval state.
createExpectedStateDef :: MethodSpecIR -> JavaEvalState -> SymbolicMonad ExpectedStateDef 
createExpectedStateDef ir jes = do
  -- Get instance field values.
  instanceFields <- 
    forM (initialInstanceFieldValues jes) $ \(expr,r,fid,v) -> do
      expValue <- 
        case Map.lookup expr (scalarPostconditions ir) of
          -- Non-modifiable case.
          Nothing -> return (Just v)
          Just PostUnchanged -> return (Just v) -- Unchanged
          Just PostArbitrary -> return Nothing -- arbitrary case
          Just (PostResult expr) -> do
            case v of
              -- Use value for scalars
              JSS.IValue _ -> fmap (Just . JSS.IValue) $ evalTypedExpr jes expr
              JSS.LValue _ -> fmap (Just . JSS.LValue) $ evalTypedExpr jes expr
              _ -> error "internal: scalarPostcondition assigned to a illegal expression"
      return ((r,fid),expValue)
  -- Get array values.
  arrays <-
    forM (jesArrayNodeList jes) $ \(r,refEquivClass,initValue) -> do
      let Just exprPost = Map.lookup refEquivClass (arrayPostconditions ir)
      expValue <-
        case exprPost of
          PostUnchanged -> return (Just initValue)
          PostArbitrary -> return Nothing
          PostResult expr -> fmap Just $ evalTypedExpr jes expr
      return (r,expValue)
  -- Return expected state definition.
  return $ ESD { esdInstanceFields = Map.fromList instanceFields
               , esdArrays = Map.fromList arrays 
               }

-- VerificationConditions {{{2

-- | Difference between spec and JVM states.
data JVMDiff
  -- | A value whose spec value difers from simulator value.
  = DV String -- ^ Name of value with divergent value.
       CValue -- ^ Value in spec
       CValue -- ^ Value from JVM bytecode.

type CounterFn = SymbolicEvalMonad SymbolicMonad (Maybe JVMDiff)

-- | Conditions generated from comparing expected and resulting states.
data VerificationConditionSet = VCS {
         vcsAssumptions :: Node
       , vcsGoal :: Node
       , vcsCounterFns :: [CounterFn]
       }

emptyVCSet :: MethodSpecIR -> JavaEvalState -> SymbolicMonad VerificationConditionSet
emptyVCSet ir jes = do
  nodes <- mapM (evalTypedExpr jes) (assumptions ir)
  n <- foldM applyBAnd (mkCBool True) nodes
  return VCS { vcsAssumptions = n
             , vcsGoal = mkCBool True
             , vcsCounterFns = []
             }

-- | Add verification condition to list.
addEqVC :: String -> Node -> Node -> StateT VerificationConditionSet SymbolicMonad ()
addEqVC name jvmNode specNode = do
  oldGoal <- gets vcsGoal
  newGoal <- lift $ applyBAnd oldGoal =<< applyEq jvmNode specNode
  let fn = do
        jvmVal <- evalNode jvmNode
        specVal <- evalNode specNode
        if jvmVal == specVal
          then return Nothing
          else return $ Just (DV name specVal jvmVal)
  modify $ \s -> s { vcsGoal = newGoal
                   , vcsCounterFns = fn : vcsCounterFns s}

-- | Return final goal from verification conditions with assumptions and result.
finalGoal :: VerificationConditionSet -> SymbolicMonad Node
finalGoal vcs = do
  negA <- applyBNot (vcsAssumptions vcs)
  applyBOr negA (vcsGoal vcs)

-- | Compare old and 
comparePathStates :: MethodSpecIR 
                  -> JavaEvalState
                  -> JSS.PathState Node
                  -> ExpectedStateDef
                  -> JSS.PathState Node
                  -> SymbolicMonad VerificationConditionSet
comparePathStates ir jes oldPathState ssd newPathState = do
  let pos = methodSpecPos ir
  let clName = jesClassName jes
  let mName = jesMethodName jes
  initialVCS <- emptyVCSet ir jes
  flip execStateT initialVCS $ do
    -- Check initialization
    do let specInits = Set.fromList (initializedClasses ir)
           jvmInits  = Set.fromList $ Map.keys $ JSS.initialization newPathState
           newInits = jvmInits `Set.difference` specInits
       unless (Set.null newInits) $ do
         let msg = "The JVM method \'" ++ mName ++ "\' initializes extra classes "
                    ++ "during execution.  This feature is not currently suported "
                    ++ "by JavaVerifier.  The extra classes are:"
             newInitNames = nest 2 (vcat (map (text . slashesToDots) (Set.toList newInits)))
         throwIOExecException pos (ftext msg $$ newInitNames) ""
    -- Check class objects
    do let specClassObjects = Set.fromList $ Map.keys $ JSS.classObjects oldPathState
       let jvmClassObjects = Set.fromList $ Map.keys $ JSS.classObjects newPathState
       let newClassObjects = jvmClassObjects `Set.difference` specClassObjects
       unless (Set.null newClassObjects) $ do
         let msg = "The JVM method \'" ++ mName ++ "\' referenced class objects "
                    ++ "during execution.  This feature is not currently suported "
                    ++ "by JavaVerifier.  The extra class objects are:"
             newNames = nest 2 
                      $ vcat (map (text . slashesToDots) (Set.toList newClassObjects))
         throwIOExecException pos (ftext msg $$ newNames) ""
    -- Check static fields
    do let specStaticFields = JSS.staticFields oldPathState
       forM_ (Map.toList $ JSS.staticFields newPathState) $ \(fid,jvmVal) -> do
         let clName = slashesToDots (fieldIdClass fid)
         let fName = clName ++ "." ++ fieldIdName fid
         let throwModificationError =
               let msg = "The JVM method \'" ++ mName ++ "\' has modified the "
                        ++ " static field " ++ fName ++ " during execution.  "
                        ++ "This feature is not currently suported by JavaVerifier."
                in throwIOExecException pos (ftext msg) ""
         case Map.lookup fid specStaticFields of
           Nothing -> throwModificationError
           Just specVal -> 
             unless (specVal == jvmVal) throwModificationError
    -- Check instance fields
    forM_ (Map.toList $ JSS.instanceFields newPathState) $ \(fieldRef@(ref,fid),jvmVal) -> do
      refName <- getRefName pos ref jes
      let fieldName = refName ++ "." ++ fieldIdName fid
      specVal <- 
        case Map.lookup fieldRef (esdInstanceFields ssd) of
          Nothing -> do
            let msg = "The JVM method \'" ++ mName ++ "\' has written to the "
                       ++ "instance field \'" ++ fieldName
                       ++ "\' which was not defined in the specification."
                res = "Please ensure all relevant fields are defined in the specification."
             in throwIOExecException pos (ftext msg) res
          Just v -> return v
      let throwIfModificationUnsupported fieldType =
            let msg = "The JVM method \'" ++ mName ++ "\' has modified a "
                       ++ fieldType ++ " instance field \'" ++ fieldName
                       ++ "\'.  JavaVerifier does not currently support "
                       ++ "modifications to this type of field."
             in throwIOExecException pos (ftext msg) ""
      case (jvmVal,specVal) of
        (_,Nothing) -> return ()
        (jv, Just sv) | jv == sv -> return ()
        (_, Just (JSS.DValue _)) -> throwIfModificationUnsupported "floating point"
        (_, Just (JSS.FValue _)) -> throwIfModificationUnsupported "floating point"
        (_, Just (JSS.RValue _)) -> throwIfModificationUnsupported "reference"
        (JSS.IValue jvmNode, Just (JSS.IValue specNode)) ->
          addEqVC fieldName jvmNode specNode
        (JSS.LValue jvmNode, Just (JSS.LValue specNode)) ->
          addEqVC fieldName jvmNode specNode
        (_, Just _) -> error "internal: comparePathStates encountered illegal field type."
    -- Check ref arrays
    do let specRefArrays = JSS.refArrays oldPathState
       let jvmRefArrays = JSS.refArrays newPathState
       unless (specRefArrays == jvmRefArrays) $ do
         let msg = "The JVM method \'" ++ mName ++ "\' has modified reference arrays "
                    ++ "during execution.  This feature is not currently suported "
                    ++ "by JavaVerifier."
         throwIOExecException pos (ftext msg) ""
    -- Get array equations and counterexample parse functions
    forM_ (Map.toList (JSS.arrays newPathState)) $ \(ref,(_,jvmNode)) -> do
      refName <- getRefName pos ref jes
      case Map.lookup ref (esdArrays ssd) of
        Nothing -> error "internal: Unexpected undefined array reference."
        Just Nothing -> return ()
        Just (Just specNode) ->
          addEqVC refName jvmNode specNode
   
-- | Attempt to verify method spec using verification method specified.
verifyMethodSpec :: MethodSpecIR -> Executor ()
verifyMethodSpec MSIR { verificationMethod = AST.Skip } = return ()
verifyMethodSpec ir = do
  cb <- gets codebase
  let refEquivClasses = JSS.partitions (specReferences ir)
  lift $ forM_ ([1::Integer ..] `zip` refEquivClasses) $ \(i,cm) -> do
    runSymSession $ do
      -- Generate input vectors.
      -- Run simulator 
      vcs <- 
        JSS.runSimulator cb $ do
          -- Create map from specification entries to JSS simulator values.
          jes <- createJavaEvalState ir cm
          -- TODO: Add method spec overrides.
          addInitializedClasses ir
          setInstanceFields ir jes
          -- Get old path state
          oldPathState <- JSS.getPathState
          -- Execute method.
          runMethod ir jes
          -- TODO: Build final equation and functions for generating counterexamples.
          newPathState <- JSS.getPathState
          JSS.liftSymbolic $ do
            ssd <- createExpectedStateDef ir jes
            -- Create verification conditions from path states.
            comparePathStates ir jes oldPathState ssd newPathState
      case verificationMethod ir of
        AST.ABC -> do
          {-
          whenVerbosity (>=2) $
             dbugM $ "Starting checkSat"
          -- Check final result.
          LV v <- getVarLit bFinalEq
          when (LV.length v /= 1) $
            error "internal: Unexpected number of in verification condition"
          b <- liftAigMonad $ checkSat (neg (v `LV.unsafeIndex` 0))
          case b of
            UnSat -> return ()
            Unknown -> error "Checking assumptions failed"
            Sat lits -> do
              let inputValues = V.map ($lits) litParseFns
              --evalAndBlast inputValues lits
              --liftIO $ putStrLn "EvalAndBlast succeeded"
              counters <- symbolicEval inputValues counterFn
              let inputMap = Map.fromList
                           $ V.toList
                           $ V.map (\(d,i) -> (d,inputValues V.! i))
                           $ defInputVec
              assert (not (null counters)) $
                liftIO $ throwIO
                       $ CounterExample classDefVec inputMap counters
-}
          error "TODO: AST.ABC"
        AST.Rewrite -> error "TODO: AST.Rewrite"
        AST.Auto -> error "TODO: AST.Auto"
        AST.Skip -> error "internal: Unexpected skip"
      
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
  execDebugLog $ "Parsing SBV type for " ++ nm
  let SBV.SBVPgm (_ver, sbvExprType, _cmds, _vc, _warn, sbvUninterpFns) = sbv
  idRecordsInIRType pos relativePath Nothing sbvExprType
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) ->
    idRecordsInIRType pos relativePath (Just name) irType
  -- Define recordDefFn
  execDebugLog $ "Defining recordDefFn for " ++ nm
  recordFn <- lift $ getRecordDefMap
  -- Check that op type matches expected type.
  execDebugLog $ "Checking expected type matches inferred type for " ++ nm
  fnType <- parseFnType astFnType
  unless (fnType == SBV.inferFunctionType recordFn sbvExprType) $ 
    let msg = (ftext "The type of the function in the imported SBV file"
                 $$ relativePath
                 $$ ftext "differs from the type provided to the extern command.")
        res = "Please check that the function exported from Cryptol via SBV "
               ++ "matches the type in the SAWScript file."
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
  valueExpr <- do
    config <- globalParserConfig Map.empty
    lift $ tcExpr config astExpr
  val <- globalEval valueExpr
  let tp = getTypeOfTypedExpr valueExpr
  modify $ \s -> s { definedNames = Map.insert name pos (definedNames s)
                   , globalLetBindings = Map.insert name (val, tp) (globalLetBindings s) }
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
  methodIR <- resolveMethodSpecIR pos thisClass method cmds 
  v <- gets runVerification
  when v $ verifyMethodSpec methodIR
  --TODO: Add methodIR to state for later verification.
execute (AST.Rule pos name params astLhsExpr astRhsExpr) = do
  execDebugLog $ "Start defining rule " ++ name
  checkNameIsUndefined pos name
  globalConfig <- globalParserConfig Map.empty
  -- | Get map from variable names to typed expressions.
  nameTypeMap <- lift $ fmap snd $ flip runStateT Map.empty $ do
    forM_ params $ \(pos, name, astType) -> do
      m <- get
      case Map.lookup name m of
        Just _ ->
          let msg = "Rule contains multiple declarations of the variable \'" 
                     ++ name ++ "\'."
           in throwIOExecException pos (ftext msg) ""
        Nothing -> do
          tp <- lift $ tcType globalConfig astType
          modify $ Map.insert name (TypedVar name tp)
  config <- globalParserConfig nameTypeMap
  lhsExpr <- lift $ tcExpr config astLhsExpr
  rhsExpr <- lift $ tcExpr config astRhsExpr
  -- TODO: Parse lhsExpr and rhsExpr and add rule.
  liftIO $ putStrLn "TODO: Support executing AST.Rule"
  execDebugLog $ "Finished defining rule " ++ name
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
        , runVerification = True
        , parsedFiles = files
        , sbvOpMap     = Map.empty
        , definedNames = Map.empty
        , sawOpMap     = Map.fromList [ ("read", getArrayValueOpDef)
                                      , ("write", setArrayValueOpDef)]
        , rules        = Map.empty
        , enabledRules = Set.empty
        , globalLetBindings = Map.empty
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
