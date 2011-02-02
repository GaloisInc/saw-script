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

-- Executor primitives {{{1

data ExecutorState = ES {
    -- | Java codebase
    codebase :: JSS.Codebase 
    -- | Flag used to control how much logging to print out.
  , verbosity :: Int
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

-- | Typecheck expression at global level.
typecheckGlobalExpr :: AST.Expr -> Executor TypedExpr
typecheckGlobalExpr astExpr = do
  globalCnsBindings <- gets globalLetBindings
  opBindings <- gets sawOpMap
  let globalParserConfig =
       TCC { localBindings = Map.empty 
           , globalCnsBindings
           , opBindings }
  lift $ tcExpr globalParserConfig astExpr

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

-- Java lookup functions {{{2

-- | Atempt to find class with given name, or throw ExecException if no class
-- with that name exists.
lookupClass :: Pos -> String -> Executor JSS.Class
lookupClass pos nm = do 
  maybeCl <- JSS.tryLookupClass nm
  case maybeCl of
    Nothing -> do
     let msg = ftext ("The Java class " ++ slashesToDots nm ++ " could not be found.")
         res = "Please check that the --classpath and --jars options are set correctly."
      in throwIOExecException pos msg res
    Just cl -> return cl

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findMethod :: Pos -> String -> JSS.Class -> Executor JSS.Method
findMethod pos nm initClass = do
  let javaClassName = slashesToDots (className initClass)
  let methodMatches m = methodName m == nm && not (JSS.methodIsAbstract m)
  let impl cl = 
        case filter methodMatches (classMethods cl) of
          [] -> do
            case superClass cl of
              Nothing ->
                let msg = ftext $ "Could not find method " ++ nm
                            ++ " in class " ++ javaClassName ++ "."
                    res = "Please check that the class and method are correct."
                 in throwIOExecException pos msg res
              Just superName -> 
                impl =<< lookupClass pos superName
          [method] -> return method
          _ -> let msg = "The method " ++ nm ++ " in class " ++ javaClassName
                           ++ " is ambiguous.  SAWScript currently requires that "
                           ++ "method names are unique."
                   res = "Please rename the Java method so that it is unique."
                in throwIOExecException pos (ftext msg) res
  impl initClass

-- | Returns method with given name in this class or one of its subclasses.
-- Throws an ExecException if method could not be found or is ambiguous.
findField :: Pos -> String -> JSS.Class -> Executor JSS.Field
findField pos nm initClass = do
  let impl cl = 
        case filter (\f -> fieldName f == nm) $ classFields cl of
          [] -> do
            case superClass cl of
              Nothing ->
                let msg = "Could not find a field named " ++ nm ++ " in " 
                            ++ slashesToDots (className initClass) ++ "."
                    res = "Please check to make sure the field name is correct."
                 in throwIOExecException pos (ftext msg) res
              Just superName -> impl =<< lookupClass pos superName
          [f] -> do
            return f
          _ -> error "internal: Found multiple fields with the same name."
  impl initClass 

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
parseFnType :: AST.FnType -> OpSession ([DagType], DagType)
parseFnType (AST.FnType args res) = do
  parsedArgs <- V.mapM parseExprType (V.fromList args)
  parsedRes <- parseExprType res
  return (V.toList parsedArgs, parsedRes)

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
getRecordDefMap :: Executor SBV.RecordDefMap
getRecordDefMap = do
  curRecDefs <- lift $ listStructuralRecords
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

-- SpecJavaRefType {{{1

-- | A parsed type from AST.JavaType
data SpecJavaRefType
  = SpecRefClass !(JSS.Class) -- ^ Specific class for a reference.
  | SpecIntArray !Int32
  | SpecLongArray !Int32
  | SpecRefConstant !TypedExpr

instance Eq SpecJavaRefType where
  SpecRefClass c1 == SpecRefClass c2 = className c1 == className c2
  SpecIntArray l1 == SpecIntArray l2 = l1 == l2
  SpecLongArray l1 == SpecLongArray l2 = l1 == l2
  _ == _ = False

-- | Returns JSS Type of SpecJavaRefType
getJSSTypeOfSpecRefType :: SpecJavaRefType -- ^ Spec Java reference to get type of.
                        -> JSS.Type -- ^ Java type
getJSSTypeOfSpecRefType (SpecRefClass cl) = JSS.ClassType (className cl)
getJSSTypeOfSpecRefType (SpecIntArray _) = JSS.ArrayType JSS.IntType
getJSSTypeOfSpecRefType (SpecLongArray _) = JSS.ArrayType JSS.LongType

-- | Pretty print SpecJavaRefType
ppSpecJavaRefType :: SpecJavaRefType -> String
ppSpecJavaRefType (SpecRefClass cl) = className cl
ppSpecJavaRefType (SpecIntArray l)  = "int[" ++ show l ++ "]"
ppSpecJavaRefType (SpecLongArray l) = "long[" ++ show l ++ "]"

-- | Converts an int into a Java array length.
checkedGetArrayLength :: Pos -> Int -> Executor Int32
checkedGetArrayLength pos l = do
  unless (0 <= l && toInteger l < toInteger (maxBound :: Int32)) $
    let msg  = "Array length " ++ show l ++ " is invalid."
     in throwIOExecException pos (ftext msg) ""
  return $ fromIntegral l

-- | Parse AST Type to SpecJavaRefType.
parseASTType :: AST.JavaType -> Executor SpecJavaRefType
parseASTType (AST.RefType pos names) = do
  let nm = intercalate "." names
  fmap SpecRefClass $ lookupClass pos nm
parseASTType (AST.IntArray pos l) =
  fmap SpecIntArray $ checkedGetArrayLength pos l
parseASTType (AST.LongArray pos l) =
  fmap SpecLongArray $ checkedGetArrayLength pos l

-- MethodSpecTranslator {{{1

-- | Method spec translator state
data MethodSpecTranslatorState = MSTS {
          -- | Class we are currently parsing.
          specClass :: JSS.Class
        , specMethodIsStatic :: Bool
        , specMethodParams :: V.Vector JSS.Type
          -- | Maps Java expressions referenced in type and const expressions
          -- to their associated type.
        , refTypeMap :: Map SpecJavaRef SpecJavaRefType
        -- | Set of Java refs in a mayAlias relation.
        , mayAliasRefs :: Map SpecJavaRef Int
        -- | Number of equivalence class
        , mayAliasClassCount :: Int
        -- | List of mayAlias classes in reverse order that they were created.
        , revAliasSets :: [([SpecJavaRef], SpecJavaRefType)]
        -- | Let bindings local to expression.
        , methodLetBindings :: Map String (Pos,TypedExpr)
        -- | Lift of assumptions parsed so far in reverse order.
        , assumptions :: [TypedExpr]
        -- | Map from Java expressions to typed expression in ensures clause.
        -- or nothing if this is bound.
        , refEnsures :: Map SpecJavaRef (Pos,Maybe TypedExpr)
        , verificationMethod :: Maybe (Pos, AST.VerificationMethod)
        }

type MethodSpecTranslator = StateT MethodSpecTranslatorState Executor

throwUnsupportedIntType :: Pos -> JSS.Type -> Executor ()
throwUnsupportedIntType pos tp =
  let msg = "SAWScript only supports integer and long integral values, and does"
            ++ "not yet support " ++ show tp ++ "."
      res = "Please modify the Java code to only use \'int\' instead."
   in throwIOExecException pos (ftext msg) res

throwUnsupportedFloatType :: Pos -> Executor ()
throwUnsupportedFloatType pos =
  let msg = "SAWScript does not yet support \'float\' or \'double\'."
      res = "Please modify the Java code to not use floating point types."
   in throwIOExecException pos (ftext msg) res

-- | Check JSS Type is a type supported by SAWScript.
checkJSSTypeIsValid :: Pos -> Bool -> JSS.Type -> Executor ()
checkJSSTypeIsValid _ _ (ArrayType IntType) = return ()
checkJSSTypeIsValid _ _ (ArrayType LongType) = return ()
checkJSSTypeIsValid pos _ (ArrayType eltType) = 
  let msg = "SAWScript currently only supports arrays of int and long, "
            ++ "and does yet support arrays with type " ++ show eltType ++ "."
      res = "Please modify the Java code to only use int or long array types."
   in throwIOExecException pos (ftext msg) res
checkJSSTypeIsValid pos _ (ClassType nm) = lookupClass pos nm >> return ()

checkJSSTypeIsValid _ False BooleanType = return ()
checkJSSTypeIsValid pos False JSS.ByteType = throwUnsupportedIntType pos JSS.ByteType
checkJSSTypeIsValid pos False JSS.CharType = throwUnsupportedIntType pos JSS.CharType
checkJSSTypeIsValid pos False JSS.ShortType = throwUnsupportedIntType pos JSS.ShortType
checkJSSTypeIsValid _ False IntType = return ()
checkJSSTypeIsValid _ False LongType = return ()
checkJSSTypeIsValid pos False DoubleType = throwUnsupportedFloatType pos
checkJSSTypeIsValid pos False FloatType = throwUnsupportedFloatType pos
checkJSSTypeIsValid pos True tp =
  let msg = "SAWScript only requires reference types to be annotated "
            ++ "with type information, and currently only supports "
            ++ "methods with array and reference values as arguments.  "
            ++ "The type " ++ show tp ++ " is not a reference type."
      res = "Please modify the Java code to only use int or long array "
            ++ "types."
   in throwIOExecException pos (ftext msg) res

-- | Get type assigned to SpecJavaRef, or throw exception if it is not assigned.
lookupRefType :: Pos -> SpecJavaRef -> MethodSpecTranslator SpecJavaRefType
lookupRefType pos ref = do
  m <- gets refTypeMap
  case Map.lookup ref m of
    Just tp -> return tp
    Nothing -> 
      let msg = "The type of " ++ ppSpecJavaRef ref ++ "must be specified "
                  ++ "before referring to it or one of its fields."
          res = "Please add a type annotation of the reference before this refence."
       in throwIOExecException pos (ftext msg) res

-- | Typecheck an AST Java expression to get specification Java expression.
-- This code will check that the result is a reference if the first Bool is
-- true.
-- Flag indicates if a reference is required.
tcASTJavaExpr :: Bool -> AST.JavaRef -> MethodSpecTranslator SpecJavaRef
tcASTJavaExpr _ (AST.This pos) = do
  isStatic <- gets specMethodIsStatic
  when isStatic $
    throwIOExecException pos (ftext "\'this\' is not defined on static methods.") ""
  return SpecThis
tcASTJavaExpr refReq (AST.Arg pos i) = do
  params <- gets specMethodParams
  -- Check that arg index is valid.
  unless (0 <= i && i < V.length params) $
    throwIOExecException pos (ftext "Invalid argument index for method.") ""
  lift $ checkJSSTypeIsValid pos refReq (params V.! i)
  return $ SpecArg i
tcASTJavaExpr refReq (AST.InstanceField pos astLhs fName) = do
  lhs <- tcASTJavaExpr True astLhs
  tp <- lookupRefType pos lhs
  case tp of
    SpecRefClass cl -> lift $ do
      f <- findField pos fName cl
      checkJSSTypeIsValid pos refReq (fieldType f)
      return $ SpecField lhs f
    _ -> let msg = "Could not find a field named " ++ fName ++ " in " 
                     ++ ppSpecJavaRef lhs ++ "."
             res = "Please check to make sure the field name is correct."
          in throwIOExecException pos (ftext msg) res

-- | Check that the reference type is undefined.
checkRefTypeIsUndefined :: Pos -> SpecJavaRef -> MethodSpecTranslator ()
checkRefTypeIsUndefined pos ref = do
  m <- gets refTypeMap 
  when (Map.member ref m) $
    let msg = "The type of " ++ ppSpecJavaRef ref ++ " is already defined."
     in throwIOExecException pos (ftext msg) ""

-- | Check that the reference type is undefined.
checkRefTypeIsDefined :: Pos -> SpecJavaRef -> MethodSpecTranslator ()
checkRefTypeIsDefined pos ref = do
  m <- gets refTypeMap 
  unless (Map.member ref m) $
    let msg = "The type of " ++ ppSpecJavaRef ref ++ " has not been defined."
        res = "Please add a \'type\' declaration to indicate the concrete type of the reference."
     in throwIOExecException pos (ftext msg) res

-- | Throw io exception indicating that a reference type is incompatible with
-- an expression type.
throwIncompatibleRefType :: MonadIO m => Pos -> SpecJavaRef -> JSS.Type -> String -> m ()
throwIncompatibleRefType pos ref refType specTypeName =
  let msg = "The type of " ++ ppSpecJavaRef ref ++ " is " ++ show refType
             ++ ", which is incompatible with the specification type "
             ++ specTypeName ++ "."
   in throwIOExecException pos (ftext msg) ""

-- | Typecheck expression at global level.
typecheckMethodExpr :: AST.Expr -> MethodSpecTranslator TypedExpr
typecheckMethodExpr astExpr = do
  locals <- gets methodLetBindings 
  lift $ do
    globalCnsBindings <- gets globalLetBindings
    opBindings <- gets sawOpMap
    let tcc = TCC { localBindings = Map.map snd locals
                  , globalCnsBindings
                  , opBindings }
    lift $ tcExpr tcc astExpr

-- Check that the Java spec reference has a type compatible with typedExpr.
checkSpecJavaExprCompat :: Pos -> SpecJavaRef -> TypedExpr -> MethodSpecTranslator ()
checkSpecJavaExprCompat pos ref expr = do
  clName <- fmap className $ gets specClass
  params <- gets specMethodParams
  let refType = getJSSTypeOfSpecRef clName params ref
  case (refType, getTypeOfTypedExpr expr) of
    (BooleanType, SymBool) -> return ()
    (IntType, SymInt (widthConstant -> Just 32)) -> return ()
    (LongType, SymInt (widthConstant -> Just 64)) -> return ()
    (  ArrayType IntType
     , SymArray (widthConstant -> Just _) (SymInt (widthConstant -> Just 32))) ->
       return ()
    (  ArrayType LongType
     , SymArray (widthConstant -> Just _) (SymInt (widthConstant -> Just 64))) ->
       return ()
    --TODO: Add additional cases as needed.
    (_,specType) -> throwIncompatibleRefType pos ref refType (ppType specType)

-- | Check that no 'ensures' or 'arbitrary' statement has been added for the
-- given reference is undefined.
checkEnsuresUndefined :: Pos -> SpecJavaRef -> MethodSpecTranslator ()
checkEnsuresUndefined pos ref = do
  m <- gets refEnsures
  case Map.lookup ref m of
    Nothing -> return ()
    Just (absPrevPos,_) -> do
      relPos <- liftIO $ posRelativeToCurrentDirectory absPrevPos
      let msg = "An ensures or arbitrary statement has already been added for " 
                  ++ ppSpecJavaRef ref ++ " at " ++ show relPos ++ "."
          res = "Please remove the conflicting statement."
       in throwIOExecException pos (ftext msg) res

-- | Code for parsing a method spec declaration.
tcDecl :: AST.MethodSpecDecl -> MethodSpecTranslator ()
tcDecl (AST.Type pos astRefs astTp) = do
  clName <- fmap className $ gets specClass
  params <- gets specMethodParams
  specType <- lift $ parseASTType astTp
  forM_ astRefs $ \astRef -> do
    ref <- tcASTJavaExpr True astRef
    -- Check type has not already been assigned.
    checkRefTypeIsUndefined pos ref
    -- Check that type of ref and the type of tp are compatible.
    do let refType = getJSSTypeOfSpecRef clName params ref
           tgtType = getJSSTypeOfSpecRefType specType
       b <- lift $ JSS.isSubtype tgtType refType
       unless b $ throwIncompatibleRefType pos ref refType (ppSpecJavaRefType specType)
    -- Add ref to refTypeMap.
    modify $ \s -> 
      s { refTypeMap = Map.insert ref specType (refTypeMap s) 
        }
tcDecl (AST.MayAlias _ []) = error "internal: mayAlias set is empty"
tcDecl (AST.MayAlias pos astRefs) = do
  refs@(firstRef:restRefs) <- mapM (tcASTJavaExpr True) astRefs
   -- Check types of references are the same. are the same.
  firstType <- lookupRefType pos firstRef 
  forM_ restRefs $ \r -> do
    restType <- lookupRefType pos r
    unless (firstType  == restType) $
      let msg = "The type assigned to " ++ ppSpecJavaRef r 
                  ++ " differs from the type assigned "
                  ++ ppSpecJavaRef r ++ "."
          res = "All references that may alias must be assigned the same type."
       in throwIOExecException pos (ftext msg) res
  -- Check refs have not already appeared in a mayAlias set.
  do s <- gets mayAliasRefs
     forM_ refs $ \ref -> 
       when (Map.member ref s) $ do
         let msg = ppSpecJavaRef ref ++ "was previously mentioned in a mayAlias"
                   ++ " declaration."
             res = "Please merge mayAlias declarations as needed so that each "
                   ++ "reference is mentioned at most once."
         throwIOExecException pos (ftext msg) res
  -- Add mayAlias to state.
  modify $ \s -> 
    let cnt = mayAliasClassCount s
     in s { mayAliasRefs = foldr (flip Map.insert cnt)  (mayAliasRefs s) refs
          , mayAliasClassCount = cnt + 1
          , revAliasSets = (refs,firstType) : revAliasSets s }
tcDecl (AST.Const pos astRef astExpr) = do
  -- Parse ref and check type is undefined.
  ref <- tcASTJavaExpr True astRef
  checkRefTypeIsUndefined pos ref
  -- Parse expression.
  expr <- typecheckMethodExpr astExpr
  -- Check ref and expr have compatible types.
  checkSpecJavaExprCompat pos ref expr
  -- Add ref to refTypeMap
  modify $ \s ->
    s { refTypeMap = Map.insert ref (SpecRefConstant expr) (refTypeMap s) }
tcDecl (AST.MethodLet pos name astExpr) = do
  -- Check var is not already bound.
  do lift $ checkNameIsUndefined pos name
     locals <- gets methodLetBindings
     case Map.lookup name locals of
       Nothing -> return ()
       Just (prevPos,_) -> throwNameAlreadyDefined pos prevPos name
  expr <- typecheckMethodExpr astExpr
  -- Add binding to methodLetBindings
  modify $ \s ->
    s { methodLetBindings = Map.insert name (pos,expr) (methodLetBindings s) }
tcDecl (AST.Assume _pos astExpr) = do
  expr <- typecheckMethodExpr astExpr
  modify $ \s -> s { assumptions = expr : assumptions s }
tcDecl (AST.Ensures pos astRef astExpr) = do
  -- Parse ref and check type is defined.
  ref <- tcASTJavaExpr False astRef
  checkRefTypeIsDefined pos ref
  -- Check ensures value is not defined for ref.
  checkEnsuresUndefined pos ref
  -- Parse expression.
  expr <- typecheckMethodExpr astExpr
  -- Check ref and expr have compatible types.
  checkSpecJavaExprCompat pos ref expr
  -- Add ref to ensures map.
  modify $ \s -> s { refEnsures = Map.insert ref (pos, Just expr) (refEnsures s) }
tcDecl (AST.Arbitrary pos astRefs) = do 
  clName <- fmap className $ gets specClass
  params <- gets specMethodParams
  forM_  astRefs $ \astRef -> do
    ref <- tcASTJavaExpr False astRef
    case getJSSTypeOfSpecRef clName params ref of
      JSS.ClassType _ ->
        let msg = "'arbitrary' command given a reference value " ++ ppSpecJavaRef ref
                  ++ "SAWScript currently requires references are unmodified by method calls."
            res = "Please modify the spec and/or Java code so that it does not "
                  ++ "modify a reference value."
         in throwIOExecException pos (ftext msg) res
      _ -> return ()
    checkEnsuresUndefined pos ref
    modify $ \s -> s { refEnsures = Map.insert ref (pos,Nothing) (refEnsures s) }
tcDecl (AST.VerifyUsing pos method) = do
  vm <- gets verificationMethod
  case vm of
   Nothing -> return ()
   Just (_oldPos,_) ->
     let msg = "The verification tactic is set multiple times in the same "
                ++ "method specification."
         res = "Please include at most one verification tactic in a single specification."
      in throwIOExecException pos (ftext msg) res

data ParsedMethodSpec = PMS {
    aliasSets :: [([SpecJavaRef], SpecJavaRefType)]
  }

-- | Returns map from Java references to type.
parseMethodSpecDecls :: JSS.Class
                     -> JSS.Method
                     -> [AST.MethodSpecDecl]
                     -> Executor ParsedMethodSpec
parseMethodSpecDecls cl method cmds = do
  let st = MSTS { specClass = cl
                , specMethodIsStatic = methodIsStatic method
                , specMethodParams = V.fromList (methodParameterTypes method)
                , refTypeMap = Map.singleton SpecThis (SpecRefClass cl)
                , mayAliasRefs = Map.empty
                , mayAliasClassCount = 0
                , revAliasSets = [] 
                , methodLetBindings = Map.empty
                , assumptions = []
                , refEnsures = Map.empty
                , verificationMethod = Nothing
                }
  MSTS { refTypeMap
       , mayAliasRefs
       , revAliasSets 
       } <- fmap snd $ runStateT (mapM_ tcDecl cmds) st
  let unaliasedRefs
        = map (\(r,tp) -> ([r],tp))
        $ filter (\(r,_) -> Map.notMember r mayAliasRefs)
        $ Map.toList refTypeMap
  return PMS { aliasSets = revAliasSets ++ unaliasedRefs }

-- Verifier command execution {{{1 

-- | Throw ExecException if SBVException is thrown.
throwSBVParseError :: MonadIO m => Pos -> Doc -> SBV.SBVException -> m a
throwSBVParseError pos relativePath e =
  let msg = text "An internal error occurred when loading the SBV" 
              <+> relativePath <> colon $$
              text (SBV.ppSBVException e)
      res = "Please reconfirm that the SBV filename is a valid SBV file from Cryptol."
   in throwIOExecException pos msg res
      
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
  idRecordsInIRType pos relativePath Nothing sbvExprType
  forM_ sbvUninterpFns $ \((name, _loc), irType, _) ->
    idRecordsInIRType pos relativePath (Just name) irType
  -- Define recordDefFn
  execDebugLog $ "Defining recordDefFn for " ++ nm
  recordFn <- getRecordDefMap
  -- Check that op type matches expected type.
  execDebugLog $ "Checking expected type matches inferred type for " ++ nm
  fnType <- lift $ parseFnType astFnType
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
-- | Configuration used for parsing global expressions.
  expr <- typecheckGlobalExpr astExpr
  val <- globalEval expr
  let tp = getTypeOfTypedExpr expr
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
  PMS { aliasSets } <- parseMethodSpecDecls thisClass method cmds 
  forM_ (JSS.partitions aliasSets) $ \(cnt, classRefMap, classTypeMap) -> do
    liftIO $ putStrLn $ "Considering equivalence class " ++ show cnt
  error $ "AST.DeclareMethodSpec"
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
  checkNameIsDefined pos name
  modify $ \s -> s { enabledRules = Set.delete name (enabledRules s) }
execute (AST.Enable pos name) = do
  checkNameIsDefined pos name
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
