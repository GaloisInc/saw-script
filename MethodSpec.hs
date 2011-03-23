{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.MethodSpec
  ( MethodSpecIR
  , methodSpecName
  , methodSpecIRMethodClass
  , methodSpecVerificationTactic
  , resolveMethodSpecIR
  , verifyMethodSpec
  ) where

-- Imports {{{1

import qualified Control.Exception as CE
import Control.Monad
import Data.Int
import Data.IORef
import Data.List (foldl', intercalate, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector.Storable as SV
import qualified Data.Vector as V
import Text.PrettyPrint.HughesPJ

import qualified Execution.Codebase as JSS
import JavaParser as JSS
import MethodSpec (partitions)
import qualified SAWScript.MethodAST as AST
import qualified SAWScript.TypeChecker as TC
import qualified Simulation as JSS
import Symbolic
import SAWScript.Utils
import SAWScript.TypeChecker
import Utils.Common
import Utils.IOStateT
import Utils.LogMonad

-- Utilities {{{1

-- | Insert multiple keys that map to the same value in a map.
mapInsertKeys :: Ord k => [k] -> a -> Map k a -> Map k a
mapInsertKeys keys val m = foldr (\i -> Map.insert i val) m keys

-- | Returns the value bound to the first key in the map, or
-- Nothing if none of the keys are in the map.
mapLookupAny :: Ord k => [k] -> Map k a -> Maybe a
mapLookupAny keys m = listToMaybe $ catMaybes $ map (\k -> Map.lookup k m) keys

int32DagType :: DagType
int32DagType = SymInt (constantWidth 32)

int64DagType :: DagType
int64DagType = SymInt (constantWidth 64)

-- | Create a node with given number of bits.
createSymbolicIntNode :: Int -> SymbolicMonad Node
createSymbolicIntNode w = do
  lv <- fmap LV $ liftAigMonad $ SV.replicateM w makeInputLit
  freshVar (SymInt (constantWidth (Wx w))) lv

-- | @createSymbolicArrayNode l w@ creates an array with length l@ and elements with width @w@.
createSymbolicArrayNode :: Int -> Int -> SymbolicMonad Node
createSymbolicArrayNode l w = do
  let arrType = SymArray (constantWidth (Wx l)) (SymInt (constantWidth (Wx w)))
  lv <- liftAigMonad $ V.replicateM l $ fmap LV $ SV.replicateM w makeInputLit
  freshVar arrType (LVN lv)

createLitVectorFromType :: DagType -> AigComputation OpSession (LitResult Lit)
createLitVectorFromType (SymInt (widthConstant -> Just (Wx w))) = do
  fmap LV $ SV.replicateM w makeInputLit
createLitVectorFromType (SymArray (widthConstant -> Just (Wx l)) eltTp) = do
  fmap LVN $ V.replicateM l $ createLitVectorFromType eltTp
createLitVectorFromType _ = error "internal: createLitVectorFromType called with unsupported type."

-- | Create a node with given number of bits.
createSymbolicFromType :: DagType -> SymbolicMonad Node
createSymbolicFromType tp = freshVar tp =<< liftAigMonad (createLitVectorFromType tp)

-- | Throw IO exception indicating name was previously defined.
throwNameAlreadyDefined :: MonadIO m => Pos -> Pos -> String -> m ()
throwNameAlreadyDefined pos absPrevPos name = do
  relPos <- liftIO $ posRelativeToCurrentDirectory absPrevPos
  throwIOExecException pos
                       (ftext "The name " <+> quotes (text name)
                          <+> ftext "has already been defined at "
                          <+> text (show relPos) <> char '.')
                       ("Please ensure all names are distinct.")

-- SpecJavaType {{{1

-- | A parsed type from AST.JavaType
data SpecJavaType
  = SpecRefClass !(JSS.Class) -- ^ Specific class for a reference.
  | SpecIntArray !Int
  | SpecLongArray !Int
  | SpecInt
  | SpecLong

-- | Pretty print SpecJavaType
ppSpecJavaType :: SpecJavaType -> String
ppSpecJavaType (SpecRefClass cl) = className cl
ppSpecJavaType (SpecIntArray l)  = "int[" ++ show l ++ "]"
ppSpecJavaType (SpecLongArray l) = "long[" ++ show l ++ "]"
ppSpecJavaType SpecInt  = "int"
ppSpecJavaType SpecLong = "long"

-- | Returns JSS Type of SpecJavaType
getJSSTypeOfSpecJavaType :: SpecJavaType -- ^ Spec Java reference to get type of.
                        -> JSS.Type -- ^ Java type
getJSSTypeOfSpecJavaType (SpecRefClass cl) = JSS.ClassType (className cl)
getJSSTypeOfSpecJavaType (SpecIntArray _) = JSS.ArrayType JSS.IntType
getJSSTypeOfSpecJavaType (SpecLongArray _) = JSS.ArrayType JSS.LongType
getJSSTypeOfSpecJavaType SpecInt  = JSS.IntType
getJSSTypeOfSpecJavaType SpecLong = JSS.LongType

-- | Converts an int into a Java array length.
checkedGetArrayLength :: MonadIO m => Pos -> Int -> m Int
checkedGetArrayLength pos l = do
  unless (0 <= l && toInteger l < toInteger (maxBound :: Int32)) $
    let msg  = "Array length " ++ show l ++ " is invalid."
     in throwIOExecException pos (ftext msg) ""
  return $ fromIntegral l

-- | Parse AST Type to SpecJavaType.
parseASTType :: JSS.HasCodebase m => AST.JavaType -> m SpecJavaType
parseASTType (AST.RefType pos names) = do
  let nm = intercalate "/" names
  fmap SpecRefClass $ lookupClass pos nm
parseASTType (AST.IntArray pos l) =
  fmap SpecIntArray $ checkedGetArrayLength pos l
parseASTType (AST.LongArray pos l) =
  fmap SpecLongArray $ checkedGetArrayLength pos l
-- Boolean AST expressions are internally treated as 32-bit integers by JVM
parseASTType (AST.BoolScalar  _) = return SpecInt
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
  deriving (Show)

instance Eq SpecJavaRefInitialValue where
  RIVArrayConst tp1 c1 _ == RIVArrayConst tp2 c2 _ = tp1 == tp2 && c1 == c2
  RIVClass c1 == RIVClass c2 = className c1 == className c2
  RIVIntArray l1 == RIVIntArray l2 = l1 == l2
  RIVLongArray l1 == RIVLongArray l2 = l1 == l2
  _ == _ = False

data SpecPostcondition
  = PostUnchanged
  | PostArbitrary DagType
  | PostResult TC.Expr
  deriving (Show)

type SpecJavaRefEquivClass = [TC.JavaExpr]

ppSpecJavaRefEquivClass :: SpecJavaRefEquivClass -> String
ppSpecJavaRefEquivClass [] = error "internal: ppSpecJavaRefEquivClass"
ppSpecJavaRefEquivClass [expr] = show expr
ppSpecJavaRefEquivClass cl = "{ " ++ intercalate ", " (map show (sort cl)) ++ " }"

-- MethodSpecTranslation immediate state {{{2

-- | Method spec translator state
-- N.B. keys in nonRefTypes, refTypeMap and constExprMap are disjoint.
data MethodSpecTranslatorState = MSTS {
         mstsPos :: Pos
       , mstsGlobalBindings :: TC.GlobalBindings
         -- | Class we are currently parsing.
       , specClass :: JSS.Class
       , mstsMethod :: JSS.Method
       -- | List of non-ref types found in type expressions.
       , nonRefTypes :: Set TC.JavaExpr
         -- | Maps Java expressions referenced in type expressions
         -- to their associated type.
       , refTypeMap :: Map TC.JavaExpr SpecJavaRefInitialValue
         -- | Maps Java references to to associated constant expression.
       , constExprMap :: Map TC.JavaExpr (CValue,DagType)
       -- | Maps Java ref expression to associated equivalence class.
       , mayAliasRefs :: Map TC.JavaExpr SpecJavaRefEquivClass
       -- | List of mayAlias classes in reverse order that they were created.
       , revAliasSets :: [(SpecJavaRefEquivClass, SpecJavaRefInitialValue)]
       -- | Map let bindings local to expression.
       , currentLetBindingMap :: Map String (Pos,TC.Expr)
       -- | List of let bindings encountered in reverse order.
       , reversedLetBindings :: [(String, TC.Expr)]
       -- | Lift of assumptions parsed so far in reverse order.
       , currentAssumptions :: [TC.Expr]
       -- | Set of expressions that have had ensures expressions declared.
       , ensuredExprs :: Set TC.JavaExpr
       -- | Map from Java expressions to typed expression in ensures clause.
       -- or nothing if an arbitrary expression for term has been given.
       , scalarEnsures :: Map TC.JavaExpr (Pos,SpecPostcondition)
       -- | Map from Java expressions to typed expression in ensures clause.
       -- or nothing if an arbitrary expression for term has been given.
       , arrayEnsures :: Map TC.JavaExpr (Pos, SpecPostcondition)
       -- | Return value found during resolution.
       , currentReturnValue :: Maybe (Pos, TC.Expr)
       -- Verification method chosen.
       , chosenVerificationMethod :: Maybe (Pos, AST.VerificationMethod)
       }

type MethodSpecTranslator = StateT MethodSpecTranslatorState OpSession

instance JSS.HasCodebase MethodSpecTranslator where
  getCodebase = gets (TC.codeBase . mstsGlobalBindings)

checkJSSTypeIsRef :: MonadIO m => Pos -> JSS.Type -> m ()
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
checkRefIsNotConst :: Pos -> TC.JavaExpr -> String -> MethodSpecTranslator ()
checkRefIsNotConst pos ref note = do
  m <- gets constExprMap
  when (Map.member ref m) $
    let msg = "The Java expression \'" ++ show ref
              ++ "\' was previously used in a const declaration.  "  ++ note
     in throwIOExecException pos (ftext msg) ""

-- | Check that the Java expression type is undefined.
checkTypeIsUndefined :: Pos -> TC.JavaExpr -> String -> MethodSpecTranslator ()
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
checkJavaTypeIsDefined :: Pos -> TC.JavaExpr -> MethodSpecTranslator ()
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

getExprTypeFn :: MethodSpecTranslator (TC.JavaExpr -> Maybe TC.DefinedJavaExprType)
getExprTypeFn = do
  rtm <- gets refTypeMap
  cem <- gets constExprMap
  return $ \e ->
             case Map.lookup e rtm of
               Just (RIVArrayConst _ _ tp) -> Just (TC.DefinedType tp)
               Just (RIVClass cl) -> Just (TC.DefinedClass cl)
               Just (RIVIntArray l) ->
                 let arrayTp = SymArray (constantWidth (Wx l)) (SymInt (constantWidth 32))
                  in Just (TC.DefinedType arrayTp)
               Just (RIVLongArray l) ->
                 let arrayTp = SymArray (constantWidth (Wx l)) (SymInt (constantWidth 64))
                  in Just (TC.DefinedType arrayTp)
               Nothing ->
                 case Map.lookup e cem of
                   Nothing ->
                     case getJSSTypeOfJavaExpr e of
                       IntType -> Just (TC.DefinedType (SymInt (constantWidth 32)))
                       LongType -> Just (TC.DefinedType (SymInt (constantWidth 64)))
                       _ -> Nothing
                   Just (_,tp) -> Just (TC.DefinedType tp)

-- | Typecheck expression at global level.
methodParserConfig :: MethodSpecTranslator TC.TCConfig
methodParserConfig = do
  globalBindings <- gets mstsGlobalBindings
  locals <- gets currentLetBindingMap
  cl <- gets specClass
  m <- gets mstsMethod
  exprTypeFn <- getExprTypeFn
  return TC.TCC { TC.globalBindings
                , TC.methodInfo = Just (m, cl)
                , TC.localBindings = Map.map snd locals
                , TC.toJavaExprType = Just exprTypeFn }

-- | Typecheck expression at global level.
typecheckJavaExpr :: AST.JavaRef -> MethodSpecTranslator TC.JavaExpr
typecheckJavaExpr astExpr = do
  config <- methodParserConfig
  lift $ TC.tcJavaExpr config astExpr

-- | Typecheck expression at global level.
typecheckMethodExpr :: AST.Expr -> MethodSpecTranslator TC.Expr
typecheckMethodExpr astExpr = do
  config <- methodParserConfig
  lift $ TC.tcExpr config astExpr

-- Check that the Java spec reference has a type compatible with typedExpr.
checkJavaExprCompat :: Pos -> String -> JSS.Type -> DagType -> MethodSpecTranslator ()
checkJavaExprCompat pos exprName exprType dagType = do
  case (exprType, dagType) of
    (BooleanType, SymBool) ->
      let msg = "The type of \'" ++ exprName ++ "\' is in the Java \'Boolean\' type "
                 ++ ", which internally to the JVM is treated as a 32-bit integer, and not "
                 ++ " a \'Boolean\' predicate as in traditional mathematics."
          res = "Please modify the expression to denote a 32-bit integer."
       in throwIOExecException pos (ftext msg) res
    (BooleanType, _) | dagType == int32DagType -> return ()
    (IntType, _) | dagType == int32DagType -> return ()
    (LongType, _) | dagType == int64DagType -> return ()
    (ArrayType IntType, SymArray (widthConstant -> Just _) eltTp)
      | eltTp == int32DagType -> return ()
    (ArrayType LongType, SymArray (widthConstant -> Just _) eltTp)
      | eltTp == int64DagType -> return ()
    (_, specType) -> throwIncompatibleExprType pos exprName exprType (ppType specType)

-- | Check that no 'ensures' or 'arbitrary' statement has been added for the
-- given reference is undefined.
checkEnsuresUndefined :: Pos -> TC.JavaExpr -> String -> MethodSpecTranslator ()
checkEnsuresUndefined pos ref msg = do
  exprs <- gets ensuredExprs
  when (Set.member ref exprs) $
    throwIOExecException pos (ftext msg) ""

-- | Get type assigned to SpecJavaRef, or throw exception if it is not assigned.
lookupRefType :: Pos -> TC.JavaExpr -> MethodSpecTranslator SpecJavaRefInitialValue
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
checkRefIsUnaliased :: Pos -> TC.JavaExpr -> String -> MethodSpecTranslator ()
checkRefIsUnaliased pos ref res = do
  s <- gets mayAliasRefs
  when (Map.member ref s) $ do
    let msg = "\'" ++ show ref ++ "\'was previously mentioned in a mayAlias"
              ++ " declaration."
    throwIOExecException pos (ftext msg) res

-- | Check that Java expression is of a type that can be assigned.
checkJavaExprIsModifiable :: Pos -> TC.JavaExpr -> String -> MethodSpecTranslator ()
checkJavaExprIsModifiable pos expr declName =
  case TC.getJSSTypeOfJavaExpr expr of
    JSS.ClassType _ ->
      let msg = declName ++ " declaration given a constant value " ++ show expr
                ++ "SAWScript currently requires constant values are unmodified by method calls."
          res = "Please modify the spec and/or Java code so that it does not "
                ++ "modify a reference value."
       in throwIOExecException pos (ftext msg) res
    _ -> return ()

-- | Add ensures statement mappping Java expr to given postcondition.
addEnsures :: Pos
           -> TC.JavaExpr
           -> SpecPostcondition
           -> MethodSpecTranslator ()
addEnsures pos javaExpr post = do
  aliasClasses <- gets mayAliasRefs
  case TC.getJSSTypeOfJavaExpr javaExpr of
    JSS.ArrayType _ -> do
      let equivCl = Map.findWithDefault [javaExpr] javaExpr aliasClasses
      modify $ \s ->
        s { ensuredExprs = foldr Set.insert (ensuredExprs s) equivCl
          , arrayEnsures = Map.insert javaExpr (pos, post) (arrayEnsures s)
          }
    _ -> do
      modify $ \s ->
        s { ensuredExprs = Set.insert javaExpr (ensuredExprs s)
          , scalarEnsures = Map.insert javaExpr (pos, post) (scalarEnsures s)
          }

-- | Code for parsing a method spec declaration.
resolveDecl :: AST.MethodSpecDecl -> MethodSpecTranslator ()
resolveDecl (AST.Type pos astExprs astTp) = do
  specType <- parseASTType astTp
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
    let javaExprType = TC.getJSSTypeOfJavaExpr javaExpr
        tgtType = getJSSTypeOfSpecJavaType specType
    -- Check that type of ref and the type of tp are compatible.
    b <- JSS.isSubtype tgtType javaExprType
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
        lift $ checkJSSTypeIsRef pos (TC.getJSSTypeOfJavaExpr ref)
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
  valueExpr <- do
    bindings <- gets mstsGlobalBindings
    let config = TC.mkGlobalTCConfig bindings Map.empty
    lift $ TC.tcExpr config astValueExpr
  val <- lift $ TC.globalEval valueExpr
  let tp = TC.getTypeOfExpr valueExpr
  -- Check ref and expr have compatible types.
  checkJavaExprCompat pos (show javaExpr) (TC.getJSSTypeOfJavaExpr javaExpr) tp
  -- Add ref to refTypeMap
  modify $ \s -> s { constExprMap = Map.insert javaExpr (val,tp) (constExprMap s) }
resolveDecl (AST.MethodLet pos name astExpr) = do
  -- Check var is not already bound within method.
  do locals <- gets currentLetBindingMap
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
  let javaExprType = TC.getJSSTypeOfJavaExpr javaExpr
      valueExprType = TC.getTypeOfExpr valueExpr
  checkJavaExprCompat pos (show javaExpr) javaExprType valueExprType
  addEnsures pos javaExpr (PostResult valueExpr)
resolveDecl (AST.Arbitrary pos astJavaExprs) = do
  forM_ astJavaExprs $ \astJavaExpr -> do
    -- Resolve and check astJavaExpr.
    javaExpr <- typecheckJavaExpr astJavaExpr
    checkJavaTypeIsDefined pos javaExpr
    exprTypeFn <- getExprTypeFn
    checkJavaExprIsModifiable pos javaExpr "\'arbitrary\'"
    checkEnsuresUndefined pos javaExpr $
      "Multiple ensures and arbitrary statements have been added for " ++ show javaExpr ++ "."
    case exprTypeFn javaExpr of
      Just (TC.DefinedType tp) ->
        addEnsures pos javaExpr (PostArbitrary tp)
      _ -> error "internal: resolveDecl Arbitrary given bad javaExpr"
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
  method <- gets mstsMethod
  case JSS.methodReturnType method of
    Nothing ->
      let msg = "Return value specified for \'" ++ JSS.methodName method ++ "\', but "
                 ++ "method returns \'void\'."
       in throwIOExecException pos (ftext msg) ""
    Just returnType ->

      let valueExprType = TC.getTypeOfExpr valueExpr
       in checkJavaExprCompat pos "the return value" returnType valueExprType
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
  , methodSpecIRThisClass :: JSS.Class
    -- | Class where method is defined.
  , methodSpecIRMethodClass :: JSS.Class
    -- | Method to verify.
  , methodSpecIRMethod :: JSS.Method
    -- | Class names expected to be initialized using JVM "/" separators.
    -- (as opposed to Java "." path separators).
  , initializedClasses :: [String]
    -- | References in specification with alias information and reference info.
  , specReferences :: [(SpecJavaRefEquivClass, SpecJavaRefInitialValue)]
    -- | List of non-reference input variables that must be available.
  , specScalarInputs :: [TC.JavaExpr]
    -- | List of constants expected in input.
  , specConstants :: [(TC.JavaExpr,CValue,DagType)]
    -- | Let bindings
  , methodLetBindings :: [(String, TC.Expr)]
  -- | Preconditions that must be true before method executes.
  , assumptions :: [TC.Expr]
  -- | Maps expressions for scalar values to their expected value after execution.
  -- This map should include results both inputs and constants.
  , scalarPostconditions :: Map TC.JavaExpr SpecPostcondition
  -- | Maps expressions ot the expected value after execution.
  -- This map should include results both inputs and constants.
  , arrayPostconditions :: Map TC.JavaExpr SpecPostcondition
  -- | Return value if any (is guaranteed to be compatible with method spec.
  , returnValue :: Maybe TC.Expr
  -- | Verification method for method.
  , methodSpecVerificationTactic :: AST.VerificationMethod
  } deriving (Show)

-- | Return user printable name of method spec (currently the class + method name).
methodSpecName :: MethodSpecIR -> String
methodSpecName ir =
 let clName = className (methodSpecIRThisClass ir)
     mName = methodName (methodSpecIRMethod ir)
  in slashesToDots clName ++ ('.' : mName)

-- | Returns all Java expressions referenced in specification.
methodSpecJavaExprs :: MethodSpecIR -> [TC.JavaExpr]
methodSpecJavaExprs ir =
  concat (map fst (specReferences ir)) ++ specScalarInputs ir

-- | Returns all Java field expressions referenced in specification.
methodSpecInstanceFieldExprs :: MethodSpecIR -> [(TC.JavaExpr, JSS.FieldId)]
methodSpecInstanceFieldExprs ir =
  [ (refExpr, f) | TC.InstanceField refExpr f <- methodSpecJavaExprs ir ]
  
-- | Interprets AST method spec commands to construct an intermediate
-- representation that
resolveMethodSpecIR :: TC.GlobalBindings
                    -> Pos
                    -> JSS.Class
                    -> String
                    -> [AST.MethodSpecDecl]
                    -> OpSession MethodSpecIR
resolveMethodSpecIR gb pos thisClass mName cmds = do
  let st = MSTS { mstsPos = pos
                , mstsGlobalBindings = gb
                , specClass = thisClass
                , mstsMethod = undefined
                , nonRefTypes = Set.empty
                , refTypeMap = Map.empty
                , constExprMap = Map.empty
                , mayAliasRefs = Map.empty
                , revAliasSets = []
                , currentLetBindingMap = Map.empty
                , reversedLetBindings = []
                , currentAssumptions = []
                , ensuredExprs = Set.empty
                , scalarEnsures = Map.empty

                , arrayEnsures = Map.empty
                , currentReturnValue = Nothing
                , chosenVerificationMethod = Nothing
                }
  flip evalStateT st $ do
    -- Initialize necessary values in translator state.
    (methodClass,method) <- findMethod pos mName thisClass
    modify $ \s -> s { mstsMethod = method }
    unless (methodIsStatic method) $
      modify $ \s ->
        s { refTypeMap =
              Map.singleton (TC.This (className thisClass)) (RIVClass thisClass) }
    -- Perform resolution
    mapM_ resolveDecl cmds
    -- Get final state
    st' <- get
    -- Get list of initial superclasses.
    superClasses <- JSS.supers thisClass
    -- Check that each declaration of a field does not have the base
    -- object in the mayAlias class.
    let allRefs = Map.keysSet (refTypeMap st') `Set.union` Map.keysSet (constExprMap st')
    let checkRef (TC.This _) = return ()
        checkRef (TC.Arg _ _) = return ()
        checkRef (TC.InstanceField lhs f) = do
          when (Map.member lhs (mayAliasRefs st')) $
            let msg = "This specification contains a mayAlias declaration "
                     ++ "containing \'" ++ show lhs ++ "\' and an additional "
                     ++ "declaration that references its field \'"
                     ++ JSS.fieldIdName f ++ "\'.  The current SAWScript "
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
                   let javaTp = TC.getJSSTypeOfJavaExpr r
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
        Just _ -> do
          let throwUndefinedReturnValue =
                let msg = "The Java method \'" ++ methodName method
                          ++ "\' has a return value, but the spec does not define it."
                 in throwIOExecException pos (ftext msg) ""
          maybe throwUndefinedReturnValue (return . Just . snd) $
                (currentReturnValue st')
    -- Get post conditions
    let scalarPostconditions =
          let getScalarPostCondition expr =
               case Map.lookup expr (scalarEnsures st') of
                 Nothing -> (expr, PostUnchanged)
                 Just (_pos,cond) -> (expr, cond)
           in Map.fromList $ map getScalarPostCondition
                           $ Set.toList (nonRefTypes st')
    -- Get verification method.
    let throwUndefinedVerification =
          let msg = "The verification method for \'" ++ methodName method
                    ++ "\' is undefined."
              res = "Please specify a verification method.  Use \'skip\' to skip verification."
           in throwIOExecException pos (ftext msg) res
    methodSpecVerificationTactic
      <- maybe throwUndefinedVerification (return . snd) $
           chosenVerificationMethod st'
    -- Return IR.
    return MSIR { methodSpecPos = pos
                , methodSpecIRThisClass = thisClass
                , methodSpecIRMethodClass = methodClass
                , methodSpecIRMethod = method
                , initializedClasses = map className superClasses
                , specReferences
                , specScalarInputs = Set.toList (nonRefTypes st')
                , specConstants
                , methodLetBindings = reverse (reversedLetBindings st')
                , assumptions = currentAssumptions st'
                , scalarPostconditions
                , arrayPostconditions = Map.map snd (arrayEnsures st')
                , returnValue
                , methodSpecVerificationTactic
                }

-- JavaStateInfo {{{1

-- | Stores information about a particular Java state.
data JavaStateInfo = JSI {
         jsiThis :: Maybe JSS.Ref
       , jsiArgs :: V.Vector (JSS.Value Node)
       , jsiPathState :: JSS.PathState Node
       }

-- | Create a Java State info from the current simulator path state, 
-- and using the given arguments for this and argument positions.
createJavaStateInfo :: Maybe JSS.Ref
                    -> [JSS.Value Node]
                    -> JSS.PathState Node
                    -> JavaStateInfo
createJavaStateInfo r args s =
  JSI { jsiThis = r, jsiArgs = V.fromList args, jsiPathState = s }

-- | Returns value associated to Java expression in this state if it is defined,
-- or Nothing if the expression is undefined.
-- N.B. This method assumes that the Java path state is well-formed, the
-- the JavaExpression syntactically referes to the correct type of method
-- (static versus instance), and correct well-typed arguments.  It does
-- not assume that all the instanceFields in the JavaStateInfo are initialized.
javaExprValue :: JavaStateInfo -> TC.JavaExpr -> Maybe (JSS.Value Node)
javaExprValue jsi (TC.This _) = 
  case jsiThis jsi of
    Just r -> Just (JSS.RValue r)
    Nothing -> error "internal: javaExprValue given TC.This for static method"
javaExprValue jsi (TC.Arg i _) =
  CE.assert (i < V.length (jsiArgs jsi)) $
    Just (jsiArgs jsi V.! i)
javaExprValue jsi (TC.InstanceField e f) = do
  JSS.RValue r <- javaExprValue jsi e
  Map.lookup (r,f) (JSS.instanceFields (jsiPathState jsi))

-- | Returns nodes associated to Java expression in initial state associated with mapping.
-- N.B. This method assumes that the Java expression is well-defined in the state of the
-- JavaStateInfo, and also assumes the state is well-typed as in @javaExprValue@.
javaExprNode :: JavaStateInfo -> TC.JavaExpr -> Node
javaExprNode jsi e =
  case javaExprValue jsi e of
    Just (JSS.IValue n) -> n
    Just (JSS.LValue n) -> n
    Just (JSS.RValue r) -> let Just (_,n) = Map.lookup r (JSS.arrays (jsiPathState jsi)) in n
    Just _ -> error $ "internal: javaExprNode given an invalid expression \'" ++ show e ++ ".\'"
    Nothing -> error $ "internal: javaExprNode given an undefined expression \'" ++ show e ++ ".\'"

-- SpecStateInfo {{{1

-- | Stores information about the JavaState at a particular specification state.
data SpecStateInfo = SSI {
         ssiJavaStateInfo :: JavaStateInfo
        -- | Maps names appearing in let bindings to the corresponding Node.
       , ssiLetNodeBindings :: Map String Node
       }

-- | Create spec state info from a Java state info and method spec IR.
createSpecStateInfo :: MethodSpecIR -> JavaStateInfo -> SymbolicMonad SpecStateInfo
createSpecStateInfo ir jsi = do
  let initialState = SSI jsi Map.empty
  flip execStateT initialState $ do
    -- create Method Let Bindings
    forM_ (methodLetBindings ir) $ \(name,expr) -> do
      ssi <- get
      n <- lift $ evalExpr ssi expr
      modify $ \s -> s { ssiLetNodeBindings = Map.insert name n (ssiLetNodeBindings s) }

-- | Evaluates a typed expression.
evalExpr :: SpecStateInfo -> TC.Expr -> SymbolicMonad Node
evalExpr ssi (TC.Apply op exprs) = do
  applyOp op =<< mapM (evalExpr ssi) exprs
evalExpr _ (TC.Cns c tp) =
  makeConstant c tp
evalExpr ssi (TC.JavaValue javaExpr _) =
  return $ javaExprNode (ssiJavaStateInfo ssi) javaExpr
evalExpr ssi (TC.Var name _tp) = do
  case Map.lookup name (ssiLetNodeBindings ssi) of
    Nothing -> error $ "internal: evalExpr given invalid variable " ++ name
    Just n -> return n

-- Method specification overrides {{{1

execOverride :: Pos
             -> String
             -> MethodSpecIR
             -> Maybe JSS.Ref
             -> [JSS.Value Node]
             -> JSS.Simulator SymbolicMonad ()
execOverride pos nm ir mbThis args = do
  -- Check Java expressions referenced in IR are defined in the path state.
  ps <- JSS.getPathState
  -- Create JavaStateInfo and SpecStateInfo from current simulator state.
  let jsi = createJavaStateInfo mbThis args ps
  forM_ (methodSpecJavaExprs ir) $ \javaExpr -> do
    when (isNothing (javaExprValue jsi javaExpr)) $ do
      let msg = "The override for \'" ++ methodSpecName ir
                  ++ "\' was called while symbolically simulating " ++ nm 
                  ++ ".  However, the method specification of \'"
                  ++ methodSpecName ir ++ "\' requires that the value of \'"
                  ++ show javaExpr ++ "\' is defined."
          res = "Please add a \'var\' or \'const\' declaration as appropriate "
                  ++ "to the specification of \'" ++ nm
                  ++ "\' to define \'" ++ show javaExpr ++ "\'."
       in throwIOExecException pos (ftext msg) res
  ssi <- JSS.liftSymbolic $ createSpecStateInfo ir jsi
  -- Check initialization status
  forM_ (initializedClasses ir) $ \c -> do
    status <- JSS.getInitializationStatus c
    when (status /= Just JSS.Initialized) $
      let msg = "The method spec " ++ methodSpecName ir ++ " requires that the class "
                  ++ slashesToDots c ++ " is initialized.  SAWScript does not "
                  ++ "support new initialized classes yet."
       in throwIOExecException pos (ftext msg) ""
  -- Assume all assumptions
  forM_ (assumptions ir) $ \e ->
    JSS.assume =<< JSS.liftSymbolic (evalExpr ssi e)
  -- Check references have correct type.
  liftIO $ do
    seenRefsIORef <- liftIO $ newIORef (Map.empty :: Map JSS.Ref TC.JavaExpr)
    forM_ (specReferences ir) $ \(ec, _iv) -> do
      seenRefs <- liftIO $ readIORef seenRefsIORef
      refs <- forM ec $ \javaExpr-> do
                let Just (JSS.RValue r) = javaExprValue jsi javaExpr
                case Map.lookup r seenRefs of
                  Nothing -> return ()
                  Just prevExpr -> do
                    let msg = "When using the method override for " ++ methodSpecName ir
                                ++ ", the expression " ++ show javaExpr
                                ++ " aliased a reference that was referred by "
                                ++ show prevExpr ++ "."
                        res = "Please use a \'mayAlias\' declaration when values may alias each other."
                     in throwIOExecException pos (ftext msg) res
                return r
      let newRefs = foldr (uncurry Map.insert) seenRefs (refs `zip` ec)
      writeIORef seenRefsIORef newRefs
  -- Check constants are really constants.
  forM_ (specConstants ir) $ \(javaExpr,c,tp) -> do
    let jvmNode = javaExprNode jsi javaExpr
    specNode <- JSS.liftSymbolic $ makeConstant c tp
    JSS.assume =<< JSS.liftSymbolic (applyEq specNode jvmNode)
  -- Update arrayPostconditions
  forM_ (Map.toList $ arrayPostconditions ir) $ \(javaExpr,pc) -> do
    let Just (JSS.RValue r) = javaExprValue jsi javaExpr
    case pc of
      PostUnchanged -> return ()
      PostArbitrary tp -> do
        n <- JSS.liftSymbolic $ createSymbolicFromType tp
        JSS.setSymbolicArray r n
      PostResult expr -> do
        n <- JSS.liftSymbolic $ evalExpr ssi expr
        JSS.setSymbolicArray r n
  -- Update scalarPostconditions
  forM_ (Map.toList $ scalarPostconditions ir) $ \(javaExpr,pc) -> do
    case javaExpr of
      TC.InstanceField refExpr f -> do
        let Just (JSS.RValue r) = javaExprValue jsi refExpr
        let scalarValueFromNode :: JSS.Type -> Node -> JSS.Value Node
            scalarValueFromNode JSS.BooleanType n = JSS.IValue n
            scalarValueFromNode JSS.IntType n = JSS.IValue n
            scalarValueFromNode JSS.LongType n = JSS.LValue n
            scalarValueFromNode _ _ = error "internal: illegal type"
        case pc of
          PostUnchanged -> return ()
          PostArbitrary tp -> do
            n <- JSS.liftSymbolic (createSymbolicFromType tp)
            let v = scalarValueFromNode (TC.getJSSTypeOfJavaExpr javaExpr) n
            JSS.setInstanceFieldValue r f v
          PostResult expr -> do
            n <- JSS.liftSymbolic $ evalExpr ssi expr
            let v = scalarValueFromNode (TC.getJSSTypeOfJavaExpr javaExpr) n
            JSS.setInstanceFieldValue r f v
      _ -> return () -- TODO: Investigate better fix. error $ "internal: Illegal scalarPostcondition " ++ show javaExpr
  -- Update return type.
  let Just returnExpr = returnValue ir
  case JSS.methodReturnType (methodSpecIRMethod ir) of
    Nothing -> return ()
    Just tp | tp == BooleanType || tp == IntType -> do
      n <- JSS.liftSymbolic (evalExpr ssi returnExpr)
      JSS.pushValue (JSS.IValue n)
    Just LongType -> do
      n <- JSS.liftSymbolic (evalExpr ssi returnExpr)
      JSS.pushValue (JSS.LValue n)
    Just _ -> error $ "internal: Unsupported return type given to execOverride"
                  ++ " that should have been caught during resolution."

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: Pos -> String -> MethodSpecIR -> JSS.Simulator SymbolicMonad ()
overrideFromSpec pos nm ir = do
  let cName = className (methodSpecIRMethodClass ir)
  let method = methodSpecIRMethod ir
  let key = JSS.methodKey method
  if methodIsStatic method
    then JSS.overrideStaticMethod cName key $ \args ->
           execOverride pos nm ir Nothing args
    else JSS.overrideInstanceMethod cName key $ \thisVal args ->
           execOverride pos nm ir (Just thisVal) args

-- MethodSpec verification {{{1
-- EquivClassMap {{{2
type EquivClassMap = (Int, Map Int [TC.JavaExpr], Map Int SpecJavaRefInitialValue)

-- | Return list of class indices to initial values.
equivClassMapEntries :: EquivClassMap
                     -> V.Vector (Int, [TC.JavaExpr], SpecJavaRefInitialValue)
equivClassMapEntries (_,em,vm)
  = V.map (\(i,v) -> (i,em Map.! i,v))
  $ V.fromList $ Map.toList vm

-- JavaVerificationState {{{2
type InputEvaluator = SV.Vector Bool -> CValue

type InputEvaluatorList = [(TC.JavaExpr, InputEvaluator)]

-- | JavaVerificationState contains information necessary to map between specification
-- expressions and the initial JVM state during verification.
data JavaVerificationState = JVS {
        -- | Name of method in printable form.
        jvsMethodName :: String
        -- | Maps Java expression to associated node.
      , jvsExprNodeMap :: Map TC.JavaExpr Node
        -- | Contains functions that translate from counterexample
        -- returned by ABC back to constant values, along with the
        -- Java expression associated with that evaluator.
      , jvsInputEvaluators :: InputEvaluatorList
        -- | Maps Spec Java expression to value for that expression.
      , jvsExprValueMap :: Map TC.JavaExpr (JSS.Value Node)
        -- | Maps JSS refs to name for that ref.
      , jvsRefNameMap :: Map JSS.Ref String
        -- | List of array references, the associated equivalence class, and the initial value.
      , jvsArrayNodeList :: [(JSS.Ref,SpecJavaRefEquivClass,Node)]
      }

-- | Returns name of reference in a state.
getRefName :: MonadIO m => Pos -> JSS.Ref -> JavaVerificationState -> m String
getRefName pos r jvs = do
  case Map.lookup r (jvsRefNameMap jvs) of
    Nothing ->
      let msg = "The JVM method \'" ++ jvsMethodName jvs ++ "\' has allocated "
                ++ "a new reference.  JavaVerifier does not currently support "
                ++ "methods that allocate new references."
       in throwIOExecException pos (ftext msg) ""
    Just e -> return (show e)

type JavaEvaluator = StateT JavaVerificationState (JSS.Simulator SymbolicMonad)

-- initializeJavaVerificationState {{{3

-- | Initialize JavaVerificationState components involving references,
-- and create them in simulator.
createJavaEvalReferences :: EquivClassMap -> JavaEvaluator ()
createJavaEvalReferences cm = do
  let liftAig = lift . JSS.liftSymbolic . liftAigMonad
      liftSym = lift . JSS.liftSymbolic
  V.forM_ (equivClassMapEntries cm) $ \(_idx, exprClass, initValue) -> do
    litCount <- liftAig $ getInputLitCount
    let refName = ppSpecJavaRefEquivClass exprClass
    let -- create array input node with length and int width.
        createInputArrayNode l w = do
          n <- liftSym $ createSymbolicArrayNode l w
          let inputEval lits =
                CArray $ V.map (\j -> mkCIntFromLsbfV $ SV.slice j w lits)
                       $ V.enumFromStepN litCount w (fromIntegral l)
          ref <- lift $ JSS.newSymbolicArray (JSS.ArrayType JSS.IntType) (fromIntegral l) n
          modify $ \s ->
            s { jvsExprNodeMap =  mapInsertKeys exprClass n (jvsExprNodeMap s)
              , jvsInputEvaluators = map (\expr -> (expr,inputEval)) exprClass
                                      ++ jvsInputEvaluators s
              , jvsExprValueMap = mapInsertKeys exprClass (JSS.RValue ref) (jvsExprValueMap s)
              , jvsRefNameMap = Map.insert ref refName (jvsRefNameMap s)
              , jvsArrayNodeList = (ref,exprClass,n):(jvsArrayNodeList s) }
    case initValue of
      RIVArrayConst javaTp c@(CArray v) tp -> do
        n <- liftSym $ makeConstant c tp
        let l = V.length v
        ref <- lift $ JSS.newSymbolicArray javaTp (fromIntegral l) n
        modify $ \s -> s
          { jvsExprNodeMap =  mapInsertKeys exprClass n (jvsExprNodeMap s)
          , jvsExprValueMap = mapInsertKeys exprClass (JSS.RValue ref) (jvsExprValueMap s)
          , jvsRefNameMap = Map.insert ref refName (jvsRefNameMap s)
          , jvsArrayNodeList = (ref,exprClass,n):(jvsArrayNodeList s)
          }
      RIVArrayConst _ _ _ -> error "internal: Illegal RIVArrayConst to runMethodVerification"
      RIVClass cl -> do
        ref <- lift $ JSS.genRef (ClassType (className cl))
        modify $ \s -> s
          { jvsExprValueMap = mapInsertKeys exprClass (JSS.RValue ref) (jvsExprValueMap s)
          , jvsRefNameMap = Map.insert ref refName (jvsRefNameMap s)
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
            s { jvsExprNodeMap = Map.insert expr node (jvsExprNodeMap s)
              , jvsInputEvaluators = (expr,inputEval) : jvsInputEvaluators s
              , jvsExprValueMap = Map.insert expr value (jvsExprValueMap s) }
    case TC.getJSSTypeOfJavaExpr expr of
      JSS.BooleanType -> do
        -- Treat JSS.Boolean as a 32-bit integer.
        n <- liftSym $ createSymbolicIntNode 32
        let inputEval lits = mkCIntFromLsbfV $ SV.slice litCount 32 lits
        addScalarNode n inputEval (JSS.IValue n)
      JSS.IntType -> do
        n <- liftSym $ createSymbolicIntNode 32
        let inputEval lits = mkCIntFromLsbfV $ SV.slice litCount 32 lits
        addScalarNode n inputEval (JSS.IValue n)
      JSS.LongType -> do
        n <- liftSym $ createSymbolicIntNode 64
        let inputEval lits = mkCIntFromLsbfV $ SV.slice litCount 64 lits
        addScalarNode n inputEval (JSS.LValue n)
      _ -> error "internal: createSpecSymbolicInputs Illegal spectype."

-- | Create an evaluator state with the initial JVM state form the IR and
-- equivalence class map.
initializeJavaVerificationState :: MethodSpecIR
                                -> EquivClassMap
                                -> JSS.Simulator SymbolicMonad JavaVerificationState
initializeJavaVerificationState ir cm = do
  let initialState = JVS
        { jvsMethodName = methodSpecName ir
        , jvsExprNodeMap = Map.empty
        , jvsInputEvaluators = []
        , jvsExprValueMap = Map.empty
        , jvsRefNameMap = Map.empty
        , jvsArrayNodeList = []
        }
  flip execStateT initialState $ do
    -- Add initialized classes
    lift $ forM_ (initializedClasses ir) $ \c -> do
      JSS.setInitializationStatus c JSS.Initialized
    -- Create references.
    createJavaEvalReferences cm
    -- Create scalars.
    createJavaEvalScalars ir
    -- Set field values.
    do m <- gets jvsExprValueMap
       let fieldExprs = [ p | p@(TC.InstanceField{},_) <- Map.toList m ]
       forM_ fieldExprs $ \((TC.InstanceField refExpr f),v) -> do
         let Just (JSS.RValue r) = Map.lookup refExpr m
         lift $ JSS.setInstanceFieldValue r f v

-- Java execution {{{2

-- Run method and get final path state
runMethod :: MethodSpecIR
          -> JavaStateInfo
          -> JSS.Simulator SymbolicMonad [(JSS.PathDescriptor, JSS.FinalResult Node)]
runMethod ir jsi = do
  let clName = className (methodSpecIRMethodClass ir)
  let method = methodSpecIRMethod ir
  let args = V.toList (jsiArgs jsi)
  if methodIsStatic method
    then JSS.invokeStaticMethod clName (methodKey method) args
    else do
      let Just thisRef = jsiThis jsi
      JSS.invokeInstanceMethod clName (methodKey method) thisRef args
  JSS.run

-- ExpectedStateDef {{{2

-- | Stores expected values in symbolic state after execution.
data ExpectedStateDef = ESD {
       -- | Expected return value or Nothing if method returns void.
       esdReturnValue :: Maybe Node
       -- | Maps instance fields to expected values.
     , esdInstanceFields :: Map (JSS.Ref, JSS.FieldId) (Maybe (JSS.Value Node))
       -- | Maps reference to expected node (or Nothing if value is arbitrary).
     , esdArrays :: Map JSS.Ref (Maybe Node)
     }

-- | Create a expected state definition from method spec and eval state.
createExpectedStateDef :: MethodSpecIR
                       -> JavaVerificationState
                       -> SpecStateInfo
                       -> SymbolicMonad ExpectedStateDef
createExpectedStateDef ir jvs ssi = do
  let jsi = ssiJavaStateInfo ssi
  esdReturnValue <-
    case returnValue ir of
      Nothing -> return Nothing
      Just expr -> fmap Just $ evalExpr ssi expr
  -- Get instance field values.
  instanceFields <- forM (methodSpecInstanceFieldExprs ir) $ \(refExpr,fid) -> do
      let javaExpr = TC.InstanceField refExpr fid
      let Just (JSS.RValue ref) = javaExprValue jsi refExpr
      let Just v = javaExprValue jsi javaExpr
      expValue <-
        case Map.lookup javaExpr (scalarPostconditions ir) of
          -- Non-modifiable case.
          Nothing -> return (Just v)
          Just PostUnchanged -> return (Just v) -- Unchanged
          Just (PostArbitrary _) -> return Nothing -- arbitrary case
          Just (PostResult expr) -> do
            case v of
              -- Use value for scalars
              JSS.IValue _ -> fmap (Just . JSS.IValue) $ evalExpr ssi expr
              JSS.LValue _ -> fmap (Just . JSS.LValue) $ evalExpr ssi expr
              _ -> error "internal: scalarPostcondition assigned to a illegal expression"
      return ((ref,fid),expValue)
  -- Get array values.
  arrays <-
    forM (jvsArrayNodeList jvs) $ \(r,refEquivClass,initValue) -> do
      expValue <-
        case mapLookupAny refEquivClass (arrayPostconditions ir) of
          Just PostUnchanged -> return (Just initValue)
          Just (PostArbitrary _) -> return Nothing
          Just (PostResult expr) ->
            fmap Just $ evalExpr ssi expr
          Nothing -> return (Just initValue)
      whenVerbosity (>= 6) $
        liftIO $ putStrLn
                $ "Expecting " ++ show refEquivClass ++ " has value " ++ show expValue
      return (r,expValue)
  -- Return expected state definition.
  return $ ESD { esdReturnValue
               , esdInstanceFields = Map.fromList instanceFields
               , esdArrays = Map.fromList arrays
               }

-- VerificationCheck {{{2

data VerificationCheck
  = PathCheck Node
  | EqualityCheck String -- ^ Name of value to compare
                  Node -- ^ Value returned by JVM symbolic simulator.
                  Node -- ^ Expected value in Spec.
  deriving (Eq, Ord, Show)

-- | Returns goal that one needs to prove.
checkGoal :: VerificationCheck -> SymbolicMonad Node
checkGoal (PathCheck n) = return n
checkGoal (EqualityCheck _ x y) = applyEq x y

checkName :: VerificationCheck -> String
checkName (PathCheck _) = "the path condition"
checkName (EqualityCheck nm _ _) = nm

-- | Returns documentation for check that fails.
checkCounterexample :: VerificationCheck
                    -> SymbolicEvalMonad SymbolicMonad Doc
checkCounterexample (PathCheck _) =
  return $ text "The path conditions were unsatisfied."
checkCounterexample (EqualityCheck nm jvmNode specNode) = do
  jvmVal <- evalNode jvmNode
  specVal <- evalNode specNode
  return $ text nm $$
             nest 2 (text "Encountered: " <> ppCValueD Mixfix jvmVal) $$
             nest 2 (text "Expected:    " <> ppCValueD Mixfix specVal)

-- | Returns assumptions in method spec.
methodAssumptions :: MethodSpecIR
                  -> SpecStateInfo
                  -> SymbolicMonad Node
methodAssumptions ir ssi = do
  nodes <- mapM (evalExpr ssi) (assumptions ir)
  foldM applyBAnd (mkCBool True) nodes

-- | Add verification condition to list.
addEqVC :: String -> Node -> Node -> StateT [VerificationCheck] SymbolicMonad ()
addEqVC name jvmNode specNode = do
  modify $ \l -> EqualityCheck name jvmNode specNode : l

-- | Compare old and new states.
comparePathStates :: MethodSpecIR
                  -> JavaVerificationState
                  -> ExpectedStateDef
                  -> JSS.PathState Node
                  -> Maybe (JSS.Value Node)
                  -> SymbolicMonad [VerificationCheck]
comparePathStates ir jvs esd newPathState mbRetVal = do
  let pos = methodSpecPos ir
  let mName = methodSpecName ir
  let initialVCS  = [PathCheck (JSS.psAssumptions newPathState)]
  flip execStateT initialVCS $ do
    -- Check return value.
    let Just expRetVal = esdReturnValue esd
    case mbRetVal of
      Nothing -> return ()
      Just (JSS.IValue rv) -> addEqVC "return value" rv expRetVal
      Just (JSS.LValue rv) -> addEqVC "return value" rv expRetVal
      Just _ ->  error "internal: The Java method has a return type unsupported by JavaVerifier."
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
    do let jvmClassObjects = Set.fromList $ Map.keys $ JSS.classObjects newPathState
       unless (Set.null jvmClassObjects) $ do
         let msg = "The JVM method \'" ++ mName ++ "\' referenced class objects "
                    ++ "during execution.  This feature is not currently suported "
                    ++ "by JavaVerifier.  The extra class objects are:"
             newNames = nest 2
                      $ vcat (map (text . slashesToDots) (Set.toList jvmClassObjects))
         throwIOExecException pos (ftext msg $$ newNames) ""
    -- Check static fields
    do forM_ (Map.toList $ JSS.staticFields newPathState) $ \(fid,_jvmVal) -> do
         let clName = slashesToDots (fieldIdClass fid)
         let fName = clName ++ "." ++ fieldIdName fid
         let msg = "The JVM method \'" ++ mName ++ "\' has modified the "
                  ++ " static field " ++ fName ++ " during execution.  "
                  ++ "This feature is not currently suported by JavaVerifier."
          in throwIOExecException pos (ftext msg) ""
    -- Check instance fields
    forM_ (Map.toList $ JSS.instanceFields newPathState) $ \(fieldRef@(ref,fid),jvmVal) -> do
      refName <- getRefName pos ref jvs
      let fieldName = refName ++ "." ++ fieldIdName fid
      specVal <-
        case Map.lookup fieldRef (esdInstanceFields esd) of
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
    do let jvmRefArrays = JSS.refArrays newPathState
       unless (Map.empty == jvmRefArrays) $ do
         let msg = "The JVM method \'" ++ mName ++ "\' has modified reference arrays "
                    ++ "during execution.  This feature is not currently suported "
                    ++ "by JavaVerifier."
         throwIOExecException pos (ftext msg) ""
    -- Get array equations and counterexample parse functions
    forM_ (Map.toList (JSS.arrays newPathState)) $ \(ref,(_,jvmNode)) -> do
      refName <- getRefName pos ref jvs
      case Map.lookup ref (esdArrays esd) of
        Nothing -> error "internal: Unexpected undefined array reference."
        Just Nothing -> return ()
        Just (Just specNode) ->
          addEqVC refName jvmNode specNode

-- verifyMethodSpec and friends {{{2

data VerificationContext = VContext {
          vcAssumptions :: Node 
        , vcInputs :: InputEvaluatorList
        , vcChecks :: [VerificationCheck]
        }

-- | Attempt to verify method spec using verification method specified.
methodSpecVCs :: Pos
              -> JSS.Codebase
              -> SSOpts
              -> [MethodSpecIR]
              -> MethodSpecIR
              -> [SymbolicMonad VerificationContext]
methodSpecVCs pos cb opts overrides ir = do
  let v = verbose opts
  let refEquivClasses = partitions (specReferences ir)
  flip map refEquivClasses $ \cm -> do
    setVerbosity v
    JSS.runSimulator cb $ do
      setVerbosity v
      when (v >= 6) $
         liftIO $ putStrLn $
           "Creating evaluation state for simulation of " ++ methodSpecName ir
      -- Create map from specification entries to JSS simulator values.
      jvs <- initializeJavaVerificationState ir cm
      -- JavaStateInfo for inital verification state.
      initialPS <- JSS.getPathState
      let jsi =
            let evm = jvsExprValueMap jvs
                mbThis = case Map.lookup (TC.This (JSS.className (methodSpecIRThisClass ir))) evm of
                           Nothing -> Nothing
                           Just (JSS.RValue r) -> Just r
                           Just _ -> error "internal: Unexpected value for This"
                method = methodSpecIRMethod ir
                args = map (evm Map.!)
                     $ map (uncurry TC.Arg)
                     $ [0..] `zip` methodParameterTypes method
             in createJavaStateInfo mbThis args initialPS
      -- Add method spec overrides.
      mapM_ (overrideFromSpec pos (methodSpecName ir)) overrides
      -- Execute method.
      when (v >= 6) $
         liftIO $ putStrLn $ "Executing " ++ methodSpecName ir
      jssResult <- runMethod ir jsi
          -- isReturn returns True if result is a normal return value.
      let isReturn JSS.ReturnVal{} = True
          isReturn JSS.Terminated = True
          isReturn _ = False
      let returnResults = filter (isReturn . snd) jssResult
      when (null returnResults) $
        let msg = "The Java method " ++ methodSpecName ir
              ++ " throws exceptions on all paths, and cannot be verified"
            res = "Please check that all fields needed for correctness are defined."
         in throwIOExecException pos (ftext msg) res
      when (length returnResults > 1) $
        error "internal: verifyMethodSpec returned multiple valid results"
      let [(ps,fr)] = returnResults
      let returnVal = case fr of
                        JSS.ReturnVal val -> Just val
                        JSS.Terminated -> Nothing
                        _ -> error "internal: Unexpected final result from JSS"
      -- Build final equation and functions for generating counterexamples.
      newPathState <- JSS.getPathStateByName ps
      JSS.liftSymbolic $ do
        when (v >= 6) $
          liftIO $ putStrLn $ "Creating expected result for " ++ methodSpecName ir
        ssi <- createSpecStateInfo ir jsi
        esd <- createExpectedStateDef ir jvs ssi
        whenVerbosity (>= 6) $
          liftIO $ putStrLn $
            "Creating verification conditions for " ++ methodSpecName ir
        as <- methodAssumptions ir ssi
        -- Create verification conditions from path states.
        vcs <- comparePathStates ir jvs esd newPathState returnVal
        return VContext {
                  vcAssumptions = as
                , vcInputs = jvsInputEvaluators jvs
                , vcChecks = vcs
                }

runABC :: MethodSpecIR
       -> InputEvaluatorList
       -> Node
       -> SymbolicEvalMonad SymbolicMonad Doc
       -> SymbolicMonad ()
runABC ir inputEvalList fGoal counterFn = do
  whenVerbosity (>= 3) $
    liftIO $ putStrLn $ "Running ABC on " ++ methodSpecName ir
  LV v <- getVarLit fGoal
  unless (SV.length v == 1) $
    error "internal: Unexpected number of in verification condition"
  b <- liftAigMonad $ checkSat (neg (v SV.! 0))
  case b of
    UnSat -> return ()
    Unknown -> do
      let msg = "ABC has returned a status code indicating that it could not "
                 ++ "determine whether the specification is correct.  This "
                 ++ "result is not expected for sequential circuits, and could"
                 ++ "indicate an internal error in ABC or JavaVerifer's "
                 ++ "connection to ABC."
       in throwIOExecException (methodSpecPos ir) (ftext msg) ""
    Sat lits -> do
      let (inputExprs,inputEvals) = unzip inputEvalList
      let inputValues = map ($lits) inputEvals
      -- Get differences between two.
      diffDoc <- symbolicEval (V.fromList inputValues) $ counterFn
      let inputExprValMap = Map.fromList (inputExprs `zip` inputValues)
      let inputDocs
            = flip map (Map.toList inputExprValMap) $ \(expr,c) ->
                 text (show expr) <+> equals <+> ppCValueD Mixfix c
      let msg = ftext ("A counterexample was found by ABC when verifying "
                         ++ methodSpecName ir ++ ".\n\n") $$
                ftext ("The inputs that generated the counterexample are:") $$
                nest 2 (vcat inputDocs) $$
                ftext ("Counterexample:") $$
                nest 2 diffDoc
      throwIOExecException (methodSpecPos ir) msg ""

-- | Attempt to verify method spec using verification method specified.
verifyMethodSpec :: Pos
                 -> JSS.Codebase
                 -> SSOpts
                 -> MethodSpecIR
                 -> [MethodSpecIR]
                 -> [Rule]
                 -> OpSession ()
verifyMethodSpec _ _ _ MSIR { methodSpecVerificationTactic = AST.Skip } _ _ = return ()
verifyMethodSpec pos cb opts ir overrides rules = do
  let v = verbose opts
  when (v >= 2) $
    liftIO $ putStrLn $ "Starting verification of " ++ methodSpecName ir
  let vcList = methodSpecVCs pos cb opts overrides ir
  forM_ vcList $ \mVC -> do
    when (v >= 6) $
      liftIO $ putStrLn $ "Considing new alias configuration of " ++ methodSpecName ir
    runSymSession $ do
      setVerbosity v
      vc <- mVC
      forM (vcChecks vc) $ \check -> do
        whenVerbosity (>= 2) $
          liftIO $ putStrLn $ "Verify " ++ checkName check
        -- Get final goal.
        fConseq <- checkGoal check
        fGoal <- applyBinaryOp bImpliesOp (vcAssumptions vc) fConseq
        -- Run verification
        let runRewriter = do
            let pgm = foldl' addRule emptyProgram rules
            rew <- liftIO $ mkRewriter pgm
            reduce rew fGoal
        case methodSpecVerificationTactic ir of
          AST.ABC -> do
            runABC ir (vcInputs vc) fGoal (checkCounterexample check)
          AST.Rewrite -> do
            newGoal <- runRewriter
            case getBool newGoal of
              Just True -> return ()
              _ -> do
               let msg = ftext ("The rewriter failed to reduce the verification condition "
                                  ++ " generated from " ++ checkName check
                                  ++ " in the Java method " ++ methodSpecName ir
                                  ++ " to 'True'.\n\n") $$
                         ftext ("The remaining goal is:") $$
                         nest 2 (prettyTermD newGoal)
                   res = "Please add new rewrite rules or modify existing ones to reduce the goal to True."
                in throwIOExecException pos msg res
          AST.Auto -> do
            newGoal <- runRewriter
            runABC ir (vcInputs vc) newGoal (checkCounterexample check)
          AST.Skip -> error "internal: verifyMethodTactic used invalid tactic."
