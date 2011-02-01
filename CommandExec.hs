{-# LANGUAGE DeriveDataTypeable #-}
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
import Data.Typeable
import qualified Data.Vector as V
import Prelude hiding (catch)
import System.Directory (makeRelativeToCurrentDirectory)
import System.Exit
import System.FilePath
import Text.PrettyPrint.HughesPJ

import qualified Execution.Codebase as JSS
import JavaParser as JSS
import MethodSpec as JSS(partitions)
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

import Debug.Trace

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
  , globalLetBindings :: Map String (CValue,DagType)
    -- | Flag used to control how much logging to print out.
  , verbosity :: Int
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

-- | Define a polymorphic record from a set of field names.
defineRecFromFields :: Set String -> OpSession SymRecDef
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

checkNameIsDefined :: Pos -> String -> Executor ()
checkNameIsDefined pos name = do
  m <- gets rules
  unless (Map.member name m) $ do
    throwIOExecException pos 
                         (text "No operator or rule named " <+> quotes (text name)
                           <+> text "has been defined.")
                         ("Please check that the name is correct.")

-- lookupClass and findMethod {{{1

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
            checkJSSTypeIsRef pos (fieldType f)
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
          _ <- lookupRecordDef (Set.fromList names)
          mapM_ (parseType . SBV.schemeType) schemes

-- }}}1

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

-- TypedExpr {{{1

-- | A type checked expression which appears insider a global let binding, method
-- declaration, or rule term.
data TypedExpr 
  = TypedApply Op [TypedExpr]
  | TypedCns CValue DagType
  | TypedJavaArrayValue SpecJavaRef DagType
  | TypedVar String DagType
  deriving (Show)

-- | Return type of a typed expression.
getTypeOfTypedExpr :: TypedExpr -> DagType
getTypeOfTypedExpr (TypedVar _ tp) = tp
getTypeOfTypedExpr (TypedCns _ tp) = tp
getTypeOfTypedExpr (TypedJavaArrayValue _ tp) = tp
getTypeOfTypedExpr (TypedApply op _) = opResultType op

-- | Evaluate a ground typed expression to a constant value.
globalEval :: TypedExpr -> Executor CValue
globalEval expr = do
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
    n <- mkNode expr
    -- Simplify definition.
    rew <- liftIO $ mkRewriter pgm
    nr <- reduce rew n
    case termConst nr of
      Nothing -> error "internal: globalEval called with an expression that could not be evaluated."
      Just c -> return c

data ExprParserState = EPS {
          localBindings :: Map String TypedExpr
        }

globalParserState :: ExprParserState
globalParserState =
  EPS { localBindings = Map.empty }

-- | Check argument count matches expected length.
checkArgCount :: Pos -> String -> [TypedExpr] -> Int -> Executor ()
checkArgCount pos opName (length -> foundOpCnt) expectedCnt = do
  unless (expectedCnt == foundOpCnt) $
    let msg = "Incorrect number of arguments to \'" ++ opName ++ "\'.  "
                ++ show expectedCnt ++ " arguments were expected, but "
                ++ show foundOpCnt ++ " arguments were found."
     in throwIOExecException pos (ftext msg) ""

-- | Convert an AST expression from parser into a typed expression.
parseExpr :: ExprParserState -> AST.Expr -> Executor TypedExpr
parseExpr st (AST.TypeExpr pos (AST.ConstantInt _ i) astTp) = do
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
parseExpr EPS { localBindings } (AST.Var pos name) = do
  case Map.lookup name localBindings of
    Just res -> return res
    Nothing -> do
      globalMap <- gets globalLetBindings
      case Map.lookup name globalMap of
        Just (c,tp) -> return $ TypedCns c tp
        Nothing -> 
          let msg = "Unknown variable " ++ name ++ "."
           in throwIOExecException pos (ftext msg) ""
parseExpr st (AST.ApplyExpr appPos "join" astArgs) = do
  args <- mapM (parseExpr st) astArgs
  checkArgCount appPos "join" args 1
  let argType = getTypeOfTypedExpr (head args)
  case argType of
    SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w)) -> do
      op <- lift $ joinOpDef l w
      return $ TypedApply (groundOp op) args
    _ -> let msg = "Illegal arguments and result type given to \'join\'.  "
                   ++ "SAWScript currently requires that the argument is ground"
                   ++ " array of integers. "
          in throwIOExecException appPos (ftext msg) ""
parseExpr st (AST.TypeExpr _ (AST.ApplyExpr appPos "split" astArgs) astResType) = do
  args <- mapM (parseExpr st) astArgs
  checkArgCount appPos "split" args 1
  resType <- parseExprType astResType
  let argType = getTypeOfTypedExpr (head args)
  case (argType, resType) of
    (  SymInt (widthConstant -> Just wl)
     , SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w))) 
      | wl == l * w -> do
        op <- lift $ splitOpDef l w
        return $ TypedApply (groundOp op) args
    _ -> let msg = "Illegal arguments and result type given to \'split\'.  "
                   ++ "SAWScript currently requires that the argument is ground type, "
                   ++ "and an explicit result type is given."
          in throwIOExecException appPos (ftext msg) ""
parseExpr st (AST.ApplyExpr appPos opName astArgs) = do
  m <- gets sawOpMap
  case Map.lookup opName m of
    Nothing ->
      let msg = "Unknown operator " ++ opName ++ "."
          res = "Please check that the operator is correct."
       in throwIOExecException appPos (ftext msg) res
    Just opDef -> do
      let defArgTypes = opDefArgTypes opDef
      args <- mapM (parseExpr st) astArgs
      checkArgCount appPos opName args (V.length defArgTypes)
      let defTypes = V.toList defArgTypes
      let argTypes = map getTypeOfTypedExpr args
      case matchSubst (defTypes `zip` argTypes) of
        Nothing -> 
          let msg = "Illegal arguments and result type given to \'" ++ opName ++ "\'."
           in throwIOExecException appPos (ftext msg) ""
        Just sub -> return $ TypedApply (mkOp opDef sub) args
parseExpr st e =
  error $ "internal: parseExpr given illegal type " ++ show e

-- }}}1

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

-- SpecJavaRef {{{1

-- | Identifies a reference to a Java value.
data SpecJavaRef 
  = SpecThis
  | SpecArg Int
  | SpecField SpecJavaRef Field

instance Eq SpecJavaRef where
  SpecThis == SpecThis = True
  SpecArg i == SpecArg j = i == j
  SpecField r1 f1 == SpecField r2 f2 = r1 == r2 && fieldName f1 == fieldName f2
  _ == _ = False

instance Ord SpecJavaRef where
  SpecThis `compare` SpecThis = EQ
  SpecThis `compare` _ = LT
  _ `compare` SpecThis = GT
  SpecArg i `compare` SpecArg j = i `compare` j
  SpecArg i `compare` _ = LT
  _ `compare` SpecArg i = GT
  SpecField r1 f1 `compare` SpecField r2 f2 = 
    case r1 `compare` r2 of 
      EQ -> fieldName f1 `compare` fieldName f2
      r -> r

instance Show SpecJavaRef where
  show SpecThis = "this"
  show (SpecArg i) = "args[" ++ show i ++ "]"
  show (SpecField r f) = show r ++ "." ++ fieldName f

-- | Pretty print SpecJavaRef
ppSpecJavaRef :: SpecJavaRef -> String
ppSpecJavaRef SpecThis = "this"
ppSpecJavaRef (SpecArg i) = "args[" ++ show i ++ "]"
ppSpecJavaRef (SpecField r f) = ppSpecJavaRef r ++ ('.' : fieldName f)

-- | Returns JSS Type of SpecJavaRef
getJSSTypeOfSpecRef :: -- | Name of class for this object
                       -- (N.B. method may be defined in a subclass of this class).
                       String
                    -> V.Vector JSS.Type -- ^ Parameters of method that we are checking
                    -> SpecJavaRef -- ^ Spec Java reference to get type of.
                    -> JSS.Type -- ^ Java type (which must be a class or array type).
getJSSTypeOfSpecRef clName _p SpecThis = JSS.ClassType clName
getJSSTypeOfSpecRef _cl params (SpecArg i) = params V.! i
getJSSTypeOfSpecRef _cl _p (SpecField _ f) = fieldType f

-- }}}1


data SpecParserState = SPS {
          specClass :: JSS.Class
        , specMethodIsStatic :: Bool
        , specMethodParams :: V.Vector JSS.Type
        , refTypeMap :: Map SpecJavaRef SpecJavaRefType
        -- | Set of Java refs in a mayAlias relation.
        , mayAliasRefs :: !(Set SpecJavaRef)
        -- | List of mayAlias classes in reverse order that they were created.
        , revAliasSets :: [([SpecJavaRef], SpecJavaRefType)]
        , methodLetBindings :: Map String TypedExpr
        }

type SpecParser = StateT SpecParserState Executor

-- | Check JSS Type is a reference type supported by SAWScript.
checkJSSTypeIsRef :: Pos -> JSS.Type -> Executor ()
checkJSSTypeIsRef pos (ArrayType IntType) = return ()
checkJSSTypeIsRef pos (ArrayType LongType) = return ()
checkJSSTypeIsRef pos (ArrayType eltType) = 
  let msg = "SAWScript currently only supports arrays of int and long, "
            ++ "and does yet support arrays with type " ++ show eltType ++ "."
      res = "Please modify the Java code to only use int or long array types."
   in throwIOExecException pos (ftext msg) res
-- TODO: Check if need to confirm that class exists in next equation.
checkJSSTypeIsRef pos (ClassType nm) = return ()
checkJSSTypeIsRef pos tp =
  let msg = "SAWScript only requires reference types to be annotated "
            ++ "with type information, and currently only supports "
            ++ "methods with array and reference values as arguments.  "
            ++ "The type " ++ show tp ++ " is not a reference type."
      res = "Please modify the Java code to only use int or long array "
            ++ "types."
   in throwIOExecException pos (ftext msg) res

-- | Get type assigned to SpecJavaRef, or throw exception if it is not assigned.
lookupRefType :: Pos -> SpecJavaRef -> SpecParser SpecJavaRefType
lookupRefType pos ref = do
  m <- gets refTypeMap
  case Map.lookup ref m of
    Just tp -> return tp
    Nothing -> 
      let msg = "The type of " ++ ppSpecJavaRef ref ++ "must be specified "
                  ++ "before referring to it or one of its fields."
          res = "Please add a type annotation of the reference before this refence."
       in throwIOExecException pos (ftext msg) res


-- | Parse AST Java reference to get specification ref.
parseASTRef :: AST.JavaRef
            -> SpecParser SpecJavaRef
parseASTRef (AST.This pos) = do
  isStatic <- gets specMethodIsStatic
  when isStatic $
    throwIOExecException pos (ftext "\'this\' is not defined on static methods.") ""
  return SpecThis
parseASTRef (AST.Arg pos i) = do
  params <- gets specMethodParams
  -- Check that arg index is valid.
  unless (0 <= i && i < V.length params) $
    throwIOExecException pos (ftext "Invalid argument index for method.") ""
  lift $ checkJSSTypeIsRef pos (params V.! i)
  return $ SpecArg i
parseASTRef (AST.InstanceField pos astLhs fName) = do
  lhs <- parseASTRef astLhs
  tp <- lookupRefType pos lhs
  case tp of
    SpecRefClass cl -> fmap (SpecField lhs) $ lift $ findField pos fName cl
    _ -> let msg = "Could not find a field named " ++ fName ++ " in " 
                     ++ ppSpecJavaRef lhs ++ "."
             res = "Please check to make sure the field name is correct."
          in throwIOExecException pos (ftext msg) res

-- | Check that the reference type is undefined.
checkRefTypeIsUndefined :: Pos -> SpecJavaRef -> SpecParser ()
checkRefTypeIsUndefined pos ref = do
  m <- gets refTypeMap 
  when (Map.member ref m) $
    let msg = "The type of " ++ ppSpecJavaRef ref ++ " is already defined."
     in throwIOExecException pos (ftext msg) ""

throwIncompatibleRefType :: MonadIO m => Pos -> SpecJavaRef -> JSS.Type -> String -> m ()
throwIncompatibleRefType pos ref refType specTypeName =
  let msg = "The type of " ++ ppSpecJavaRef ref ++ " is " ++ show refType
             ++ ", which is incompatible with the specification type "
             ++ specTypeName ++ "."
   in throwIOExecException pos (ftext msg) ""

parseDecl :: AST.MethodSpecDecl -> SpecParser ()
parseDecl (AST.Type pos astRefs astTp) = do
  clName <- fmap className $ gets specClass
  params <- gets specMethodParams
  specType <- lift $ parseASTType astTp
  forM_ astRefs $ \astRef -> do
    ref <- parseASTRef astRef
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
parseDecl (AST.MayAlias pos []) = error "internal: mayAlias set is empty"
parseDecl (AST.MayAlias pos astRefs) = do
  refs@(firstRef:restRefs) <- mapM parseASTRef astRefs
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
       when (Set.member ref s) $ do
         let msg = ppSpecJavaRef ref ++ "was previously mentioned in a mayAlias"
                   ++ " declaration."
             res = "Please merge mayAlias declarations as needed so that each "
                   ++ "reference is mentioned at most once."
         throwIOExecException pos (ftext msg) res
  modify $ \s -> 
    s { mayAliasRefs = foldr Set.insert (mayAliasRefs s) refs
      , revAliasSets = (refs,firstType) : revAliasSets s }
parseDecl (AST.Const pos astRef astExpr) = do
  ref <- parseASTRef astRef
  checkRefTypeIsUndefined pos ref
  bindings <- gets methodLetBindings 
  let parserState = EPS
        { localBindings = bindings
        }
  expr <- lift $ parseExpr parserState astExpr
  -- Check ref and expr have compatible types.
  clName <- fmap className $ gets specClass
  params <- gets specMethodParams
  let refType = getJSSTypeOfSpecRef clName params ref
  case (refType, getTypeOfTypedExpr expr) of
    (  ArrayType IntType
     , SymArray (widthConstant -> Just _) (SymInt (widthConstant -> Just 32))) ->
       return ()
    (  ArrayType LongType
     , SymArray (widthConstant -> Just _) (SymInt (widthConstant -> Just 64))) ->
       return ()
    (_,specType) -> throwIncompatibleRefType pos ref refType (ppType specType)
  modify $ \s ->
    s { refTypeMap = Map.insert ref (SpecRefConstant expr) (refTypeMap s) }
parseDecl (AST.MethodLet _pos _ref _expr) = error "AST.MethodLet"
parseDecl (AST.Assume _pos _expr) = error "AST.Assume"
parseDecl (AST.Ensures _pos _ref _Expr) = error "AST.Ensures"
parseDecl (AST.Arbitrary _pos _refs) = error "AST.Arbitrary"
parseDecl (AST.VerifyUsing _pos _method) = error "AST.VerifyUsing"

data ParsedMethodSpec = PMS {
    aliasSets :: [([SpecJavaRef], SpecJavaRefType)]
  }

-- | Returns map from Java references to type.
parseMethodSpecDecls :: JSS.Class
                     -> JSS.Method
                     -> [AST.MethodSpecDecl]
                     -> Executor ParsedMethodSpec
parseMethodSpecDecls cl method cmds = do
  let st = SPS { specClass = cl
               , specMethodIsStatic = methodIsStatic method
               , specMethodParams = V.fromList (methodParameterTypes method)
               , refTypeMap = Map.singleton SpecThis (SpecRefClass cl)
               , mayAliasRefs = Set.empty
               , revAliasSets = [] 
               , methodLetBindings = Map.empty
               }
  SPS { refTypeMap
      , mayAliasRefs
      , revAliasSets 
      } <- fmap snd $ runStateT (mapM_ parseDecl cmds) st
  let unaliasedRefs
        = map (\(r,tp) -> ([r],tp))
        $ filter (\(r,tp) -> Set.notMember r mayAliasRefs)
        $ Map.toList refTypeMap
  return PMS { aliasSets = revAliasSets ++ unaliasedRefs }

      
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
    let -- | Throw ExecException if SBVException is thrown.
        throwSBVParseError :: MonadIO m => Pos -> Doc -> SBV.SBVException -> m a
        throwSBVParseError pos relativePath e =
          let msg = text "An internal error occurred when loading the SBV" 
                      <+> relativePath <> colon $$
                      text (SBV.ppSBVException e)
              res = "Please reconfirm that the SBV filename is a valid SBV file from Cryptol."
           in throwIOExecException pos msg res
     in flip catchMIO (throwSBVParseError pos relativePath) $ lift $
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
  expr <- parseExpr globalParserState astExpr
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
