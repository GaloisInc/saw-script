-- | Provides 
{- |
Module           : $Header$
Description      : Provides typechecked representation for method specifications and function for creating it from AST representation.
Stability        : provisional
Point-of-contact : jhendrix, atomb
-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE EmptyDataDecls #-}
module SAWScript.MethodSpecIR 
  ( -- * MethodSpec record
    MethodSpecIR
  , specName
  , specPos
  , specThisClass
  , specMethod
  , specMethodClass
  , specInitializedClasses
  , specBehaviors
  , specValidationPlan
  , specAddBehaviorCommand
  , specAddVarDecl
  , specAddAliasSet
  , initMethodSpec
  , resolveMethodSpecIR
    -- * Method behavior.
  , BehaviorSpec
  , bsLoc
  , bsRefExprs
  , bsMayAliasSet
  , RefEquivConfiguration
  , bsRefEquivClasses
  , bsLogicAssignments
  , bsLogicClasses
  , BehaviorCommand(..)
  , bsCommands
    -- * Equivalence classes for references.
  , JavaExprEquivClass
  , ppJavaExprEquivClass
    -- * Validation plan
  , VerifyCommand(..)
  , ValidationPlan(..)
  ) where

-- Imports {{{1

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Data.Graph.Inductive (scc, Gr, mkGraph)
import Data.List (intercalate, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Text.PrettyPrint.Leijen
import qualified Language.JVM.Common as JP

import Verinf.Symbolic

import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.Java.Common as JSS
import qualified Verifier.LLVM.Codebase as LSS
import qualified Data.JVM.Symbolic.AST as JSS

import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.CongruenceClosure (CCSet)
import SAWScript.JavaExpr
import SAWScript.Utils

-- Utility definitions {{{1

checkLineNumberInfoAvailable :: MonadIO m => Pos -> JSS.Method -> m ()
checkLineNumberInfoAvailable pos m = do
  when (null (JSS.sourceLineNumberInfo m)) $
    let msg = ftext $ "Source does not contain line number infomation."
     in throwIOExecException pos msg ""

typecheckPC :: MonadIO m => Pos -> JSS.Method -> MethodLocation -> m JSS.Breakpoint
typecheckPC pos m (LineOffset off) = do
  checkLineNumberInfoAvailable pos m
  case JSS.sourceLineNumberOrPrev m 0 of
    Nothing -> 
      let msg = ftext $ "Could not find line number of start of method."
       in throwIOExecException pos msg ""
    Just base -> do
      let ln = toInteger base + off
      case JSS.lookupLineStartPC m (fromInteger ln) of
        Just pc -> return (JSS.BreakLineNum (fromIntegral ln))
        Nothing -> do
          let msg = ftext $ "Could not find line " ++ show ln ++ "."
           in throwIOExecException pos msg ""
typecheckPC pos m (LineExact ln) = do
  checkLineNumberInfoAvailable pos m
  case JSS.lookupLineStartPC m (fromInteger ln) of
    Just pc -> return (JSS.BreakLineNum (fromIntegral ln))
    Nothing -> do
      let msg = ftext $ "Could not find line " ++ show ln ++ "."
       in throwIOExecException pos msg ""
typecheckPC pos _ (PC pc) = do
  -- TODO: Check valid instruction locations to ensure pc is valid.
  when (pc <= 0) $ do
    let msg = ftext $ "Invalid program counter."
     in throwIOExecException pos msg ""
  return (JSS.BreakPC (fromInteger pc))

-- ExprActualTypeMap {{{1

-- | Maps Java expressions for references to actual type.
type ExprActualTypeMap = Map JavaExpr JSS.Type

-- Alias definitions {{{1

type JavaExprEquivClass = [JavaExpr]

-- | Returns a name for the equivalence class.
ppJavaExprEquivClass :: JavaExprEquivClass -> String
ppJavaExprEquivClass [] = error "internal: ppJavaExprEquivClass"
ppJavaExprEquivClass [expr] = ppJavaExpr expr
ppJavaExprEquivClass cl = "{ " ++ intercalate ", " (map ppJavaExpr (sort cl)) ++ " }"

-- MethodTypecheckContext {{{1

-- | Global context for method spec typechecker.
data MethodTypecheckContext s = MTC {
         -- | Position of method spec declaration.
         mtcPos :: Pos
         -- Bindings at global level.
       , mtcGlobalBindings :: GlobalBindings s
         -- | Class we are currently parsing.
       , mtcClass :: JSS.Class
         -- | Method that spec is for.
       , mtcMethod :: JSS.Method
         -- | Names of rules (used for resolving verify commands).
       , mtcRuleNames :: Set String
       }

typecheckerConfig :: MethodTypecheckContext s -- ^ Context for typechecker
                  -> JSS.PC -- ^ PC to parse from.
                  -> ExprActualTypeMap -- ^ Maps Java expressions for references to actual type.
                  -> Map String (MixedExpr s) -- ^ Local bindings
                  -> TCConfig s
typecheckerConfig mtc pc actualTypeMap localBindings =
  TCC { globalBindings = mtcGlobalBindings mtc
      , localBindings = localBindings
      , methodInfo = Just
          MethodInfo { miClass  = mtcClass mtc
                     , miMethod = mtcMethod mtc
                     , miPC = pc
                     , miJavaExprType = flip Map.lookup actualTypeMap
                     }
      }

-- BehaviorSpec {{{1

-- | Postconditions used for implementing behavior specification.
data BehaviorCommand s
     -- | An assertion that is assumed to be true in the specificaiton.
   = AssertPred Pos (LogicExpr s)
     -- | An assumption made in a conditional behavior specification.
   | AssumePred (LogicExpr s)
     -- | Assign Java expression the value given by the mixed expression.
   | EnsureInstanceField Pos JavaExpr JSS.FieldId (MixedExpr s)
     -- | Assign array value of Java expression the value given by the rhs.
   | EnsureArray Pos JavaExpr (LogicExpr s)
     -- | Modify the Java expression to an arbitrary value.
     -- May point to integral type or array.
   | ModifyInstanceField JavaExpr JSS.FieldId
     -- | Modify the Java array to an arbitrary value.
     -- May point to integral type or array.
   | ModifyArray JavaExpr (SharedTerm s)
     -- | Specifies value method returns.
   | Return (MixedExpr s)
  deriving (Show)

data BehaviorSpec s = BS {
         -- | Program counter for spec.
         bsLoc :: JSS.Breakpoint
         -- | Maps all expressions seen along path to actual type.
       , bsActualTypeMap :: ExprActualTypeMap
         -- | Stores which Java expressions must alias each other.
       , bsMustAliasSet :: CCSet JavaExprF
         -- | May alias relation between Java expressions.
       , bsMayAliasClasses :: [[JavaExpr]]
         -- | Equations 
       , bsLogicAssignments :: [(Pos, JavaExpr, LogicExpr s)]
         -- | Commands to execute in reverse order.
       , bsReversedCommands :: [BehaviorCommand s]
       } deriving (Show)

-- | Returns list of all Java expressions that are references.
bsExprs :: BehaviorSpec s -> [JavaExpr]
bsExprs bs = Map.keys (bsActualTypeMap bs)

-- | Returns list of all Java expressions that are references.
bsRefExprs :: BehaviorSpec s -> [JavaExpr]
bsRefExprs bs = filter isRefJavaExpr (bsExprs bs)

bsMayAliasSet :: BehaviorSpec s -> CCSet JavaExprF
bsMayAliasSet bs =
  CC.foldr CC.insertEquivalenceClass
           (bsMustAliasSet bs)
           (bsMayAliasClasses bs)

-- | Check that all expressions that may alias have equal types.
bsCheckAliasTypes :: Pos -> BehaviorSpec s -> IO ()
bsCheckAliasTypes pos bs = mapM_ checkClass (CC.toList (bsMayAliasSet bs))
  where atm = bsActualTypeMap bs
        checkClass [] = error "internal: Equivalence class empty"
        checkClass (x:l) = do
          let Just xType = Map.lookup x atm
          forM l $ \y -> do
            let Just yType = Map.lookup x atm
            when (xType /= yType) $ do
              let msg = "Different types are assigned to " ++ show x ++ " and " ++ show y ++ "."
                  res = "All references that may alias must be assigned the same type."
              throwIOExecException pos (ftext msg) res

type RefEquivConfiguration = [(JavaExprEquivClass, JSS.Type)]

-- | Returns all possible potential equivalence classes for spec.
bsRefEquivClasses :: BehaviorSpec s -> [RefEquivConfiguration]
bsRefEquivClasses bs = 
  map (map parseSet . CC.toList) $ Set.toList $
    mayAliases (bsMayAliasClasses bs) (bsMustAliasSet bs)
 where parseSet l@(e:_) =
         case Map.lookup e (bsActualTypeMap bs) of
           Just tp -> (l,tp)
           Nothing -> error $ "internal: bsRefEquivClass given bad expression: " ++ show e
       parseSet [] = error "internal: bsRefEquivClasses given empty list."

bsPrimitiveExprs :: BehaviorSpec s -> [JavaExpr]
bsPrimitiveExprs bs =
  [ e | (e, ty) <- Map.toList (bsActualTypeMap bs), JSS.isPrimitiveType ty ]
 
bsLogicEqs :: BehaviorSpec s -> [(JavaExpr, JavaExpr)]
bsLogicEqs bs = undefined -- FIXME -- [ (lhs,rhs) | (_,lhs,JavaValue rhs _ _) <- bsLogicAssignments bs ]

-- | Returns logic assignments to equivance class.
bsAssignmentsForClass :: BehaviorSpec s -> JavaExprEquivClass -> [LogicExpr s]
bsAssignmentsForClass bs cl = res 
  where s = Set.fromList cl
        isJavaExpr = undefined -- FIXME
        {-
        isJavaExpr (JavaValue _ _ _) = True
        isJavaExpr _ = False
        -}
        res = [ rhs 
              | (_,lhs,rhs) <- bsLogicAssignments bs
              , Set.member lhs s
              , not (isJavaExpr rhs) ]

-- | Retuns ordering of Java expressions to corresponding logic value.
bsLogicClasses :: BehaviorSpec s
               -> RefEquivConfiguration
               -> Maybe [(JavaExprEquivClass, SharedTerm s, [LogicExpr s])]
bsLogicClasses bs rec
    | all (\l -> length l == 1) components =
       Just [ (cl, at, bsAssignmentsForClass bs cl)
            | [n] <- components
            , let (cl,at) = v V.! n ]
    | otherwise = Nothing
  where allClasses
          = CC.toList
            -- Add logic equations.
          $ flip (foldr (uncurry CC.insertEquation)) (bsLogicEqs bs)
            -- Add primitive expression.
          $ flip (foldr CC.insertTerm) (bsPrimitiveExprs bs)
            -- Create initial set with references.
          $ CC.fromList (map fst rec)
        logicClasses = 
          [ (cl,tp) | cl@(e:_) <- allClasses
                                 , let Just at = Map.lookup e (bsActualTypeMap bs)
                                 , Just tp <- [logicTypeOfActual at]
                                 ]
        v = V.fromList logicClasses
        -- Create nodes.
        grNodes = [0..] `zip` logicClasses
        -- Create edges
        exprNodeMap = Map.fromList [ (e,n) | (n,(cl,_)) <- grNodes, e <- cl ]
        grEdges = [ (s,t,()) | (t,(cl,_)) <- grNodes
                             , src:_ <- [bsAssignmentsForClass bs cl]
                             , se <- Set.toList (logicExprJavaExprs src)
                             , let Just s = Map.lookup se exprNodeMap ]
        -- Compute strongly connected components.
        components = scc (mkGraph grNodes grEdges :: Gr (JavaExprEquivClass, SharedTerm s) ())

-- BehaviorTypechecker {{{1

data BehaviorTypecheckState s = BTS {
         btsLoc :: JSS.Breakpoint
         -- | Maps expressions to actual type (forgets expressions within conditionals and
         -- blocks).
       , btsActualTypeMap :: ExprActualTypeMap
         -- | Maps let bindings already seen to position they were defined.
       , btsLetBindings :: Map String (Pos, MixedExpr s)
         -- | Flag indicating if return has been set.
       , btsReturnSet :: Bool
         -- | Paths along execution.
       , btsPaths :: [BehaviorSpec s]
       }

type BehaviorTypechecker s =
  StateT (BehaviorTypecheckState s) (ReaderT (MethodTypecheckContext s) IO)

-- BehaviorTypechecker Utilities {{{1

-- | Get codebase used in behavior typechecker.
getBTCCodebase :: BehaviorTypechecker s JSS.Codebase
getBTCCodebase = asks (codeBase . mtcGlobalBindings)

forEachPath_ :: (BehaviorSpec s -> IO a) -> BehaviorTypechecker s ()
forEachPath_ fn = mapM_ (liftIO . fn) =<< gets btsPaths

modifyPaths :: (BehaviorSpec s -> BehaviorSpec s) -> BehaviorTypechecker s ()
modifyPaths fn = do 
  modify $ \bts -> bts { btsPaths = map fn (btsPaths bts) }

-- Actual Type utilities {{{2

-- | Checks actual type is undefined.
checkActualTypeUndefined :: Pos -> JavaExpr -> BehaviorTypechecker s ()
checkActualTypeUndefined pos expr = do
  --Check type is not defined
  forEachPath_ $ \bs -> do
    when (Map.member expr (bsActualTypeMap bs)) $
      let msg = "The Java expression \'" ++ show expr ++ "\' has been already defined."
       in throwIOExecException pos (ftext msg) ""

-- | Records that the given expression is bound to the actual type.
recordActualType :: Pos -> JavaExpr -> JSS.Type -> BehaviorTypechecker s ()
recordActualType pos expr at = do
  -- Record actual type undefined or unchanged.
  bts <- get
  newPaths <- forM (btsPaths bts) $ \bs ->
    case Map.lookup expr (bsActualTypeMap bs) of
      Nothing ->
        return bs { bsActualTypeMap = Map.insert expr at (bsActualTypeMap bs)
                  , bsMustAliasSet = 
                      if JSS.isRefType (jssTypeOfJavaExpr expr) then
                        CC.insertTerm expr (bsMustAliasSet bs)
                      else
                        bsMustAliasSet bs
                  }
      Just prevAt -> do
        when (at /= prevAt) $
          let msg = "\"" ++ ppJavaExpr expr ++ "\" is already defined."
           in throwIOExecException pos (ftext msg) ""
        return bs
  -- Update main state.
  put bts { btsActualTypeMap = Map.insert expr at (btsActualTypeMap bts)
          , btsPaths = newPaths }

-- | Returns actual type of Java expression.
getActualType :: Pos -> JavaExpr -> BehaviorTypechecker s JSS.Type
getActualType pos expr = do
  typeMap <- gets btsActualTypeMap
  case Map.lookup expr typeMap of
    Just tp -> return tp
    Nothing ->
      let msg = "The type of " ++ ppJavaExpr expr ++ " has not been defined."
          res = "Please add a declaration to indicate the concrete type of this Java expression."
       in throwIOExecException pos (ftext msg) res


-- | Returns equivalence class of Java expression in translator step.
-- N.B. If this expression denotes a primitive type or does not belong to an
-- equivalence class, this returns a singleton list containing only the
-- expression.
--getJavaEquivClass :: JavaExpr -> BehaviorTypechecker JavaExprEquivClass
--getJavaEquivClass expr = Map.findWithDefault [expr] expr <$> gets btsMayAliasMap

-- Exception utilities {{{2

-- | Throw IO exception indicating name was previously defined.
throwVarIsPreviouslyDefined :: MonadIO m => Pos -> Pos -> String -> m ()
throwVarIsPreviouslyDefined pos absPrevPos name = do
  relPos <- liftIO $ posRelativeToCurrentDirectory absPrevPos
  throwIOExecException pos
                       (ftext "The variable " <+> squotes (text name)
                          <+> ftext "is already bound at "
                          <+> text (show relPos) <> char '.')
                       ("Please ensure all names are distinct.")

throwInvalidAssignment :: MonadIO m => Pos -> String -> String -> m a
throwInvalidAssignment pos lhs tp =
  let msg = lhs ++ " cannot be assigned a value with type " ++ tp ++ "."
   in throwIOExecException pos (ftext msg) ""

{-
checkLogicExprIsPred :: MonadIO m => Pos -> LogicExpr s -> m ()
checkLogicExprIsPred pos sc expr =
  case typeOfLogicExpr expr of
    SymBool -> return ()
    _ -> let msg = "Expression does not denote a predicate."
          in throwIOExecException pos (ftext msg) ""
-}

{-
-- Typecheck utilities {{{2

behaviorTypecheckerConfig :: MethodTypecheckContext 
                          -> BehaviorTypecheckState
                          -> TCConfig
behaviorTypecheckerConfig mtc bts = typecheckerConfig mtc (btsPC bts) types lets
 where types = btsActualTypeMap bts
       lets  = Map.map snd (btsLetBindings bts)

runTypechecker :: (TCConfig -> IO res) -> BehaviorTypechecker res
runTypechecker typeChecker = do
  cfg <- liftM2 behaviorTypecheckerConfig ask get
  liftIO (typeChecker cfg)

-- | Check that a type declaration has been provided for this expression.
typecheckRecordedJavaExpr :: (Expr -> TCConfig -> IO JavaExpr)
                          -> Expr
                          -> BehaviorTypechecker (JavaExpr, JSS.Type)
typecheckRecordedJavaExpr typeChecker astExpr = do
  let pos = exprPos astExpr
  expr <- runTypechecker $ typeChecker astExpr
  at <- getActualType pos expr
  return (expr, at)

-- | Typecheckes a 'valueOf' expression and returns Java expression inside
-- of it.  The type must be an array, and if a DagType is provided, the expression
-- must be compatible with the type.
typecheckValueOfLhs :: Expr -> Maybe DagType
                    -> BehaviorTypechecker (JavaExpr, DagType)
typecheckValueOfLhs astExpr maybeExpectedType = do
  let pos = exprPos astExpr
  (expr, at) <- typecheckRecordedJavaExpr tcValueOfExpr astExpr
  -- Check expression is a compatible array type.
  unless (JSS.isRefType (jssTypeOfJavaExpr expr)) $ do
    let msg = "Found primitive value " ++ show expr ++ " where reference is expected."
    throwIOExecException pos (ftext msg) ""
  case at of
    ArrayInstance l tp -> do
      let javaValueType = jssArrayDagType l tp
      case maybeExpectedType of
        Nothing -> return ()
        Just expectedType -> do
          when (javaValueType /= expectedType) $ do
            let formattedExpr = "\'valueOf(" ++ ppJavaExpr expr ++ ")\'"
            throwInvalidAssignment pos formattedExpr (ppType expectedType)
      return (expr, javaValueType)
    _ ->
      let msg = ftext $ "Type of " ++ show expr ++ " is not an array."
       in throwIOExecException pos msg ""

coercePrimitiveExpr :: Pos
                    -> String
                    -> JSS.Type -- ^ Expected left-hand side type.
                    -> LogicExpr
                    -> BehaviorTypechecker LogicExpr
coercePrimitiveExpr pos lhsName javaType expr = do
  oc <- asks (opCache . mtcGlobalBindings)
  let valueType = typeOfLogicExpr expr
  undefined
  case javaType of
    JSS.BooleanType 
      | valueType == SymBool ->
         let op = iteOp int32DagType
             t = Cns (mkCInt 32 1) int32DagType
             f = Cns (mkCInt 32 0) int32DagType
          in return (Apply op [expr, t, f])
      | valueType == int32DagType -> return expr
    JSS.ByteType 
      | valueType == int8DagType -> 
         return $ Apply (signedExtOp oc (constantWidth 8) 32) [expr]
      | valueType == int32DagType -> return expr
    JSS.CharType 
      | valueType == int16DagType ->
         return $ Apply (unsignedExtOp oc (constantWidth 16) 32) [expr]
      | valueType == int32DagType -> return expr
    JSS.IntType
      | valueType == int32DagType -> return expr
    JSS.LongType
      | valueType == int64DagType -> return expr
    JSS.ShortType 
      | valueType == int16DagType ->
         return $ Apply (signedExtOp oc (constantWidth 16) 32) [expr]
      | valueType == int32DagType -> return expr
    _ -> throwInvalidAssignment pos lhsName (ppType valueType)

typecheckLogicExpr :: Pos -> String -> JSS.Type -> Expr
                   -> BehaviorTypechecker LogicExpr
typecheckLogicExpr lhsPos lhsName lhsType rhsAst =
  -- Check lhs can be assigned value in rhs (coercing if necessary).
  coercePrimitiveExpr lhsPos lhsName lhsType
    =<< runTypechecker (tcLogicExpr rhsAst)

typecheckMixedExpr :: Pos -> String -> JSS.Type -> Expr
                   -> BehaviorTypechecker (MixedExpr, JSS.Type)
typecheckMixedExpr lhsPos lhsName lhsType rhsAst =
  if JSS.isRefType lhsType then do
    rhsExpr <- runTypechecker (tcJavaExpr rhsAst)
    -- Check lhs can be assigned value on rhs.
    let rhsType = jssTypeOfJavaExpr rhsExpr
    cb <- getBTCCodebase
    typeOk <- liftIO $ JSS.isSubtype cb rhsType lhsType
    unless (typeOk) $ do
      throwInvalidAssignment lhsPos lhsName (show rhsType)
    -- Get actual type.
    at <- getActualType (exprPos rhsAst) rhsExpr
    -- Return result.
    return (JE rhsExpr, at)
  else do
    -- Check lhs can be assigned value in rhs (coercing if necessary).
    rhsExpr <- typecheckLogicExpr lhsPos lhsName lhsType rhsAst
    return (LE rhsExpr, PrimitiveType lhsType)
-}

-- Command utilities {{{2

-- | Return commands in behavior in order they appeared in spec.
bsCommands :: BehaviorSpec s -> [BehaviorCommand s]
bsCommands = reverse . bsReversedCommands

-- | Add command to typechecker.
addCommand :: BehaviorCommand s -> BehaviorTypechecker s ()
addCommand bc = modifyPaths $ \bs ->
  bs { bsReversedCommands = bc : bsReversedCommands bs }

bsAddCommand :: BehaviorCommand s -> BehaviorSpec s -> BehaviorSpec s
bsAddCommand bc bs =
  bs { bsReversedCommands = bc : bsReversedCommands bs }

-- | Make sure expr can be assigned a postcondition.
checkValuePostconditionTarget :: Pos -> JavaExpr -> BehaviorTypechecker s ()
checkValuePostconditionTarget pos (CC.Term expr) = do
  case expr of
    Local _ _ _ -> 
      let msg = "Cannot defined post-conditions on values local to method."
       in throwIOExecException pos (ftext msg) ""
    InstanceField{} -> return ()

recordLogicAssertion :: Pos -> JavaExpr -> LogicExpr s -> BehaviorTypechecker s ()
recordLogicAssertion pos lhs rhs =
  modifyPaths $ \bs ->
    bs { bsLogicAssignments = (pos, lhs, rhs) : bsLogicAssignments bs }

-- resolveDecl {{{1

-- | Code for parsing a method spec declaration.
{-
resolveDecl :: [BehaviorDecl (SharedTerm s)] -> BehaviorTypechecker s ()
resolveDecl [] = return ()
resolveDecl (VarDecl _ exprAstList typeAst:r) = do
  -- Get actual type.
  at <- runTypechecker $ tcActualType typeAst
  -- Parse expressions.
  cb <- getBTCCodebase
  forM_ exprAstList $ \exprAst -> do
    -- Typecheck Java expression.
    let pos = exprPos exprAst
    expr <- runTypechecker $ tcJavaExpr exprAst
    -- Check that type of exprAst and the type of tp are compatible.
    do let exprType = jssTypeOfJavaExpr expr
           tgtType = jssTypeOfActual at
       typeOk <- liftIO $ JSS.isSubtype cb tgtType exprType
       unless typeOk $
         let msg = ftext ("The expression " ++ show expr ++ " is incompatible with")
                     <+> ppASTJavaType typeAst <> char '.'
          in throwIOExecException pos msg ""
    -- Record actual type.
    checkActualTypeUndefined pos expr
    recordActualType pos expr at
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (MethodLet pos lhs rhsAst:r) = do
  -- Typecheck rhs.
  rhsExpr <- runTypechecker $ tcMixedExpr rhsAst
  -- Record variable binding.
  do bts <- get
     let locals = btsLetBindings bts
     case Map.lookup lhs locals of
       Just (prevPos,_) -> throwVarIsPreviouslyDefined pos prevPos lhs
       Nothing -> return ()
     put bts { btsLetBindings = Map.insert lhs (pos,rhsExpr) locals }
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (MayAlias _ exprAstList:r) = do
  -- Record may alias relation in each path.
  exprList <- forM exprAstList $ \exprAst -> do
     (expr,_) <- typecheckRecordedJavaExpr TC.tcJavaExpr exprAst
     -- Check expression is a reference.
     unless (JSS.isRefType (TC.jssTypeOfJavaExpr expr)) $ do
       let msg = "\'mayAlias\' provided a non-reference value."
        in throwIOExecException (exprPos exprAst) (ftext msg) ""
     return expr
  -- Update each path with new alias.
  modifyPaths $ \bs -> bs { bsMayAliasClasses = exprList:bsMayAliasClasses bs }
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (AssertPred pos ast:r) = do
  -- Typecheck expression.
  expr <- runTypechecker $ TC.tcLogicExpr ast
  -- Check expr is a Boolean
  checkLogicExprIsPred (exprPos ast) expr
  -- Add assertion.
  addCommand (AssertPred pos expr)
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (AssertImp pos lhsAst@(ApplyExpr _ "valueOf" _) rhsAst:r) = do
  -- Typecheck rhs
  rhsExpr <- runTypechecker $ TC.tcLogicExpr rhsAst
  let rhsType = TC.typeOfLogicExpr rhsExpr
  -- Typecheck lhs
  (lhsExpr, _) <- typecheckValueOfLhs lhsAst (Just rhsType)
  -- Record assertion.
  recordLogicAssertion pos lhsExpr rhsExpr
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (AssertImp pos lhsAst rhsAst:r) = do
  -- Typecheck lhs expression.
  let lhsPos = exprPos lhsAst
  lhsExpr <- runTypechecker $ TC.tcJavaExpr lhsAst
  let lhsName = "\'" ++ show lhsExpr ++ "\'"
  let lhsType = TC.jssTypeOfJavaExpr lhsExpr
  -- Typecheck right-hand side.
  if JSS.isRefType lhsType then do
    (rhsExpr,rhsActualType) <- typecheckRecordedJavaExpr TC.tcJavaExpr rhsAst
    -- Check lhs can be assigned value on rhs.
    let rhsJSSType = TC.jssTypeOfJavaExpr rhsExpr
    cb <- getBTCCodebase
    typeOk <- liftIO $ JSS.isSubtype cb rhsJSSType lhsType
    unless (typeOk) $ do
      throwInvalidAssignment lhsPos lhsName (show rhsJSSType)
    -- Record actual type.
    recordActualType lhsPos lhsExpr rhsActualType
    -- Record must alias assertion.
    modifyPaths $ \bs ->
      bs { bsMustAliasSet = CC.insertEquation lhsExpr rhsExpr (bsMustAliasSet bs) }
  else do
    -- Check lhs can be assigned value in rhs (coercing if necessary).
    rhsExpr <- typecheckLogicExpr lhsPos lhsName lhsType rhsAst
    -- Record actual type.
    recordActualType lhsPos lhsExpr (TC.PrimitiveType lhsType)
    -- Record value assertion.
    recordLogicAssertion pos lhsExpr rhsExpr
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (EnsureImp pos lhsAst@(ApplyExpr _ "valueOf" _) rhsAst:r) = do
  -- Typecheck rhs
  rhsExpr <- runTypechecker $ TC.tcLogicExpr rhsAst
  let rhsType = TC.typeOfLogicExpr rhsExpr
  -- Typecheck lhs
  (lhsExpr, _) <- typecheckValueOfLhs lhsAst (Just rhsType)
  -- Update postcondition.
  addCommand (EnsureArray pos lhsExpr rhsExpr)
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (EnsureImp _ astLhsExpr astRhsExpr:r) = do
  -- Typecheck lhs expression.
  let lhsPos = exprPos astLhsExpr
  (lhsExpr,_) <- typecheckRecordedJavaExpr TC.tcJavaExpr astLhsExpr
  let lhsName = "\'" ++ show lhsExpr ++ "\'"
  let lhsType = TC.jssTypeOfJavaExpr lhsExpr
  -- Typecheck right hand side.
  (rhsExpr,_) <- typecheckMixedExpr lhsPos lhsName lhsType astRhsExpr
  -- Add postcondition based on left-hand side expression.
  checkValuePostconditionTarget lhsPos lhsExpr
  case lhsExpr of
    CC.Term (TC.InstanceField ref f) ->
      addCommand (EnsureInstanceField lhsPos ref f rhsExpr)
    _ -> error "internal: Unexpected expression"
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (Modify _ astExprs:r) = mapM_ resolveExpr astExprs >> resolveDecl r
  where resolveExpr ast@(ApplyExpr _ "valueOf" _) = do
          (expr, tp) <- typecheckValueOfLhs ast Nothing
          -- Add modify statement.
          addCommand $ ModifyArray expr tp
        resolveExpr ast = do
          ---- Typecheck ast
          let pos = exprPos ast
          (expr, _) <- typecheckRecordedJavaExpr TC.tcJavaExpr ast
          ---- Check this type is valid for a modifies clause.
          let exprType = TC.jssTypeOfJavaExpr expr
          when (JSS.isRefType exprType)  $ do
            let msg = "Modify may not refer to reference types."
            throwIOExecException pos (ftext msg) ""
          -- Add modify statement.
          checkValuePostconditionTarget pos expr
          case expr of
            CC.Term (TC.InstanceField ref f) -> 
              addCommand (ModifyInstanceField ref f)
            _ -> error "internal: Unexpected expression"
resolveDecl (Return pos ast:r) = do
  method <- asks mtcMethod
  case JSS.methodReturnType method of
    Nothing ->
      let msg = "Return value specified for \'" ++ JSS.methodName method 
                   ++ "\', but method returns \'void\'."
       in throwIOExecException pos (ftext msg) ""
    Just returnType -> do
      -- Typecheck expression.
      (expr,_) <- typecheckMixedExpr (exprPos ast) "The return value" returnType ast
      -- Record return is set.
      do bts <- get
         when (btsReturnSet bts) $ do
           let msg = "Multiple return values specified in a single method spec."
           throwIOExecException pos (ftext msg) ""
         put bts { btsReturnSet = True }
      -- Add return statement.
      addCommand (Return expr)
  -- Resolve remaining declarations.
  resolveDecl r
resolveDecl (MethodIf p c t:r) =
  resolveDecl (MethodIfElse p c t (Block []):r)
resolveDecl (MethodIfElse pos condAst t f:r) = do
  -- Typecheck condition.
  cond <- runTypechecker $ TC.tcLogicExpr condAst
  checkLogicExprIsPred (exprPos condAst) cond
  -- Branch execution.
  bts <- get
  tBts <- lift $ flip execStateT bts $ do
    -- Add assumption.
    addCommand (AssumePred cond)
    -- Resolve commands.
    resolveDecl [t]
  fBts <- lift $ flip execStateT bts $ do
    let negCond = TC.Apply bNotOp [cond]
    addCommand $ AssumePred negCond
    resolveDecl [f]
  when (btsReturnSet tBts /= btsReturnSet fBts) $ do
    let msg = "Return value set in one branch, but not the other."
        res = "Please ensure that both branches set the return value."
     in throwIOExecException pos (ftext msg) res
  put BTS { -- Use originl local type map and let bindings.
            btsPC = btsPC bts
          , btsActualTypeMap = btsActualTypeMap bts
          , btsLetBindings = btsLetBindings bts
            -- Use return set from tBts.
          , btsReturnSet = btsReturnSet tBts
            -- Union paths.
          , btsPaths = btsPaths tBts ++ btsPaths fBts
          }
  resolveDecl r
resolveDecl (Block ast:r) = do
  oldBts <- get
  -- Resolve declarations in block.
  resolveDecl ast
  -- Forget concrete types and let bindings.
  modify $ \bts -> bts { btsActualTypeMap = btsActualTypeMap oldBts
                       , btsLetBindings = btsLetBindings oldBts }
  -- Resolve remaining declarations.
  resolveDecl r
-}

-- CCSet utilities {{1

-- | 
splitClass :: (CC.OrdFoldable f, CC.Traversable f)
           => [CC.Term f] -> Set (CCSet f) -> Set (CCSet f)
splitClass [] sets = sets
splitClass (h:l) sets = splitClass l (sets `Set.union` newSets)
 where insertEqualToH t = Set.map (CC.insertEquation h t) sets
       newSets = Set.unions (map insertEqualToH l)

-- | Returns all congruence-closed sets generated by the may alias
-- configurations.
mayAliases :: (CC.OrdFoldable f, CC.Traversable f)
           => [[CC.Term f]] -> CCSet f -> Set (CCSet f)
mayAliases l s = foldr splitClass (Set.singleton s) l


initMethodSpec :: Pos -> JSS.Codebase -> String -> String
               -> IO (MethodSpecIR s)
initMethodSpec pos cb cname mname = do
  let cname' = JP.dotsToSlashes cname -- TODO: necessary?
  thisClass <- lookupClass cb pos cname'
  (methodClass,method) <- findMethod cb pos mname thisClass
  superClasses <- JSS.supers cb thisClass
  let this = thisJavaExpr methodClass
      initTypeMap | JSS.methodIsStatic method = Map.empty
                  | otherwise = Map.singleton this (JSS.ClassType (JSS.className methodClass))
      initBS = BS { bsLoc = JSS.BreakEntry
                  , bsActualTypeMap = initTypeMap
                  , bsMustAliasSet =
                      if JSS.methodIsStatic method then
                        CC.empty
                      else
                        CC.insertTerm this CC.empty
                  , bsMayAliasClasses = []
                  , bsLogicAssignments = []
                  , bsReversedCommands = []
                  }
      initMS = MSIR { specPos = pos
                    , specThisClass = thisClass
                    , specMethodClass = methodClass
                    , specMethod = method
                    , specInitializedClasses =
                        map JSS.className superClasses
                    , specBehaviors = initBS
                    , specValidationPlan = Skip
                    }
  return initMS



-- resolveBehaviorSpecs {{{1

{-
resolveBehaviorSpecs :: MethodTypecheckContext s
                     -> JSS.Breakpoint
                     -> [BehaviorDecl (SharedTerm s)]
                     -> IO (BehaviorTypecheckState s)
resolveBehaviorSpecs mtc loc cmds = do
  let method = mtcMethod mtc
  let this = thisJavaExpr (mtcClass mtc)
  let initTypeMap | JSS.methodIsStatic method = Map.empty
                  | otherwise = 
                      Map.singleton this (ClassInstance (mtcClass mtc))
      initPath = BS { bsLoc = loc
                    , bsActualTypeMap = initTypeMap
                    , bsMustAliasSet = 
                        if JSS.methodIsStatic method then
                          CC.empty
                        else
                          CC.insertTerm this CC.empty
                    , bsMayAliasClasses = []
                    , bsLogicAssignments = []
                    , bsReversedCommands = []
                    }
      initBts = BTS { btsLoc = loc
                    , btsActualTypeMap = initTypeMap
                    , btsLetBindings = Map.empty
                    , btsPaths = [initPath]
                    , btsReturnSet = False
                    }
  bts <- undefined {- flip runReaderT mtc $
           flip execStateT initBts $ do
             resolveDecl cmds -}
  -- Check expressions that may alias to verify they have equivalent types.
  mapM_ (bsCheckAliasTypes (mtcPos mtc)) (btsPaths bts)
  if loc == JSS.BreakEntry then
    -- TODO: Check all arguments are defined.
    return ()
  else
    -- TODO: Check all expected locals are defined.
    return ()
  -- Ensure returns is set if method has return value.
  when (isJust (JSS.methodReturnType method) && not (btsReturnSet bts)) $
    let msg = "The Java method \'" ++ JSS.methodName method
                     ++ "\' has a return value, but the spec does not define it."
     in throwIOExecException (mtcPos mtc) (ftext msg) ""
  -- Return paths parsed from this spec.
  return bts
-}

-- resolveValidationPlan {{{1

-- | Commands issued to verify method.
data VerifyCommand
   = Rewrite
   | ABC
   | SmtLib (Maybe Int) (Maybe String) -- version, file
   | Yices (Maybe Int)
   -- | Expand Pos Op [LogicExpr s] (SharedTerm s)
    -- | Enable use of a rule or extern definition.
   | VerifyEnable String
     -- | Disable use of a rule or extern definition.
   | VerifyDisable String
   | VerifyAt JSS.PC [VerifyCommand]
 deriving (Show)

data ValidationPlan
  = Skip
  | QuickCheck Integer (Maybe Integer)
  | GenBlif (Maybe FilePath)
  | RunVerify [VerifyCommand]
  deriving (Show)

checkRuleIsDefined :: MonadIO m => Pos -> String -> Set String -> m ()
checkRuleIsDefined pos nm ruleNames = do
  when (Set.notMember nm ruleNames) $ do
    let msg = "Unknown rule or definition " ++ show nm ++ "."
    throwIOExecException pos (ftext msg) ""

data VerifyTypecheckerState s = VTS {
         vtsMTC :: MethodTypecheckContext s
       , vtsBehaviors :: Map JSS.PC (BehaviorTypecheckState s)
       , vtsRuleNames :: Set String
         -- | Current PC (if inside at command).
       , vtsLine :: Maybe (JSS.Breakpoint, BehaviorTypecheckState s)
       }

type VerifyTypechecker s = StateT (VerifyTypecheckerState s) IO

{-
resolveVerifyCommand :: VerifyCommand -> VerifyTypechecker [VerifyCommand]
resolveVerifyCommand cmd =
  case cmd of
    ABC -> return [ABC]
    Rewrite -> return [Rewrite]
    SmtLib v f -> return [SmtLib v f]
    Yices v -> return [Yices v]
    Expand ast -> do
      -- Evaluate expression.
      mtc <- gets vtsMTC
      mpc <- gets vtsPC
      let cfg = case mpc of
                  Just (_,bts) -> behaviorTypecheckerConfig mtc bts
                  _ -> TCC { globalBindings = mtcGlobalBindings mtc
                           , localBindings = Map.empty
                           , methodInfo = Nothing
                           }
      let pos = exprPos ast
      expr <- liftIO $ tcLogicExpr ast cfg
      case expr of
        Apply op args -> 
          case opDefDefinition (opDef op) of
            Just rhs -> return [Expand pos op args rhs]
            _ -> let msg = show (opName op) ++ " is not a defined operation."
                  in throwIOExecException pos (ftext msg) ""
        _ -> let msg = "Expand must be given an application to expand."
              in throwIOExecException pos (ftext msg) ""
    VerifyEnable pos nm -> do
      ruleNames <- gets vtsRuleNames
      checkRuleIsDefined pos nm ruleNames
      return [VerifyEnable nm]
    VerifyDisable pos nm -> do
      ruleNames <- gets vtsRuleNames
      checkRuleIsDefined pos nm ruleNames
      return [VerifyDisable nm]
    VerifyAt pos astPC astCmd -> do
      m <- gets (mtcMethod . vtsMTC)
      pc <- typecheckPC pos m astPC
      mOldPC <- gets vtsPC
      case mOldPC of
        Just (oldPC,_) | oldPC /= pc -> do
          let msg = "A different verification PC already specified."
          throwIOExecException pos (ftext msg) ""
        _ -> return ()
      -- Get behavior
      behaviors <- gets vtsBehaviors
      case Map.lookup pc behaviors of
        Nothing ->
          let msg = "No behavior is specified at PC " ++ show pc ++ "."
           in throwIOExecException pos (ftext msg) ""
        Just bts -> 
          withStateT (\s -> s { vtsPC = Just (pc,bts) }) $ do
            cmds <- resolveVerifyCommand astCmd
            return [VerifyAt pc cmds]
    VerifyBlock cmds ->
      concat <$> mapM resolveVerifyCommand cmds
-}

{-
resolveValidationPlan :: Set String -- ^ Names of rules in spec.
                      -> MethodTypecheckContext
                      -> Map JSS.PC BehaviorTypecheckState
                      -> [MethodSpecDecl] -> IO ValidationPlan
resolveValidationPlan ruleNames mtc allBehaviors decls = 
  case [ (p,d) | SpecPlan p d <- decls ] of
    [] -> return $ Skip
    [(_,Blif mpath)] -> return $ GenBlif mpath
    [(_,QuickCheck n mlimit)] -> return $ QuickCheck n mlimit
    [(_,Verify cmds)] ->
       let initVTS = VTS { vtsMTC = mtc
                         , vtsBehaviors = allBehaviors
                         , vtsRuleNames = ruleNames
                         , vtsPC = Nothing
                         }
        in RunVerify <$> evalStateT (resolveVerifyCommand cmds) initVTS
    _:(pos,_):_ ->
      let msg = "Multiple validation approaches set in method specification."
       in throwIOExecException pos (ftext msg) ""
-}

-- MethodSpecIR {{{1

data MethodSpecIR s = MSIR {
    specPos :: Pos
    -- | Class used for this instance.
  , specThisClass :: JSS.Class
    -- | Class where method is defined.
  , specMethodClass :: JSS.Class
    -- | Method to verify.
  , specMethod :: JSS.Method
    -- | Class names expected to be initialized using JVM "/" separators.
    -- (as opposed to Java "." path separators). Currently this is set
    -- to the list of superclasses of specThisClass.
  , specInitializedClasses :: [String]
    -- | Behavior specifications for method at different PC values.
    -- A list is used because the behavior may depend on the inputs.
  , specBehaviors :: BehaviorSpec s -- Map JSS.Breakpoint [BehaviorSpec s]
    -- | Describes how the method is expected to be validatioed.
  , specValidationPlan :: ValidationPlan
  } deriving (Show)

-- | Return user printable name of method spec (currently the class + method name).
specName :: MethodSpecIR s -> String
specName ir =
 let clName = JSS.className (specThisClass ir)
     mName = JSS.methodName (specMethod ir)
  in JSS.slashesToDots clName ++ ('.' : mName)

specAddVarDecl :: JavaExpr -> JSS.Type
               -> MethodSpecIR s -> MethodSpecIR s
specAddVarDecl expr jt ms = ms { specBehaviors = bs' }
  where bs = specBehaviors ms
        bs' = bs { bsActualTypeMap =
                     Map.insert expr jt (bsActualTypeMap bs) }

specAddAliasSet :: [JavaExpr] -> MethodSpecIR s -> MethodSpecIR s
specAddAliasSet exprs ms = ms { specBehaviors = bs' }
  where bs = specBehaviors ms
        bs' = bs { bsMayAliasClasses = exprs : bsMayAliasClasses bs }

specAddBehaviorCommand :: BehaviorCommand s
                       -> MethodSpecIR s -> MethodSpecIR s
specAddBehaviorCommand bc ms =
  ms { specBehaviors = bsAddCommand bc (specBehaviors ms) }


-- | Interprets AST method spec commands to construct an intermediate
-- representation that
resolveMethodSpecIR :: GlobalBindings s
                    -> Set String -- ^ Names of rules in spec.
                    -> Pos
                    -> JSS.Class
                    -> String
                    -> [BehaviorSpec s]
                    -> IO (MethodSpecIR s)
resolveMethodSpecIR gb ruleNames pos thisClass mName cmds = do
  let cb = codeBase gb
  (methodClass,method) <- findMethod cb pos mName thisClass
  let mtc = MTC { mtcPos = pos
                , mtcGlobalBindings = gb
                , mtcClass = thisClass
                , mtcMethod = method
                , mtcRuleNames = ruleNames
                }
  -- Get list of initial superclasses.
  superClasses <- JSS.supers cb thisClass
  -- Resolve behavior spec for PC 0.
  methodBehavior <- undefined -- resolveBehaviorSpecs mtc JSS.BreakEntry cmds -- FIXME
  --  Resolve behavior specs at other PCs.
  -- FIXME: not yet implemented
  {-
  let specAtCmds = [ (specPos, pc, bcmds) | SpecAt specPos pc bcmds <- cmds ]
  localBehaviors <- forM specAtCmds $ \(specPos,astPC,bcmds) -> do
      pc <- typecheckPC specPos method astPC
      bs <- resolveBehaviorSpecs mtc pc bcmds
      return (pc, bs)
      -}
  -- TODO: Check that no duplicates appear in local behavior specifications.
  let allBehaviors = Map.fromList $ (JSS.BreakEntry, methodBehavior) : [] -- localBehaviors
  -- Resolve verification plan.
  plan <- undefined -- resolveValidationPlan ruleNames mtc allBehaviors cmds
  -- Return IR.
  return MSIR { specPos = pos
              , specThisClass = thisClass
              , specMethodClass = methodClass
              , specMethod = method
              , specInitializedClasses = map JSS.className superClasses
              , specBehaviors = methodBehavior -- Map.map btsPaths allBehaviors
              , specValidationPlan = plan
              }
