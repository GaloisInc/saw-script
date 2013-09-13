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
{-# LANGUAGE ScopedTypeVariables #-}
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
  --, resolveMethodSpecIR
    -- * Method behavior.
  , BehaviorSpec
  , bsLoc
  , bsRefExprs
  , bsMayAliasSet
  , RefEquivConfiguration
  , bsRefEquivClasses
  , bsActualTypeMap
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
--import Control.Monad.Reader
--import Control.Monad.State
import Data.Graph.Inductive (scc, Gr, mkGraph)
import Data.List (intercalate, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (isJust, catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
--import Text.PrettyPrint.Leijen hiding ((<$>))
import qualified Language.JVM.Common as JP

--import Verinf.Symbolic

import qualified Verifier.Java.Codebase as JSS
import qualified Verifier.Java.Common as JSS
--import qualified Verifier.LLVM.Codebase as LSS
--import qualified Data.JVM.Symbolic.AST as JSS

import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.CongruenceClosure (CCSet)
import SAWScript.JavaExpr
import SAWScript.Utils

-- ExprActualTypeMap {{{1

-- | Maps Java expressions for references to actual type.
type ExprActualTypeMap = Map JavaExpr JavaActualType

-- Alias definitions {{{1

type JavaExprEquivClass = [JavaExpr]

-- | Returns a name for the equivalence class.
ppJavaExprEquivClass :: JavaExprEquivClass -> String
ppJavaExprEquivClass [] = error "internal: ppJavaExprEquivClass"
ppJavaExprEquivClass [expr] = ppJavaExpr expr
ppJavaExprEquivClass cl = "{ " ++ intercalate ", " (map ppJavaExpr (sort cl)) ++ " }"

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
   | ModifyArray JavaExpr JavaActualType
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

{-
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
-}

type RefEquivConfiguration = [(JavaExprEquivClass, JavaActualType)]

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
  [ e | (e, PrimitiveType _) <- Map.toList (bsActualTypeMap bs) ]
 
asJavaExpr :: Map String JavaExpr -> LogicExpr s -> Maybe JavaExpr
asJavaExpr m (asCtor -> Just (i, [e])) =
  case e of
    (asStringLit -> Just s) | i == parseIdent "Java.mkValue" -> Map.lookup s m
    _ -> Nothing
asJavaExpr _ _ = Nothing

bsLogicEqs :: Map String JavaExpr -> BehaviorSpec s -> [(JavaExpr, JavaExpr)]
bsLogicEqs m bs =
  [ (lhs,rhs') | (_,lhs,rhs) <- bsLogicAssignments bs
               , let Just rhs' = asJavaExpr m rhs]

-- | Returns logic assignments to equivance class.
bsAssignmentsForClass :: Map String JavaExpr -> BehaviorSpec s -> JavaExprEquivClass
                      -> [LogicExpr s]
bsAssignmentsForClass m bs cl = res 
  where s = Set.fromList cl
        res = [ rhs 
              | (_,lhs,rhs) <- bsLogicAssignments bs
              , Set.member lhs s
              , not (isJust (asJavaExpr m rhs)) ]

-- | Retuns ordering of Java expressions to corresponding logic value.
bsLogicClasses :: forall s.
                  SharedContext s
               -> Map String JavaExpr
               -> BehaviorSpec s
               -> RefEquivConfiguration
               -> IO (Maybe [(JavaExprEquivClass, SharedTerm s, [LogicExpr s])])
bsLogicClasses sc m bs cfg = do
  let allClasses = CC.toList
                   -- Add logic equations.
                   $ flip (foldr (uncurry CC.insertEquation)) (bsLogicEqs m bs)
                   -- Add primitive expression.
                   $ flip (foldr CC.insertTerm) (bsPrimitiveExprs bs)
                   -- Create initial set with references.
                   $ CC.fromList (map fst cfg)
  logicClasses <- (catMaybes <$>) $
                  forM allClasses $ \(cl@(e:_)) -> do
                    case Map.lookup e (bsActualTypeMap bs) of
                      Just at -> do
                        mtp <- logicTypeOfActual sc at
                        case mtp of
                          Just tp -> return (Just (cl, tp))
                          Nothing -> return Nothing
                      Nothing -> return Nothing
  let v = V.fromList logicClasses
      -- Create nodes.
      grNodes = [0..] `zip` logicClasses
      -- Create edges
      exprNodeMap = Map.fromList [ (e,n) | (n,(cl,_)) <- grNodes, e <- cl ]
      grEdges = [ (s,t,()) | (t,(cl,_)) <- grNodes
                           , src:_ <- [bsAssignmentsForClass m bs cl]
                           , se <- Set.toList (logicExprJavaExprs src)
                           , let Just s = Map.lookup se exprNodeMap ]
      -- Compute strongly connected components.
      components = scc (mkGraph grNodes grEdges :: Gr (JavaExprEquivClass, SharedTerm s) ())
  return $ if all (\l -> length l == 1) components
             then Just [ (cl, at, bsAssignmentsForClass m bs cl)
                       | [n] <- components
                       , let (cl,at) = v V.! n ]
             else Nothing

-- Command utilities {{{2

-- | Return commands in behavior in order they appeared in spec.
bsCommands :: BehaviorSpec s -> [BehaviorCommand s]
bsCommands = reverse . bsReversedCommands

bsAddCommand :: BehaviorCommand s -> BehaviorSpec s -> BehaviorSpec s
bsAddCommand bc bs =
  bs { bsReversedCommands = bc : bsReversedCommands bs }

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


initMethodSpec :: Pos -> JSS.Codebase
               -> String -> String
               -> IO (MethodSpecIR s)
initMethodSpec pos cb cname mname = do
  let cname' = JP.dotsToSlashes cname
  thisClass <- lookupClass cb pos cname'
  (methodClass,method) <- findMethod cb pos mname thisClass
  superClasses <- JSS.supers cb thisClass
  let this = thisJavaExpr methodClass
      initTypeMap | JSS.methodIsStatic method = Map.empty
                  | otherwise = Map.singleton this (ClassInstance methodClass)
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
  }

-- | Return user printable name of method spec (currently the class + method name).
specName :: MethodSpecIR s -> String
specName ir =
 let clName = JSS.className (specThisClass ir)
     mName = JSS.methodName (specMethod ir)
  in JSS.slashesToDots clName ++ ('.' : mName)

specAddVarDecl :: JavaExpr -> JavaActualType
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
