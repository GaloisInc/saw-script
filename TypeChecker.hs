{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}
module SAWScript.TypeChecker 
  ( SpecJavaRef(..)
  , ppSpecJavaRef
  , getJSSTypeOfSpecRef
  , parseExprType
  , TypedExpr(..)
  , getTypeOfTypedExpr
  , TCConfig(..)
  , tcExpr
  ) where

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import qualified JavaParser as JSS
import qualified SAWScript.MethodAST as AST
import SAWScript.Utils
import Symbolic
import Utils.IOStateT

-- SpecJavaRef {{{1

-- | Identifies a reference to a Java value.
data SpecJavaRef 
  = SpecThis
  | SpecArg Int
  | SpecField SpecJavaRef JSS.Field

instance Eq SpecJavaRef where
  SpecThis == SpecThis = True
  SpecArg i == SpecArg j = i == j
  SpecField r1 f1 == SpecField r2 f2 = r1 == r2 && JSS.fieldName f1 == JSS.fieldName f2
  _ == _ = False

instance Ord SpecJavaRef where
  SpecThis `compare` SpecThis = EQ
  SpecThis `compare` _ = LT
  _ `compare` SpecThis = GT
  SpecArg i `compare` SpecArg j = i `compare` j
  SpecArg _ `compare` _ = LT
  _ `compare` SpecArg _ = GT
  SpecField r1 f1 `compare` SpecField r2 f2 = 
    case r1 `compare` r2 of 
      EQ -> JSS.fieldName f1 `compare` JSS.fieldName f2
      r -> r

instance Show SpecJavaRef where
  show SpecThis = "this"
  show (SpecArg i) = "args[" ++ show i ++ "]"
  show (SpecField r f) = show r ++ "." ++ JSS.fieldName f

-- | Pretty print SpecJavaRef
ppSpecJavaRef :: SpecJavaRef -> String
ppSpecJavaRef SpecThis = "this"
ppSpecJavaRef (SpecArg i) = "args[" ++ show i ++ "]"
ppSpecJavaRef (SpecField r f) = ppSpecJavaRef r ++ ('.' : JSS.fieldName f)

-- | Returns JSS Type of SpecJavaRef
-- N.B. The JSS.Type may refer to a class that does not exist in the codebase.
getJSSTypeOfSpecRef :: -- | Name of class for this object
                       -- (N.B. method may be defined in a subclass of this class).
                       String
                    -> V.Vector JSS.Type -- ^ Parameters of method that we are checking
                    -> SpecJavaRef -- ^ Spec Java reference to get type of.
                    -> JSS.Type -- ^ Java type (which must be a class or array type).
getJSSTypeOfSpecRef clName _p SpecThis = JSS.ClassType clName
getJSSTypeOfSpecRef _cl params (SpecArg i) = params V.! i
getJSSTypeOfSpecRef _cl _p (SpecField _ f) = JSS.fieldType f

-- Typecheck expression types {{{1

-- | Convert expression type from AST into WidthExpr
parseExprWidth :: AST.ExprWidth -> WidthExpr
parseExprWidth (AST.WidthConst _ i) = constantWidth (Wx i)
parseExprWidth (AST.WidthVar _ nm) = varWidth nm
parseExprWidth (AST.WidthAdd _ u v) = addWidth (parseExprWidth u) (parseExprWidth v)

-- | Convert expression type from AST into DagType.
-- Uses Executor monad for parsing record types.
parseExprType :: AST.ExprType -> OpSession DagType
parseExprType (AST.BitType _) = return SymBool
parseExprType (AST.BitvectorType _ w) = return $ SymInt (parseExprWidth w)
parseExprType (AST.Array _ w tp) =
  fmap (SymArray (parseExprWidth w)) $ parseExprType tp
parseExprType (AST.Record _ fields) = do
  let names = [ nm | (_,nm,_) <- fields ]
  def <- getStructuralRecord (Set.fromList names)
  tps <- mapM parseExprType [ tp | (_,_,tp) <- fields ]
  let sub = emptySubst { shapeSubst = Map.fromList $ names `zip` tps }
  return $ SymRec def sub
parseExprType (AST.ShapeVar _ v) = return (SymShapeVar v)

-- TypedExpr {{{1

-- | A type-checked expression which appears insider a global let binding,
-- method declaration, or rule term.
data TypedExpr
   = TypedApply Op [TypedExpr]
   | TypedCns CValue DagType
   | TypedJavaValue SpecJavaRef DagType
   | TypedVar String DagType
   deriving (Show)

-- | Return type of a typed expression.
getTypeOfTypedExpr :: TypedExpr -> DagType
getTypeOfTypedExpr (TypedVar _ tp) = tp
getTypeOfTypedExpr (TypedCns _ tp) = tp
getTypeOfTypedExpr (TypedJavaValue _ tp) = tp
getTypeOfTypedExpr (TypedApply op _) = opResultType op

-- | Additional information used by parseExpr to control parseExpr.
data TCConfig = TCC {
         localBindings :: Map String TypedExpr
       , globalCnsBindings :: Map String (CValue,DagType)
       , opBindings :: Map String OpDef
       }

-- | Check argument count matches expected length.
checkArgCount :: MonadIO m => Pos -> String -> [TypedExpr] -> Int -> m ()
checkArgCount pos nm (length -> foundOpCnt) expectedCnt = do
  unless (expectedCnt == foundOpCnt) $
    let msg = "Incorrect number of arguments to \'" ++ nm ++ "\'.  "
                ++ show expectedCnt ++ " arguments were expected, but "
                ++ show foundOpCnt ++ " arguments were found."
     in throwIOExecException pos (ftext msg) ""

-- | Convert an AST expression from parser into a typed expression.
tcExpr :: TCConfig -> AST.Expr -> OpSession TypedExpr
tcExpr _st (AST.TypeExpr pos (AST.ConstantInt _ i) astTp) = do
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
tcExpr TCC { localBindings, globalCnsBindings } (AST.Var pos name) = do
  case Map.lookup name localBindings of
    Just res -> return res
    Nothing -> do
      case Map.lookup name globalCnsBindings of
        Just (c,tp) -> return $ TypedCns c tp
        Nothing -> 
          let msg = "Unknown variable \'" ++ name ++ "\'."
           in throwIOExecException pos (ftext msg) ""
tcExpr st (AST.ApplyExpr appPos "join" astArgs) = do
  args <- mapM (tcExpr st) astArgs
  checkArgCount appPos "join" args 1
  let argType = getTypeOfTypedExpr (head args)
  case argType of
    SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w)) -> do
      op <- joinOpDef l w
      return $ TypedApply (groundOp op) args
    _ -> let msg = "Illegal arguments and result type given to \'join\'.  "
                   ++ "SAWScript currently requires that the argument is ground"
                   ++ " array of integers. "
          in throwIOExecException appPos (ftext msg) ""
tcExpr st (AST.TypeExpr _ (AST.ApplyExpr appPos "split" astArgs) astResType) = do
  args <- mapM (tcExpr st) astArgs
  checkArgCount appPos "split" args 1
  resType <- parseExprType astResType
  let argType = getTypeOfTypedExpr (head args)
  case (argType, resType) of
    (  SymInt (widthConstant -> Just wl)
     , SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w))) 
      | wl == l * w -> do
        op <- splitOpDef l w
        return $ TypedApply (groundOp op) args
    _ -> let msg = "Illegal arguments and result type given to \'split\'.  "
                   ++ "SAWScript currently requires that the argument is ground type, "
                   ++ "and an explicit result type is given."
          in throwIOExecException appPos (ftext msg) ""
tcExpr st (AST.ApplyExpr appPos nm astArgs) = do
  case Map.lookup nm (opBindings st) of
    Nothing ->
      let msg = "Unknown operator " ++ nm ++ "."
          res = "Please check that the operator is correct."
       in throwIOExecException appPos (ftext msg) res
    Just opDef -> do
      args <- mapM (tcExpr st) astArgs
      let defArgTypes = opDefArgTypes opDef
      checkArgCount appPos nm args (V.length defArgTypes)
      let defTypes = V.toList defArgTypes
      let argTypes = map getTypeOfTypedExpr args
      case matchSubst (defTypes `zip` argTypes) of
        Nothing -> 
          let msg = "Illegal arguments and result type given to \'" ++ nm ++ "\'."
           in throwIOExecException appPos (ftext msg) ""
        Just sub -> return $ TypedApply (mkOp opDef sub) args
--TODO: Add more typechecking equations for parsing expressions.
tcExpr st e =
  error $ "internal: tcExpr given illegal type " ++ show e

