{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE ViewPatterns       #-}
module SAWScript.TypeChecker
  ( SpecJavaExpr(..)
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

-- SpecJavaExpr {{{1

-- | Identifies a reference to a Java value.
data SpecJavaExpr
  = SpecThis String
  | SpecArg Int JSS.Type
  | SpecField SpecJavaExpr JSS.Field

instance Eq SpecJavaExpr where
  SpecThis _      == SpecThis _      = True
  SpecArg i _     == SpecArg j _     = i == j
  SpecField r1 f1 == SpecField r2 f2 = r1 == r2 && JSS.fieldName f1 == JSS.fieldName f2
  _               == _               = False

instance Ord SpecJavaExpr where
  SpecThis _      `compare` SpecThis _      = EQ
  SpecThis _      `compare` _               = LT
  _               `compare` SpecThis _      = GT
  SpecArg i _     `compare` SpecArg j _     = i `compare` j
  SpecArg _ _     `compare` _               = LT
  _               `compare` SpecArg _ _     = GT
  SpecField r1 f1 `compare` SpecField r2 f2 =
        case r1 `compare` r2 of
          EQ -> JSS.fieldName f1 `compare` JSS.fieldName f2
          r  -> r

instance Show SpecJavaExpr where
  show (SpecThis _)    = "this"
  show (SpecArg i _)   = "args[" ++ show i ++ "]"
  show (SpecField r f) = show r ++ "." ++ JSS.fieldName f

-- | Returns JSS Type of SpecJavaExpr
getJSSTypeOfSpecRef :: SpecJavaExpr -- ^ Spec Java reference to get type of.
                    -> JSS.Type
getJSSTypeOfSpecRef (SpecThis cl)   = JSS.ClassType cl
getJSSTypeOfSpecRef (SpecArg _ tp)  = tp
getJSSTypeOfSpecRef (SpecField _ f) = JSS.fieldType f

-- Typecheck expression types {{{1

-- | Convert expression type from AST into WidthExpr
tcheckExprWidth :: AST.ExprWidth -> WidthExpr
tcheckExprWidth (AST.WidthConst _ i  ) = constantWidth (Wx i)
tcheckExprWidth (AST.WidthVar   _ nm ) = varWidth nm
tcheckExprWidth (AST.WidthAdd   _ u v) = addWidth (tcheckExprWidth u) (tcheckExprWidth v)

-- | Convert expression type from AST into DagType.
-- Uses Executor monad for parsing record types.
parseExprType :: AST.ExprType -> OpSession DagType
parseExprType (AST.BitType       _)   = return SymBool
parseExprType (AST.BitvectorType _ w) = return $ SymInt (tcheckExprWidth w)
parseExprType (AST.Array _ w tp)      = fmap (SymArray (tcheckExprWidth w)) $ parseExprType tp
parseExprType (AST.Record _ fields)   = do
       let names = [ nm | (_,nm,_) <- fields ]
       def <- getStructuralRecord (Set.fromList names)
       tps <- mapM parseExprType [ tp | (_,_,tp) <- fields ]
       let sub = emptySubst { shapeSubst = Map.fromList $ names `zip` tps }
       return $ SymRec def sub
parseExprType (AST.ShapeVar _ v)      = return (SymShapeVar v)

-- TypedExpr {{{1

-- | A type-checked expression which appears insider a global let binding,
-- method declaration, or rule term.
data TypedExpr
   = TypedApply Op [TypedExpr]
   | TypedCns CValue DagType
   | TypedJavaValue SpecJavaExpr DagType
   | TypedVar String DagType
   deriving (Show)

-- | Return type of a typed expression.
getTypeOfTypedExpr :: TypedExpr -> DagType
getTypeOfTypedExpr (TypedVar _ tp)       = tp
getTypeOfTypedExpr (TypedCns _ tp)       = tp
getTypeOfTypedExpr (TypedJavaValue _ tp) = tp
getTypeOfTypedExpr (TypedApply op _)     = opResultType op

-- | Additional information used by parseExpr to control parseExpr.
data TCConfig = TCC {
         localBindings     :: Map String TypedExpr
       , globalCnsBindings :: Map String (CValue,DagType)
       , opBindings        :: Map String OpDef
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
tcExpr _st e =
  error $ "internal: tcExpr given illegal type " ++ show e

