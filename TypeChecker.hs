{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE ViewPatterns       #-}
module SAWScript.TypeChecker
  ( SpecJavaExpr(..)
  , getJSSTypeOfSpecRef
  , TypedExpr(..)
  , getTypeOfTypedExpr
  , TCConfig(..)
  , tcExpr
  , tcType
  ) where

import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import qualified JavaParser as JSS
import qualified Execution.Codebase as JSS
import qualified SAWScript.MethodAST as AST
import SAWScript.TIMonad
import SAWScript.Utils
import Symbolic

tcExpr :: TCConfig -> AST.Expr -> OpSession TypedExpr
tcExpr cfg e = runTI cfg (tcE e)

tcType :: TCConfig -> AST.ExprType -> OpSession DagType
tcType cfg t = runTI cfg (tcT t)

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
tcT :: AST.ExprType -> SawTI DagType
tcT (AST.BitType       _)   = return SymBool
tcT (AST.BitvectorType _ w) = return $ SymInt (tcheckExprWidth w)
tcT (AST.Array _ w tp)      = fmap (SymArray (tcheckExprWidth w)) $ tcT tp
tcT (AST.Record _ fields)   = do let names = [ nm | (_,nm,_) <- fields ]
                                 def <- liftTI $ getStructuralRecord (Set.fromList names)
                                 tps <- mapM tcT [ tp | (_,_,tp) <- fields ]
                                 let sub = emptySubst { shapeSubst = Map.fromList $ names `zip` tps }
                                 return $ SymRec def sub
tcT (AST.ShapeVar _ v)      = return (SymShapeVar v)

-- TypedExpr {{{1

-- | A type-checked expression which appears insider a global let binding,
-- method declaration, or rule term.
data TypedExpr
   = TypedApply Op [TypedExpr]
   | TypedCns CValue DagType
   | TypedJavaValue SpecJavaExpr DagType
   | TypedVar String DagType
   deriving (Show)

applySubstToTypedExpr :: TypedExpr -> TypeSubst -> TypedExpr
applySubstToTypedExpr _t _s = error "TBD: applySubstToTypedExpr"

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
       , codeBase          :: JSS.Codebase
       , methodInfo        :: Maybe (JSS.Method, JSS.Class)
       , toJavaExprType    :: SpecJavaExpr -> Maybe DagType
       }

type SawTI = TI OpSession TCConfig

-- | Check argument count matches expected length
checkArgCount :: Pos -> String -> [TypedExpr] -> Int -> SawTI ()
checkArgCount pos nm (length -> foundOpCnt) expectedCnt = do
  unless (expectedCnt == foundOpCnt) $
    typeErr pos $ ftext $ "Incorrect number of arguments to \'" ++ nm ++ "\'.  "
                        ++ show expectedCnt ++ " arguments were expected, but "
                        ++ show foundOpCnt ++ " arguments were found."

-- | Convert an AST expression from parser into a typed expression.
tcE :: AST.Expr -> SawTI TypedExpr
tcE (AST.TypeExpr pos (AST.ConstantInt _ i) astTp) = do
  tp <- tcT astTp
  let nonGround = typeErr pos $   text "The type" <+> text (ppType tp)
                              <+> ftext "bound to literals must be a ground type."
  case tp of
    SymInt (widthConstant -> Just (Wx w)) -> return $ TypedCns (mkCInt (Wx w) i) tp
    SymInt      _ -> nonGround
    SymShapeVar _ -> nonGround
    _             -> typeErr pos $   text "Incompatible type" <+> text (ppType tp)
                                 <+> ftext "assigned to integer literal."
tcE (AST.Var pos name) = do
  locals  <- gets localBindings
  globals <- gets globalCnsBindings
  case name `Map.lookup` locals of
    Just res -> return res
    Nothing -> do
      case name `Map.lookup` globals of
        Just (c,tp) -> return $ TypedCns c tp
        Nothing -> typeErr pos $ ftext $ "Unknown variable \'" ++ name ++ "\'."
tcE (AST.ApplyExpr appPos "join" astArgs) = do
  args <- mapM tcE astArgs
  checkArgCount appPos "join" args 1
  let argType = getTypeOfTypedExpr (head args)
  case argType of
    SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w)) -> do
         op <- liftTI $ joinOpDef l w
         return $ TypedApply (groundOp op) args
    _ -> typeErr appPos $ ftext $ "Illegal arguments and result type given to \'join\'."
                                ++ " SAWScript currently requires that the argument is ground"
                                ++ " array of integers. "
tcE (AST.TypeExpr _ (AST.ApplyExpr appPos "split" astArgs) astResType) = do
  args <- mapM tcE astArgs
  checkArgCount appPos "split" args 1
  resType <- tcT astResType
  let argType = getTypeOfTypedExpr (head args)
  case (argType, resType) of
    (  SymInt (widthConstant -> Just wl)
     , SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w)))
      | wl == l * w -> do
        op <- liftTI $ splitOpDef l w
        return $ TypedApply (groundOp op) args
    _ -> typeErr appPos $ ftext $ "Illegal arguments and result type given to \'split\'."
                                ++ " SAWScript currently requires that the argument is ground type, "
                                ++ " and an explicit result type is given."
tcE (AST.ApplyExpr appPos nm astArgs) = do
  opBindings <- gets opBindings
  case Map.lookup nm opBindings of
    Nothing -> typeErrWithR appPos (ftext ("Unknown operator " ++ nm ++ ".")) "Please check that the operator is correct."
    Just opDef -> do
      args <- mapM tcE astArgs
      let defArgTypes = opDefArgTypes opDef
      checkArgCount appPos nm args (V.length defArgTypes)
      let defTypes = V.toList defArgTypes
      let argTypes = map getTypeOfTypedExpr args
      case matchSubst (defTypes `zip` argTypes) of
        Nothing  -> typeErr appPos (ftext ("Illegal arguments and result type given to \'" ++ nm ++ "\'."))
        Just sub -> return $ TypedApply (mkOp opDef sub) args
tcE (AST.TypeExpr p e astResType) = do
   te <- tcE e
   let tet = getTypeOfTypedExpr te
   resType <- tcT astResType
   case matchSubst [(tet, resType)] of
     Nothing -> mismatch p "type-annotation" (text (show astResType)) (text (show tet))
     Just s  -> return $ applySubstToTypedExpr te s
tcE (AST.ArgsExpr p i) = do
   mbMethodInfo <- gets methodInfo
   case mbMethodInfo of
     Nothing          -> typeErr p $ ftext $ "Use of 'args[" ++ show i ++ "]' is illegal outside of method specifications"
     Just (method, _) -> do
       let params = JSS.methodParameterTypes method
       unless (0 <= i && i < length params) $ typeErr p $ ftext $ "'args[" ++ show i ++ "]' refers to an illegal argument index"
       toJavaT <- gets toJavaExprType
       let te = SpecArg i (params !! i)
       case toJavaT te of
         Nothing -> typeErr p $ ftext $ "The type of 'args[" ++ show i ++ "]' has not been declared"
         Just t' -> return $ TypedJavaValue te t'
-- TODO: Add more typechecking equations for parsing expressions.
tcE e =
  error $ "internal: tcE: TBD: " ++ show e
