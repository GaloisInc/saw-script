{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards        #-}
module SAWScript.TypeChecker
  ( SpecJavaExpr(..)
  , getJSSTypeOfSpecRef
  , JavaExprDagType(..)
  , TypedExpr(..)
  , getTypeOfTypedExpr
  , TCConfig(..)
  , tcExpr
  , tcType
  , tcJavaExpr
  ) where

import Control.Monad
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import qualified JavaParser as JSS
import qualified Execution.Codebase as JSS
import Execution(HasCodebase(..))
import qualified SAWScript.MethodAST as AST
import SAWScript.TIMonad
import SAWScript.Utils
import Symbolic

tcJavaExpr :: TCConfig -> AST.JavaRef -> OpSession SpecJavaExpr
tcJavaExpr cfg e = runTI cfg (tcASTJavaExpr e)

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
  SpecField r1 f1 == SpecField r2 f2 =
    r1 == r2 && JSS.fieldName f1 == JSS.fieldName f2
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

-- | Check JSS Type is a type supported by SAWScript.
checkJSSTypeIsValid :: Pos -> JSS.Type -> SawTI ()
checkJSSTypeIsValid pos t = case t of
                              JSS.ArrayType JSS.IntType  -> return ()
                              JSS.ArrayType JSS.LongType -> return ()
                              JSS.ClassType nm           -> findClass pos nm >> return ()
                              JSS.ByteType               -> badI
                              JSS.CharType               -> badI
                              JSS.ShortType              -> badI
                              JSS.DoubleType             -> badF
                              JSS.FloatType              -> badF
                              JSS.ArrayType et           -> badA et
                              _                          -> return ()
  where badA et = typeErrWithR pos (ftext ("SAWScript currently only supports arrays of int and long, and does yet support arrays with type " ++ show et ++ "."))
                                   "Please modify the Java code to only use int or long array types."
        badI    = typeErrWithR pos (ftext ("SAWScript only supports integer and long integral values and does not yet support " ++ show t ++ "."))
                                   "Please modify the Java code to only use 'int' instead."
        badF    = typeErrWithR pos (ftext "SAWScript does not yet support \'float\' or \'double\' types.")
                                   "Please modify the Java code to not use floating point types."

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
   | TypedArray [TypedExpr] DagType
   | TypedRecord [(String, TypedExpr)] DagType
   | TypedDeref TypedExpr String DagType
   | TypedJavaValue SpecJavaExpr DagType
   | TypedVar String DagType
   deriving (Show)

-- | Return type of a typed expression.
getTypeOfTypedExpr :: TypedExpr -> DagType
getTypeOfTypedExpr (TypedVar         _ tp) = tp
getTypeOfTypedExpr (TypedCns         _ tp) = tp
getTypeOfTypedExpr (TypedArray       _ tp) = tp
getTypeOfTypedExpr (TypedRecord      _ tp) = tp
getTypeOfTypedExpr (TypedDeref     _ _ tp)   = tp
getTypeOfTypedExpr (TypedJavaValue   _ tp) = tp
getTypeOfTypedExpr (TypedApply       op _) = opResultType op

-- | Identifies the type of a Java expression.
data JavaExprDagType
  = JEDTClass String
  | JEDTType DagType
  | JEDTUndefined
  | JEDTBadContext

data TCConfig = TCC {
         localBindings     :: Map String TypedExpr
       , globalCnsBindings :: Map String (CValue,DagType)
       , opBindings        :: Map String OpDef
       , codeBase          :: JSS.Codebase
       , methodInfo        :: Maybe (JSS.Method, JSS.Class)
       , toJavaExprType    :: SpecJavaExpr -> JavaExprDagType
       , sawOptions        :: SSOpts
       }

type SawTI = TI OpSession TCConfig

debugTI :: String -> SawTI ()
debugTI msg = do os <- gets sawOptions
                 liftIO $ debugVerbose os $ putStrLn msg

instance HasCodebase SawTI where
  getCodebase    = gets codeBase
  putCodebase cb = modify $ \s -> s{ codeBase = cb }

getMethodInfo :: SawTI (JSS.Method, JSS.Class)
getMethodInfo = do
  maybeMI <- gets methodInfo
  case maybeMI of
    Nothing -> error $ "internal: getMethodInfo called when parsing outside a method declaration"
    Just p -> return p

tcASTJavaExpr :: AST.JavaRef -> SawTI SpecJavaExpr
tcASTJavaExpr (AST.This pos) = do
  (method, cl) <- getMethodInfo
  when (JSS.methodIsStatic method) $ typeErr pos (ftext "\'this\' is not defined on static methods.")
  return (SpecThis (JSS.className cl))
tcASTJavaExpr (AST.Arg pos i) = do
  (method, _) <- getMethodInfo
  let params = V.fromList (JSS.methodParameterTypes method)
  -- Check that arg index is valid.
  unless (0 <= i && i < V.length params) $ typeErr pos (ftext "Invalid argument index for method.")
  checkJSSTypeIsValid pos (params V.! i)
  return $ SpecArg i (params V.! i)
tcASTJavaExpr (AST.InstanceField pos astLhs fName) = do
  lhs <- tcASTJavaExpr astLhs
  case getJSSTypeOfSpecRef lhs of
    JSS.ClassType lhsClassName -> do
      cl <- findClass pos lhsClassName
      f <- findField pos fName cl
      checkJSSTypeIsValid pos (JSS.fieldType f)
      return $ SpecField lhs f
    _ -> typeErrWithR pos (ftext ("Could not find a field named " ++ fName ++ " in " ++ show lhs ++ "."))
                          "Please check to make sure the field name is correct."

-- | Check argument count matches expected length
checkArgCount :: Pos -> String -> [TypedExpr] -> Int -> SawTI ()
checkArgCount pos nm (length -> foundOpCnt) expectedCnt = do
  unless (expectedCnt == foundOpCnt) $
    typeErr pos $ ftext $ "Incorrect number of arguments to \'" ++ nm ++ "\'.  "
                        ++ show expectedCnt ++ " arguments were expected, but "
                        ++ show foundOpCnt ++ " arguments were found."

-- | Convert an AST expression from parser into a typed expression.
tcE :: AST.Expr -> SawTI TypedExpr
tcE (AST.ConstantInt p _)
  = typeErrWithR p (ftext ("The use of constant literal requires a type-annotation")) "Please provide the bit-size of the constant with a type-annotation"
tcE (AST.ApplyExpr p nm _)
  | nm `elem` ["split", "trunc", "signedExt"]
  = typeErrWithR p (ftext ("Use of operator '" ++ nm ++ "' requires a type-annotation.")) "Please provide an annotation for the surrounding expression."
tcE (AST.Var pos name) = do
  locals  <- gets localBindings
  globals <- gets globalCnsBindings
  case name `Map.lookup` locals of
    Just res -> return res
    Nothing -> do
      case name `Map.lookup` globals of
        Just (c,tp) -> return $ TypedCns c tp
        Nothing -> typeErr pos $ ftext $ "Unknown variable \'" ++ name ++ "\'."
tcE (AST.ConstantBool _ b) = return $ TypedCns (mkCBool b) SymBool
tcE (AST.MkArray p [])
  = typeErrWithR p (ftext ("Use of empty array-comprehensions requires a type-annotation")) "Please provide the type of the empty-array value"
tcE (AST.MkArray p (es@(_:_))) = do
        es' <- mapM tcE es
        let go []                 = error "internal: impossible happened in tcE-non-empty-mkArray"
            go [(_, x)]           = return x
            go ((i, x):(j, y):rs) = if x == y then go rs else mismatch p ("array elements " ++ show i ++ " and " ++ show j) x y
        t   <- go $ zip [(1::Int)..] $ map getTypeOfTypedExpr es'
        return $ TypedArray es' (SymArray (constantWidth (Wx (length es))) t)
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
tcE (AST.TypeExpr p (AST.MkArray _ []) astResType) = do
   resType <- tcT astResType
   case resType of
     SymArray we _ | Just (Wx 0) <- widthConstant we -> return $ TypedArray [] resType
     _  -> unexpected p "Empty-array comprehension" "empty-array type" resType
tcE (AST.MkRecord _ flds) = do
   flds' <- mapM tcE [e | (_, _, e) <- flds]
   let names = [nm | (_, nm, _) <- flds]
   def <- liftTI $ getStructuralRecord (Set.fromList names)
   let t = SymRec def $ emptySubst { shapeSubst = Map.fromList $ names `zip` (map getTypeOfTypedExpr flds') }
   return $ TypedRecord (names `zip` flds') t
tcE (AST.TypeExpr p e astResType) = do
   te <- tcE e
   let tet = getTypeOfTypedExpr te
   resType <- tcT astResType
   if tet /= resType
      then mismatch p "type-annotation" tet resType
      else return te
tcE (AST.JavaValue p jref) = tcJRef p jref
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
tcE (AST.ApplyExpr appPos nm astArgs) = do
  opBindings <- gets opBindings
  case Map.lookup nm opBindings of
    Nothing -> typeErrWithR appPos (ftext ("Unknown operator '" ++ nm ++ "'.")) "Please check that the operator is correct."
    Just opDef -> do
      args <- mapM tcE astArgs
      let defArgTypes = opDefArgTypes opDef
      checkArgCount appPos nm args (V.length defArgTypes)
      let defTypes = V.toList defArgTypes
      let argTypes = map getTypeOfTypedExpr args
      case matchSubst (defTypes `zip` argTypes) of
        Nothing  -> do
          debugTI $ show defTypes
          debugTI $ show argTypes
          mismatchArgs appPos ("in call to '" ++ nm ++ "'") argTypes defTypes
        Just sub -> do
          debugTI $ "Making expression with operator " ++ opDefName opDef ++ " and substitution " ++  show sub
          return $ TypedApply (mkOp opDef sub) args
tcE (AST.NotExpr      p l)   = lift1Bool     p "not" (groundOp bNotOpDef)        l
tcE (AST.BitComplExpr p l)   = lift1Word     p "~"   (wordOpX  iNotOpDef)        l
tcE (AST.NegExpr      p l)   = lift1Word     p "-"   (wordOpX  negOpDef)         l
tcE (AST.MulExpr      p l r) = lift2WordEq   p "*"   (wordOpEX mulOpDef)         l r
tcE (AST.SDivExpr     p l r) = lift2WordEq   p "/s"  (wordOpEX signedDivOpDef)   l r
tcE (AST.SRemExpr     p l r) = lift2WordEq   p "%s"  (wordOpEX signedRemOpDef)   l r
tcE (AST.PlusExpr     p l r) = lift2WordEq   p "+"   (wordOpEX addOpDef)         l r
tcE (AST.SubExpr      p l r) = lift2WordEq   p "-"   (wordOpEX subOpDef)         l r
tcE (AST.ShlExpr      p l r) = lift2Word     p "<<"  (shftOpVS shlOpDef)         l r
tcE (AST.SShrExpr     p l r) = lift2Word     p ">>s" (shftOpVS shrOpDef)         l r
tcE (AST.UShrExpr     p l r) = lift2Word     p ">>u" (shftOpVS ushrOpDef)        l r
tcE (AST.BitAndExpr   p l r) = lift2WordEq   p "&"   (wordOpEX iAndOpDef)        l r
tcE (AST.BitOrExpr    p l r) = lift2WordEq   p "|"   (wordOpEX iOrOpDef)         l r
tcE (AST.BitXorExpr   p l r) = lift2WordEq   p "^"   (wordOpEX iXorOpDef)        l r
tcE (AST.AppendExpr   p l r) = lift2Word     p "#"   (wordOpXY appendIntOpDef)   l r
tcE (AST.EqExpr       p l r) = lift2ShapeCmp p "=="  (shapeOpX eqOpDef)          l r
tcE (AST.IneqExpr     p l r) = lift2ShapeCmp p "!="  (shapeOpX eqOpDef)          l r >>= \e -> return $ TypedApply (groundOp bNotOpDef) [e]
tcE (AST.SGeqExpr     p l r) = lift2WordCmp  p ">=s" (wordOpX  signedLeqOpDef)   l r >>= return . flipBinOpArgs
tcE (AST.SLeqExpr     p l r) = lift2WordCmp  p "<=s" (wordOpX  signedLeqOpDef)   l r
tcE (AST.SGtExpr      p l r) = lift2WordCmp  p ">s"  (wordOpX  signedLtOpDef)    l r >>= return . flipBinOpArgs
tcE (AST.SLtExpr      p l r) = lift2WordCmp  p "<s"  (wordOpX  signedLtOpDef)    l r
tcE (AST.UGeqExpr     p l r) = lift2WordCmp  p ">=u" (wordOpX  unsignedLeqOpDef) l r >>= return . flipBinOpArgs
tcE (AST.ULeqExpr     p l r) = lift2WordCmp  p "<=u" (wordOpX  unsignedLeqOpDef) l r
tcE (AST.UGtExpr      p l r) = lift2WordCmp  p ">u"  (wordOpX  unsignedLtOpDef)  l r >>= return . flipBinOpArgs
tcE (AST.ULtExpr      p l r) = lift2WordCmp  p "<u"  (wordOpX  unsignedLtOpDef)  l r
tcE (AST.AndExpr      p l r) = lift2Bool     p "&&"  (groundOp bAndOpDef)        l r
tcE (AST.OrExpr       p l r) = lift2Bool     p "||"  (groundOp bOrOpDef)         l r
tcE (AST.IteExpr      p t l r) = do
        [t', l', r'] <- mapM tcE [t, l, r]
        let [tt, lt, rt] = map getTypeOfTypedExpr [t', l', r']
        if tt /= SymBool
           then mismatch p "test expression of if-then-else" tt SymBool
           else if lt /= rt
                then mismatch p "branches of if-then-else expression" lt rt
                else return $ TypedApply (shapeOpX iteOpDef lt) [t', l', r']
tcE (AST.DerefField p e f) = do
   e' <- tcE e
   case getTypeOfTypedExpr e' of
     rt@(SymRec recDef recSubst) -> do let fldNms = map opDefName $ V.toList $ recDefFieldOps recDef
                                           ftypes = V.toList $ recFieldTypes recDef recSubst
                                       case f `lookup` zip fldNms ftypes of
                                         Nothing -> unexpected p "record field selection" ("record containing field " ++ show f) rt
                                         Just ft -> return $ TypedDeref e' f ft
     rt  -> unexpected p "record field selection" ("record containing field " ++ show f) rt

tcJRef :: Pos -> AST.JavaRef -> SawTI TypedExpr
tcJRef p jr = do sje <- tcASTJavaExpr jr
                 toJavaT <- gets toJavaExprType
                 case toJavaT sje of
                   JEDTBadContext ->
                     let msg = "The Java value \'" ++ show sje ++ "\' appears in a global context."
                         res = "Java values may not be references outside method declarations."
                      in typeErrWithR p (ftext msg) res
                   JEDTUndefined ->
                     let msg = "The Java value \'" ++ show sje ++ "\' is missing a \'type\' annotation."
                         res = "Please add a type declaration to Java values before "
                                ++ "referring to them in SAWScript expressions."
                      in typeErrWithR p (ftext msg) res
                   JEDTClass _ ->
                     let msg = "The Java value " ++ show sje ++ " denotes a Java reference,"
                               ++ " and cannot be directly used in a SAWScript expression."
                         res = "Please alter the expression, perhaps by referring to "
                               ++ "an field in the reference."
                      in typeErrWithR p (ftext msg) res
                   JEDTType t -> return $ TypedJavaValue sje t

lift1Bool :: Pos -> String -> Op -> AST.Expr -> SawTI TypedExpr
lift1Bool p nm o l = do
  l' <- tcE l
  let lt = getTypeOfTypedExpr l'
  case lt of
    SymBool -> return $ TypedApply o [l']
    _       -> mismatch p ("argument to operator '" ++ nm ++ "'")  lt SymBool

lift1Word :: Pos -> String -> (WidthExpr -> Op) -> AST.Expr -> SawTI TypedExpr
lift1Word p nm opMaker l = do
  l' <- tcE l
  let lt = getTypeOfTypedExpr l'
  case lt of
    SymInt wl -> return $ TypedApply (opMaker wl) [l']
    _         -> unexpected p ("Argument to operator '" ++ nm ++ "'") "word" lt

lift2Bool :: Pos -> String -> Op -> AST.Expr -> AST.Expr -> SawTI TypedExpr
lift2Bool p nm o l r = do
  l' <- tcE l
  r' <- tcE r
  let lt = getTypeOfTypedExpr l'
      rt = getTypeOfTypedExpr r'
  case (lt, rt) of
    (SymBool, SymBool) -> return $ TypedApply o [l', r']
    (SymBool, _      ) -> mismatch p ("second argument to operator '" ++ nm ++ "'") rt SymBool
    (_      , _      ) -> mismatch p ("first argument to operator '"  ++ nm ++ "'") lt SymBool

lift2Word :: Pos -> String -> (WidthExpr -> WidthExpr -> Op) -> AST.Expr -> AST.Expr -> SawTI TypedExpr
lift2Word = lift2WordGen False
lift2WordEq :: Pos -> String -> (WidthExpr -> WidthExpr -> Op) -> AST.Expr -> AST.Expr -> SawTI TypedExpr
lift2WordEq = lift2WordGen True

-- The bool argument says if the args should be of the same type
lift2WordGen :: Bool -> Pos -> String -> (WidthExpr -> WidthExpr -> Op) -> AST.Expr -> AST.Expr -> SawTI TypedExpr
lift2WordGen checkEq p nm opMaker l r = do
  l' <- tcE l
  r' <- tcE r
  let lt = getTypeOfTypedExpr l'
      rt = getTypeOfTypedExpr r'
  case (lt, rt) of
    (SymInt wl, SymInt wr) -> if not checkEq || wl == wr
                              then return $ TypedApply (opMaker wl wr) [l', r']
                              else mismatch p ("arguments to operator '" ++ nm ++ "'") lt rt
    (SymInt _,  _)         -> unexpected p ("Second argument to operator '" ++ nm ++ "'") "word" rt
    (_       ,  _)         -> unexpected p ("First argument to operator '"  ++ nm ++ "'") "word" lt

lift2ShapeCmp :: Pos -> String -> (DagType -> Op) -> AST.Expr -> AST.Expr -> SawTI TypedExpr
lift2ShapeCmp p nm opMaker l r = do
  l' <- tcE l
  r' <- tcE r
  let lt = getTypeOfTypedExpr l'
      rt = getTypeOfTypedExpr r'
  if lt == rt
     then return $ TypedApply (opMaker lt) [l', r']
     else mismatch p ("arguments to operator '" ++ nm ++ "'") lt rt

lift2WordCmp :: Pos -> String -> (WidthExpr -> Op) -> AST.Expr -> AST.Expr -> SawTI TypedExpr
lift2WordCmp p nm opMaker l r = do
  l' <- tcE l
  r' <- tcE r
  let lt = getTypeOfTypedExpr l'
      rt = getTypeOfTypedExpr r'
  case (lt, rt) of
    (SymInt wl, SymInt wr) -> if wl == wr
                              then return $ TypedApply (opMaker wl) [l', r']
                              else mismatch p ("arguments to operator '" ++ nm ++ "'") lt rt
    (SymInt _,  _)         -> unexpected p ("Second argument to operator '" ++ nm ++ "'") "word" rt
    (_       ,  _)         -> unexpected p ("First argument to operator '"  ++ nm ++ "'") "word" lt

-- substitution constructor helpers
wordOpX :: OpDef -> WidthExpr -> Op
wordOpX  opDef wx    = mkOp opDef (emptySubst { widthSubst = Map.fromList [("x", wx)           ] })

wordOpEX :: OpDef -> WidthExpr -> WidthExpr -> Op
wordOpEX opDef wx _  = mkOp opDef (emptySubst { widthSubst = Map.fromList [("x", wx)           ] })

wordOpXY :: OpDef -> WidthExpr -> WidthExpr -> Op
wordOpXY opDef wx wy = mkOp opDef (emptySubst { widthSubst = Map.fromList [("x", wx), ("y", wy)] })

shftOpVS :: OpDef -> WidthExpr -> WidthExpr -> Op
shftOpVS opDef wv ws = mkOp opDef (emptySubst { widthSubst = Map.fromList [("v", wv), ("s", ws)] })

shapeOpX :: OpDef -> DagType -> Op
shapeOpX opDef wx = mkOp opDef (emptySubst { shapeSubst = Map.fromList [("x", wx)] })

flipBinOpArgs :: TypedExpr -> TypedExpr
flipBinOpArgs (TypedApply o [a, b]) = TypedApply o [b, a]
flipBinOpArgs e                     = error $ "internal: flipBinOpArgs: received: " ++ show e

findClass :: Pos -> String -> SawTI JSS.Class
findClass p s = do
        debugTI $ "Trying to find the class " ++ show s
        lookupClass p s
