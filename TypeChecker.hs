{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE ViewPatterns         #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards        #-}
module SAWScript.TypeChecker
  ( JavaExpr(..)
  , getJSSTypeOfJavaExpr
  , DefinedJavaExprType(..)
  , Expr(..)
  , getTypeOfExpr
  , typedExprVarNames
  , globalEval
  , GlobalBindings(..)
  , TCConfig(..)
  , mkGlobalTCConfig
  , tcExpr
  , tcType
  , tcJavaExpr
  ) where

import Control.Monad
import Data.Map(Map)
import qualified Data.Map as Map
import qualified Data.Vector as V
import Data.Set (Set)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ

import qualified JavaParser as JSS
import qualified Execution.Codebase as JSS
import Execution(HasCodebase(..))
import qualified SAWScript.MethodAST as AST
import SAWScript.TIMonad
import SAWScript.Utils
import Symbolic

tcJavaExpr :: TCConfig -> AST.JavaRef -> OpSession JavaExpr
tcJavaExpr cfg e = runTI cfg (tcASTJavaExpr e)

tcExpr :: TCConfig -> AST.Expr -> OpSession Expr
tcExpr cfg e = runTI cfg (tcE e)

tcType :: TCConfig -> AST.ExprType -> OpSession DagType
tcType cfg t = runTI cfg (tcT t)

-- JavaExpr {{{1

-- | Identifies a reference to a Java value.
data JavaExpr
  = This String -- | Name of classname for this object.
  | Arg Int JSS.Type
  | InstanceField JavaExpr JSS.FieldId

instance Eq JavaExpr where
  This _      == This _      = True
  Arg i _     == Arg j _     = i == j
  InstanceField r1 f1 == InstanceField r2 f2 = r1 == r2 && f1 == f2
  _               == _               = False

instance Ord JavaExpr where
  This _      `compare` This _      = EQ
  This _      `compare` _               = LT
  _               `compare` This _      = GT
  Arg i _     `compare` Arg j _     = i `compare` j
  Arg _ _     `compare` _               = LT
  _               `compare` Arg _ _     = GT
  InstanceField r1 f1 `compare` InstanceField r2 f2 =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r

instance Show JavaExpr where
  show (This _)    = "this"
  show (Arg i _)   = "args[" ++ show i ++ "]"
  show (InstanceField r f) = show r ++ "." ++ JSS.fieldIdName f

-- | Returns JSS Type of JavaExpr
getJSSTypeOfJavaExpr :: JavaExpr -- ^ Spec Java reference to get type of.
                     -> JSS.Type
getJSSTypeOfJavaExpr (This cl)   = JSS.ClassType cl
getJSSTypeOfJavaExpr (Arg _ tp)  = tp
getJSSTypeOfJavaExpr (InstanceField _ f) = JSS.fieldIdType f

-- Typecheck DagType {{{1

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

-- Expr {{{1

-- | A type-checked expression which appears insider a global let binding,
-- method declaration, or rule term.
data Expr
   = Apply Op [Expr]
   | Cns CValue DagType
   | JavaValue JavaExpr DagType
   | Var String DagType
   deriving (Show)

-- | Return type of a typed expression.
getTypeOfExpr :: Expr -> DagType
getTypeOfExpr (Apply       op _) = opResultType op
getTypeOfExpr (Cns         _ tp) = tp
getTypeOfExpr (JavaValue   _ tp) = tp
getTypeOfExpr (Var         _ tp) = tp

-- | Returns names of variables appearing in typedExpr.
typedExprVarNames :: Expr -> Set String
typedExprVarNames (Apply _ exprs) = Set.unions (map typedExprVarNames exprs)
typedExprVarNames (Cns _ _)       = Set.empty
typedExprVarNames (JavaValue _ _) = Set.empty
typedExprVarNames (Var nm _)      = Set.singleton nm

-- | Evaluate a ground typed expression to a constant value.
globalEval :: Expr -> OpSession CValue
globalEval expr = do
  let mkNode :: Expr -> SymbolicMonad Node
      mkNode (Var _nm _tp) =
        error "internal: globalEval called with non-ground expression"
      mkNode (JavaValue _nm _tp) =
        error "internal: globalEval called with expression containing Java references."
      mkNode (Cns c tp) = makeConstant c tp
      mkNode (Apply op args) = applyOp op =<< mapM mkNode args
  runSymSession $ do
    n <- mkNode expr
    symbolicEval V.empty $ evalNode n

-- DefinedJavaExprType {{{1

-- | Identifies the type of a Java expression.
data DefinedJavaExprType
  = DefinedClass JSS.Class
  | DefinedType DagType

-- }}}1

-- | Context for resolving top level expressions.
data GlobalBindings = GlobalBindings {
         codeBase      :: JSS.Codebase
       , ssOpts        :: SSOpts
       , opBindings    :: Map String OpDef
       , constBindings :: Map String (CValue,DagType)
       }

-- | Context for resolving expressions at the top level or within a method.
data TCConfig = TCC {
         globalBindings :: GlobalBindings
       , methodInfo     :: Maybe (JSS.Method, JSS.Class)
       , localBindings  :: Map String Expr
       , toJavaExprType :: Maybe (JavaExpr -> Maybe DefinedJavaExprType)
       }

mkGlobalTCConfig :: GlobalBindings -> Map String Expr -> TCConfig
mkGlobalTCConfig globalBindings localBindings = do
  TCC { globalBindings
      , methodInfo = Nothing
      , localBindings
      , toJavaExprType = Nothing }

type SawTI = TI OpSession TCConfig

debugTI :: String -> SawTI ()
debugTI msg = do os <- gets (ssOpts . globalBindings)
                 liftIO $ debugVerbose os $ putStrLn msg

instance HasCodebase SawTI where
  getCodebase = gets (codeBase . globalBindings)

getMethodInfo :: SawTI (JSS.Method, JSS.Class)
getMethodInfo = do
  maybeMI <- gets methodInfo
  case maybeMI of
    Nothing -> error $ "internal: getMethodInfo called when parsing outside a method declaration"
    Just p -> return p

tcASTJavaExpr :: AST.JavaRef -> SawTI JavaExpr
tcASTJavaExpr (AST.This pos) = do
  (method, cl) <- getMethodInfo
  when (JSS.methodIsStatic method) $ typeErr pos (ftext "\'this\' is not defined on static methods.")
  return (This (JSS.className cl))
tcASTJavaExpr (AST.Arg pos i) = do
  (method, _) <- getMethodInfo
  let params = V.fromList (JSS.methodParameterTypes method)
  -- Check that arg index is valid.
  unless (0 <= i && i < V.length params) $ typeErr pos (ftext "Invalid argument index for method.")
  checkJSSTypeIsValid pos (params V.! i)
  return $ Arg i (params V.! i)
tcASTJavaExpr (AST.InstanceField pos astLhs fName) = do
  lhs <- tcASTJavaExpr astLhs
  case getJSSTypeOfJavaExpr lhs of
    JSS.ClassType lhsClassName -> do
      cl <- findClass pos lhsClassName
      f <- findField pos fName cl
      checkJSSTypeIsValid pos (JSS.fieldIdType f)
      return $ InstanceField lhs f
    _ -> typeErrWithR pos (ftext ("Could not find a field named " ++ fName ++ " in " ++ show lhs ++ "."))
                          "Please check to make sure the field name is correct."

-- | Check argument count matches expected length
checkArgCount :: Pos -> String -> [Expr] -> Int -> SawTI ()
checkArgCount pos nm (length -> foundOpCnt) expectedCnt = do
  unless (expectedCnt == foundOpCnt) $
    typeErr pos $ ftext $ "Incorrect number of arguments to \'" ++ nm ++ "\'.  "
                        ++ show expectedCnt ++ " arguments were expected, but "
                        ++ show foundOpCnt ++ " arguments were found."

-- | Convert an AST expression from parser into a typed expression.
tcE :: AST.Expr -> SawTI Expr
tcE (AST.ConstantInt p _)
  = typeErrWithR p (ftext ("The use of constant literal requires a type-annotation")) "Please provide the bit-size of the constant with a type-annotation"
tcE (AST.ApplyExpr p nm _)
  | nm `elem` ["split", "trunc", "signedExt"]
  = typeErrWithR p (ftext ("Use of operator '" ++ nm ++ "' requires a type-annotation.")) "Please provide an annotation for the surrounding expression."
tcE (AST.Var pos name) = do
  locals  <- gets localBindings
  globals <- gets (constBindings . globalBindings)
  case name `Map.lookup` locals of
    Just res -> return res
    Nothing -> do
      case name `Map.lookup` globals of
        Just (c,tp) -> return $ Cns c tp
        Nothing -> typeErr pos $ ftext $ "Unknown variable \'" ++ name ++ "\'."
tcE (AST.ConstantBool _ b) = return $ Cns (mkCBool b) SymBool
tcE (AST.MkArray p [])
  = typeErrWithR p (ftext ("Use of empty array-comprehensions requires a type-annotation")) "Please provide the type of the empty-array value"
tcE (AST.MkArray p (es@(_:_))) = do
  es' <- mapM tcE es
  let go []                 = error "internal: impossible happened in tcE-non-empty-mkArray"
      go [(_, x)]           = return x
      go ((i, x):rs@((j, y):_)) = if x == y then go rs else mismatch p ("array elements " ++ show i ++ " and " ++ show j) x y
  t   <- go $ zip [(1::Int)..] $ map getTypeOfExpr es'
  op <- liftTI $ mkArrayOp (length es') t
  return $ Apply op es'
tcE (AST.TypeExpr pos (AST.ConstantInt posCnst i) astTp) = do
  tp <- tcT astTp
  let nonGround = typeErr pos $   text "The type" <+> text (ppType tp)
                              <+> ftext "bound to literals must be a ground type."
  case tp of
    SymInt (widthConstant -> Just (Wx w)) -> do warnRanges posCnst tp i w
                                                return $ Cns (mkCInt (Wx w) i) tp
    SymInt      _ -> nonGround
    SymShapeVar _ -> nonGround
    _             -> typeErr pos $   text "Incompatible type" <+> text (ppType tp)
                                 <+> ftext "assigned to integer literal."
tcE (AST.TypeExpr _ (AST.ApplyExpr appPos "split" astArgs) astResType) = do
  args <- mapM tcE astArgs
  checkArgCount appPos "split" args 1
  resType <- tcT astResType
  let argType = getTypeOfExpr (head args)
  case (argType, resType) of
    (  SymInt (widthConstant -> Just wl)
     , SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w)))
      | wl == l * w -> do
        op <- liftTI $ splitOpDef l w
        return $ Apply (groundOp op) args
    _ -> typeErr appPos $ ftext $ "Illegal arguments and result type given to \'split\'."
                                ++ " SAWScript currently requires that the argument is ground type, "
                                ++ " and an explicit result type is given."
tcE (AST.TypeExpr p (AST.MkArray _ []) astResType) = do
  resType <- tcT astResType
  case resType of
    SymArray we _ 
      | Just (Wx 0) <- widthConstant we -> do
         op <- liftTI $ mkArrayOp 0 resType
         return $ Apply op []
    _  -> unexpected p "Empty-array comprehension" "empty-array type" resType
tcE (AST.MkRecord _ flds) = do
   flds' <- mapM tcE [e | (_, _, e) <- flds]
   let names = [nm | (_, nm, _) <- flds]
   def <- liftTI $ getStructuralRecord (Set.fromList names)
   let fldTps = map getTypeOfExpr flds'
   let sub = emptySubst { shapeSubst = Map.fromList $ names `zip` fldTps }
   return $ Apply (mkOp (recDefCtor def) sub) flds'
tcE (AST.TypeExpr p e astResType) = do
   te <- tcE e
   let tet = getTypeOfExpr te
   resType <- tcT astResType
   if tet /= resType
      then mismatch p "type-annotation" tet resType
      else return te
tcE (AST.JavaValue p jref) = tcJRef p jref
tcE (AST.ApplyExpr appPos "join" astArgs) = do
  args <- mapM tcE astArgs
  checkArgCount appPos "join" args 1
  let argType = getTypeOfExpr (head args)
  case argType of
    SymArray (widthConstant -> Just l) (SymInt (widthConstant -> Just w)) -> do
         op <- liftTI $ joinOpDef l w
         return $ Apply (groundOp op) args
    _ -> typeErr appPos $ ftext $ "Illegal arguments and result type given to \'join\'."
                                ++ " SAWScript currently requires that the argument is ground"
                                ++ " array of integers. "
tcE (AST.ApplyExpr appPos nm astArgs) = do
  opBindings <- gets (opBindings . globalBindings)
  case Map.lookup nm opBindings of
    Nothing -> typeErrWithR appPos (ftext ("Unknown operator '" ++ nm ++ "'.")) "Please check that the operator is correct."
    Just opDef -> do
      args <- mapM tcE astArgs
      let defArgTypes = opDefArgTypes opDef
      checkArgCount appPos nm args (V.length defArgTypes)
      let defTypes = V.toList defArgTypes
      let argTypes = map getTypeOfExpr args
      case matchSubst (defTypes `zip` argTypes) of
        Nothing  -> do
          debugTI $ show defTypes
          debugTI $ show argTypes
          mismatchArgs appPos ("in call to '" ++ nm ++ "'") argTypes defTypes
        Just sub -> do
          debugTI $ "Making expression with operator " ++ opDefName opDef ++ " and substitution " ++  show sub
          return $ Apply (mkOp opDef sub) args
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
tcE (AST.IneqExpr     p l r) = lift2ShapeCmp p "!="  (shapeOpX eqOpDef)          l r >>= \e -> return $ Apply (groundOp bNotOpDef) [e]
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
        let [tt, lt, rt] = map getTypeOfExpr [t', l', r']
        if tt /= SymBool
           then mismatch p "test expression of if-then-else" tt SymBool
           else if lt /= rt
                then mismatch p "branches of if-then-else expression" lt rt
                else return $ Apply (shapeOpX iteOpDef lt) [t', l', r']
tcE (AST.DerefField p e f) = do
   e' <- tcE e
   case getTypeOfExpr e' of
     rt@(SymRec recDef recSubst) -> do let fops = recDefFieldOps recDef
                                       case V.find (\op -> opDefName op == f) fops of
                                         Nothing -> unexpected p "record field selection" ("record containing field " ++ show f) rt
                                         Just fop -> return $ Apply (mkOp fop recSubst) [e']
     rt  -> unexpected p "record field selection" ("record containing field " ++ show f) rt

tcJRef :: Pos -> AST.JavaRef -> SawTI Expr
tcJRef p jr = do
  sje <- tcASTJavaExpr jr
  mbToJavaT <- gets toJavaExprType
  case mbToJavaT of
    Nothing -> 
      let msg = "The Java value \'" ++ show sje ++ "\' appears in a global context."
          res = "Java values may not be references outside method declarations."
       in typeErrWithR p (ftext msg) res
    Just toJavaT -> do
      case toJavaT sje of
        Nothing ->
          let msg = "The Java value \'" ++ show sje ++ "\' is missing a \'type\' annotation."
              res = "Please add a type declaration to Java values before "
                     ++ "referring to them in SAWScript expressions."
           in typeErrWithR p (ftext msg) res
        Just (DefinedClass _) ->
          let msg = "The Java value " ++ show sje ++ " denotes a Java reference,"
                    ++ " and cannot be directly used in a SAWScript expression."
              res = "Please alter the expression, perhaps by referring to "
                    ++ "an field in the reference."
           in typeErrWithR p (ftext msg) res
        Just (DefinedType t) -> return $ JavaValue sje t

lift1Bool :: Pos -> String -> Op -> AST.Expr -> SawTI Expr
lift1Bool p nm o l = do
  l' <- tcE l
  let lt = getTypeOfExpr l'
  case lt of
    SymBool -> return $ Apply o [l']
    _       -> mismatch p ("argument to operator '" ++ nm ++ "'")  lt SymBool

lift1Word :: Pos -> String -> (WidthExpr -> Op) -> AST.Expr -> SawTI Expr
lift1Word p nm opMaker l = do
  l' <- tcE l
  let lt = getTypeOfExpr l'
  case lt of
    SymInt wl -> return $ Apply (opMaker wl) [l']
    _         -> unexpected p ("Argument to operator '" ++ nm ++ "'") "word" lt

lift2Bool :: Pos -> String -> Op -> AST.Expr -> AST.Expr -> SawTI Expr
lift2Bool p nm o l r = do
  l' <- tcE l
  r' <- tcE r
  let lt = getTypeOfExpr l'
      rt = getTypeOfExpr r'
  case (lt, rt) of
    (SymBool, SymBool) -> return $ Apply o [l', r']
    (SymBool, _      ) -> mismatch p ("second argument to operator '" ++ nm ++ "'") rt SymBool
    (_      , _      ) -> mismatch p ("first argument to operator '"  ++ nm ++ "'") lt SymBool

lift2Word :: Pos -> String -> (WidthExpr -> WidthExpr -> Op) -> AST.Expr -> AST.Expr -> SawTI Expr
lift2Word = lift2WordGen False
lift2WordEq :: Pos -> String -> (WidthExpr -> WidthExpr -> Op) -> AST.Expr -> AST.Expr -> SawTI Expr
lift2WordEq = lift2WordGen True

-- The bool argument says if the args should be of the same type
lift2WordGen :: Bool -> Pos -> String -> (WidthExpr -> WidthExpr -> Op) -> AST.Expr -> AST.Expr -> SawTI Expr
lift2WordGen checkEq p nm opMaker l r = do
  l' <- tcE l
  r' <- tcE r
  let lt = getTypeOfExpr l'
      rt = getTypeOfExpr r'
  case (lt, rt) of
    (SymInt wl, SymInt wr) -> if not checkEq || wl == wr
                              then return $ Apply (opMaker wl wr) [l', r']
                              else mismatch p ("arguments to operator '" ++ nm ++ "'") lt rt
    (SymInt _,  _)         -> unexpected p ("Second argument to operator '" ++ nm ++ "'") "word" rt
    (_       ,  _)         -> unexpected p ("First argument to operator '"  ++ nm ++ "'") "word" lt

lift2ShapeCmp :: Pos -> String -> (DagType -> Op) -> AST.Expr -> AST.Expr -> SawTI Expr
lift2ShapeCmp p nm opMaker l r = do
  l' <- tcE l
  r' <- tcE r
  let lt = getTypeOfExpr l'
      rt = getTypeOfExpr r'
  if lt == rt
     then return $ Apply (opMaker lt) [l', r']
     else mismatch p ("arguments to operator '" ++ nm ++ "'") lt rt

lift2WordCmp :: Pos -> String -> (WidthExpr -> Op) -> AST.Expr -> AST.Expr -> SawTI Expr
lift2WordCmp p nm opMaker l r = do
  l' <- tcE l
  r' <- tcE r
  let lt = getTypeOfExpr l'
      rt = getTypeOfExpr r'
  case (lt, rt) of
    (SymInt wl, SymInt wr) -> if wl == wr
                              then return $ Apply (opMaker wl) [l', r']
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

flipBinOpArgs :: Expr -> Expr
flipBinOpArgs (Apply o [a, b]) = Apply o [b, a]
flipBinOpArgs e                     = error $ "internal: flipBinOpArgs: received: " ++ show e

findClass :: Pos -> String -> SawTI JSS.Class
findClass p s = do
        debugTI $ "Trying to find the class " ++ show s
        lookupClass p s

-- Only warn if the constant is beyond range for both signed/unsigned versions
-- This is less precise than it can be, but less annoying too..
warnRanges :: Pos -> DagType -> Integer -> Int -> SawTI ()
warnRanges pos tp i w'
  | violatesBoth = typeWarn pos $  ftext ("Constant \"" ++ show i ++ " : " ++ ppType tp ++ "\" will be subject to modular reduction.")
                                $$ complain srange "a signed"    (if j >= 2^(w-1) then j - (2^w) else j)
                                $$ complain urange "an unsigned" j
  | True         = return ()
  where violatesBoth = not (inRange srange || inRange urange)
        w :: Integer
        w = fromIntegral w'
        j :: Integer
        j = i `mod` (2^w)
        srange, urange :: (Integer, Integer)
        srange = (-(2^(w-1)), (2^(w-1))-1)
        urange = (0, 2^w-1)
        inRange (a, b) = i >= a && i <= b
        complain (a, b) ctx i' =    ftext ("In " ++ ctx ++ " context, range will be: [" ++ show a ++ ", " ++ show b ++ "]")
                                 $$ ftext ("And the constant will assume the value " ++ show i')
