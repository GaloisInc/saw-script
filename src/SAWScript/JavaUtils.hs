{- |
Module      : SAWScript.JavaUtils
Description : Miscellaneous utilities for Java.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.JavaUtils where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Lens
import Control.Monad
import Control.Monad.IO.Class
import qualified Data.Array as Array
import Data.Int
import Data.IORef
import qualified Data.Map as Map
import Data.Maybe
import qualified Data.Set as Set

import Verifier.Java.Simulator as JSS
import Verifier.Java.SAWImport
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm

import qualified SAWScript.CongruenceClosure as CC
import SAWScript.JavaExpr

type SAWBackend = SharedContext
type SpecPathState = Path SharedContext
type SpecJavaValue = Value Term
type SAWJavaSim = Simulator SharedContext
type LocalMap t = Map.Map LocalVariableIndex (Value t)

boolExtend' :: SharedContext -> Term -> IO Term
boolExtend' sc x = do
  n31 <- scNat sc 31
  n1 <- scNat sc 1
  scBvUExt sc n31 n1 x

arrayApply :: SharedContext
            -> (SharedContext -> Term -> Term -> IO b)
            -> Term -> IO b
arrayApply sc fn tm = do
  ty <- scTypeOf sc =<< scWhnf sc tm
  case ty of
    (asVecType -> Just (n :*: _)) -> do
      l <- scNat sc n
      fn sc l tm
    _ -> fail "Invalid type passed to extendArray"

extendToIValue :: SharedContext -> JSS.Type -> Term -> IO Term
extendToIValue sc ty tm = do
  case ty of
    JSS.BooleanType -> scApplyJava_boolExtend sc tm
    JSS.ByteType -> scApplyJava_byteExtend sc tm
    JSS.ShortType -> scApplyJava_shortExtend sc tm
    JSS.CharType -> scApplyJava_charExtend sc tm
    JSS.IntType -> return tm
    JSS.ArrayType JSS.BooleanType -> arrayApply sc scApplyJava_extendBoolArray tm
    JSS.ArrayType JSS.ByteType -> arrayApply sc scApplyJava_extendByteArray tm
    JSS.ArrayType JSS.CharType -> arrayApply sc scApplyJava_extendCharArray tm
    JSS.ArrayType JSS.ShortType -> arrayApply sc scApplyJava_extendShortArray tm
    JSS.ArrayType JSS.IntType -> return tm
    _ -> fail $ "Invalid type passed to extendToIValue: " ++ show ty

truncateIValue :: SharedContext -> JSS.Type -> Term -> IO Term
truncateIValue sc ty tm = do
  case ty of
    JSS.BooleanType -> scApplyJava_boolTrunc sc tm
    JSS.ByteType -> scApplyJava_byteTrunc sc tm
    JSS.ShortType -> scApplyJava_shortTrunc sc tm
    JSS.CharType -> scApplyJava_shortTrunc sc tm
    JSS.IntType -> return tm
    JSS.ArrayType JSS.BooleanType -> arrayApply sc scApplyJava_truncBoolArray tm
    JSS.ArrayType JSS.ByteType -> arrayApply sc scApplyJava_truncByteArray tm
    JSS.ArrayType JSS.CharType -> arrayApply sc scApplyJava_truncCharArray tm
    JSS.ArrayType JSS.ShortType -> arrayApply sc scApplyJava_truncShortArray tm
    JSS.ArrayType JSS.IntType -> return tm
    _ -> fail $ "Invalid type passed to truncateIValue: " ++ show ty

termTypeCompatible :: SharedContext -> Term -> JSS.Type -> IO Bool
termTypeCompatible sc tm ty = do
  tm' <- scWhnf sc tm
  case (tm', ty) of
    (asBoolType -> Just (), JSS.BooleanType) -> return True
    (asBitvectorType -> Just 8, JSS.ByteType) -> return True
    (asBitvectorType -> Just 16, JSS.ShortType) -> return True
    (asBitvectorType -> Just 16, JSS.CharType) -> return True
    (asBitvectorType -> Just 32, JSS.IntType) -> return True
    (asBitvectorType -> Just 64, JSS.LongType) -> return True
    (asVecType -> Just (_ :*: elty), JSS.ArrayType ety) ->
      termTypeCompatible sc elty ety
    _ -> return False

termTypeToJSSType :: SharedContext -> Term -> IO JSS.Type
termTypeToJSSType sc t = do
  ty <- scWhnf sc t
  case ty of
    (asBoolType -> Just ()) -> return JSS.BooleanType
    (asBitvectorType -> Just 8) -> return JSS.ByteType
    (asBitvectorType -> Just 16) -> return JSS.ShortType
    (asBitvectorType -> Just 32) -> return JSS.IntType
    (asBitvectorType -> Just 64) -> return JSS.IntType
    (asVecType -> Just (_ :*: ety)) ->
      JSS.ArrayType <$> termTypeToJSSType sc ety
    _ -> fail "Invalid type for termTypeToJSSType"

-- SpecPathState {{{1

-- | Add assertion for predicate to path state.
addAssertionPS :: SharedContext -> Term
               -> SpecPathState
               -> IO SpecPathState
addAssertionPS sc x p = do
  p & pathAssertions %%~ \a -> liftIO (scAnd sc a x)

-- | Set value bound to array in path state.
-- Assumes value is an array with a ground length.
setArrayValuePS :: Ref -> Int32 -> Term
                -> SpecPathState
                -> SpecPathState
setArrayValuePS r n v =
  pathMemory . memScalarArrays %~ Map.insert r (n, v)

-- | Set value of bound to instance field in path state.
setInstanceFieldValuePS :: Ref -> FieldId -> SpecJavaValue
                        -> SpecPathState -> SpecPathState
setInstanceFieldValuePS r f v =
  pathMemory . memInstanceFields %~ Map.insert (r, f) v

-- | Set value of bound to static field in path state.
setStaticFieldValuePS :: FieldId -> SpecJavaValue
                      -> SpecPathState -> SpecPathState
setStaticFieldValuePS f v =
  pathMemory . memStaticFields %~ Map.insert f v

-- | Get value of bound to instance field in path state.
getInstanceFieldValuePS :: SpecPathState -> Ref -> FieldId
                        -> Maybe SpecJavaValue
getInstanceFieldValuePS ps r f =
  Map.lookup (r, f) (ps ^. pathMemory . memInstanceFields)

-- | Get value of bound to static field in path state.
getStaticFieldValuePS :: SpecPathState -> FieldId
                      -> Maybe SpecJavaValue
getStaticFieldValuePS ps f =
  Map.lookup f (ps ^. pathMemory . memStaticFields)

-- | Returns value constructor from node.
mkJSSValue :: SharedContext -> Type -> Term -> IO SpecJavaValue
mkJSSValue _ (ClassType _) _ = fail "mkJSSValue called on class type"
mkJSSValue _ (ArrayType _) _ = fail "mkJSSValue called on array type"
mkJSSValue _ FloatType  _ = fail "mkJSSValue called on float type"
mkJSSValue _ DoubleType _ = fail "mkJSSValue called on double type"
mkJSSValue sc LongType  n = do
  ty <- scTypeOf sc n
  case ty of
    (asBitvectorType -> Just 64) -> return (LValue n)
    _ -> fail "internal: invalid LValue passed to mkJSSValue."
mkJSSValue sc ty n = IValue <$> extendToIValue sc ty n

writeJavaTerm :: (MonadSim SharedContext m) =>
                 SharedContext
              -> JavaExpr
              -> TypedTerm
              -> Simulator SharedContext m ()
writeJavaTerm sc e tm = do
  v <- valueOfTerm sc (exprType e) tm
  writeJavaValue e v

writeJavaValue :: (MonadSim SharedContext m) =>
                  JavaExpr
               -> SpecJavaValue
               -> Simulator SharedContext m ()
writeJavaValue (CC.Term e) v =
  case e of
    ReturnVal _ -> fail "Can't set return value"
    Local _ idx _ -> setLocal idx v
    InstanceField rexp f -> do
      rv <- readJavaValueSim rexp
      case rv of
        RValue r -> setInstanceFieldValue r f v
        _ -> fail "Instance argument of instance field evaluates to non-reference"
    StaticField f -> setStaticFieldValue f v

writeJavaValuePS :: (Functor m, Monad m) =>
                    JavaExpr
                 -> SpecJavaValue
                 -> SpecPathState
                 -> m SpecPathState
writeJavaValuePS (CC.Term e) v ps =
  case e of
    ReturnVal _ -> return (ps & set pathRetVal (Just v))
    Local _ i _ ->
      case ps ^. pathStack of
        [] -> fail "no stack frames"
        (cf:cfs) -> do
          let cf' = cf & cfLocals %~ Map.insert i v
          return (ps & pathStack .~ (cf':cfs))
    InstanceField rexp f -> do
      rv <- readJavaValue ((^. cfLocals) <$> currentCallFrame ps) ps rexp
      case rv of
        RValue r -> return (setInstanceFieldValuePS r f v ps)
        _ -> fail "Instance argument of instance field evaluates to non-reference"
    StaticField f -> return (setStaticFieldValuePS f v ps)

readJavaTerm :: (Functor m, Monad m, MonadIO m) =>
                SharedContext -> Maybe (LocalMap Term) -> Path' Term -> JavaExpr -> m Term
readJavaTerm sc mcf ps et =
  termOfValue sc ps (exprType et) =<< readJavaValue mcf ps et

readJavaTermSim :: (Functor m, Monad m) =>
                   SharedContext
                -> JavaExpr
                -> Simulator SharedContext m Term
readJavaTermSim sc e = do
  ps <- getPath "readJavaTermSim"
  readJavaTerm sc ((^. cfLocals) <$> currentCallFrame ps) ps e

termOfValue :: (Functor m, Monad m, MonadIO m) =>
               SharedContext -> Path' Term -> JSS.Type -> SpecJavaValue -> m Term
termOfValue sc _ tp (IValue t) = liftIO $ truncateIValue sc tp t
termOfValue _ _ _ (LValue t) = return t
termOfValue sc ps tp (RValue r@(Ref _ (ArrayType ety))) = do
  case (Map.lookup r (ps ^. pathMemory . memScalarArrays), ety) of
    (Just (_, a), JSS.LongType) -> return a
    (Just (_, a), _) -> liftIO $ truncateIValue sc tp a
    (Nothing, _) -> fail "Reference not found in arrays map"
termOfValue _ _ _ (RValue (Ref _ (ClassType _))) =
  fail "Translating objects to terms not yet implemented" -- TODO
termOfValue _ _ _ _ = fail "Can't convert term to value"

termOfValueSim :: (Functor m, Monad m) =>
                  SharedContext -> JSS.Type -> SpecJavaValue
               -> Simulator SharedContext m Term
termOfValueSim sc tp v = do
  ps <- getPath "termOfValueSim"
  termOfValue sc ps tp v

valueOfTerm :: (MonadSim SharedContext m) =>
               SharedContext
            -> JSS.Type
            -> TypedTerm
            -> Simulator SharedContext m SpecJavaValue
valueOfTerm sc jty (TypedTerm _schema t) = do
  ty <- liftIO $ (scTypeOf sc t >>= scWhnf sc)
  case (ty, jty) of
    (asBoolType -> Just (), JSS.BooleanType) -> IValue <$> (liftIO $ scApplyJava_boolExtend sc t)
    -- TODO: remove the following case when no longer needed, and use extendToIValue
    (asBitvectorType -> Just 1, JSS.BooleanType) -> IValue <$> (liftIO $ scApplyJava_byteExtend sc t)
    (asBitvectorType -> Just 8, JSS.ByteType) -> IValue <$> (liftIO $ scApplyJava_byteExtend sc t)
    (asBitvectorType -> Just 16, JSS.ShortType) -> IValue <$> (liftIO $ scApplyJava_shortExtend sc t)
    (asBitvectorType -> Just 16, JSS.CharType) -> IValue <$> (liftIO $ scApplyJava_charExtend sc t)
    (asBitvectorType -> Just 32, JSS.IntType) -> return (IValue t)
    (asBitvectorType -> Just 64, JSS.LongType) -> return (LValue t)
    (asVecType -> Just (n :*: _), JSS.ArrayType JSS.LongType) -> do
      RValue <$> newSymbolicArray (ArrayType JSS.LongType) (fromIntegral n) t
    (asVecType -> Just (n :*: _), JSS.ArrayType ety) -> do
      t' <- liftIO $ extendToIValue sc jty t
      RValue <$> newSymbolicArray (ArrayType ety) (fromIntegral n) t'
    _ -> fail $ "Can't translate term of type: " ++ show ty ++ " to Java type " ++ show jty
-- If vector of other things, allocate array, translate those things, and store
-- If record, allocate appropriate object, translate fields, assign fields
-- For the last case, we need information about the desired Java type

-- NB: the CallFrame parameter allows this function to use a different
-- call frame than the one in the current state, which can be useful to
-- access parameters of a method that has returned.
readJavaValue :: (Functor m, Monad m) =>
                 Maybe (LocalMap Term)
              -> Path' Term
              -> JavaExpr
              -> m SpecJavaValue
readJavaValue mlocals ps (CC.Term e) = do
  case e of
    ReturnVal _ ->
      case ps ^. pathRetVal of
        Just rv -> return rv
        Nothing -> fail "Return value not found"
    Local _ idx _ ->
      case mlocals of
        Just locals ->
          case Map.lookup idx locals of
            Just v -> return v
            Nothing -> fail $ "Local variable " ++ show idx ++ " not found"
        Nothing -> fail "Trying to read local variable with no call frame."
    InstanceField rexp f -> do
      rv <- readJavaValue mlocals ps rexp
      case rv of
        RValue ref -> do
          let ifields = ps ^. pathMemory . memInstanceFields
          case Map.lookup (ref, f) ifields of
            Just fv -> return fv
            _ -> fail $ "Instance field '" ++ fieldIdName f ++ "' not found."
        _ -> fail "Object of instance field selector evaluated to non-reference."
    StaticField f -> do
      let sfields = ps ^. pathMemory . memStaticFields
      case Map.lookup f sfields of
        Just v -> return v
        _ -> fail $ "Static field '" ++ fieldIdName f ++
                    "' not found in class '" ++ JSS.unClassName (fieldIdClass f) ++ "'"

readJavaValueSim :: (Monad m) =>
                    JavaExpr
                 -> Simulator SharedContext m SpecJavaValue
readJavaValueSim e = do
  ps <- getPath "readJavaValueSim"
  readJavaValue ((^. cfLocals) <$> currentCallFrame ps) ps e

logicExprToTerm :: SharedContext
                -> Maybe (LocalMap Term)
                -> Path' Term -> LogicExpr
                -> IO Term
logicExprToTerm sc mlocals ps le = do
  let exprs = logicExprJavaExprs le
  args <- forM exprs $ \expr -> do
    t <- readJavaTerm sc mlocals ps expr
    return (expr, t)
  let argMap = Map.fromList args
      argTerms = mapMaybe (\k -> Map.lookup k argMap) exprs
  useLogicExpr sc le argTerms

-- NB: uses call frame from path
mixedExprToTerm :: SharedContext
                -> Path' Term -> MixedExpr
                -> IO Term
mixedExprToTerm sc ps me = do
  let mlocals = (^. cfLocals) <$> currentCallFrame ps
  case me of
    LE le -> logicExprToTerm sc mlocals ps le
    JE je -> readJavaTerm sc mlocals ps je

logicExprToTermSim :: (Functor m, Monad m) =>
                      SharedContext
                   -> LogicExpr
                   -> Simulator SAWBackend m Term
logicExprToTermSim sc le = do
  ps <- getPath "logicExprToTermSim"
  liftIO $ logicExprToTerm sc ((^. cfLocals) <$> currentCallFrame ps) ps le

freshJavaVal :: (MonadIO m, Functor m) =>
                Maybe (IORef [Term])
             -> SharedContext
             -> JavaActualType
             -> Simulator SAWBackend m SpecJavaValue
freshJavaVal _ _ (PrimitiveType ty) = do
  case ty of
    BooleanType -> withSBE $ \sbe -> IValue <$> freshBool sbe
    ByteType    -> withSBE $ \sbe -> IValue <$> freshByte sbe
    CharType    -> withSBE $ \sbe -> IValue <$> freshChar sbe
    ShortType   -> withSBE $ \sbe -> IValue <$> freshShort sbe
    IntType     -> withSBE $ \sbe -> IValue <$> freshInt sbe
    LongType    -> withSBE $ \sbe -> LValue <$> freshLong sbe
    _ -> fail $ "Can't create fresh primitive value of type " ++ show ty
freshJavaVal argsRef sc (ArrayInstance n ty) | isPrimitiveType ty = do
  -- TODO: should this use bvAt?
  elts <- liftIO $ do
    ety <- scBitvector sc (fromIntegral (JSS.stackWidth ty))
    ntm <- scNat sc (fromIntegral n)
    aty <- scVecType sc ntm ety
    atm <- scFreshGlobal sc "_" aty
    maybe (return ()) (\r -> modifyIORef r (atm :)) argsRef
    mapM (scAt sc ntm ety atm) =<< mapM (scNat sc) [0..(fromIntegral n) - 1]
  case ty of
    LongType -> RValue <$> newLongArray elts
    _ | isIValue ty -> RValue <$> newIntArray (ArrayType ty) elts
    _ -> fail $ "Can't create array with element type " ++ show ty
-- TODO: allow input declarations to specialize types of fields
freshJavaVal _ _ (ArrayInstance _ _) =
  fail $ "Can't create fresh array of non-scalar elements"
freshJavaVal argsRef sc (ClassInstance c) = do
  r <- createInstance (className c) Nothing
  forM_ (classFields c) $ \f -> do
    let ty = fieldType f
    v <- freshJavaVal argsRef sc (PrimitiveType ty)
    setInstanceFieldValue r (FieldId (className c) (fieldName f) ty) v
  return (RValue r)

isArrayType :: Type -> Bool
isArrayType (ArrayType _) = True
isArrayType _ = False

refInstanceFields :: (Ord f) =>
                     Map.Map (Ref, f) v
                  -> Ref
                  -> Map.Map f v
refInstanceFields m r =
  Map.fromList [ (f, v) | ((mr, f), v) <- Map.toList m, mr == r ]

pathRefInstanceFields :: Path SharedContext
                      -> Ref
                      -> Map.Map FieldId SpecJavaValue
pathRefInstanceFields ps =
  refInstanceFields (ps ^. pathMemory . memInstanceFields)

pathArrayRefs :: Path SharedContext
              -> Ref
              -> [Ref]
pathArrayRefs ps r =
  concat
  [ Array.elems a
  | (ar, a) <- Map.toList (ps ^. pathMemory . memRefArrays)
  , ar == r
  ]

pathStaticFieldRefs :: Path SharedContext
                    -> [Ref]
pathStaticFieldRefs ps =
  valueRefs $ map snd $ Map.toList (ps ^. pathMemory . memStaticFields)

reachableFromRef :: SpecPathState -> Set.Set Ref -> Ref -> Set.Set Ref
reachableFromRef _ seen r | r `Set.member` seen = Set.empty
reachableFromRef ps seen r =
  Set.unions
  [ Set.singleton r
  , Set.unions (map (reachableFromRef ps seen') refArrayRefs)
  , Set.unions (map (reachableFromRef ps seen') instFieldRefs)
  ]
  where refArrayRefs = pathArrayRefs ps r
        instFieldRefs = valueRefs $ map snd $ Map.toList $ pathRefInstanceFields ps r
        seen' = Set.insert r seen

reachableRefs :: SpecPathState -> [SpecJavaValue] -> Set.Set Ref
reachableRefs ps vs  =
  Set.unions [ reachableFromRef ps Set.empty r | r <- roots ]
  where roots = pathStaticFieldRefs ps ++ valueRefs vs

valueRefs :: [SpecJavaValue] -> [Ref]
valueRefs vs = [ r | RValue r <- vs ]

useLogicExprPS :: JSS.Path SharedContext
               -> SharedContext
               -> LogicExpr
               -> IO Term
useLogicExprPS ps sc le = do
  let mlocals = (^. cfLocals) <$> currentCallFrame ps
  args <- mapM (readJavaTerm sc mlocals ps) (logicExprJavaExprs le)
  useLogicExpr sc le args

evalAssumptions :: SharedContext -> SpecPathState -> [LogicExpr] -> IO Term
evalAssumptions sc ps as = do
  assumptionList <- mapM (useLogicExprPS ps sc) as
  true <- scBool sc True
  foldM (scAnd sc) true assumptionList
