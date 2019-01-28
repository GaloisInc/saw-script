{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module SAWScript.JVM.CrucibleResolveSetupValue
  ( JVMVal(..)
  , JVMRefVal
  , resolveSetupVal
  -- , typeOfJVMVal
  , typeOfSetupValue
  , resolveTypedTerm
  , resolveSAWPred
  -- , resolveSetupFieldIndex
  , equalValsPred
  , refIsNull
  , refIsEqual
  ) where

import Control.Lens
--import Control.Monad (zipWithM, foldM)
--import Data.Foldable (toList)
--import Data.Maybe (fromMaybe, listToMaybe, fromJust)
import Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
--import qualified Data.Vector as V

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)

--import           Data.Parameterized.Classes ((:~:)(..), testEquality)
--import           Data.Parameterized.Some (Some(..))
--import           Data.Parameterized.NatRepr
--                   (NatRepr(..), someNat, natValue, LeqProof(..), isPosNat)

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import qualified What4.ProgramLoc as W4

import qualified Lang.Crucible.Backend.SAWCore as Crucible
--import qualified SAWScript.CrucibleLLVM as Crucible

import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
--import Verifier.SAW.Cryptol (importType, emptyEnv)
import Verifier.SAW.TypedTerm
--import Text.LLVM.DebugUtils as L

-- crucible
import qualified Lang.Crucible.Backend as Crucible (IsSymInterface)
import qualified Lang.Crucible.CFG.Expr as Crucible (App(..))
import qualified Lang.Crucible.Simulator as Crucible (RegValue, RegValue'(..), extensionEval)
import qualified Lang.Crucible.Simulator.Evaluation as Crucible (evalApp)

-- what4
import qualified What4.Interface as W4
import qualified What4.Partial as W4

-- crucible-jvm
import qualified Lang.Crucible.JVM.Translation as CJ

-- sbv
import qualified Verifier.SAW.Simulator.SBV as SBV (sbvSolveBasic, toWord, toBool)
import qualified Data.SBV.Dynamic as SBV (svAsInteger, svAsBool)

-- jvm-parser
import qualified Language.JVM.Parser as J

--import SAWScript.JavaExpr (JavaType(..))
import SAWScript.Prover.Rewrite
import SAWScript.JVM.CrucibleMethodSpecIR

--import qualified SAWScript.LLVMBuiltins as LB

data JVMVal
  = RVal (Crucible.RegValue Sym CJ.JVMRefType)
  | IVal (Crucible.RegValue Sym CJ.JVMIntType)
  | LVal (Crucible.RegValue Sym CJ.JVMLongType)
  --- | DVal (Crucible.RegValue Sym CJ.JVMDoubleType)
  --- | FVal (Crucible.RegValue Sym CJ.JVMFloatType)
{-
  | ElemVal (JVMRefVal sym) Int -- reference to some element in an array.
  | FieldVal (JVMRefVal sym) String -- FIXME: 2nd argument should match implementation of field names.
  | ArrayVal [JVMVal sym]
-}

instance Show JVMVal where
  show (RVal _) = "RVal"
  show (IVal _) = "IVal"
  show (LVal _) = "LVal"

type JVMRefVal = Crucible.RegValue Sym CJ.JVMRefType

-- | This is a representation of somewhere a JVM value can be stored.
{-
data JVMPtr
  = JPRef JVMRefVal
  | JPField JVMRefVal String -- FIXME: 2nd argument should match implementation of field names.
  | JPElement JVMRefVal Int
-}

-- Use the LLVM metadata to determine the struct field index
-- corresponding to the given field name.
--resolveSetupValueInfo ::
--  CrucibleContext                 {- ^ crucible context  -} ->
--  Map AllocIndex (W4.ProgramLoc, JavaType) {- ^ allocation types  -} ->
--  Map AllocIndex JIdent           {- ^ allocation type names -} ->
--  SetupValue                      {- ^ pointer to struct -} ->
--  L.Info                          {- ^ field index       -}
--resolveSetupValueInfo cc env nameEnv v =
--  case v of
--    -- SetupGlobal g ->
--    SetupVar i
--      | Just alias <- Map.lookup i nameEnv
--      , let mdMap = Crucible.llvmMetadataMap (cc^.ccTypeCtx)
--      -> L.Pointer (guessAliasInfo mdMap alias)
--    SetupField a n ->
--       fromMaybe L.Unknown $
--       do L.Pointer (L.Structure xs) <- return (resolveSetupValueInfo cc env nameEnv a)
--          listToMaybe [L.Pointer i | (n',_,i) <- xs, n == n' ]
--
--    _ -> L.Unknown

-- Use the LLVM metadata to determine the struct field index
-- corresponding to the given field name.
--resolveSetupFieldIndex ::
--  CrucibleContext                 {- ^ crucible context  -} ->
--  Map AllocIndex (W4.ProgramLoc, Crucible.MemType) {- ^ allocation types  -} ->
--  Map AllocIndex Crucible.Ident   {- ^ allocation type names -} ->
--  SetupValue                      {- ^ pointer to struct -} ->
--  String                          {- ^ field name        -} ->
--  Maybe Int                       {- ^ field index       -}
--resolveSetupFieldIndex cc env nameEnv v n =
--  case resolveSetupValueInfo cc env nameEnv v of
--    L.Pointer (L.Structure xs) ->
--      case [o | (n',o,_) <- xs, n == n' ] of
--        [] -> Nothing
--        o:_ ->
--          do Crucible.PtrType symTy <- typeOfSetupValue cc env nameEnv v
--             Crucible.StructType si <- let ?lc = lc in Crucible.asMemType symTy
--             V.findIndex (\fi -> Crucible.bytesToBits (Crucible.fiOffset fi) == toInteger o) (Crucible.siFields si)
--
--    _ -> Nothing
--  where
--    lc = cc^.ccTypeCtx

typeOfSetupValue ::
  Monad m =>
  CrucibleContext ->
  Map AllocIndex (W4.ProgramLoc, Allocation) ->
  Map AllocIndex JIdent ->
  SetupValue ->
  m J.Type
typeOfSetupValue _cc env _nameEnv val =
  case val of
    SetupVar i ->
      case Map.lookup i env of
        Nothing -> fail ("typeOfSetupValue: Unresolved prestate variable:" ++ show i)
        Just (_, alloc) -> return (allocationType alloc)
    SetupTerm tt ->
      case ttSchema tt of
        Cryptol.Forall [] [] ty ->
          case toJVMType (Cryptol.evalValType Map.empty ty) of
            Nothing -> fail "typeOfSetupValue: non-representable type"
            Just jty -> return jty
        s -> fail $ unlines [ "typeOfSetupValue: expected monomorphic term"
                            , "instead got:"
                            , show (Cryptol.pp s)
                            ]
{-
    SetupStruct vs ->
      fail "typeOfSetupValue: unimplemented jvm_struct"
      {-
      do memTys <- traverse (typeOfSetupValue cc env nameEnv) vs
         let si = Crucible.mkStructInfo dl False memTys
         return (Crucible.StructType si)
      -}
    SetupArray [] -> fail "typeOfSetupValue: invalid empty jvm_array"
    SetupArray (v : vs) ->
      do _memTy <- typeOfSetupValue cc env nameEnv v
         _memTys <- traverse (typeOfSetupValue cc env nameEnv) vs
         -- TODO: check that all memTys are compatible with memTy
         -- return (Crucible.ArrayType (length (v:vs)) memTy)
         fail "typeOfSetupValue: unimplemented jvm_array"
    SetupField v n ->
      do ty <- typeOfSetupValue cc env nameEnv v
         let msg = "typeOfSetupValue: jvm_field requires object reference"
         case ty of
           JVMSetupBaseType (JavaClass cname) ->
             case getTypeOfField cc cname n of
               Just fty -> return (JVMSetupPtr)
               Nothing -> fail ("Unable to resolve field name: " ++ show (cname, n))
           _ -> fail msg
    SetupElem v i ->
      do ty <- typeOfSetupValue cc env nameEnv v
         let msg = "typeOfSetupValue: jvm_elem requires array reference"
         case ty of
           JVMSetupBaseType (JavaArray n elemTy)
             | i < n -> return (JVMSetupPtrType elemTy)
             | otherwise -> fail $ "typeOfSetupValue: array type index out of bounds: " ++ show (i, n)
           JVMSetupBaseType (JavaClass cname) ->
             fail "typeOfSetupValue: unimplemented positional field access: " ++ show (i, cname)
           _ -> fail msg
-}
    SetupNull ->
      -- We arbitrarily set the type of NULL to java.lang.Object,
      -- because a) it is memory-compatible with any type that NULL
      -- can be used at, and b) it prevents us from doing any
      -- type-safe field accesses.
      return (J.ClassType (J.mkClassName "java/lang/Object"))
    SetupGlobal name ->
      fail ("typeOfSetupValue: unimplemented jvm_global: " ++ name)
      {-
      do let m = cc^.ccLLVMModule
             tys = [ (L.globalSym g, L.globalType g) | g <- L.modGlobals m ] ++
                   [ (L.decName d, L.decFunType d) | d <- L.modDeclares m ] ++
                   [ (L.defName d, L.defFunType d) | d <- L.modDefines m ]
         case lookup (L.Symbol name) tys of
           Nothing -> fail $ "typeOfSetupValue: unknown global " ++ show name
           Just ty ->
             case let ?lc = lc in Crucible.liftType ty of
               Nothing -> fail $ "typeOfSetupValue: invalid type " ++ show ty
               Just symTy -> return (Crucible.PtrType symTy)
      -}

--getTypeOfField ::
--  CrucibleContext ->
--  String {- class name -} ->
--  String {- field name -} ->
--  Maybe JavaType
--getTypeOfField cc cname fn = Nothing -- FIXME: implement

-- | Translate a SetupValue into a Crucible JVM value, resolving
-- references
resolveSetupVal ::
  CrucibleContext ->
  Map AllocIndex JVMRefVal ->
  Map AllocIndex (W4.ProgramLoc, Allocation) ->
  Map AllocIndex JIdent ->
  SetupValue ->
  IO JVMVal
resolveSetupVal cc env _tyenv _nameEnv val =
  case val of
    SetupVar i
      | Just v <- Map.lookup i env -> return (RVal v)
      | otherwise -> fail ("resolveSetupVal: Unresolved prestate variable:" ++ show i)
    SetupTerm tm -> resolveTypedTerm cc tm
{-
    SetupStruct _vs ->
      do vals <- mapM (resolveSetupVal cc env tyenv nameEnv) vs
         let tps = map (typeOfJVMVal dl) vals
         let flds = case Crucible.typeF (Crucible.mkStructType (V.fromList (mkFields dl 0 0 tps))) of
               Crucible.Struct v -> v
               _ -> error "impossible"
         return $ Crucible.JVMValStruct (V.zip flds (V.fromList vals))
    SetupArray [] -> fail "resolveSetupVal: invalid empty array"
    SetupArray vs ->
      do vals <- V.mapM (resolveSetupVal cc env tyenv nameEnv) (V.fromList vs)
         -- let tp = typeOfJVMVal dl (V.head vals)
         return $ ArrayVal vals
    SetupField v n ->
      do ty <- typeOfSetupValue cc env nameEnv v
         let msg = "typeOfSetupValue: jvm_field requires object reference"
         case ty of
           JVMSetupBaseType (JavaClass cname) ->
             case getTypeOfField cc cname n of
               Just fty -> return ()
               Nothing -> fail ("Unable to resolve field name: " ++ show (cname, n))
           _ -> fail msg
         v' <- resolveSetupVal cc env tyenv nameEnv v
         case v' of
           RVal ref -> return (FieldVal ref n)
           _ -> fail msg
    SetupElem v i ->
      do ty <- typeOfSetupValue cc tyenv nameEnv v
         let msg = "resolveSetupVal: crucible_elem requires array reference"
         case ty of
           JVMSetupBaseType (JavaArray n elemTy)
             | i < n -> return ()
             | otherwise -> fail $ "resolveSetupVal: array index out of bounds: " ++ show (i, n)
           _ -> fail msg
         v' <- resolveSetupVal cc env tyenv nameEnv v
         case v' of
           RVal ref -> return (ElemVal ref i)
           _ -> fail msg
-}
    SetupNull ->
      return (RVal (W4.maybePartExpr sym Nothing))
    SetupGlobal name ->
      fail $ "resolveSetupVal: unimplemented jvm_global: " ++ name
  where
    sym = cc^.ccBackend

resolveTypedTerm ::
  CrucibleContext ->
  TypedTerm       ->
  IO JVMVal
resolveTypedTerm cc tm =
  case ttSchema tm of
    Cryptol.Forall [] [] ty ->
      resolveSAWTerm cc (Cryptol.evalValType Map.empty ty) (ttTerm tm)
    _ -> fail "resolveSetupVal: expected monomorphic term"

resolveSAWPred ::
  CrucibleContext ->
  Term ->
  IO (W4.Pred Sym)
resolveSAWPred cc tm =
  Crucible.bindSAWTerm (cc^.ccBackend) W4.BaseBoolRepr tm

resolveSAWTerm ::
  CrucibleContext ->
  Cryptol.TValue ->
  Term ->
  IO JVMVal
resolveSAWTerm cc tp tm =
  case tp of
    Cryptol.TVBit ->
      do b <- resolveBoolTerm sym tm
         x0 <- W4.bvLit sym W4.knownNat 0
         x1 <- W4.bvLit sym W4.knownNat 1
         x <- W4.bvIte sym b x1 x0
         return (IVal x)
    Cryptol.TVInteger ->
      fail "resolveSAWTerm: unimplemented type Integer (FIXME)"
    Cryptol.TVIntMod _ ->
      fail "resolveSAWTerm: unimplemented type Z n (FIXME)"
    Cryptol.TVSeq sz Cryptol.TVBit ->
      case sz of
        8  -> fail "resolveSAWTerm: unimplemented type char (FIXME)"
        16 -> fail "resolveSAWTerm: unimplemented type short (FIXME)"
        32 -> IVal <$> resolveBitvectorTerm sym W4.knownNat tm
        64 -> LVal <$> resolveBitvectorTerm sym W4.knownNat tm
        _  -> fail ("Invalid bitvector width: " ++ show sz)
        {-
    Cryptol.TVSeq sz Cryptol.TVBit ->
      case someNat sz of
        Just (Some w)
          | Just LeqProof <- isPosNat w ->
            do sc <- Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym)
               ss <- basic_ss sc
               tm' <- rewriteSharedTerm sc ss tm
               mx <- case getAllExts tm' of
                       [] -> do
                         -- Evaluate in SBV to test whether 'tm' is a concrete value
                         modmap <- scGetModuleMap sc
                         sbv <- SBV.toWord =<< SBV.sbvSolveBasic modmap Map.empty [] tm'
                         return (SBV.svAsInteger sbv)
                       _ -> return Nothing
               v <- case mx of
                      Just x  -> W4.bvLit sym w x
                      Nothing -> Crucible.bindSAWTerm sym (W4.BaseBVRepr w) tm'
               Crucible.ptrToPtrVal <$> Crucible.llvmPointer_bv sym v
        _ -> fail ("Invalid bitvector width: " ++ show sz)
        -}
    Cryptol.TVSeq _sz _tp' ->
      fail "resolveSAWTerm: unimplemented sequence type"
{-
    Cryptol.TVSeq sz tp' ->
      do sc    <- Crucible.saw_ctx <$> (readIORef (W4.sbStateManager sym))
         sz_tm <- scNat sc (fromIntegral sz)
         tp_tm <- importType sc emptyEnv (Cryptol.tValTy tp')
         let f i = do i_tm <- scNat sc (fromIntegral i)
                      tm' <- scAt sc sz_tm tp_tm tm i_tm
                      resolveSAWTerm cc tp' tm'
         ArrayVal <$> mapM f [ 0 .. (sz-1) ]
         {-
         case toJavaType tp' of
           Nothing -> fail "resolveSAWTerm: invalid type"
           Just mt -> ArrayVal <$> mapM f [ 0 .. (sz-1) ]
         -}
-}
    Cryptol.TVStream _tp' ->
      fail "resolveSAWTerm: unsupported infinite stream type"
    Cryptol.TVTuple _tps ->
      fail "resolveSAWTerm: unsupported tuple type"
    Cryptol.TVRec _flds ->
      fail "resolveSAWTerm: unsupported record type"
    Cryptol.TVFun _ _ ->
      fail "resolveSAWTerm: unsupported function type"
  where
    sym = cc^.ccBackend

resolveBitvectorTerm ::
  forall w.
  (1 W4.<= w) =>
  Sym ->
  W4.NatRepr w ->
  Term ->
  IO (W4.SymBV Sym w)
resolveBitvectorTerm sym w tm =
  do sc <- Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym)
     ss <- basic_ss sc
     tm' <- rewriteSharedTerm sc ss tm
     mx <- case getAllExts tm' of
             [] ->
               do -- Evaluate in SBV to test whether 'tm' is a concrete value
                  modmap <- scGetModuleMap sc
                  sbv <- SBV.toWord =<< SBV.sbvSolveBasic modmap Map.empty [] tm'
                  return (SBV.svAsInteger sbv)
             _ -> return Nothing
     case mx of
       Just x  -> W4.bvLit sym w x
       Nothing -> Crucible.bindSAWTerm sym (W4.BaseBVRepr w) tm'

resolveBoolTerm :: Sym -> Term -> IO (W4.Pred Sym)
resolveBoolTerm sym tm =
  do sc <- Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym)
     ss <- basic_ss sc
     tm' <- rewriteSharedTerm sc ss tm
     mx <- case getAllExts tm' of
             [] ->
               do -- Evaluate in SBV to test whether 'tm' is a concrete value
                  modmap <- scGetModuleMap sc
                  sbv <- SBV.toBool <$> SBV.sbvSolveBasic modmap Map.empty [] tm'
                  return (SBV.svAsBool sbv)
             _ -> return Nothing
     case mx of
       Just x  -> return (W4.backendPred sym x)
       Nothing -> Crucible.bindSAWTerm sym W4.BaseBoolRepr tm'

toJVMType :: Cryptol.TValue -> Maybe J.Type
toJVMType tp =
  case tp of
    Cryptol.TVBit -> Just J.BooleanType
    Cryptol.TVInteger -> Nothing
    Cryptol.TVIntMod _ -> Nothing
    Cryptol.TVSeq n Cryptol.TVBit ->
      case n of
        8  -> Just J.CharType
        16 -> Just J.ShortType
        32 -> Just J.IntType
        64 -> Just J.LongType
        _  -> Nothing
    Cryptol.TVSeq _n t ->
      do t' <- toJVMType t
         Just (J.ArrayType t')
    Cryptol.TVStream _tp' -> Nothing
    Cryptol.TVTuple tps -> Nothing
    Cryptol.TVRec _flds -> Nothing
    Cryptol.TVFun _ _ -> Nothing

{-
toJavaType :: Cryptol.TValue -> Maybe JavaType
toJavaType tp =
  case tp of
    Cryptol.TVBit -> Just JavaBoolean
    Cryptol.TVInteger -> Nothing
    Cryptol.TVIntMod _ -> Nothing
    Cryptol.TVSeq n Cryptol.TVBit ->
      case n of
        8  -> Just JavaChar
        16 -> Just JavaShort
        32 -> Just JavaInt
        64 -> Just JavaLong
        _  -> Nothing
    Cryptol.TVSeq n t ->
      do t' <- toJavaType t
         let n' = fromInteger n -- FIXME: check for overflow
         Just (JavaArray n' t')
    Cryptol.TVStream _tp' -> Nothing
    Cryptol.TVTuple tps -> Nothing
    Cryptol.TVRec _flds -> Nothing
    Cryptol.TVFun _ _ -> Nothing
-}

--typeOfJVMVal :: Crucible.DataLayout -> JVMVal -> Crucible.Type
--typeOfJVMVal _dl val =
--  case val of
--    Crucible.JVMValInt _bkl bv ->
--       Crucible.bitvectorType (Crucible.intWidthSize (fromIntegral (natValue (W4.bvWidth bv))))
--    Crucible.JVMValFloat _ _    -> error "FIXME: typeOfJVMVal JVMValFloat"
--    Crucible.JVMValStruct flds -> Crucible.mkStructType (fmap fieldType flds)
--    Crucible.JVMValArray tp vs -> Crucible.arrayType (fromIntegral (V.length vs)) tp
--  where
--    fieldType (f, _) = (f ^. Crucible.fieldVal, Crucible.fieldPad f)

equalValsPred ::
  CrucibleContext ->
  JVMVal ->
  JVMVal ->
  IO (W4.Pred Sym)
equalValsPred cc v1 v2 = go (v1, v2)
  where
  go :: (JVMVal, JVMVal) -> IO (W4.Pred Sym)
  go (RVal r1, RVal r2) = refIsEqual sym r1 r2
  go (IVal i1, IVal i2) = W4.bvEq sym i1 i2
  go (LVal l1, LVal l2) = W4.bvEq sym l1 l2
  go _ = return (W4.falsePred sym)

  sym = cc^.ccBackend


refIsNull :: Sym -> JVMRefVal -> IO (W4.Pred Sym)
refIsNull sym ref =
  case ref of
    W4.PE p _ -> W4.notPred sym p
    W4.Unassigned -> return (W4.truePred sym)

refIsEqual :: Sym -> JVMRefVal -> JVMRefVal -> IO (W4.Pred Sym)
refIsEqual sym ref1 ref2 =
  case ref1 of
    W4.Unassigned ->
      case ref2 of
        W4.Unassigned -> return (W4.truePred sym)
        W4.PE p2 r2 -> W4.notPred sym p2
    W4.PE p1 r1 ->
      case ref2 of
        W4.Unassigned -> W4.notPred sym p1
        W4.PE p2 r2 ->
          do n1 <- W4.notPred sym p1
             n2 <- W4.notPred sym p2
             n <- W4.andPred sym n1 n2
             p <- W4.andPred sym p1 p2
             e <- doAppJVM sym (Crucible.ReferenceEq W4.knownRepr (Crucible.RV r1) (Crucible.RV r2))
             W4.orPred sym n =<< W4.andPred sym p e

-- TODO: move to crucible-jvm?
doAppJVM ::
  Crucible.IsSymInterface sym =>
  sym -> Crucible.App CJ.JVM (Crucible.RegValue' sym) tp -> IO (Crucible.RegValue sym tp)
doAppJVM sym =
  Crucible.evalApp sym CJ.jvmIntrinsicTypes out
    (Crucible.extensionEval CJ.jvmExtensionImpl sym CJ.jvmIntrinsicTypes out) (return . Crucible.unRV)
  where
    out _verbosity = putStrLn -- FIXME: use verbosity
