{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE GADTs #-}

module SAWScript.CrucibleResolveSetupValue
  ( LLVMVal, LLVMPtr
  , resolveSetupVal
  , typeOfLLVMVal
  , typeOfSetupValue
  , resolveTypedTerm
  , resolveSAWPred
  , resolveSetupFieldIndex
  , equalValsPred
  ) where

import Control.Lens
import Control.Monad (zipWithM, foldM)
import Data.Foldable (toList)
import Data.Maybe (fromMaybe, listToMaybe, fromJust)
import Data.IORef
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import qualified Text.LLVM.AST as L

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Utils.PP as Cryptol (pp)

import qualified Lang.Crucible.BaseTypes as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (Some(..))
import qualified Lang.Crucible.Solver.Interface as Crucible hiding (mkStruct)
import qualified Lang.Crucible.Solver.SimpleBuilder as Crucible

import qualified Lang.Crucible.LLVM.Bytes as Crucible
import qualified Lang.Crucible.LLVM.DataLayout as Crucible
import qualified Lang.Crucible.LLVM.Extension as Crucible
import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.MemModel.Type as Crucible
import qualified Lang.Crucible.LLVM.MemModel.Pointer as Crucible
import qualified Lang.Crucible.Solver.Interface as Crucible (bvLit, bvAdd, Pred)
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible
-- import           Lang.Crucible.Utils.MonadST
import qualified Data.Parameterized.NatRepr as NatRepr

import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.Cryptol (importType, emptyEnv)
import Text.LLVM.DebugUtils as L

import qualified Verifier.SAW.Simulator.SBV as SBV (sbvSolveBasic, toWord)
import qualified Data.SBV.Dynamic as SBV (svAsInteger)

import SAWScript.TypedTerm
import SAWScript.Prover.Rewrite

import SAWScript.CrucibleMethodSpecIR

--import qualified SAWScript.LLVMBuiltins as LB

type LLVMVal = Crucible.LLVMVal Sym
type LLVMPtr wptr = Crucible.LLVMPtr Sym wptr

-- | Use the LLVM metadata to determine the struct field index
-- corresponding to the given field name.
resolveSetupValueInfo ::
  CrucibleContext wptr            {- ^ crucible context  -} ->
  Map AllocIndex Crucible.MemType {- ^ allocation types  -} ->
  SetupValue                      {- ^ pointer to struct -} ->
  L.Info                          {- ^ field index       -}
resolveSetupValueInfo cc env v =
  case v of
    -- SetupGlobal g ->
    SetupField a n ->
       fromMaybe L.Unknown $
       do L.Pointer (L.Structure xs) <- return (resolveSetupValueInfo cc env a)
          listToMaybe [L.Pointer i | (n',_,i) <- xs, n == n' ]

    _ -> L.Unknown

-- | Use the LLVM metadata to determine the struct field index
-- corresponding to the given field name.
resolveSetupFieldIndex ::
  CrucibleContext wptr            {- ^ crucible context  -} ->
  Map AllocIndex Crucible.MemType {- ^ allocation types  -} ->
  SetupValue                      {- ^ pointer to struct -} ->
  String                          {- ^ field name        -} ->
  Maybe Int                       {- ^ field index       -}
resolveSetupFieldIndex cc env v n =
  case resolveSetupValueInfo cc env v of
    L.Pointer (L.Structure xs) ->
      case [o | (n',o,_) <- xs, n == n' ] of
        [] -> Nothing
        o:_ ->
          do Crucible.PtrType symTy <- typeOfSetupValue cc env v
             Crucible.StructType si <- let ?lc = lc in TyCtx.asMemType symTy
             V.findIndex (\fi -> Crucible.bytesToBits (Crucible.fiOffset fi) == toInteger o) (Crucible.siFields si)

    _ -> Nothing
  where
    lc = cc^.ccTypeCtx

typeOfSetupValue ::
  Monad m =>
  CrucibleContext wptr ->
  Map AllocIndex Crucible.MemType ->
  SetupValue ->
  m Crucible.MemType
typeOfSetupValue cc env val =
  do let ?lc = cc^.ccTypeCtx
     typeOfSetupValue' cc env val

typeOfSetupValue' ::
  Monad m =>
  CrucibleContext wptr ->
  Map AllocIndex Crucible.MemType ->
  SetupValue ->
  m Crucible.MemType
typeOfSetupValue' cc env val =
  case val of
    SetupVar i ->
      case Map.lookup i env of
        Nothing -> fail ("typeOfSetupValue: Unresolved prestate variable:" ++ show i)
        Just memTy -> return (Crucible.PtrType (Crucible.MemType memTy))
    SetupTerm tt ->
      case ttSchema tt of
        Cryptol.Forall [] [] ty ->
          case toLLVMType dl (Cryptol.evalValType Map.empty ty) of
            Nothing -> fail "typeOfSetupValue: non-representable type"
            Just memTy -> return memTy
        s -> fail $ unlines [ "typeOfSetupValue: expected monomorphic term"
                            , "instead got:"
                            , show (Cryptol.pp s)
                            ]
    SetupStruct vs ->
      do memTys <- traverse (typeOfSetupValue cc env) vs
         let si = Crucible.mkStructInfo dl False memTys
         return (Crucible.StructType si)
    SetupArray [] -> fail "typeOfSetupValue: invalid empty crucible_array"
    SetupArray (v : vs) ->
      do memTy <- typeOfSetupValue cc env v
         _memTys <- traverse (typeOfSetupValue cc env) vs
         -- TODO: check that all memTys are compatible with memTy
         return (Crucible.ArrayType (length (v:vs)) memTy)
    SetupField v n ->
      case resolveSetupFieldIndex cc env v n of
        Nothing -> fail ("Unable to resolve field name: " ++ show n)
        Just i  -> typeOfSetupValue' cc env (SetupElem v i)
    SetupElem v i ->
      do memTy <- typeOfSetupValue cc env v
         let msg = "typeOfSetupValue: crucible_elem requires pointer to struct or array"
         case memTy of
           Crucible.PtrType symTy ->
             case let ?lc = lc in TyCtx.asMemType symTy of
               Just memTy' ->
                 case memTy' of
                   Crucible.ArrayType n memTy''
                     | i < n -> return (Crucible.PtrType (Crucible.MemType memTy''))
                     | otherwise -> fail $ "typeOfSetupValue: array type index out of bounds: " ++ show (i, n)
                   Crucible.StructType si ->
                     case Crucible.siFieldInfo si i of
                       Just fi -> return (Crucible.PtrType (Crucible.MemType (Crucible.fiType fi)))
                       Nothing -> fail $ "typeOfSetupValue: struct type index out of bounds: " ++ show i
                   _ -> fail msg
               Nothing -> fail msg
           _ -> fail msg
    SetupNull ->
      -- We arbitrarily set the type of NULL to void*, because a) it
      -- is memory-compatible with any type that NULL can be used at,
      -- and b) it prevents us from doing a type-safe dereference
      -- operation.
      return (Crucible.PtrType Crucible.VoidType)
    SetupGlobal name ->
      do let m = cc^.ccLLVMModule
             tys = [ (L.globalSym g, L.globalType g) | g <- L.modGlobals m ] ++
                   [ (L.decName d, L.decFunType d) | d <- L.modDeclares m ] ++
                   [ (L.defName d, L.defFunType d) | d <- L.modDefines m ]
         case lookup (L.Symbol name) tys of
           Nothing -> fail $ "typeOfSetupValue: unknown global " ++ show name
           Just ty ->
             case let ?lc = lc in TyCtx.liftType ty of
               Nothing -> fail $ "typeOfSetupValue: invalid type " ++ show ty
               Just symTy -> return (Crucible.PtrType symTy)
  where
    lc = cc^.ccTypeCtx
    dl = TyCtx.llvmDataLayout lc

-- | Translate a SetupValue into a Crucible LLVM value, resolving
-- references
resolveSetupVal ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) ->
  Map AllocIndex Crucible.MemType ->
  SetupValue             ->
  IO LLVMVal
resolveSetupVal cc env tyenv val =
  case val of
    SetupVar i
      | Just ptr <- Map.lookup i env -> return (Crucible.ptrToPtrVal ptr)
      | otherwise -> fail ("resolveSetupVal: Unresolved prestate variable:" ++ show i)
    SetupTerm tm -> resolveTypedTerm cc tm
    SetupStruct vs -> do
      vals <- mapM (resolveSetupVal cc env tyenv) vs
      let tps = map (typeOfLLVMVal dl) vals
      let flds = case Crucible.typeF (Crucible.mkStruct (V.fromList (mkFields dl 0 0 tps))) of
            Crucible.Struct v -> v
            _ -> error "impossible"
      return $ Crucible.LLVMValStruct (V.zip flds (V.fromList vals))
    SetupArray [] -> fail "resolveSetupVal: invalid empty array"
    SetupArray vs -> do
      vals <- V.mapM (resolveSetupVal cc env tyenv) (V.fromList vs)
      let tp = typeOfLLVMVal dl (V.head vals)
      return $ Crucible.LLVMValArray tp vals
    SetupField v n ->
      case resolveSetupFieldIndex cc tyenv v n of
        Nothing -> fail ("Unable to resolve field name: " ++ show n)
        Just i  -> resolveSetupVal cc env tyenv (SetupElem v i)
    SetupElem v i ->
      do memTy <- typeOfSetupValue cc tyenv v
         let msg = "resolveSetupVal: crucible_elem requires pointer to struct or array"
         delta <- case memTy of
           Crucible.PtrType symTy ->
             case let ?lc = lc in TyCtx.asMemType symTy of
               Just memTy' ->
                 case memTy' of
                   Crucible.ArrayType n memTy''
                     | i < n -> return (fromIntegral i * Crucible.memTypeSize dl memTy'')
                   Crucible.StructType si ->
                     case Crucible.siFieldOffset si i of
                       Just d -> return d
                       Nothing -> fail $ "resolveSetupVal: struct type index out of bounds: " ++ show (i, memTy')
                   _ -> fail msg
               Nothing -> fail msg
           _ -> fail msg
         ptr <- resolveSetupVal cc env tyenv v
         case ptr of
           Crucible.LLVMValInt blk off ->
             do delta' <- Crucible.bvLit sym (Crucible.bvWidth off) (Crucible.bytesToInteger delta)
                off' <- Crucible.bvAdd sym off delta'
                return (Crucible.LLVMValInt blk off')
           _ -> fail "resolveSetupVal: crucible_elem requires pointer value"
    SetupNull ->
      Crucible.ptrToPtrVal <$> Crucible.mkNullPointer sym Crucible.PtrWidth
    SetupGlobal name ->
      do let mem = cc^.ccEmptyMemImpl
         Crucible.ptrToPtrVal <$> Crucible.doResolveGlobal sym mem (L.Symbol name)
  where
    sym = cc^.ccBackend
    lc = cc^.ccTypeCtx
    dl = TyCtx.llvmDataLayout lc

resolveTypedTerm ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch ->
  TypedTerm       ->
  IO LLVMVal
resolveTypedTerm cc tm =
  case ttSchema tm of
    Cryptol.Forall [] [] ty ->
      resolveSAWTerm cc (Cryptol.evalValType Map.empty ty) (ttTerm tm)
    _ -> fail "resolveSetupVal: expected monomorphic term"

resolveSAWPred ::
  CrucibleContext wptr ->
  Term ->
  IO (Crucible.Pred Sym)
resolveSAWPred cc tm =
  Crucible.bindSAWTerm (cc^.ccBackend) Crucible.BaseBoolRepr tm

resolveSAWTerm ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch ->
  Cryptol.TValue ->
  Term ->
  IO LLVMVal
resolveSAWTerm cc tp tm =
    case tp of
      Cryptol.TVBit ->
        fail "resolveSAWTerm: unimplemented type Bit (FIXME)"
      Cryptol.TVInteger ->
        fail "resolveSAWTerm: unimplemented type Integer (FIXME)"
      Cryptol.TVSeq sz Cryptol.TVBit ->
        case Crucible.someNat sz of
          Just (Crucible.Some w)
            | Just Crucible.LeqProof <- Crucible.isPosNat w ->
              do sc <- Crucible.saw_ctx <$> readIORef (Crucible.sbStateManager sym)
                 ss <- basic_ss sc
                 tm' <- rewriteSharedTerm sc ss tm
                 mx <- case getAllExts tm' of
                         [] -> do
                           -- Evaluate in SBV to test whether 'tm' is a concrete value
                           sbv <- SBV.toWord =<< SBV.sbvSolveBasic (scModule sc) Map.empty [] tm'
                           return (SBV.svAsInteger sbv)
                         _ -> return Nothing
                 v <- case mx of
                        Just x  -> Crucible.bvLit sym w x
                        Nothing -> Crucible.bindSAWTerm sym (Crucible.BaseBVRepr w) tm'
                 Crucible.ptrToPtrVal <$> Crucible.llvmPointer_bv sym v
          _ -> fail ("Invalid bitvector width: " ++ show sz)
      Cryptol.TVSeq sz tp' ->
        do sc    <- Crucible.saw_ctx <$> (readIORef (Crucible.sbStateManager sym))
           sz_tm <- scNat sc (fromIntegral sz)
           tp_tm <- importType sc emptyEnv (Cryptol.tValTy tp')
           let f i = do i_tm <- scNat sc (fromIntegral i)
                        tm' <- scAt sc sz_tm tp_tm tm i_tm
                        resolveSAWTerm cc tp' tm'
           case toLLVMType dl tp' of
             Nothing -> fail "resolveSAWTerm: invalid type"
             Just mt -> do
               gt <- Crucible.toStorableType mt
               Crucible.LLVMValArray gt . V.fromList <$> mapM f [ 0 .. (sz-1) ]
      Cryptol.TVStream _tp' ->
        fail "resolveSAWTerm: invalid infinite stream type"
      Cryptol.TVTuple tps ->
        do sc <- Crucible.saw_ctx <$> (readIORef (Crucible.sbStateManager sym))
           tms <- mapM (scTupleSelector sc tm) [1 .. length tps]
           vals <- zipWithM (resolveSAWTerm cc) tps tms
           storTy <-
             case toLLVMType dl tp of
               Just memTy -> Crucible.toStorableType memTy
               _ -> fail "resolveSAWTerm: invalid tuple type"
           fields <-
             case Crucible.typeF storTy of
               Crucible.Struct fields -> return fields
               _ -> fail "resolveSAWTerm: impossible: expected struct"
           return (Crucible.LLVMValStruct (V.zip fields (V.fromList vals)))
      Cryptol.TVRec _flds ->
        fail "resolveSAWTerm: unimplemented record type (FIXME)"
      Cryptol.TVFun _ _ ->
        fail "resolveSAWTerm: invalid function type"
  where
    sym = cc^.ccBackend
    dl = TyCtx.llvmDataLayout (cc^.ccTypeCtx)

toLLVMType :: Crucible.DataLayout -> Cryptol.TValue -> Maybe Crucible.MemType
toLLVMType dl tp =
    case tp of
      Cryptol.TVBit -> Nothing -- FIXME
      Cryptol.TVInteger -> Nothing
      Cryptol.TVSeq n Cryptol.TVBit
        | n > 0 -> Just (Crucible.IntType (fromInteger n))
        | otherwise -> Nothing
      Cryptol.TVSeq n t -> do
        t' <- toLLVMType dl t
        let n' = fromIntegral n
        Just (Crucible.ArrayType n' t')
      Cryptol.TVStream _tp' -> Nothing
      Cryptol.TVTuple tps -> do
        tps' <- mapM (toLLVMType dl) tps
        let si = Crucible.mkStructInfo dl False tps'
        return (Crucible.StructType si)
      Cryptol.TVRec _flds -> Nothing -- FIXME
      Cryptol.TVFun _ _ -> Nothing

mkFields ::
  Crucible.DataLayout ->
  Crucible.Alignment ->
  Crucible.Bytes ->
  [Crucible.Type] ->
  [(Crucible.Type, Crucible.Bytes)]
mkFields _ _ _ [] = []
mkFields dl a off (ty : tys) = (ty, pad) : mkFields dl a' off' tys
    where
      end = off + Crucible.typeSize ty
      off' = Crucible.padToAlignment end nextAlign
      pad = off' - end
      a' = max a (typeAlignment dl ty)
      nextAlign = case tys of
        [] -> a'
        (ty' : _) -> typeAlignment dl ty'



typeAlignment :: Crucible.DataLayout -> Crucible.Type -> Crucible.Alignment
typeAlignment dl ty =
  case Crucible.typeF ty of
    Crucible.Bitvector bytes -> Crucible.integerAlignment dl (fromInteger (Crucible.bytesToBits bytes))
    Crucible.Float           -> fromJust (Crucible.floatAlignment dl 32)
    Crucible.Double          -> fromJust (Crucible.floatAlignment dl 64)
    Crucible.Array _sz ty'   -> typeAlignment dl ty'
    Crucible.Struct flds     -> V.foldl max 0 (fmap (typeAlignment dl . (^. Crucible.fieldVal)) flds)

typeOfLLVMVal :: Crucible.DataLayout -> LLVMVal -> Crucible.Type
typeOfLLVMVal _dl val =
  case val of
    Crucible.LLVMValInt _bkl bv ->
       Crucible.bitvectorType (Crucible.intWidthSize (fromIntegral (NatRepr.natValue (Crucible.bvWidth bv))))
    Crucible.LLVMValReal _ _    -> error "FIXME: typeOfLLVMVal LLVMValReal"
    Crucible.LLVMValStruct flds -> Crucible.mkStruct (fmap fieldType flds)
    Crucible.LLVMValArray tp vs -> Crucible.arrayType (fromIntegral (V.length vs)) tp
  where
    fieldType (f, _) = (f ^. Crucible.fieldVal, Crucible.fieldPad f)

equalValsPred ::
  CrucibleContext wptr ->
  LLVMVal ->
  LLVMVal ->
  IO (Crucible.Pred Sym)
equalValsPred cc v1 v2 = go (v1, v2)
  where
  go :: (LLVMVal, LLVMVal) -> IO (Crucible.Pred Sym)

  go (Crucible.LLVMValInt blk1 off1, Crucible.LLVMValInt blk2 off2)
       | Just Crucible.Refl <- Crucible.testEquality (Crucible.bvWidth off1) (Crucible.bvWidth off2)
       = do blk_eq <- Crucible.natEq sym blk1 blk2
            off_eq <- Crucible.bvEq sym off1 off2
            Crucible.andPred sym blk_eq off_eq
  go (Crucible.LLVMValReal xsz x, Crucible.LLVMValReal ysz y) | xsz == ysz
       = Crucible.realEq sym x y
  go (Crucible.LLVMValStruct xs, Crucible.LLVMValStruct ys)
       | V.length xs == V.length ys
       = do cs <- mapM go (zip (map snd (toList xs)) (map snd (toList ys)))
            foldM (Crucible.andPred sym) (Crucible.truePred sym) cs
  go (Crucible.LLVMValArray _tpx xs, Crucible.LLVMValArray _tpy ys)
       | V.length xs == V.length ys
       = do cs <- mapM go (zip (toList xs) (toList ys))
            foldM (Crucible.andPred sym) (Crucible.truePred sym) cs

  go _ = return (Crucible.falsePred sym)

  sym = cc^.ccBackend
