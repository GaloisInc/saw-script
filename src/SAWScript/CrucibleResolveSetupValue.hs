module SAWScript.CrucibleResolveSetupValue
  ( LLVMVal
  , resolveSetupVal
  , typeOfLLVMVal
  , typeOfSetupValue
  , resolveTypedTerm
  ) where

import Control.Lens
import Control.Monad (zipWithM)
import Data.Maybe (fromJust)
import Data.IORef
import Data.Word (Word64)
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import qualified Cryptol.Eval.Type as Cryptol (TValue(..), tValTy, evalValType)
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))

import qualified Lang.Crucible.Core as Crucible
import qualified Lang.Crucible.Solver.SimpleBuilder as Crucible
import qualified Lang.Crucible.Utils.Arithmetic as Crucible

import qualified Lang.Crucible.LLVM.DataLayout as Crucible
import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.MemModel.Common as Crucible
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible
-- import           Lang.Crucible.Utils.MonadST
import qualified Data.Parameterized.NatRepr as NatRepr

import Verifier.SAW.SharedTerm
import Verifier.SAW.Cryptol (importType, emptyEnv)

import qualified Verifier.SAW.Simulator.SBV as SBV (sbvSolveBasic, toWord)
import qualified Data.SBV.Dynamic as SBV (svAsInteger)

import SAWScript.Builtins
import SAWScript.TypedTerm

import SAWScript.CrucibleMethodSpecIR

--import qualified SAWScript.LLVMBuiltins as LB

type LLVMVal = Crucible.LLVMVal Sym Crucible.PtrWidth

typeOfSetupValue ::
  Crucible.DataLayout ->
  Map AllocIndex Crucible.MemType ->
  SetupValue ->
  IO Crucible.MemType
typeOfSetupValue dl env val =
  case val of
    SetupVar i ->
      case Map.lookup i env of
        Nothing -> fail ("Unresolved prestate variable:" ++ show i)
        Just memTy -> return memTy
    SetupTerm tt ->
      case ttSchema tt of
        Cryptol.Forall [] [] ty ->
          case toLLVMType dl (Cryptol.evalValType Map.empty ty) of
            Nothing -> fail "typeOfSetupValue: non-representable type"
            Just memTy -> return memTy
        _ -> fail "typeOfSetupValue: expected monomorphic term"
    SetupStruct vs ->
      do memTys <- traverse (typeOfSetupValue dl env) vs
         let si = Crucible.mkStructInfo dl False memTys
         return (Crucible.StructType si)
    SetupArray [] -> fail "typeOfSetupValue: invalid empty crucible_array"
    SetupArray (v : vs) ->
      do memTy <- typeOfSetupValue dl env v
         _memTys <- traverse (typeOfSetupValue dl env) vs
         -- TODO: check that all memTys are compatible with memTy
         return (Crucible.ArrayType (length (v:vs)) memTy)
    SetupNull ->
      -- We arbitrarily set the type of NULL to void*, because a) it
      -- is memory-compatible with any type that NULL can be used at,
      -- and b) it prevents us from doing a type-safe dereference
      -- operation.
      return (Crucible.PtrType Crucible.VoidType)
    SetupGlobal _name ->
      do fail "typeOfSetupValue: unimplemented SetupGlobal"

resolveSetupVal ::
  CrucibleContext        ->
  Map AllocIndex LLVMVal ->
  SetupValue             ->
  IO LLVMVal
resolveSetupVal cc env val =
  case val of
    SetupVar i
      | Just val' <- Map.lookup i env -> return val'
      | otherwise -> fail ("Unresolved prestate variable:" ++ show i)
    SetupTerm tm -> resolveTypedTerm cc tm
    SetupStruct vs -> do
      vals <- mapM (resolveSetupVal cc env) vs
      let tps = map (typeOfLLVMVal dl) vals
      let flds = case Crucible.typeF (Crucible.mkStruct (V.fromList (mkFields dl 0 0 tps))) of
            Crucible.Struct v -> v
            _ -> error "impossible"
      return $ Crucible.LLVMValStruct (V.zip flds (V.fromList vals))
    SetupArray [] -> fail "resolveSetupVal: invalid empty array"
    SetupArray vs -> do
      vals <- V.mapM (resolveSetupVal cc env) (V.fromList vs)
      let tp = typeOfLLVMVal dl (V.head vals)
      return $ Crucible.LLVMValArray tp vals
    SetupNull ->
      Crucible.packMemValue sym ptrType Crucible.LLVMPointerRepr =<< Crucible.mkNullPointer sym
    SetupGlobal _name -> fail "SetupGlobal not implemented"
--    SetupGlobal name -> withMem cc $ \_sym impl -> do
--      r <- Crucible.doResolveGlobal sym impl (L.Symbol name)
--      v <- Crucible.packMemValue sym ptrType Crucible.llvmPointerRepr r
--      return (v, impl)

  where
  sym = ccBackend cc
  dl = TyCtx.llvmDataLayout (Crucible.llvmTypeCtx (ccLLVMContext cc))
  ptrType = Crucible.bitvectorType (dl^.Crucible.ptrSize)


resolveTypedTerm ::
  CrucibleContext ->
  TypedTerm       ->
  IO LLVMVal
resolveTypedTerm cc tm =
  case ttSchema tm of
    Cryptol.Forall [] [] ty ->
      resolveSAWTerm cc (Cryptol.evalValType Map.empty ty) (ttTerm tm)
    _ -> fail "resolveSetupVal: expected monomorphic term"


resolveSAWTerm ::
  CrucibleContext ->
  Cryptol.TValue ->
  Term ->
  IO LLVMVal
resolveSAWTerm cc tp tm =
    case tp of
      Cryptol.TVBit ->
        fail "resolveSAWTerm: unimplemented type Bit (FIXME)"
      Cryptol.TVSeq sz Cryptol.TVBit ->
        case Crucible.someNat sz of
          Just (Crucible.Some w)
            | Just Crucible.LeqProof <- Crucible.isPosNat w ->
              do sc <- Crucible.saw_ctx <$> readIORef (Crucible.sbStateManager sym)
                 -- Evaluate in SBV to test whether 'tm' is a concrete value
                 sbv <- SBV.toWord =<< SBV.sbvSolveBasic (scModule sc) Map.empty [] tm
                 case SBV.svAsInteger sbv of
                   Just x -> do
                     loc <- Crucible.curProgramLoc sym
                     let v = Crucible.BVElt w x loc
                     return (Crucible.LLVMValInt w v)
                   Nothing -> do
                     v <- Crucible.bindSAWTerm sym (Crucible.BaseBVRepr w) tm
                     return (Crucible.LLVMValInt w v)
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
    sym = ccBackend cc
    dl = TyCtx.llvmDataLayout (Crucible.llvmTypeCtx (ccLLVMContext cc))

toLLVMType :: Crucible.DataLayout -> Cryptol.TValue -> Maybe Crucible.MemType
toLLVMType dl tp =
    case tp of
      Cryptol.TVBit -> Nothing -- FIXME
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
  Word64 ->
  [Crucible.Type] ->
  [(Crucible.Type, Word64)]
mkFields _ _ _ [] = []
mkFields dl a off (ty : tys) = (ty, pad) : mkFields dl a' off' tys
    where
      end = off + Crucible.typeSize ty
      off' = Crucible.nextPow2Multiple end (fromIntegral nextAlign)
      pad = off' - end
      a' = max a (typeAlignment dl ty)
      nextAlign = case tys of
        [] -> a'
        (ty' : _) -> typeAlignment dl ty'



typeAlignment :: Crucible.DataLayout -> Crucible.Type -> Crucible.Alignment
typeAlignment dl ty =
  case Crucible.typeF ty of
    Crucible.Bitvector bytes -> Crucible.integerAlignment dl (fromIntegral (bytes*8))
    Crucible.Float           -> fromJust (Crucible.floatAlignment dl 32)
    Crucible.Double          -> fromJust (Crucible.floatAlignment dl 64)
    Crucible.Array _sz ty'   -> typeAlignment dl ty'
    Crucible.Struct flds     -> V.foldl max 0 (fmap (typeAlignment dl . (^. Crucible.fieldVal)) flds)

typeOfLLVMVal :: Crucible.DataLayout -> LLVMVal -> Crucible.Type
typeOfLLVMVal dl val =
  case val of
    Crucible.LLVMValPtr {}      -> ptrType
    Crucible.LLVMValFunPtr {}   -> ptrType
    Crucible.LLVMValInt w _bv   -> Crucible.bitvectorType (Crucible.intWidthSize (fromIntegral (NatRepr.natValue w)))
    Crucible.LLVMValReal _      -> error "FIXME: typeOfLLVMVal LLVMValReal"
    Crucible.LLVMValStruct flds -> Crucible.mkStruct (fmap fieldType flds)
    Crucible.LLVMValArray tp vs -> Crucible.arrayType (fromIntegral (V.length vs)) tp
  where
    ptrType = Crucible.bitvectorType (dl^.Crucible.ptrSize)
    fieldType (f, _) = (f ^. Crucible.fieldVal, Crucible.fieldPad f)
