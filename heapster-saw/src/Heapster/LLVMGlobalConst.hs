{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}

module Heapster.LLVMGlobalConst (
  permEnvAddGlobalConst
  ) where

import Data.Bits
import Data.List
import Control.Monad (MonadPlus(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))
import Control.Monad.Trans.Class (MonadTrans(..))
import GHC.TypeLits (KnownNat)
import qualified Text.PrettyPrint.HughesPJ as PPHPJ

import qualified Data.BitVector.Sized as BV
import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L

import Data.Binding.Hobbits hiding (sym)

import Data.Parameterized.NatRepr
import Data.Parameterized.Some

import Lang.Crucible.Types
import Lang.Crucible.LLVM.DataLayout
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.PrettyPrint

import Verifier.SAW.Name (mkSafeIdent)
import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor (ModuleName)
import Verifier.SAW.SharedTerm
import Heapster.Permissions


-- FIXME: move these utilities to OpenTerm.hs

-- | Generate a SAW core term for a bitvector literal whose length is given by
-- the first integer and whose value is given by the second
bvLitOfIntOpenTerm :: Integer -> Integer -> OpenTerm
bvLitOfIntOpenTerm n i =
  bvLitOpenTerm (map (testBit i) $ reverse [0..(fromIntegral n)-1])

-- | Helper function to build a SAW core term of type @BVVec w len a@, i.e., a
-- bitvector-indexed vector, containing a given list of elements of type
-- @a@. The roundabout way we do this currently requires a default element of
-- type @a@, even though this value is never actually used. Also required is the
-- bitvector width @w@.
bvVecValueOpenTerm :: NatRepr w -> OpenTerm -> [OpenTerm] -> OpenTerm ->
                      OpenTerm
bvVecValueOpenTerm w tp ts def_tm =
  applyOpenTermMulti (globalOpenTerm "Prelude.genBVVecFromVec")
  [natOpenTerm (fromIntegral $ length ts), tp, arrayValueOpenTerm tp ts,
   def_tm, natOpenTerm (natValue w),
   bvLitOfIntOpenTerm (intValue w) (fromIntegral $ length ts)]

-- | Helper function to build a SAW core term of type @BVVec w len a@, i.e., a
-- bitvector-indexed vector, containing a single repeated value
repeatBVVecOpenTerm :: NatRepr w -> OpenTerm -> OpenTerm -> OpenTerm ->
                       OpenTerm
repeatBVVecOpenTerm w len tp t =
  applyOpenTermMulti (globalOpenTerm "Prelude.repeatBVVec")
  [natOpenTerm (natValue w), len, tp, t]

-- | The information needed to translate an LLVM global to Heapster
data LLVMTransInfo = LLVMTransInfo {
  llvmTransInfoEnv :: PermEnv,
  llvmTransInfoEndianness :: EndianForm,
  llvmTransInfoDebugLevel :: DebugLevel }

-- | The monad for translating LLVM globals to Heapster
type LLVMTransM = ReaderT LLVMTransInfo Maybe

-- | Run the 'LLVMTransM' monad
runLLVMTransM :: LLVMTransM a -> LLVMTransInfo -> Maybe a
runLLVMTransM = runReaderT

-- | Use 'debugTrace' to output a string message and then call 'mzero'
traceAndZeroM :: String -> LLVMTransM a
traceAndZeroM msg =
  do dlevel <- llvmTransInfoDebugLevel <$> ask
     debugTraceTraceLvl dlevel msg mzero

-- | Helper function to pretty-print the value of a global
ppLLVMValue :: L.Value -> String
ppLLVMValue val =
  show $ PPHPJ.nest 2 $ ppValue val

-- | Helper function to pretty-print an LLVM constant expression
ppLLVMConstExpr :: L.ConstExpr -> String
ppLLVMConstExpr ce =
  ppLLVMLatest (show $ PPHPJ.nest 2 $ L.ppConstExpr ce)

-- | Translate a typed LLVM 'L.Value' to a Heapster shape + elements of the
-- translation of that shape to 0 or more SAW core types
translateLLVMValue :: (1 <= w, KnownNat w) => NatRepr w -> L.Type -> L.Value ->
                      LLVMTransM (PermExpr (LLVMShapeType w), [OpenTerm])
translateLLVMValue w tp@(L.PrimType (L.Integer n)) (L.ValInteger i) =
  translateLLVMType w tp >>= \(sh,_) ->
  return (sh, [bvLitOfIntOpenTerm (fromIntegral n) i])
translateLLVMValue w _ (L.ValSymbol sym) =
  do env <- llvmTransInfoEnv <$> ask
     -- (p, ts) <- lift (lookupGlobalSymbol env (GlobalSymbol sym) w)
     (p, ts) <- case lookupGlobalSymbol env (GlobalSymbol sym) w of
       Just (p, GlobalTrans ts) -> return (p, ts)
       Nothing -> traceAndZeroM ("Could not find symbol: " ++ show sym)
     return (PExpr_FieldShape (LLVMFieldShape p), ts)
translateLLVMValue w _ (L.ValArray tp elems) =
  do
    -- First, translate the elements and their type
    ts <- concat <$> map snd <$> mapM (translateLLVMValue w tp) elems
    (sh, saw_tps) <- translateLLVMType w tp
    let saw_tp = tupleTypeOpenTerm' saw_tps

    -- Compute the array stride as the length of the element shape
    sh_len_expr <- lift $ llvmShapeLength sh
    sh_len <- fromInteger <$> lift (bvMatchConstInt sh_len_expr)

    -- Generate a default element of type tp using the zero initializer; this is
    -- currently needed by bvVecValueOpenTerm
    (_,def_tms) <- translateZeroInit w tp
    let def_tm = tupleOpenTerm' def_tms

    -- Finally, build our array shape and SAW core value
    return (PExpr_ArrayShape (bvInt $ fromIntegral $ length elems) sh_len sh,
            [bvVecValueOpenTerm w saw_tp ts def_tm])
translateLLVMValue w _ (L.ValPackedStruct elems) =
  mapM (translateLLVMTypedValue w) elems >>= \(unzip -> (shs,tss)) ->
  return (foldr PExpr_SeqShape PExpr_EmptyShape shs, concat tss)
translateLLVMValue _ _ (L.ValString []) = mzero
translateLLVMValue _ _ (L.ValString bytes) =
  let sh =
        foldr1 PExpr_SeqShape $
        map (PExpr_FieldShape . LLVMFieldShape . ValPerm_Eq .
             PExpr_LLVMWord . bvBV . BV.word8) bytes in
  -- let tm = foldr1 pairOpenTerm $ map (const unitOpenTerm) bytes in

  -- NOTE: the equality permissions have no translations, so the sequence of
  -- them doesn't either
  return (sh, [])
-- NOTE: we don't translate strings to one big bitvector value because that
-- seems to mess up the endianness
{-
translateLLVMValue _ _ (L.ValString bytes) =
  do endianness <- llvmTransInfoEndianness <$> ask
     case bvFromBytes endianness bytes of
       Some (BVExpr e) ->
         return (PExpr_FieldShape (LLVMFieldShape $
                                   ValPerm_Eq $ PExpr_LLVMWord e),
                 unitOpenTerm)
-}
-- NOTE: we don't convert string values to arrays because we sometimes need to
-- statically know the values of the bytes in a string value as eq perms
{-
translateLLVMValue w tp (L.ValString bytes) =
  translateLLVMValue w tp (L.ValArray
                           (L.PrimType (L.Integer 8))
                           (map (L.ValInteger . toInteger) bytes))
-}
translateLLVMValue w _ (L.ValConstExpr ce) =
  translateLLVMConstExpr w ce
translateLLVMValue w tp L.ValZeroInit =
  translateZeroInit w tp
translateLLVMValue _ _ v =
  traceAndZeroM ("translateLLVMValue does not yet handle:\n" ++ ppLLVMValue v)

-- | Helper function for 'translateLLVMValue'
translateLLVMTypedValue :: (1 <= w, KnownNat w) => NatRepr w -> L.Typed L.Value ->
                           LLVMTransM (PermExpr (LLVMShapeType w), [OpenTerm])
translateLLVMTypedValue w (L.Typed tp v) = translateLLVMValue w tp v

-- | Translate an LLVM type into a shape plus the SAW core types of the 0 or
-- more elements of the translation of that shape
translateLLVMType :: (1 <= w, KnownNat w) => NatRepr w -> L.Type ->
                     LLVMTransM (PermExpr (LLVMShapeType w), [OpenTerm])
translateLLVMType _ (L.PrimType (L.Integer n))
  | Just (Some (n_repr :: NatRepr n)) <- someNat n
  , Left leq_pf <- decideLeq (knownNat @1) n_repr =
    withKnownNat n_repr $ withLeqProof leq_pf $
    return (PExpr_FieldShape (LLVMFieldShape $ ValPerm_Exists $ nu $ \bv ->
                               ValPerm_Eq $ PExpr_LLVMWord $
                               PExpr_Var (bv :: Name (BVType n))),
            [bvTypeOpenTerm n])
translateLLVMType _ tp =
  traceAndZeroM ("translateLLVMType does not yet handle:\n"
                 ++ show (ppType tp))

-- | Helper function for 'translateLLVMValue' applied to a constant expression
translateLLVMConstExpr :: (1 <= w, KnownNat w) => NatRepr w -> L.ConstExpr ->
                          LLVMTransM (PermExpr (LLVMShapeType w), [OpenTerm])
translateLLVMConstExpr w (L.ConstGEP _ _ _ (L.Typed tp ptr) ixs) =
  translateLLVMValue w tp ptr >>= \ptr_trans ->
  translateLLVMGEP w tp ptr_trans ixs
translateLLVMConstExpr w (L.ConstConv L.BitCast
                          (L.Typed fromTp v) toTp)
  | L.isPointer fromTp && L.isPointer toTp
  = -- A bitcast from one LLVM pointer type to another is a no-op for us
    translateLLVMValue w fromTp v
translateLLVMConstExpr _ ce =
  traceAndZeroM ("translateLLVMConstExpr does not yet handle:\n"
                 ++ ppLLVMConstExpr ce)

-- | Helper function for 'translateLLVMValue' applied to a constant
-- @getelementptr@ expression.
--
-- For now, we only support uses of @getelementptr@ where all indices are zero,
-- as this will return the pointer argument without needing to compute an offset
-- into the pointer. Of course, this does mean that any @getelementptr@
-- expressions involving non-zero indices aren't supported (see #1875 for a
-- contrived example of this). Thankfully, this function is only used to
-- translate LLVM globals, and using @getelementptr@ to initialize globals is
-- quite rare in practice. As such, we choose to live with this limitation until
-- someone complains about it.
translateLLVMGEP :: (1 <= w, KnownNat w) => NatRepr w -> L.Type ->
                    (PermExpr (LLVMShapeType w), [OpenTerm]) ->
                    [L.Typed L.Value] ->
                    LLVMTransM (PermExpr (LLVMShapeType w), [OpenTerm])
translateLLVMGEP _ tp vtrans ixs
  | all (isZeroIdx . L.typedValue) ixs
  = return vtrans
  | otherwise
  = traceAndZeroM ("translateLLVMGEP cannot handle arguments:\n" ++
                   "  " ++ intercalate "," (show tp : map show ixs))
  where
    -- Check if an index is equal to 0.
    isZeroIdx :: L.Value -> Bool
    isZeroIdx (L.ValInteger 0) = True
    isZeroIdx _                = False

-- | Build an LLVM value for a @zeroinitializer@ field of the supplied type
translateZeroInit :: (1 <= w, KnownNat w) => NatRepr w -> L.Type ->
                     LLVMTransM (PermExpr (LLVMShapeType w), [OpenTerm])
translateZeroInit w tp@(L.PrimType (L.Integer _)) =
   translateLLVMValue w tp (L.ValInteger 0)
translateZeroInit w (L.Array len tp) =
  -- First, translate the zero element and its type
  do (sh, elem_tms) <- translateZeroInit w tp
     let elem_tm = tupleOpenTerm' elem_tms
     (_, saw_tps) <- translateLLVMType w tp
     let saw_tp = tupleTypeOpenTerm' saw_tps

     -- Compute the array stride as the length of the element shape
     sh_len_expr <- lift $ llvmShapeLength sh
     sh_len <- fromInteger <$> lift (bvMatchConstInt sh_len_expr)

     let arr_len = bvInt $ fromIntegral len
     let saw_len = bvLitOfIntOpenTerm (intValue w) (fromIntegral len)
     return (PExpr_ArrayShape arr_len sh_len sh,
             [repeatBVVecOpenTerm w saw_len saw_tp elem_tm])

translateZeroInit w (L.PackedStruct tps) =
  mapM (translateZeroInit w) tps >>= \(unzip -> (shs,tss)) ->
  return (foldr PExpr_SeqShape PExpr_EmptyShape shs, concat tss)

translateZeroInit _ tp =
  traceAndZeroM ("translateZeroInit cannot handle type:\n"
                 ++ show (ppType tp))


-- | Top-level call to 'translateLLVMValue', running the 'LLVMTransM' monad
translateLLVMValueTop :: (1 <= w, KnownNat w) => DebugLevel -> EndianForm ->
                         NatRepr w -> PermEnv -> L.Global ->
                         Maybe (PermExpr (LLVMShapeType w), [OpenTerm])
translateLLVMValueTop dlevel endianness w env global =
  let sym = show (L.globalSym global) in
  let trans_info = LLVMTransInfo { llvmTransInfoEnv = env,
                                   llvmTransInfoEndianness = endianness,
                                   llvmTransInfoDebugLevel = dlevel } in
  debugTraceTraceLvl dlevel ("Global: " ++ sym ++ "; value =\n" ++
                             maybe "None" ppLLVMValue
                             (L.globalValue global)) $
  (\x -> case x of
      Just (sh,ts) ->
        debugTraceTraceLvl dlevel (sym ++ " translated to " ++
                                   show (length ts) ++ " terms for perm:\n" ++
                                   permPrettyString emptyPPInfo sh) x
      Nothing -> debugTraceTraceLvl dlevel (sym ++ " not translated") x) $
  flip runLLVMTransM trans_info $
  do val <- lift $ L.globalValue global
     translateLLVMValue w (L.globalType global) val

-- | Add an LLVM global constant to a 'PermEnv', if the global has a type and
-- value we can translate to Heapster, otherwise silently ignore it
permEnvAddGlobalConst :: (1 <= w, KnownNat w) => SharedContext -> ModuleName ->
                         DebugLevel -> EndianForm -> NatRepr w -> PermEnv ->
                         L.Global -> IO PermEnv
permEnvAddGlobalConst sc mod_name dlevel endianness w env global =
  case translateLLVMValueTop dlevel endianness w env global of
    Nothing -> return env
    Just (sh, []) ->
      let p = ValPerm_LLVMBlock $ llvmReadBlockOfShape sh in
      return $ permEnvAddGlobalSyms env [PermEnvGlobalEntry (GlobalSymbol $
                                                             L.globalSym global)
                                         p (GlobalTrans [])]
    Just (sh, ts) ->
      do let (L.Symbol glob_str) = L.globalSym global
         ident <-
           scFreshenGlobalIdent sc $ mkSafeIdent mod_name $ show glob_str
         let t = tupleOpenTerm' ts
         complete_t <- completeOpenTerm sc t
         let tps = map openTermType ts
         complete_tp <- completeOpenTerm sc $ tupleTypeOpenTerm' tps
         scInsertDef sc mod_name ident complete_tp complete_t
         let p = ValPerm_LLVMBlock $ llvmReadBlockOfShape sh
         return $ permEnvAddGlobalSyms env
           [PermEnvGlobalEntry (GlobalSymbol $ L.globalSym global) p
            (GlobalTrans [globalOpenTerm ident])]
