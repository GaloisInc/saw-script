{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Heapster.LLVMGlobalConst (
  permEnvAddGlobalConst
  ) where

import Data.Bits
import Data.List
import Control.Monad.Reader
import GHC.TypeLits
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

import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor (ModuleName)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Heapster.Permissions


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
  L.withConfig (L.Config True True True) (show $ PPHPJ.nest 2 $ L.ppValue val)

-- | Helper function to pretty-print an LLVM constant expression
ppLLVMConstExpr :: L.ConstExpr -> String
ppLLVMConstExpr ce =
  L.withConfig (L.Config True True True) (show $ PPHPJ.nest 2 $ L.ppConstExpr ce)

-- | Translate a typed LLVM 'L.Value' to a Heapster shape + an element of the
-- translation of that shape to a SAW core type
translateLLVMValue :: (1 <= w, KnownNat w) => NatRepr w -> L.Type -> L.Value ->
                      LLVMTransM (PermExpr (LLVMShapeType w), OpenTerm)
translateLLVMValue w tp@(L.PrimType (L.Integer n)) (L.ValInteger i) =
  translateLLVMType w tp >>= \(sh,_) ->
  return (sh, bvLitOfIntOpenTerm (fromIntegral n) i)
translateLLVMValue w _ (L.ValSymbol sym) =
  do env <- llvmTransInfoEnv <$> ask
     -- (p, ts) <- lift (lookupGlobalSymbol env (GlobalSymbol sym) w)
     (p, t) <- case (lookupGlobalSymbol env (GlobalSymbol sym) w) of
       Just (p,[t]) -> return (p,t)
       Just (p,ts) -> return (p,tupleOpenTerm ts)
       Nothing -> traceAndZeroM ("Could not find symbol: " ++ show sym)
     return (PExpr_FieldShape (LLVMFieldShape p), t)
translateLLVMValue w _ (L.ValArray tp elems) =
  do
    -- First, translate the elements and their type
    ts <- map snd <$> mapM (translateLLVMValue w tp) elems
    (sh, saw_tp) <- translateLLVMType w tp

    -- Compute the array stride as the length of the element shape
    sh_len_expr <- lift $ llvmShapeLength sh
    sh_len <- fromInteger <$> lift (bvMatchConstInt sh_len_expr)

    -- Generate a default element of type tp using the zero initializer; this is
    -- currently needed by bvVecValueOpenTerm
    def_v <- llvmZeroInitValue tp
    (_,def_tm) <- translateLLVMValue w tp def_v

    -- Finally, build our array shape and SAW core value
    return (PExpr_ArrayShape (bvInt $ fromIntegral $ length elems) sh_len sh,
            bvVecValueOpenTerm w saw_tp ts def_tm)
translateLLVMValue w _ (L.ValPackedStruct elems) =
  mapM (translateLLVMTypedValue w) elems >>= \(unzip -> (shs,ts)) ->
  return (foldr PExpr_SeqShape PExpr_EmptyShape shs, tupleOpenTerm ts)
translateLLVMValue _ _ (L.ValString []) = mzero
translateLLVMValue _ _ (L.ValString bytes) =
  let sh =
        foldr1 PExpr_SeqShape $
        map (PExpr_FieldShape . LLVMFieldShape . ValPerm_Eq .
             PExpr_LLVMWord . bvBV . BV.word8) bytes in
  let tm = foldr1 pairOpenTerm $ map (const unitOpenTerm) bytes in
  return (sh, tm)
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
  llvmZeroInitValue tp >>= translateLLVMValue w tp
translateLLVMValue _ _ v =
  traceAndZeroM ("translateLLVMValue does not yet handle:\n" ++ ppLLVMValue v)

-- | Helper function for 'translateLLVMValue'
translateLLVMTypedValue :: (1 <= w, KnownNat w) => NatRepr w -> L.Typed L.Value ->
                           LLVMTransM (PermExpr (LLVMShapeType w), OpenTerm)
translateLLVMTypedValue w (L.Typed tp v) = translateLLVMValue w tp v

-- | Translate an LLVM type into a shape plus the SAW core type of elements of
-- the translation of that shape
translateLLVMType :: (1 <= w, KnownNat w) => NatRepr w -> L.Type ->
                     LLVMTransM (PermExpr (LLVMShapeType w), OpenTerm)
translateLLVMType _ (L.PrimType (L.Integer n))
  | Just (Some (n_repr :: NatRepr n)) <- someNat n
  , Left leq_pf <- decideLeq (knownNat @1) n_repr =
    withKnownNat n_repr $ withLeqProof leq_pf $
    return (PExpr_FieldShape (LLVMFieldShape $ ValPerm_Exists $ nu $ \bv ->
                               ValPerm_Eq $ PExpr_LLVMWord $
                               PExpr_Var (bv :: Name (BVType n))),
            (bvTypeOpenTerm n))
translateLLVMType _ tp =
  traceAndZeroM ("translateLLVMType does not yet handle:\n"
                 ++ show (L.ppType tp))

-- | Helper function for 'translateLLVMValue' applied to a constant expression
translateLLVMConstExpr :: (1 <= w, KnownNat w) => NatRepr w -> L.ConstExpr ->
                          LLVMTransM (PermExpr (LLVMShapeType w), OpenTerm)
translateLLVMConstExpr w (L.ConstGEP _ _ _ (L.Typed tp ptr : ixs)) =
  translateLLVMValue w tp ptr >>= \ptr_trans ->
  translateLLVMGEP w tp ptr_trans ixs
translateLLVMConstExpr w (L.ConstConv L.BitCast
                          (L.Typed tp@(L.PtrTo _) v) (L.PtrTo _)) =
  -- A bitcast from one LLVM pointer type to another is a no-op for us
  translateLLVMValue w tp v
translateLLVMConstExpr _ ce =
  traceAndZeroM ("translateLLVMConstExpr does not yet handle:\n"
                 ++ ppLLVMConstExpr ce)

-- | Helper function for 'translateLLVMValue' applied to a @getelemptr@
-- expression
translateLLVMGEP :: (1 <= w, KnownNat w) => NatRepr w -> L.Type ->
                    (PermExpr (LLVMShapeType w), OpenTerm) ->
                    [L.Typed L.Value] ->
                    LLVMTransM (PermExpr (LLVMShapeType w), OpenTerm)
translateLLVMGEP _ _ vtrans [] = return vtrans
translateLLVMGEP w (L.Array _ tp) vtrans (L.Typed _ (L.ValInteger 0) : ixs) =
  translateLLVMGEP w tp vtrans ixs
translateLLVMGEP w (L.PtrTo tp) vtrans (L.Typed _ (L.ValInteger 0) : ixs) =
  translateLLVMGEP w tp vtrans ixs
translateLLVMGEP w (L.PackedStruct [tp]) vtrans (L.Typed
                                                 _ (L.ValInteger 0) : ixs) =
  translateLLVMGEP w tp vtrans ixs
translateLLVMGEP _ tp _ ixs =
  traceAndZeroM ("translateLLVMGEP cannot handle arguments:\n" ++
                 "  " ++ intercalate "," (show tp : map show ixs))

-- | Build an LLVM value for a @zeroinitializer@ field of the supplied type
llvmZeroInitValue :: L.Type -> LLVMTransM (L.Value)
llvmZeroInitValue (L.PrimType (L.Integer _)) = return $ L.ValInteger 0
llvmZeroInitValue (L.Array len tp) =
  L.ValArray tp <$> replicate (fromIntegral len) <$> llvmZeroInitValue tp
llvmZeroInitValue (L.PackedStruct tps) =
  L.ValPackedStruct <$> zipWith L.Typed tps <$> mapM llvmZeroInitValue tps
llvmZeroInitValue tp =
  traceAndZeroM ("llvmZeroInitValue cannot handle type:\n"
                 ++ show (L.ppType tp))

-- | Top-level call to 'translateLLVMValue', running the 'LLVMTransM' monad
translateLLVMValueTop :: (1 <= w, KnownNat w) => DebugLevel -> EndianForm ->
                         NatRepr w -> PermEnv -> L.Global ->
                         Maybe (PermExpr (LLVMShapeType w), OpenTerm)
translateLLVMValueTop dlevel endianness w env global =
  let sym = show (L.globalSym global) in
  let trans_info = LLVMTransInfo { llvmTransInfoEnv = env,
                                   llvmTransInfoEndianness = endianness,
                                   llvmTransInfoDebugLevel = dlevel } in
  debugTraceTraceLvl dlevel ("Global: " ++ sym ++ "; value =\n" ++
                             maybe "None" ppLLVMValue
                             (L.globalValue global)) $
  (\x -> case x of
      Just _ -> debugTraceTraceLvl dlevel (sym ++ " translated") x
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
    Just (sh, t) ->
      do let (L.Symbol glob_str) = L.globalSym global
         ident <-
           scFreshenGlobalIdent sc $ mkSafeIdent mod_name $ show glob_str
         complete_t <- completeOpenTerm sc t
         tp <- completeOpenTermType sc t
         scInsertDef sc mod_name ident tp complete_t
         let p = ValPerm_LLVMBlock $ llvmReadBlockOfShape sh
         let t_ident = globalOpenTerm ident
         return $ permEnvAddGlobalSyms env
           [PermEnvGlobalEntry (GlobalSymbol $ L.globalSym global) p [t_ident]]
