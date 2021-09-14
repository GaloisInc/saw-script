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

import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L

import Data.Binding.Hobbits hiding (sym)

import Data.Parameterized.NatRepr
import Data.Parameterized.Some

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Verifier.SAW.OpenTerm
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

-- | The monad for translating LLVM globals to Heapster
type LLVMTransM = ReaderT (PermEnv, DebugLevel) Maybe

-- | Run the 'LLVMTransM' monad
runLLVMTransM :: LLVMTransM a -> (PermEnv, DebugLevel) -> Maybe a
runLLVMTransM = runReaderT

-- | Use 'debugTrace' to output a string message and then call 'mzero'
traceAndZeroM :: String -> LLVMTransM a
traceAndZeroM msg =
  do (_,dlevel) <- ask
     debugTrace dlevel msg mzero

-- | Helper function to pretty-print the value of a global
ppLLVMValue :: L.Value -> String
ppLLVMValue val =
  L.withConfig (L.Config True True True) (show $ PPHPJ.nest 2 $ L.ppValue val)

-- | Helper function to pretty-print an LLVM constant expression
ppLLVMConstExpr :: L.ConstExpr -> String
ppLLVMConstExpr ce =
  L.withConfig (L.Config True True True) (show $ PPHPJ.nest 2 $ L.ppConstExpr ce)

-- | Translate a typed LLVM 'L.Value' to a Heapster permission + translation
translateLLVMValue :: (1 <= w, KnownNat w) => NatRepr w -> L.Type -> L.Value ->
                      LLVMTransM (PermExpr (LLVMShapeType w), OpenTerm)
translateLLVMValue w tp@(L.PrimType (L.Integer n)) (L.ValInteger i) =
  translateLLVMType w tp >>= \(sh,_) ->
  return (sh, bvLitOfIntOpenTerm (fromIntegral n) i)
translateLLVMValue w _ (L.ValSymbol sym) =
  do (env,_) <- ask
     -- (p, ts) <- lift (lookupGlobalSymbol env (GlobalSymbol sym) w)
     (p, t) <- case (lookupGlobalSymbol env (GlobalSymbol sym) w) of
       Just (p,[t]) -> return (p,t)
       Just (p,ts) -> return (p,tupleOpenTerm ts)
       Nothing -> traceAndZeroM ("Could not find symbol: " ++ show sym)
     return (PExpr_FieldShape (LLVMFieldShape p), t)
translateLLVMValue w _ (L.ValArray tp elems) =
  do
    -- First, translate the elements
    ts <- map snd <$> mapM (translateLLVMValue w tp) elems

    -- Array shapes can only handle field shapes elements, so translate the
    -- element type to and ensure it returns a field shape; FIXME: this could
    -- actually handle sequences of field shapes if necessary
    (sh, saw_tp) <- translateLLVMType w tp
    fsh <- case sh of
      PExpr_FieldShape fsh -> return fsh
      _ -> mzero

    -- Compute the array stride as the length of the element shape
    sh_len_expr <- lift $ llvmShapeLength sh
    sh_len <- fromInteger <$> lift (bvMatchConstInt sh_len_expr)

    -- Generate a default element of type tp using the zero initializer; this is
    -- currently needed by bvVecValueOpenTerm
    def_v <- llvmZeroInitValue tp
    (_,def_tm) <- translateLLVMValue w tp def_v

    -- Finally, build our array shape and SAW core value
    return (PExpr_ArrayShape (bvInt $ fromIntegral $ length elems) sh_len [fsh],
            bvVecValueOpenTerm w saw_tp ts def_tm)
translateLLVMValue w _ (L.ValPackedStruct elems) =
  mapM (translateLLVMTypedValue w) elems >>= \(unzip -> (shs,ts)) ->
  return (foldr PExpr_SeqShape PExpr_EmptyShape shs, tupleOpenTerm ts)
translateLLVMValue w tp (L.ValString bytes) =
  translateLLVMValue w tp (L.ValArray
                           (L.PrimType (L.Integer 8))
                           (map (L.ValInteger . toInteger) bytes))
  {-
  return (PExpr_ArrayShape (bvInt $ fromIntegral $ length bytes) 1
          [LLVMFieldShape (ValPerm_Exists $ nu $ \(bv :: Name (BVType 8)) ->
                            ValPerm_Eq $ PExpr_LLVMWord $ PExpr_Var bv)],
          [arrayValueOpenTerm (bvTypeOpenTerm (8::Int)) $
           map (\b -> bvLitOpenTerm $ map (testBit b) [7,6..0]) bytes])
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

-- | Add an LLVM global constant to a 'PermEnv', if the global has a type and
-- value we can translate to Heapster, otherwise silently ignore it
permEnvAddGlobalConst :: (1 <= w, KnownNat w) => DebugLevel -> NatRepr w ->
                         PermEnv -> L.Global -> PermEnv
permEnvAddGlobalConst dlevel w env global =
  let sym = show (L.globalSym global) in
  debugTrace dlevel ("Global: " ++ sym ++ "; value =\n" ++
                     maybe "None" ppLLVMValue
                     (L.globalValue global)) $
  maybe env id $
  (\x -> case x of
      Just _ -> debugTrace dlevel (sym ++ " translated") x
      Nothing -> debugTrace dlevel (sym ++ " not translated") x) $
  flip runLLVMTransM (env,dlevel) $
  do val <- lift $ L.globalValue global
     (sh, t) <- translateLLVMValue w (L.globalType global) val
     let p = ValPerm_LLVMBlock $ llvmReadBlockOfShape sh
     return $ permEnvAddGlobalSyms env
       [PermEnvGlobalEntry (GlobalSymbol $ L.globalSym global) p [t]]
