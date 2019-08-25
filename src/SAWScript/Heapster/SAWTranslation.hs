{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWScript.Heapster.SAWTranslation where

import Data.Kind
import GHC.TypeLits
import Control.Monad.Reader

import Data.Binding.Hobbits
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty, take, view)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.TraversableFC

import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.LLVM.Extension
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Arch.X86
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core
import Lang.Crucible.CFG.Extension
import Lang.Crucible.Analysis.Fixpoint.Components

import Verifier.SAW.OpenTerm
import Verifier.SAW.Term.Functor

import SAWScript.Heapster.CruUtil
import SAWScript.Heapster.Permissions
import SAWScript.Heapster.Implication
import SAWScript.Heapster.TypedCrucible


----------------------------------------------------------------------
-- * Monads for SAW Translation
----------------------------------------------------------------------

-- | The result of a type-level translation at 'CrucibleType' @a@
data TypeTransRes (a :: CrucibleType) where
  -- | LLVM pointers have their translations dictated by their permissions, so
  -- their "values" are empty, i.e., the unit type
  TpTrans_LLVM :: TypeTransRes (LLVMPointerType w)

  -- | Splittings are also translated to unit
  TpTrans_Spl :: TypeTransRes SplittingType

  -- | The translation for any other type. NOTE: it is an error to use this
  -- constructor with one of the types already listed above.
  TpTrans_Other :: OpenTerm -> TypeTransRes a


-- | A context mapping bound names to their type-level SAW translations
type TypeTransCtx (ctx :: RList CrucibleType) = MapRList TypeTransRes ctx

-- | The type translation monad = a reader monad for 'TypeTransCtx'
type TypeTransM ctx = Reader (TypeTransCtx ctx)


-- | The result of a permission-level translation at 'CrucibleType' @a@
data PermTransRes (a :: CrucibleType) where
  -- | LLVM pointer permissions can be broken into multiple SAW terms, one for
  -- each pointer permission
  PermTrans_LLVMPtr :: [OpenTerm] -> PermTransRes (LLVMPointerType w)

  -- | The @true@ permission translated to unit, i.e., nothing
  PermTrans_True :: PermTransRes a

  -- | An @eq(e)@ permission is also translated to unit
  PermTrans_Eq :: PermTransRes a

  -- | Any other permissions are just SAW terms
  PermTrans_Any :: OpenTerm -> PermTransRes a

-- | A context mapping bound names to their perm translations
type PermTransCtx (ctx :: RList CrucibleType) = MapRList PermTransRes ctx


-- | A mapping from a block entrypoint to its corresponding SAW variable that is
-- bound to its translation
data TypedEntryTrans ext blocks ret args =
  TypedEntryTrans (TypedEntry ext blocks ret args) OpenTerm

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks ret args =
  TypedBlockTrans [TypedEntryTrans ext blocks ret args]

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks ret args =
  MapRList (TypedBlockTrans ext blocks ret) blocks

-- | Translate an entrypoint ID by looking up its SAW function
translateTypedEntryID :: TypedEntryID blocks args ghosts ->
                         TypedBlockMapTrans ext blocks ret args ->
                         OpenTerm
translateTypedEntryID entryID blkMap =
  let TypedBlockTrans entries = mapRListLookup (entryBlockID entryID) blkMap in
  foldr (\(TypedEntryTrans entry trm) rest ->
          case entry of
            TypedEntry entryID' _ _ _
              | Just Refl <- testEquality entryID entryID' -> trm
            _ -> rest)
  (error "translateTypedEntryID")
  entries


-- | Contextual info for a permission-level translation
data PermTransInfo ext blocks ret args ctx =
  PermTransInfo
  {
    ptiTpCtx :: TypeTransCtx ctx,
    ptiPermCtx :: PermTransCtx ctx,
    ptiPermSet :: Mb ctx (PermSet ctx),
    ptiBlockTrans :: TypedBlockMapTrans ext blocks ret args,
    ptiCatchHandler :: Maybe OpenTerm
  }

permTransInfoExtend :: TypeTransRes tp -> ValuePerm tp -> PermTransRes tp ->
                       PermTransInfo ext blocks ret args ctx ->
                       PermTransInfo ext blocks ret args (ctx :> tp)
permTransInfoExtend = error "FIXME HERE NOW"

-- | The monad for permission-level translation
type PermTransM ext blocks ret args ctx =
  Reader (PermTransInfo ext blocks ret args ctx)

-- | Perform a type-level translation in a permisison translation
permTpTranslate :: TypeTransM ctx a -> PermTransM ext blocks ret args ctx a
permTpTranslate m = ask >>= return . runReader m . ptiTpCtx

-- | Build a lambda in a perm-level translation
permTransLambda :: String -> OpenTerm ->
                   PermTransM ext blocks ret args (ctx :> tp) OpenTerm ->
                   PermTransM ext blocks ret args ctx OpenTerm
permTransLambda x tp body_m =
  do info <- ask
     return $ lambdaOpenTerm x tp (\x -> runReader body_m $
                                         error "FIXME HERE NOW")


----------------------------------------------------------------------
-- * Type-Level Translation
----------------------------------------------------------------------

-- | The typeclass for type-level translation
class TypeTranslate a where
  tpTranslate :: Mb ctx a -> TypeTransM ctx OpenTerm

-- | The typeclass for type-level translations of expressions
class TypeExprTranslate (f :: CrucibleType -> Type) where
  tpExprTranslate :: Mb ctx (f a) -> TypeTransM ctx (TypeTransRes a)

instance TypeTranslate (NatRepr n) where
  tpTranslate mb_n = return $ natOpenTerm $ mbLift $ fmap intValue mb_n

instance TypeTranslate (TypeRepr a) where
  tpTranslate [nuP| (AnyRepr) |] =
    return $ error "TypeTranslate: Any"
  tpTranslate [nuP| (UnitRepr) |] =
    return $ unitTypeOpenTerm
  tpTranslate [nuP| (BoolRepr) |] =
    return $ dataTypeOpenTerm "Prelude.Bool" []
  tpTranslate [nuP| (NatRepr) |] =
    return $ dataTypeOpenTerm "Prelude.Nat" []
  tpTranslate [nuP| (IntegerRepr) |] =
    return $ error "TypeTranslate: IntegerRepr"
  tpTranslate [nuP| (RealValRepr) |] =
    return $ error "TypeTranslate: RealValRepr"
  tpTranslate [nuP| (ComplexRealRepr) |] =
    return $ error "TypeTranslate: ComplexRealRepr"
  tpTranslate [nuP| (BVRepr w) |] =
    applyOpenTerm (globalOpenTerm "Prelude.bitvector") <$> tpTranslate w
  tpTranslate [nuP| (LLVMPointerRepr _) |] =
    return $ unitTypeOpenTerm
  tpTranslate [nuP| (IntrinsicRepr _ _) |] =
    return $ error "TypeTranslate: IntrinsicRepr (other than LLVMPointerRepr)"
  tpTranslate [nuP| (RecursiveRepr _ _) |] =
    return $ error "TypeTranslate: RecursiveRepr"
  tpTranslate [nuP| (FloatRepr _) |] =
    return $ dataTypeOpenTerm "Prelude.Float" []
  tpTranslate [nuP| (IEEEFloatRepr _) |] =
    return $ error "TypeTranslate: IEEEFloatRepr"
  tpTranslate [nuP| (CharRepr) |] =
    return $ error "TypeTranslate: CharRepr"
  tpTranslate [nuP| (StringRepr) |] =
    return $ dataTypeOpenTerm "Prelude.String" []
  tpTranslate [nuP| (FunctionHandleRepr _ _) |] =
    return $ error "TypeTranslate: FunctionHandleRepr"
  tpTranslate [nuP| (MaybeRepr tp) |] =
    applyOpenTerm (globalOpenTerm "Prelude.Maybe") <$> tpTranslate tp
  tpTranslate [nuP| (VectorRepr _) |] =
    return $ error "TypeTranslate: VectorRepr (can't map to Vec without size)"
  tpTranslate [nuP| (StructRepr _) |] =
    return $ error "TypeTranslate: StructRepr"
  tpTranslate [nuP| (VariantRepr _) |] =
    return $ error "TypeTranslate: VariantRepr"
  tpTranslate [nuP| (ReferenceRepr _) |] =
    return $ error "TypeTranslate: ReferenceRepr"
  tpTranslate [nuP| (WordMapRepr _ _) |] =
    return $ error "TypeTranslate: WordMapRepr"
  tpTranslate [nuP| (StringMapRepr _) |] =
    return $ error "TypeTranslate: StringMapRepr"
  tpTranslate [nuP| (SymbolicArrayRepr _ _) |] =
    return $ error "TypeTranslate: SymbolicArrayRepr"
  tpTranslate [nuP| (SymbolicStructRepr _) |] =
    return $ error "TypeTranslate: SymbolicStructRepr"
