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

import Data.Maybe
import Data.Kind
import GHC.TypeLits
import qualified Data.Functor.Constant as Constant
import Control.Lens hiding ((:>),Index)
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
-- * The Pure Translation Monad
----------------------------------------------------------------------

-- | The result of translating a 'PermExpr' at 'CrucibleType' @a@
data ExprTrans (a :: CrucibleType) where
  -- | LLVM pointers have their translations dictated by their permissions, so
  -- their "values" are empty, i.e., the unit type
  ETrans_LLVM :: ExprTrans (LLVMPointerType w)

  -- | Splittings are also translated to unit
  ETrans_Spl :: ExprTrans SplittingType

  -- | The translation for any other type. NOTE: it is an error to use this
  -- constructor with one of the types already listed above.
  ETrans_Other :: OpenTerm -> ExprTrans a


-- | A context mapping bound names to their type-level SAW translations
type ExprTransCtx (ctx :: RList CrucibleType) = MapRList ExprTrans ctx

-- | Map an expression translation result to an 'OpenTerm' or 'Nothing' if it
-- has no pure content, i.e., if it is a splitting or LLVM value
exprTransToTerm :: ExprTrans a -> Maybe OpenTerm
exprTransToTerm ETrans_LLVM = Nothing
exprTransToTerm ETrans_Spl = Nothing
exprTransToTerm (ETrans_Other t) = Just t

-- | Map a context of pure translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones that are always translated to unit
exprCtxToTerms :: ExprTransCtx ctx -> [OpenTerm]
exprCtxToTerms MNil = []
exprCtxToTerms (ctx :>: (exprTransToTerm -> Just t)) = exprCtxToTerms ctx ++ [t]
exprCtxToTerms (ctx :>: _) = exprCtxToTerms ctx


-- | The type translation monad = a reader monad for 'ExprTransCtx'
type PureTransM ctx = Reader (ExprTransCtx ctx)


-- | Run a 'PureTransM' computation in an extended context
inExtPureTransM :: ExprTrans tp -> PureTransM (ctx :> tp) a ->
                   PureTransM ctx a
inExtPureTransM tp_trans = withReader (:>: tp_trans)

-- | Build a lambda in a translation monad
lambdaTransM :: String -> OpenTerm -> (OpenTerm -> Reader r OpenTerm) ->
                Reader r OpenTerm
lambdaTransM x tp body_m =
  do r <- ask
     return $ lambdaOpenTerm x tp (\x -> runReader (body_m x) r)

-- | Build a pi in a translation monad
piTransM :: String -> OpenTerm -> (OpenTerm -> Reader r OpenTerm) ->
            Reader r OpenTerm
piTransM x tp body_m =
  do r <- ask
     return $ piOpenTerm x tp (\x -> runReader (body_m x) r)

-- | Build a let-binding in a translation monad
letTransM :: String -> OpenTerm -> OpenTerm ->
             (OpenTerm -> Reader r OpenTerm) -> Reader r OpenTerm
letTransM x tp rhs body_m =
  do r <- ask
     return $ letOpenTerm x tp rhs (\x -> runReader (body_m x) r)


----------------------------------------------------------------------
-- * The Pure Translation
----------------------------------------------------------------------

-- | The typeclass for the pure translation
class PureTranslate a res | a -> res where
  ptranslate :: Mb ctx a -> PureTransM ctx res

instance PureTranslate (NatRepr n) OpenTerm where
  ptranslate mb_n = return $ natOpenTerm $ mbLift $ fmap intValue mb_n

instance PureTranslate (TypeRepr a) OpenTerm where
  ptranslate [nuP| (AnyRepr) |] =
    return $ error "PureTranslate: Any"
  ptranslate [nuP| (UnitRepr) |] =
    return $ unitTypeOpenTerm
  ptranslate [nuP| (BoolRepr) |] =
    return $ dataTypeOpenTerm "Prelude.Bool" []
  ptranslate [nuP| (NatRepr) |] =
    return $ dataTypeOpenTerm "Prelude.Nat" []
  ptranslate [nuP| (IntegerRepr) |] =
    return $ error "PureTranslate: IntegerRepr"
  ptranslate [nuP| (RealValRepr) |] =
    return $ error "PureTranslate: RealValRepr"
  ptranslate [nuP| (ComplexRealRepr) |] =
    return $ error "PureTranslate: ComplexRealRepr"
  ptranslate [nuP| (BVRepr w) |] =
    applyOpenTerm (globalOpenTerm "Prelude.bitvector") <$> ptranslate w
  ptranslate [nuP| (LLVMPointerRepr _) |] =
    return $ unitTypeOpenTerm
  ptranslate [nuP| (IntrinsicRepr _ _) |] =
    return $ error "PureTranslate: IntrinsicRepr (other than LLVMPointerRepr)"
  ptranslate [nuP| (RecursiveRepr _ _) |] =
    return $ error "PureTranslate: RecursiveRepr"
  ptranslate [nuP| (FloatRepr _) |] =
    return $ dataTypeOpenTerm "Prelude.Float" []
  ptranslate [nuP| (IEEEFloatRepr _) |] =
    return $ error "PureTranslate: IEEEFloatRepr"
  ptranslate [nuP| (CharRepr) |] =
    return $ error "PureTranslate: CharRepr"
  ptranslate [nuP| (StringRepr) |] =
    return $ dataTypeOpenTerm "Prelude.String" []
  ptranslate [nuP| (FunctionHandleRepr _ _) |] =
    return $ error "PureTranslate: FunctionHandleRepr"
  ptranslate [nuP| (MaybeRepr tp) |] =
    applyOpenTerm (globalOpenTerm "Prelude.Maybe") <$> ptranslate tp
  ptranslate [nuP| (VectorRepr _) |] =
    return $ error "PureTranslate: VectorRepr (can't map to Vec without size)"
  ptranslate [nuP| (StructRepr _) |] =
    return $ error "PureTranslate: StructRepr"
  ptranslate [nuP| (VariantRepr _) |] =
    return $ error "PureTranslate: VariantRepr"
  ptranslate [nuP| (ReferenceRepr _) |] =
    return $ error "PureTranslate: ReferenceRepr"
  ptranslate [nuP| (WordMapRepr _ _) |] =
    return $ error "PureTranslate: WordMapRepr"
  ptranslate [nuP| (StringMapRepr _) |] =
    return $ error "PureTranslate: StringMapRepr"
  ptranslate [nuP| (SymbolicArrayRepr _ _) |] =
    return $ error "PureTranslate: SymbolicArrayRepr"
  ptranslate [nuP| (SymbolicStructRepr _) |] =
    return $ error "PureTranslate: SymbolicStructRepr"


instance PureTranslate (ExprVar a) (ExprTrans a) where
  ptranslate mb_x
    | Left memb <- mbNameBoundP mb_x = mapRListLookup memb <$> ask
  ptranslate mb_x = error "ptranslate: unbound variable!"

instance PureTranslate (PermExpr a) (ExprTrans a) where
  ptranslate = error "FIXME HERE NOW"

instance ress ~ (CtxToRList as) =>
         PureTranslate (PermExprs as) (ExprTransCtx ress) where
  ptranslate = error "FIXME HERE NOW"

instance PureTranslate (BVFactor w) OpenTerm where
  ptranslate = error "FIXME HERE NOW"


-- [| p :: ValuePerm |] = type of the impure translation of reg with perms p
instance PureTranslate (ValuePerm a) OpenTerm where
  ptranslate = error "FIXME HERE NOW"

instance PureTranslate (ValuePerms a) [OpenTerm] where
  ptranslate = error "FIXME HERE NOW"


----------------------------------------------------------------------
-- * The Translations of Permission Implications
----------------------------------------------------------------------

-- | The result of translating a "proof element" of a permission of type
-- @'ValuePerm' a@. The idea here is that, for a permission implication or typed
-- statement that consumes or emits permission @p@, the translation consumes or
-- emits an element of the SAW type @'ptranslate' p@.
data PermTrans ctx (a :: CrucibleType) where
  -- | The @true@ permission translated to unit, i.e., nothing
  PTrans_True :: TypeCtx ctx => PermTrans ctx a

  -- | An @eq(e)@ permission is also translated to unit
  PTrans_Eq :: Mb ctx (PermExpr a) -> PermTrans ctx a

  -- | LLVM pointer permissions can be broken into multiple SAW terms, one for
  -- each pointer permission
  PTrans_LLVMPtr :: (1 <= w, KnownNat w, TypeCtx ctx) =>
                    [LLVMPermTrans ctx w] -> PermTrans ctx (LLVMPointerType w)

  -- | LLVM frame permissions are translated to unit
  PTrans_LLVMFrame :: (1 <= w, KnownNat w) =>
                      Mb ctx (LLVMFramePerm w) ->
                      PermTrans ctx (LLVMFrameType w)

  -- | Any other permissions are just SAW terms. Note that this can include LLVM
  -- pointer permissions that have not yet been broken into multiple SAW terms.
  PTrans_Other :: Mb ctx (ValuePerm a) -> OpenTerm -> PermTrans ctx a


data LLVMPermTrans ctx w
  = LLVMPermTrans_Field (Mb ctx (LLVMFieldPerm w)) OpenTerm
  | LLVMPermTrans_Array (Mb ctx (LLVMArrayPerm w)) OpenTerm
  | LLVMPermTrans_Free (Mb ctx (PermExpr (BVType w)))


-- | A context mapping bound names to their perm translations
type PermTransCtx ctx ps = MapRList (PermTrans ctx) ps


-- | Map a perm translation result to an 'OpenTerm'
permTransToTerm :: PermTrans ctx a -> Maybe OpenTerm
permTransToTerm PTrans_True = Nothing
permTransToTerm (PTrans_Eq _) = Nothing
permTransToTerm (PTrans_LLVMPtr pts) =
  Just $ tupleOpenTerm $ catMaybes $ map llvmPermTransToTerm pts
permTransToTerm (PTrans_LLVMFrame _) = Nothing
permTransToTerm (PTrans_Other _ t) = Just t

-- | Map a translation of an LLVM pointer perm to an 'OpenTerm'
llvmPermTransToTerm :: LLVMPermTrans ctx w -> Maybe OpenTerm
llvmPermTransToTerm (LLVMPermTrans_Field _ t) = Just t
llvmPermTransToTerm (LLVMPermTrans_Array _ t) = Just t
llvmPermTransToTerm (LLVMPermTrans_Free _) = Nothing

-- | Map a context of perm translations to a list of 'OpenTerm's, dropping the
-- "invisible" ones that are always translated to unit
permCtxToTerms :: PermTransCtx ctx ps -> [OpenTerm]
permCtxToTerms =
  catMaybes . mapRListToList . mapMapRList (Constant.Constant . permTransToTerm)

-- | Extract out the permission of a permission translation result
permTransPerm :: PermTrans ctx a -> Mb ctx (ValuePerm a)
permTransPerm PTrans_True = pure ValPerm_True
permTransPerm (PTrans_Eq e) = fmap ValPerm_Eq e
permTransPerm (PTrans_LLVMPtr ts) =
  fmap ValPerm_LLVMPtr $ sequenceA $ map llvmPermTransPerm ts
permTransPerm (PTrans_Other p _) = p

llvmPermTransPerm :: LLVMPermTrans ctx a -> Mb ctx (LLVMPtrPerm a)
llvmPermTransPerm (LLVMPermTrans_Field pp _) = fmap LLVMPP_Field pp
llvmPermTransPerm (LLVMPermTrans_Array pp _) = fmap LLVMPP_Array pp
llvmPermTransPerm (LLVMPermTrans_Free e) = fmap LLVMPP_Free e

extMb :: Mb ctx a -> Mb (ctx :> tp) a
extMb = mbCombine . fmap (nu . const)

-- | Extend the context of a permission translation result
extPermTrans :: PermTrans ctx a -> PermTrans (ctx :> tp) a
extPermTrans PTrans_True = PTrans_True
extPermTrans (PTrans_Eq e) = PTrans_Eq $ extMb e
extPermTrans (PTrans_LLVMPtr pts) = PTrans_LLVMPtr $ map extLLVMPermTrans pts
extPermTrans (PTrans_Other p t) = PTrans_Other (extMb p) t

extLLVMPermTrans :: LLVMPermTrans ctx a -> LLVMPermTrans (ctx :> tp) a
extLLVMPermTrans (LLVMPermTrans_Field pp t) =
  LLVMPermTrans_Field (extMb pp) t
extLLVMPermTrans (LLVMPermTrans_Array pp t) =
  LLVMPermTrans_Array (extMb pp) t
extLLVMPermTrans (LLVMPermTrans_Free e) = LLVMPermTrans_Free $ extMb e

-- | Extend the context of a permission translation context
extPermTransCtx :: PermTransCtx ctx ps -> PermTransCtx (ctx :> tp) ps
extPermTransCtx = mapMapRList extPermTrans

-- | Add another permission translation to a permission translation context
consPermTransCtx :: PermTransCtx ctx ps -> PermTrans ctx a ->
                    PermTransCtx ctx (ps :> a)
consPermTransCtx = (:>:)


----------------------------------------------------------------------
-- * The Impure Translation Monad
----------------------------------------------------------------------

-- | A mapping from a block entrypoint to its corresponding SAW variable that is
-- bound to its translation
data TypedEntryTrans ext blocks ret args =
  TypedEntryTrans (TypedEntry ext blocks ret args) OpenTerm

-- | A mapping from a block to the SAW functions for each entrypoint
data TypedBlockTrans ext blocks ret args =
  TypedBlockTrans [TypedEntryTrans ext blocks ret args]

-- | A mapping from all block entrypoints to their SAW translations
type TypedBlockMapTrans ext blocks ret =
  MapRList (TypedBlockTrans ext blocks ret) blocks

-- | Translate an entrypoint ID by looking up its SAW function
translateTypedEntryID :: TypedEntryID blocks args ghosts ->
                         TypedBlockMapTrans ext blocks ret ->
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
data ImpTransInfo ext blocks ret args ps ctx =
  ImpTransInfo
  {
    itiExprCtx :: ExprTransCtx ctx,
    itiPermCtx :: PermTransCtx ctx ctx,
    itiPermStack :: PermTransCtx ctx ps,
    itiBlockTrans :: TypedBlockMapTrans ext blocks ret,
    itiCatchHandler :: Maybe OpenTerm
  }

extPermTransInfo :: ExprTrans tp -> PermTrans (ctx :> tp) tp ->
                    ImpTransInfo ext blocks ret args ps ctx ->
                    ImpTransInfo ext blocks ret args ps (ctx :> tp)
extPermTransInfo tp_trans perm_trans (ImpTransInfo {..}) =
  ImpTransInfo
  { itiExprCtx = itiExprCtx :>: tp_trans
  , itiPermCtx = consPermTransCtx (extPermTransCtx itiPermCtx) perm_trans
  , itiPermStack = extPermTransCtx itiPermStack
  , .. }

-- | The monad for permission-level translation
type ImpTransM ext blocks ret args ps ctx =
  Reader (ImpTransInfo ext blocks ret args ps ctx)

-- | Embed a pure translation into an impure translation
embedPureM :: PureTransM ctx a -> ImpTransM ext blocks ret args ps ctx a
embedPureM = withReader itiExprCtx

-- | Run an 'ImpTransM' computation in an extended context
inExtImpTransM :: ExprTrans tp -> PermTrans (ctx :> tp) tp ->
                  ImpTransM ext blocks ret args ps (ctx :> tp) a ->
                  ImpTransM ext blocks ret args ps ctx a
inExtImpTransM tp_trans perm_trans =
  withReader $ extPermTransInfo tp_trans perm_trans

-- | Apply the translation of a function-like construct (i.e., a
-- 'TypedJumpTarget' or 'TypedFnHandle') to the pure plus impure translations of
-- its arguments
translateApply :: OpenTerm -> ExprTransCtx tps -> PermTransCtx ctx tps ->
                  OpenTerm
translateApply f p_args i_args =
  applyOpenTermMulti f (exprCtxToTerms p_args ++ permCtxToTerms i_args)


----------------------------------------------------------------------
-- * The Impure Translation
----------------------------------------------------------------------

-- | The typeclass for the impure translation
class ImpureTranslate a res ext blocks ret args ps ctx | ctx a -> res where
  itranslate :: Mb ctx a -> ImpTransM ext blocks ret args ps ctx res

-- | The typeclass for the impure translation of a functor at any type to an
-- 'OpenTerm'
class ImpureTranslate1 f ext blocks ret args ps ctx where
  itranslate1 :: Mb ctx (f a) -> ImpTransM ext blocks ret args ps ctx OpenTerm

instance ImpureTranslate1 f ext blocks ret args ps ctx =>
         ImpureTranslate (PermImpl f ps) OpenTerm ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImpureTranslate (TypedReg tp) (PermTrans ctx tp)
         ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImpureTranslate (TypedExpr ext tp) (PermTrans ctx tp)
         ext blocks ret args ps ctx where
  itranslate = error "FIXME HERE NOW"

instance ImpureTranslate (TypedEntryID blocks args' ghosts) OpenTerm
         ext blocks ret args ps ctx where
  itranslate mb_entryID =
    translateTypedEntryID (mbLift mb_entryID) <$> itiBlockTrans <$> ask

-- A sequence of distinguished permissions on variables translates to a list of
-- pure translations of the variables and impure translations of the permissions
-- on them
instance ImpureTranslate (DistPerms tps) (ExprTransCtx tps, PermTransCtx ctx tps)
         ext blocks ret args ps ctx where
  itranslate [nuP| DistPermsNil |] = return (MNil, MNil)
  itranslate [nuP| DistPermsCons perms x _ |] =
    do (p_trs,i_trs) <- itranslate perms
       p_tr <- embedPureM $ ptranslate x
       i_tr <- itranslate (fmap TypedReg x)
       return (p_trs :>: p_tr, i_trs :>: i_tr)

instance ImpureTranslate (TypedJumpTarget blocks ps) OpenTerm
         ext blocks ret args ps ctx where
  itranslate [nuP| TypedJumpTarget entryID _ perms |] =
    do f <- itranslate entryID
       (p_args, i_args) <- itranslate perms
       return $ translateApply f p_args i_args

{-
FIXME HERE NOW:
- Write the translation for PermImpl and for TypedStmt, to see what prims we need
- Need something special for TypedStmt to bind vars; maybe just do seqs?
- ImpTranslate for statement sequences, blocks / entrypoints, and CFGs
-}
