{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Verifier.SAW.Heapster.Permissions where

import Prelude hiding (pred)

import Data.Maybe
import Data.List hiding (sort)
import Data.List.NonEmpty (NonEmpty(..))
import Data.String
import Data.Proxy
import Data.Reflection
import Data.Functor.Constant
import qualified Data.BitVector.Sized as BV
import Data.BitVector.Sized (BV)
import Numeric.Natural
import GHC.TypeLits
import Data.Kind
import Control.Applicative hiding (empty)
import Control.Monad.Identity hiding (ap)
import Control.Monad.State hiding (ap)
import Control.Monad.Reader hiding (ap)
import Control.Lens hiding ((:>), Index, Empty, ix, op)

import Data.Binding.Hobbits hiding (sym)
import Data.Type.RList (append, memberElem, mapRAssign, mapToList, Eq1(..))
import qualified Data.Type.RList as RL
import Data.Binding.Hobbits.MonadBind as MB
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap
import Data.Binding.Hobbits.NameSet (NameSet, SomeName(..), toList,
                                     SomeRAssign(..), namesListToNames,
                                     nameSetIsSubsetOf)
import qualified Data.Binding.Hobbits.NameSet as NameSet

import Data.Parameterized.Context (Assignment, AssignView(..),
                                   pattern Empty, viewAssign)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.BoolRepr
import Data.Parameterized.NatRepr

import Prettyprinter as PP
import Prettyprinter.Render.String (renderString)

import Lang.Crucible.Types
import Lang.Crucible.FunctionHandle
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.LLVM.Bytes
import Lang.Crucible.CFG.Core
import Verifier.SAW.Term.Functor (Ident)
import Verifier.SAW.OpenTerm

import Verifier.SAW.Heapster.CruUtil

import Debug.Trace


----------------------------------------------------------------------
-- * Utility Functions
----------------------------------------------------------------------

-- | Delete the nth element of a list
deleteNth :: Int -> [a] -> [a]
deleteNth i xs | i >= length xs = error "deleteNth"
deleteNth i xs = take i xs ++ drop (i+1) xs

-- | Replace the nth element of a list
replaceNth :: Int -> a -> [a] -> [a]
replaceNth i _ xs | i >= length xs = error "replaceNth"
replaceNth i x xs = take i xs ++ x : drop (i+1) xs

-- | Insert an element at the nth location in a list
insertNth :: Int -> a -> [a] -> [a]
insertNth i x xs = take i xs ++ x : drop i xs


-- | Find all elements of list @l@ where @f@ returns a value and return that
-- value plus its index into @l@
findMaybeIndices :: (a -> Maybe b) -> [a] -> [(Int, b)]
findMaybeIndices f l = catMaybes $ zipWith (\i a -> (i,) <$> f a) [0 ..] l

-- | Find the index of the first element of a list that returns the maximal
-- positive value from the supplied ranking function, or return 'Nothing' if all
-- elements have non-positive rank
findBestIndex :: (a -> Int) -> [a] -> Maybe Int
findBestIndex rank_f l =
  fst $ foldl (\(best_ix,best_rank) (ix,rank) ->
                if rank > best_rank then (Just ix, rank) else
                  (best_ix,best_rank))
  (Nothing, 0) (zipWith (\i a -> (i,rank_f a)) [0 ..] l)

-- | Combine all elements of a list like 'foldr1' unless the list is empty, in
-- which case return the default case
foldr1WithDefault :: (a -> a -> a) -> a -> [a] -> a
foldr1WithDefault _ def [] = def
foldr1WithDefault _ _ [a] = a
foldr1WithDefault f def (a:as) = f a $ foldr1WithDefault f def as

-- | Map a function across a list and then call 'foldr1WithDefault'. This is a
-- form of map-reduce where the default is returned as a special case for the
-- empty list.
foldMapWithDefault :: (b -> b -> b) -> b -> (a -> b) -> [a] -> b
foldMapWithDefault comb def f l = foldr1WithDefault comb def $ map f l


----------------------------------------------------------------------
-- * Pretty-printing
----------------------------------------------------------------------

newtype StringF a = StringF { unStringF :: String }

data PPInfo =
  PPInfo { ppExprNames :: NameMap (StringF :: CrucibleType -> Type),
           ppPermNames :: NameMap (StringF :: Type -> Type),
           ppVarIndex :: Int }

emptyPPInfo :: PPInfo
emptyPPInfo = PPInfo NameMap.empty NameMap.empty 1

-- | Record an expression variable in a 'PPInfo' with the given base name
ppInfoAddExprName :: String -> ExprVar a -> PPInfo -> PPInfo
ppInfoAddExprName base x info =
  info { ppExprNames =
           NameMap.insert x (StringF (base ++ show (ppVarIndex info)))
           (ppExprNames info),
           ppVarIndex = ppVarIndex info + 1 }

ppInfoAddExprNames :: String -> RAssign Name (tps :: RList CrucibleType) ->
                      PPInfo -> PPInfo
ppInfoAddExprNames _ MNil info = info
ppInfoAddExprNames base (ns :>: n) info =
  ppInfoAddExprNames base ns $ ppInfoAddExprName base n info

-- | Record a permission variable in a 'PPInfo' with the given base name
ppInfoAddPermName :: String -> Name (a :: Type) -> PPInfo -> PPInfo
ppInfoAddPermName base x info =
  info { ppPermNames =
           NameMap.insert x (StringF (base ++ show (ppVarIndex info)))
           (ppPermNames info),
           ppVarIndex = ppVarIndex info + 1 }

ppInfoAddPermNames :: String -> RAssign Name (tps :: RList Type) ->
                      PPInfo -> PPInfo
ppInfoAddPermNames _ MNil info = info
ppInfoAddPermNames base (ns :>: n) info =
  ppInfoAddPermNames base ns $ ppInfoAddPermName base n info


type PermPPM = Reader PPInfo

instance NuMatching (Doc ann) where
  nuMatchingProof = unsafeMbTypeRepr

instance Closable (Doc ann) where
  toClosed = unsafeClose

instance Liftable (Doc ann) where
  mbLift = unClosed . mbLift . fmap toClosed


class PermPretty a where
  permPrettyM :: a -> PermPPM (Doc ann)

class PermPrettyF f where
  permPrettyMF :: f a -> PermPPM (Doc ann)

permPretty :: PermPretty a => PPInfo -> a -> Doc ann
permPretty info a = runReader (permPrettyM a) info

renderDoc :: Doc ann -> String
renderDoc doc = renderString (layoutSmart opts doc)
  where opts = LayoutOptions (AvailablePerLine 80 0.8)

permPrettyString :: PermPretty a => PPInfo -> a -> String
permPrettyString info a = renderDoc $ permPretty info a

tracePretty :: Doc ann -> a -> a
tracePretty doc = trace (renderDoc doc)

-- | Pretty-print a comma-separated list using 'fillSep'
ppCommaSep :: [Doc ann] -> Doc ann
ppCommaSep [] = mempty
ppCommaSep ds =
  PP.group $ align $ fillSep (map (<> comma) (take (length ds - 1) ds)
                              ++ [last ds])

-- | Pretty-print a comma-separated list using 'fillSep' enclosed inside either
-- parentheses (if the supplied flag is 'True') or brackets (if it is 'False')
ppEncList :: Bool -> [Doc ann] -> Doc ann
ppEncList flag ds =
  (if flag then parens else brackets) $ ppCommaSep ds

instance (PermPretty a, PermPretty b) => PermPretty (a,b) where
  permPrettyM (a,b) = tupled <$> sequence [permPrettyM a, permPrettyM b]

instance (PermPretty a, PermPretty b, PermPretty c) => PermPretty (a,b,c) where
  permPrettyM (a,b,c) =
    tupled <$> sequence [permPrettyM a, permPrettyM b, permPrettyM c]

instance PermPretty a => PermPretty [a] where
  permPrettyM as = ppEncList False <$> mapM permPrettyM as

instance PermPretty (ExprVar a) where
  permPrettyM x =
    do maybe_str <- NameMap.lookup x <$> ppExprNames <$> ask
       case maybe_str of
         Just (StringF str) -> return $ pretty str
         Nothing -> return $ pretty (show x)

instance PermPrettyF (Name :: CrucibleType -> Type) where
  permPrettyMF = permPrettyM

instance PermPretty (Name (a :: Type)) where
  permPrettyM x =
    do maybe_str <- NameMap.lookup x <$> ppPermNames <$> ask
       case maybe_str of
         Just (StringF str) -> return $ pretty str
         Nothing -> return $ pretty (show x)

instance PermPretty (SomeName CrucibleType) where
  permPrettyM (SomeName x) = permPrettyM x

instance PermPretty (SomeName Type) where
  permPrettyM (SomeName x) = permPrettyM x

instance PermPrettyF f => PermPretty (RAssign f ctx) where
  permPrettyM xs =
    ppCommaSep <$> sequence (RL.mapToList permPrettyMF xs)

instance PermPretty (TypeRepr a) where
  permPrettyM UnitRepr = return $ pretty "unit"
  permPrettyM BoolRepr = return $ pretty "bool"
  permPrettyM NatRepr = return $ pretty "nat"
  permPrettyM (BVRepr w) = return (pretty "bv" <+> pretty (intValue w))
  permPrettyM (LLVMPointerRepr w) =
    return (pretty "llvmptr" <+> pretty (intValue w))
  permPrettyM (LLVMFrameRepr w) =
    return (pretty "llvmframe" <+> pretty (intValue w))
  permPrettyM LifetimeRepr = return $ pretty "lifetime"
  permPrettyM RWModalityRepr = return $ pretty "rwmodality"
  permPrettyM (LLVMShapeRepr w) =
    return (pretty "llvmshape" <+> pretty (intValue w))
  permPrettyM (LLVMBlockRepr w) =
    return (pretty "llvmblock" <+> pretty (intValue w))
  permPrettyM PermListRepr = return $ pretty "permlist"
  permPrettyM (StructRepr flds) =
    (pretty "struct" <+>) <$> parens <$> permPrettyM (assignToRList flds)
  permPrettyM (ValuePermRepr tp) = (pretty "perm" <+>) <$> permPrettyM tp
  permPrettyM tp =
    return (pretty "not-yet-printable type" <+> parens (pretty tp))

instance PermPrettyF TypeRepr where
  permPrettyMF = permPrettyM

instance PermPretty (CruCtx ctx) where
  permPrettyM = permPrettyM . cruCtxToTypes

-- | A pair of a variable and its 'CrucibleType', for pretty-printing
data VarAndType a = VarAndType (ExprVar a) (TypeRepr a)

instance PermPretty (VarAndType a) where
  permPrettyM (VarAndType x tp) =
    do x_pp <- permPrettyM x
       tp_pp <- permPrettyM tp
       return (x_pp <> colon <> tp_pp)

instance PermPrettyF VarAndType where
  permPrettyMF = permPrettyM


permPrettyExprMb :: PermPretty a =>
                    (RAssign (Constant (Doc ann)) ctx -> PermPPM (Doc ann) -> PermPPM (Doc ann)) ->
                    Mb (ctx :: RList CrucibleType) a -> PermPPM (Doc ann)
permPrettyExprMb f mb =
  fmap mbLift $ strongMbM $ flip nuMultiWithElim1 mb $ \ns a ->
  local (ppInfoAddExprNames "z" ns) $
  do docs <- traverseRAssign (\n -> Constant <$> permPrettyM n) ns
     f docs $ permPrettyM a

-- FIXME: no longer needed?
{-
permPrettyPermMb :: PermPretty a =>
                    (RAssign (Constant (Doc ann)) ctx -> PermPPM (Doc ann) -> PermPPM (Doc ann)) ->
                    Mb (ctx :: RList Type) a -> PermPPM (Doc ann)
permPrettyPermMb f mb =
  fmap mbLift $ strongMbM $ flip nuMultiWithElim1 mb $ \ns a ->
  local (ppInfoAddPermNames "z" ns) $
  do docs <- traverseRAssign (\n -> Constant <$> permPrettyM n) ns
     f docs $ permPrettyM a
-}

instance PermPretty a => PermPretty (Mb (ctx :: RList CrucibleType) a) where
  permPrettyM =
    permPrettyExprMb $ \docs ppm ->
    (\pp -> PP.group (ppEncList True (RL.toList docs) <>
                      nest 2 (dot <> line <> pp))) <$> ppm

-- FIXME: no longer needed?
{-
instance PermPretty a => PermPretty (Mb (ctx :: RList Type) a) where
  permPrettyM =
    permPrettyPermMb $ \docs ppm ->
    (\pp -> PP.group (tupled (RL.toList docs) <> dot <> line <> pp)) <$> ppm
-}

instance PermPretty Integer where
  permPrettyM = return . pretty


----------------------------------------------------------------------
-- * Expressions for Permissions
----------------------------------------------------------------------

-- | The Haskell type of expression variables
type ExprVar = (Name :: CrucibleType -> Type)

-- | Crucible type for lifetimes; we give them a Crucible type so they can be
-- existentially bound in the same way as other Crucible objects
type LifetimeType = IntrinsicType "Lifetime" EmptyCtx

-- | The object-level representation of 'LifetimeType'
lifetimeTypeRepr :: TypeRepr LifetimeType
lifetimeTypeRepr = knownRepr

-- | Pattern for building/destructing lifetime types
pattern LifetimeRepr :: () => (ty ~ LifetimeType) => TypeRepr ty
pattern LifetimeRepr <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "Lifetime") ->
                 Just Refl)
  Empty
  where LifetimeRepr = IntrinsicRepr knownSymbol Empty

-- | A lifetime is an expression of type 'LifetimeType'
--type Lifetime = PermExpr LifetimeType

-- | Crucible type for read/write modalities; we give them a Crucible type so
-- they can be used as variables in recursive permission definitions
type RWModalityType = IntrinsicType "RWModality" EmptyCtx

-- | The object-level representation of 'RWModalityType'
rwModalityTypeRepr :: TypeRepr RWModalityType
rwModalityTypeRepr = knownRepr

-- | Pattern for building/destructing RWModality types
pattern RWModalityRepr :: () => (ty ~ RWModalityType) => TypeRepr ty
pattern RWModalityRepr <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "RWModality") ->
                 Just Refl)
  Empty
  where RWModalityRepr = IntrinsicRepr knownSymbol Empty

-- | Crucible type for lists of expressions and permissions on them
type PermListType = IntrinsicType "PermList" EmptyCtx

-- | Pattern for building/desctructing permission list types
pattern PermListRepr :: () => ty ~ PermListType => TypeRepr ty
pattern PermListRepr <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "PermList") ->
                 Just Refl) Empty
  where
    PermListRepr = IntrinsicRepr knownSymbol Empty

-- | Crucible type for LLVM stack frame objects
type LLVMFrameType w = IntrinsicType "LLVMFrame" (EmptyCtx ::> BVType w)

-- | Pattern for building/desctructing LLVM frame types
pattern LLVMFrameRepr :: () => (1 <= w, ty ~ LLVMFrameType w) =>
                         NatRepr w -> TypeRepr ty
pattern LLVMFrameRepr w <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "LLVMFrame") ->
                 Just Refl)
  (viewAssign -> AssignExtend Empty (BVRepr w))
  where
    LLVMFrameRepr w = IntrinsicRepr knownSymbol (Ctx.extend Empty (BVRepr w))

-- | Crucible type for value permissions themselves
type ValuePermType a = IntrinsicType "Perm" (EmptyCtx ::> a)

-- | Pattern for building/desctructing permissions as expressions
pattern ValuePermRepr :: () => (ty ~ ValuePermType a) => TypeRepr a ->
                         TypeRepr ty
pattern ValuePermRepr a <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "Perm") ->
                 Just Refl)
  (viewAssign -> AssignExtend Empty a)
  where
    ValuePermRepr a = IntrinsicRepr knownSymbol (Ctx.extend Empty a)

-- | Crucible type for LLVM shapes
type LLVMShapeType w = IntrinsicType "LLVMShape" (EmptyCtx ::> BVType w)

-- | Pattern for building/desctructing LLVM frame types
pattern LLVMShapeRepr :: () => (1 <= w, ty ~ LLVMShapeType w) =>
                         NatRepr w -> TypeRepr ty
pattern LLVMShapeRepr w <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "LLVMShape") ->
                 Just Refl)
  (viewAssign -> AssignExtend Empty (BVRepr w))
  where
    LLVMShapeRepr w = IntrinsicRepr knownSymbol (Ctx.extend Empty (BVRepr w))

-- | Crucible type for LLVM memory blocks
type LLVMBlockType w = IntrinsicType "LLVMBlock" (EmptyCtx ::> BVType w)

-- | Pattern for building/desctructing LLVM frame types
pattern LLVMBlockRepr :: () => (1 <= w, ty ~ LLVMBlockType w) =>
                         NatRepr w -> TypeRepr ty
pattern LLVMBlockRepr w <-
  IntrinsicRepr (testEquality (knownSymbol :: SymbolRepr "LLVMBlock") ->
                 Just Refl)
  (viewAssign -> AssignExtend Empty (BVRepr w))
  where
    LLVMBlockRepr w = IntrinsicRepr knownSymbol (Ctx.extend Empty (BVRepr w))


-- | Expressions that are considered "pure" for use in permissions. Note that
-- these are in a normal form, that makes them easier to analyze.
data PermExpr (a :: CrucibleType) where
  -- | A variable of any type
  PExpr_Var :: ExprVar a -> PermExpr a

  -- | A unit literal
  PExpr_Unit :: PermExpr UnitType

  -- | A literal Boolean number
  PExpr_Bool :: Bool -> PermExpr BoolType

  -- | A literal natural number
  PExpr_Nat :: Natural -> PermExpr NatType

  -- | A literal string
  PExpr_String :: String -> PermExpr (StringType Unicode)

  -- | A bitvector expression is a linear expression in @N@ variables, i.e., sum
  -- of constant times variable factors plus a constant
  --
  -- FIXME: make the offset a 'Natural'
  PExpr_BV :: (1 <= w, KnownNat w) =>
              [BVFactor w] -> BV w -> PermExpr (BVType w)

  -- | A struct expression is an expression for each argument of the struct type
  PExpr_Struct :: PermExprs (CtxToRList args) -> PermExpr (StructType args)

  -- | The @always@ lifetime that is always current
  PExpr_Always :: PermExpr LifetimeType

  -- | An LLVM value that represents a word, i.e., whose region identifier is 0
  PExpr_LLVMWord :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                    PermExpr (LLVMPointerType w)

  -- | An LLVM value built by adding an offset to an LLVM variable
  PExpr_LLVMOffset :: (1 <= w, KnownNat w) =>
                      ExprVar (LLVMPointerType w) ->
                      PermExpr (BVType w) ->
                      PermExpr (LLVMPointerType w)

  -- | A literal function pointer
  PExpr_Fun :: FnHandle args ret -> PermExpr (FunctionHandleType args ret)

  -- | An empty permission list
  PExpr_PermListNil :: PermExpr PermListType

  -- | A cons of an expression and a permission on it to a permission list
  PExpr_PermListCons :: TypeRepr a -> PermExpr a -> ValuePerm a ->
                        PermExpr PermListType -> PermExpr PermListType

  -- | A read/write modality 
  PExpr_RWModality :: RWModality -> PermExpr RWModalityType

  -- | The empty / vacuously true shape
  PExpr_EmptyShape :: PermExpr (LLVMShapeType w)

  -- | A named shape along with arguments for it, with optional read/write and
  -- lifetime modalities that are applied to the body of the shape
  PExpr_NamedShape :: KnownNat w => Maybe (PermExpr RWModalityType) ->
                      Maybe (PermExpr LifetimeType) ->
                      NamedShape b args w -> PermExprs args ->
                      PermExpr (LLVMShapeType w)

  -- | The equality shape
  PExpr_EqShape :: PermExpr (LLVMBlockType w) -> PermExpr (LLVMShapeType w)

  -- | A shape for a pointer to another memory block, i.e., a @memblock@
  -- permission, with a given shape. This @memblock@ permission will have the
  -- same read/write and lifetime modalities as the @memblock@ permission
  -- containing this pointer shape, unless they are specifically overridden by
  -- the pointer shape; i.e., we have that
  --
  -- > [l]memblock(rw,off,len,ptrsh(rw',l',sh)) =
  -- >   [l]memblock(rw,off,len,fieldsh([l']memblock(rw',0,len(sh),sh)))
  --
  -- where @rw'@ and/or @l'@ can be 'Nothing', in which case they default to
  -- @rw@ and @l@, respectively.
  PExpr_PtrShape :: Maybe (PermExpr RWModalityType) ->
                    Maybe (PermExpr LifetimeType) ->
                    PermExpr (LLVMShapeType w) -> PermExpr (LLVMShapeType w)

  -- | A shape for a single field with a given permission
  PExpr_FieldShape :: (1 <= w, KnownNat w) => LLVMFieldShape w ->
                      PermExpr (LLVMShapeType w)

  -- | A shape for an array with the given stride, length (in number of
  -- elements = total length / stride), and fields
  PExpr_ArrayShape :: (1 <= w, KnownNat w) =>
                      PermExpr (BVType w) -> Bytes -> [LLVMFieldShape w] ->
                      PermExpr (LLVMShapeType w)

  -- | A sequence of two shapes
  PExpr_SeqShape :: PermExpr (LLVMShapeType w) -> PermExpr (LLVMShapeType w) ->
                    PermExpr (LLVMShapeType w)

  -- | A disjunctive shape
  PExpr_OrShape :: PermExpr (LLVMShapeType w) -> PermExpr (LLVMShapeType w) ->
                   PermExpr (LLVMShapeType w)

  -- | An existential shape
  PExpr_ExShape :: KnownRepr TypeRepr a =>
                   Binding a (PermExpr (LLVMShapeType w)) ->
                   PermExpr (LLVMShapeType w)

  -- | A permission as an expression
  PExpr_ValPerm :: ValuePerm a -> PermExpr (ValuePermType a)


-- | A sequence of permission expressions
type PermExprs = RAssign PermExpr

-- | Pattern for an empty 'PermExprs' list
pattern PExprs_Nil :: () => (tps ~ RNil) => PermExprs tps
pattern PExprs_Nil = MNil

-- | Pattern for a non-empty 'PermExprs' list
pattern PExprs_Cons :: () => (tps ~ (tps' :> a)) =>
                       PermExprs tps' -> PermExpr a -> PermExprs tps
pattern PExprs_Cons es e <- es :>: e
  where
    PExprs_Cons es e = es :>: e

{-# COMPLETE PExprs_Nil, PExprs_Cons #-}

{-
data PermExprs (as :: RList CrucibleType) where
  PExprs_Nil :: PermExprs RNil
  PExprs_Cons :: PermExprs as -> PermExpr a -> PermExprs (as :> a)
-}

-- | Convert a 'PermExprs' to an 'RAssign'
exprsToRAssign :: PermExprs as -> RAssign PermExpr as
exprsToRAssign PExprs_Nil = MNil
exprsToRAssign (PExprs_Cons es e) = exprsToRAssign es :>: e

-- | Convert an 'RAssign' to a 'PermExprs'
rassignToExprs :: RAssign PermExpr as -> PermExprs as
rassignToExprs MNil = PExprs_Nil
rassignToExprs (es :>: e) = PExprs_Cons (rassignToExprs es) e 

-- | Convert a list of names to a 'PermExprs' list
namesToExprs :: RAssign Name as -> PermExprs as
namesToExprs MNil = PExprs_Nil
namesToExprs (ns :>: n) = PExprs_Cons (namesToExprs ns) (PExpr_Var n)

-- | Create a list of phantom 'Proxy' arguments from a 'PermExprs' list
proxiesOfExprs :: PermExprs as -> RAssign Proxy as
proxiesOfExprs PExprs_Nil = MNil
proxiesOfExprs (PExprs_Cons es _) = proxiesOfExprs es :>: Proxy

-- | Append two 'PermExprs' lists
appendExprs :: PermExprs as -> PermExprs bs -> PermExprs (as :++: bs)
appendExprs as PExprs_Nil = as
appendExprs as (PExprs_Cons bs b) = PExprs_Cons (appendExprs as bs) b

-- | Convenience function to get the known type of an expression-like construct
exprType :: KnownRepr TypeRepr a => f a -> TypeRepr a
exprType _ = knownRepr

-- | Convenience function to get the known type of bound name
bindingType :: KnownRepr TypeRepr a => Binding a b -> TypeRepr a
bindingType _ = knownRepr

-- | Convenience function to get the bit width of an LLVM pointer type
exprLLVMTypeWidth :: KnownNat w => f (LLVMPointerType w) -> NatRepr w
exprLLVMTypeWidth _ = knownNat

-- | Convenience function to get the bit width of an LLVM pointer type
shapeLLVMTypeWidth :: KnownNat w => f (LLVMShapeType w) -> NatRepr w
shapeLLVMTypeWidth _ = knownNat

-- | Convenience function to get the number of bytes = the bit width divided by
-- 8 of an LLVM pointer type as an expr. Note that this assumes the bit width is
-- a multiple of 8, so does not worry about rounding.
exprLLVMTypeBytesExpr :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                         f (LLVMPointerType sz) -> PermExpr (BVType w)
exprLLVMTypeBytesExpr e = bvInt (intValue (exprLLVMTypeWidth e) `div` 8)

-- | Convenience function to get the width of an LLVM pointer type of an
-- expression in a binding as an expression
mbExprLLVMTypeBytesExpr :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                           Mb ctx (f (LLVMPointerType sz)) ->
                           PermExpr (BVType w)
mbExprLLVMTypeBytesExpr mb_e =
  bvInt $ div (intValue $ mbLift $ fmap exprLLVMTypeWidth mb_e) 8

-- | Pattern-match a permission list expression as a typed list of permissions
-- consed onto a terminator, which can either be the empty list (represented by
-- 'Nothing') or a variable expression
matchPermList :: PermExpr PermListType -> (Some ExprPerms,
                                           Maybe (ExprVar PermListType))
matchPermList PExpr_PermListNil = (Some MNil, Nothing)
matchPermList (PExpr_Var ps) = (Some MNil, Just ps)
matchPermList (PExpr_PermListCons _ e p l)
  | (Some eperms, term) <- matchPermList l
  = (Some (RL.append (MNil :>: ExprAndPerm e p) eperms), term)

-- | Pattern-match a permission list expression as a list of permissions on
-- variables with an empty list (not a variable) as a terminator
matchVarPermList :: PermExpr PermListType -> Maybe (Some DistPerms)
matchVarPermList PExpr_PermListNil = Just $ Some MNil
matchVarPermList (PExpr_PermListCons _ (PExpr_Var x) p l)
  | Just (Some perms) <- matchVarPermList l =
    Just $ Some $ RL.append (MNil :>: VarAndPerm x p) perms
matchVarPermList _ = Nothing

-- | Fold over all permissions associated with a specific variable in a
-- permission list
foldPermList :: ExprVar a -> (ValuePerm a -> r -> r) -> r ->
                PermExpr PermListType -> r
foldPermList _ _ r PExpr_PermListNil = r
foldPermList _ _ r (PExpr_Var _) = r
foldPermList x f r (PExpr_PermListCons _ (PExpr_Var y) p plist)
  | Just Refl <- testEquality x y =
    f p $ foldPermList x f r plist
foldPermList x f r (PExpr_PermListCons _ _ _ plist) =
  foldPermList x f r plist

-- | Fold over all atomic permissions associated with a specific variable in a
-- permission list
foldPermListAtomic :: ExprVar a -> (AtomicPerm a -> r -> r) -> r ->
                      PermExpr PermListType -> r
foldPermListAtomic x f =
  foldPermList x (\p rest ->
                   case p of
                     ValPerm_Conj ps -> foldr f rest ps
                     _ -> rest)

-- | Find a permission on a specific variable in a permission list
findPermInList :: ExprVar a -> (ValuePerm a -> Bool) -> PermExpr PermListType ->
                  Maybe (ValuePerm a)
findPermInList x pred plist =
  foldPermList x (\p rest -> if pred p then Just p else rest) Nothing plist

-- | Find an atomic permission on a specific variable in a permission list
findAtomicPermInList :: ExprVar a -> (AtomicPerm a -> Bool) ->
                        PermExpr PermListType -> Maybe (AtomicPerm a)
findAtomicPermInList x pred plist =
  foldPermListAtomic x (\p rest ->
                         if pred p then Just p else rest) Nothing plist

-- FIXME: move this down below the mkNuMatching calls or move
-- llvmAtomicPermToBlock up before them... or just remove this function
{-
-- | Find a permission on a specific variable in a permission list that is
-- equivalent to a block permission
findBlockPermInList :: ExprVar (LLVMPointerType w) ->
                       (LLVMBlockPerm w -> Bool) ->
                       PermExpr PermListType -> Maybe (LLVMBlockPerm w)
findBlockPermInList x pred plist =
  foldPermListAtomic x (\p rest ->
                         case llvmAtomicPermToBlock p of
                           Just bp | pred bp -> Just bp
                           _ -> rest) Nothing plist
-}

-- | A bitvector variable, possibly multiplied by a constant
data BVFactor w where
  -- | A variable of type @'BVType' w@ multiplied by a constant @i@, which
  -- should be in the range @0 <= i < 2^w@
  BVFactor :: (1 <= w, KnownNat w) => BV w -> ExprVar (BVType w) ->
              BVFactor w

-- | Whether a permission allows reads or writes
data RWModality
  = Write
  | Read
  deriving Eq


instance Eq (PermExpr a) where
  (PExpr_Var x1) == (PExpr_Var x2) = x1 == x2
  (PExpr_Var _) == _ = False

  PExpr_Unit == PExpr_Unit = True
  PExpr_Unit == _ = False

  (PExpr_Nat n1) == (PExpr_Nat n2) = n1 == n2
  (PExpr_Nat _) == _ = False

  (PExpr_String str1) == (PExpr_String str2) = str1 == str2
  (PExpr_String _) == _ = False

  (PExpr_Bool b1) == (PExpr_Bool b2) = b1 == b2
  (PExpr_Bool _) == _ = False

  (PExpr_BV factors1 const1) == (PExpr_BV factors2 const2) =
    const1 == const2 && eqFactors factors1 factors2
    where
      eqFactors :: [BVFactor w] -> [BVFactor w] -> Bool
      eqFactors [] [] = True
      eqFactors (f : fs1) fs2
        | elem f fs2 = eqFactors fs1 (delete f fs2)
      eqFactors _ _ = False
  (PExpr_BV _ _) == _ = False

  (PExpr_Struct args1) == (PExpr_Struct args2) = args1 == args2 where
  (PExpr_Struct _) == _ = False

  PExpr_Always == PExpr_Always = True
  PExpr_Always == _ = False

  (PExpr_LLVMWord e1) == (PExpr_LLVMWord e2) = e1 == e2
  (PExpr_LLVMWord _) == _ = False

  (PExpr_LLVMOffset x1 e1) == (PExpr_LLVMOffset x2 e2) =
    x1 == x2 && e1 == e2
  (PExpr_LLVMOffset _ _) == _ = False

  (PExpr_Fun fh1) == (PExpr_Fun fh2) = fh1 == fh2
  (PExpr_Fun _) == _ = False

  PExpr_PermListNil == PExpr_PermListNil = True
  PExpr_PermListNil == _ = False

  (PExpr_PermListCons tp1 e1 p1 l1) == (PExpr_PermListCons tp2 e2 p2 l2)
    | Just Refl <- testEquality tp1 tp2
    = e1 == e2 && p1 == p2 && l1 == l2
  (PExpr_PermListCons _ _ _ _) == _ = False

  (PExpr_RWModality rw1) == (PExpr_RWModality rw2) = rw1 == rw2
  (PExpr_RWModality _) == _ = False

  PExpr_EmptyShape == PExpr_EmptyShape = True
  PExpr_EmptyShape == _ = False

  (PExpr_NamedShape maybe_rw1 maybe_l1 nmsh1 args1)
    == (PExpr_NamedShape maybe_rw2 maybe_l2 nmsh2 args2)
    | Just (Refl,Refl) <- namedShapeEq nmsh1 nmsh2 =
      maybe_rw1 == maybe_rw2 && maybe_l1 == maybe_l2 && args1 == args2
  (PExpr_NamedShape _ _ _ _) == _ = False

  (PExpr_EqShape b1) == (PExpr_EqShape b2) = b1 == b2
  (PExpr_EqShape _) == _ = False

  (PExpr_PtrShape rw1 l1 sh1) == (PExpr_PtrShape rw2 l2 sh2) =
    rw1 == rw2 && l1 == l2 && sh1 == sh2
  (PExpr_PtrShape _ _ _) == _ = False

  (PExpr_FieldShape p1) == (PExpr_FieldShape p2) = p1 == p2
  (PExpr_FieldShape _) == _ = False

  (PExpr_ArrayShape len1 s1 flds1) == (PExpr_ArrayShape len2 s2 flds2) =
    len1 == len2 && s1 == s2 && flds1 == flds2
  (PExpr_ArrayShape _ _ _) == _ = False

  (PExpr_SeqShape sh1 sh1') == (PExpr_SeqShape sh2 sh2') =
    sh1 == sh2 && sh1' == sh2'
  (PExpr_SeqShape _ _) == _ = False

  (PExpr_OrShape sh1 sh1') == (PExpr_OrShape sh2 sh2') =
    sh1 == sh2 && sh1' == sh2'
  (PExpr_OrShape _ _) == _ = False

  (PExpr_ExShape mb_sh1) == (PExpr_ExShape mb_sh2)
    | Just Refl <- testEquality (bindingType mb_sh1) (bindingType mb_sh2)
    = mbLift $ mbMap2 (==) mb_sh1 mb_sh2
  (PExpr_ExShape _) == _ = False

  (PExpr_ValPerm p1) == (PExpr_ValPerm p2) = p1 == p2
  (PExpr_ValPerm _) == _ = False


instance Eq1 PermExpr where
  eq1 = (==)

instance Eq (BVFactor w) where
  (BVFactor i1 x1) == (BVFactor i2 x2) = i1 == i2 && x1 == x2

instance PermPretty (PermExpr a) where
  permPrettyM (PExpr_Var x) = permPrettyM x
  permPrettyM PExpr_Unit = return $ pretty "()"
  permPrettyM (PExpr_Nat n) = return $ pretty $ show n
  permPrettyM (PExpr_String str) = return (pretty '"' <> pretty str <> pretty '"')
  permPrettyM (PExpr_Bool b) = return $ pretty b
  permPrettyM (PExpr_BV factors constant) =
    do pps <- mapM permPrettyM factors
       return $ encloseSep mempty mempty (pretty "+")
         (pps ++ [pretty $ BV.asUnsigned constant])
  permPrettyM (PExpr_Struct args) =
    (\pp -> pretty "struct" <+> parens pp) <$> permPrettyM args
  permPrettyM PExpr_Always = return $ pretty "always"
  permPrettyM (PExpr_LLVMWord e) = (pretty "LLVMword" <+>) <$> permPrettyM e
  permPrettyM (PExpr_LLVMOffset x e) =
    (\ppx ppe -> ppx <+> pretty "&+" <+> ppe)
    <$> permPrettyM x <*> permPrettyM e
  permPrettyM (PExpr_Fun fh) = return $ angles $ pretty ("fun" ++ show fh)
  permPrettyM e@PExpr_PermListNil = prettyPermListM e
  permPrettyM e@(PExpr_PermListCons _ _ _ _) = prettyPermListM e
  permPrettyM (PExpr_RWModality rw) = permPrettyM rw
  permPrettyM PExpr_EmptyShape = return $ pretty "emptysh"
  permPrettyM (PExpr_NamedShape maybe_rw maybe_l nmsh args) =
    do l_pp <- maybe (return mempty) permPrettyLifetimePrefix maybe_l
       rw_pp <- case maybe_rw of
         Just rw -> parens <$> permPrettyM rw
         Nothing -> return mempty
       args_pp <- permPrettyM args
       return (l_pp <> rw_pp <> pretty (namedShapeName nmsh) <>
               pretty '<' <> align (args_pp <> pretty '>'))
  permPrettyM (PExpr_EqShape b) =
    ((pretty "eqsh" <>) . parens) <$> permPrettyM b
  permPrettyM (PExpr_PtrShape maybe_rw maybe_l sh) =
    do l_pp <- maybe (return mempty) permPrettyLifetimePrefix maybe_l
       rw_pp <- case maybe_rw of
         Just rw -> (<> pretty ",") <$> permPrettyM rw
         Nothing -> return mempty
       sh_pp <- permPrettyM sh
       return (l_pp <> pretty "ptrsh" <> parens (rw_pp <> sh_pp))
  permPrettyM (PExpr_FieldShape fld) =
    (pretty "fieldsh" <>) <$> permPrettyM fld
  permPrettyM (PExpr_ArrayShape len stride flds) =
    do len_pp <- permPrettyM len
       flds_pp <- mapM permPrettyM flds
       let stride_pp = pretty (toInteger stride)
       return (pretty "arraysh" <> tupled [len_pp, stride_pp,
                                           ppEncList False flds_pp])
  permPrettyM (PExpr_SeqShape sh1 sh2) =
    do pp1 <- permPrettyM sh1
       pp2 <- permPrettyM sh2
       return $ nest 2 $ sep [pp1 <> pretty ';', pp2]
  permPrettyM (PExpr_OrShape sh1 sh2) =
    do pp1 <- permPrettyM sh1
       pp2 <- permPrettyM sh2
       return $ nest 2 $ sep [pp1 <+> pretty "orsh", pp2]
  permPrettyM (PExpr_ExShape mb_sh) =
    flip permPrettyExprMb mb_sh $ \(_ :>: Constant pp_n) ppm ->
    do pp <- ppm
       return $ nest 2 $ sep [pretty "exsh" <+> pp_n <> dot, pp]
  permPrettyM (PExpr_ValPerm p) = permPrettyM p

instance (1 <= w, KnownNat w) => PermPretty (LLVMFieldShape w) where
  permPrettyM fsh@(LLVMFieldShape p)
    | Just Refl <- testEquality (natRepr fsh) (exprLLVMTypeWidth p) =
      parens <$> permPrettyM p
  permPrettyM (LLVMFieldShape p) =
    do p_pp <- permPrettyM p
       return $ tupled [pretty (intValue $ exprLLVMTypeWidth p), p_pp]

prettyPermListM :: PermExpr PermListType -> PermPPM (Doc ann)
prettyPermListM PExpr_PermListNil =
  -- Special case for an empty list of permissions
  return $ pretty "empty"
prettyPermListM e =
  case matchPermList e of
    (Some perms, Just term_var) ->
      do pps <- sequence (RL.mapToList permPrettyMF perms)
         pp_term <- permPrettyM term_var
         return $ align $ fillSep (map (<> comma) (take (length pps - 1) pps)
                                   ++ [last pps <+> pretty "::", pp_term])
    (Some perms, Nothing) -> permPrettyM perms

instance PermPrettyF PermExpr where
  permPrettyMF = permPrettyM

instance PermPretty (BVFactor w) where
  permPrettyM (BVFactor i x) =
    ((pretty (BV.asUnsigned i) <> pretty "*") <>) <$> permPrettyM x

instance PermPretty RWModality where
  permPrettyM Read = return $ pretty "R"
  permPrettyM Write = return $ pretty "W"

-- | The 'Write' modality as an expression
pattern PExpr_Write :: PermExpr RWModalityType
pattern PExpr_Write = PExpr_RWModality Write

-- | The 'Read' modality as an expression
pattern PExpr_Read :: PermExpr RWModalityType
pattern PExpr_Read = PExpr_RWModality Read

-- | Build a "default" expression for a given type
zeroOfType :: TypeRepr tp -> PermExpr tp
zeroOfType (BVRepr w) = withKnownNat w $ PExpr_BV [] $ BV.mkBV w 0
zeroOfType LifetimeRepr = PExpr_Always
zeroOfType _ = error "zeroOfType"


----------------------------------------------------------------------
-- * Operations on Bitvector and LLVM Pointer Expressions
----------------------------------------------------------------------

-- | Build a 'BVFactor' for a variable
varFactor :: (1 <= w, KnownNat w) => ExprVar (BVType w) -> BVFactor w
varFactor = BVFactor $ BV.one knownNat

-- | Normalize a bitvector expression @1*x + 0@ to just @x@
bvNormVar :: PermExpr (BVType w) -> PermExpr (BVType w)
bvNormVar (PExpr_BV [BVFactor i x] off)
  | i == BV.one knownNat && off == BV.zero knownNat = PExpr_Var x
bvNormVar e = e

-- | Normalize a bitvector expression, so that every variable has at most one
-- factor and the factors are sorted by variable name. NOTE: we shouldn't
-- actually have to call this if we always construct our expressions with the
-- combinators below.
bvNormalize :: PermExpr (BVType w) -> PermExpr (BVType w)
bvNormalize e@(PExpr_Var _) = e
bvNormalize (PExpr_BV factors off) =
  PExpr_BV
  (norm (sortBy (\(BVFactor _ x) (BVFactor _ y) -> compare x y) factors))
  off
  where
    norm [] = []
    norm ((BVFactor (BV.BV 0) _) : factors') = norm factors'
    norm ((BVFactor i1 x1) : (BVFactor i2 x2) : factors')
      | x1 == x2 = norm ((BVFactor (BV.add knownNat i1 i2) x1) : factors')
    norm (f : factors') = f : norm factors'

-- | Merge two normalized / sorted lists of 'BVFactor's
bvMergeFactors :: [BVFactor w] -> [BVFactor w] -> [BVFactor w]
bvMergeFactors fs1 fs2 =
  filter (\(BVFactor i _) -> i /= BV.zero knownNat) $
  helper fs1 fs2
  where
    helper factors1 [] = factors1
    helper [] factors2 = factors2
    helper ((BVFactor i1 x1):factors1) ((BVFactor i2 x2):factors2)
      | x1 == x2
      = BVFactor (BV.add knownNat i1 i2) x1 : helper factors1 factors2
    helper (f1@(BVFactor _ x1):factors1) (f2@(BVFactor _ x2):factors2)
      | x1 < x2 = f1 : helper factors1 (f2 : factors2)
    helper (f1@(BVFactor _ _):factors1) (f2@(BVFactor _ _):factors2) =
      f2 : helper (f1 : factors1) factors2

-- | Convert a bitvector expression to a sum of factors plus a constant
bvMatch :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
           ([BVFactor w], BV w)
bvMatch (PExpr_Var x) = ([varFactor x], BV.zero knownNat)
bvMatch (PExpr_BV factors constant) = (factors, constant)

-- | Test if a bitvector expression is a constant value
bvMatchConst :: PermExpr (BVType w) -> Maybe (BV w)
bvMatchConst (PExpr_BV [] constant) = Just constant
bvMatchConst _ = Nothing

-- | Test if a bitvector expression is a constant unsigned 'Integer' value
bvMatchConstInt :: PermExpr (BVType w) -> Maybe Integer
bvMatchConstInt = fmap BV.asUnsigned . bvMatchConst


-- | Normalize a bitvector expression to a canonical form. Currently this just
-- means converting @1*x+0@ to @x@.
normalizeBVExpr :: PermExpr (BVType w) -> PermExpr (BVType w)
normalizeBVExpr (PExpr_BV [BVFactor (BV.BV 1) x] (BV.BV 0)) = PExpr_Var x
normalizeBVExpr e = e

-- | Test whether two bitvector expressions are semantically equal
bvEq :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvEq e1 e2 = normalizeBVExpr e1 == normalizeBVExpr e2

-- | Test whether a bitvector expression is less than another for all
-- substitutions to the free variables. The comparison is unsigned. This is an
-- underapproximation, meaning that it could return 'False' in cases where it is
-- actually 'True'. The current algorithm returns 'False' when the right-hand
-- side is 0, 'True' for constant expressions @k1 < k2@, and 'False' otherwise.
bvLt :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvLt _ (PExpr_BV [] (BV.BV 0)) = False
bvLt e1 e2 | bvEq e1 e2 = False
bvLt (PExpr_BV [] k1) (PExpr_BV [] k2) = BV.ult k1 k2
bvLt _ _ = False

-- | Test whether a bitvector expression is less than another for all
-- substitutions to the free variables. The comparison is signed. This is an
-- underapproximation, meaning that it could return 'False' in cases where it is
-- actually 'True'. The current algorithm only returns 'True' for constant
-- expressions @k1 < k2@.
bvSLt :: (1 <= w, KnownNat w) =>
         PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvSLt (bvMatchConst -> Just i1) (bvMatchConst -> Just i2) =
  trace ("bvSLt " ++ show i1 ++ " " ++ show i2) (BV.slt knownNat i1 i2)
bvSLt _ _ = False

-- | Test whether a bitvector expression @e@ is in a 'BVRange' for all
-- substitutions to the free variables. This is an underapproximation, meaning
-- that it could return 'False' in cases where it is actually 'True'. It is
-- implemented by testing whether @e - off < len@ using the unsigned comparison
-- 'bvLt', where @off@ and @len@ are the offset and length of the 'BVRange'.
bvInRange :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> BVRange w -> Bool
bvInRange e (BVRange off len) = bvLt (bvSub e off) len

-- | Test whether a bitvector @e@ equals @0@
bvIsZero :: PermExpr (BVType w) -> Bool
bvIsZero (PExpr_Var _) = False
bvIsZero (PExpr_BV [] (BV.BV 0)) = True
bvIsZero (PExpr_BV _ _) = False

-- | Test whether a bitvector @e@ could equal @0@, i.e., whether the equation
-- @e=0@ has any solutions.
--
-- NOTE: this is an overapproximation, meaning that it may return 'True' for
-- complex expressions that technically cannot unify with @0@.
bvZeroable :: PermExpr (BVType w) -> Bool
bvZeroable (PExpr_Var _) = True
bvZeroable (PExpr_BV _ (BV.BV 0)) = True
bvZeroable (PExpr_BV [] _) = False
bvZeroable (PExpr_BV _ _) =
  -- NOTE: there are cases that match this pattern but are still not solvable,
  -- like 8*x + 3 = 0.
  True

-- | Test whether two bitvector expressions are potentially unifiable, i.e.,
-- whether some substitution to the variables could make them equal. This is an
-- overapproximation, meaning that some expressions are marked as "could" equal
-- when they actually cannot.
bvCouldEqual :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvCouldEqual e1@(PExpr_BV _ _) e2 =
  -- NOTE: we can only call bvSub when at least one side matches PExpr_BV
  bvZeroable (bvSub e1 e2)
bvCouldEqual e1 e2@(PExpr_BV _ _) = bvZeroable (bvSub e1 e2)
bvCouldEqual _ _ = True

-- | Test whether a bitvector expression could potentially be less than another,
-- for some substitution to the free variables. The comparison is unsigned. This
-- is an overapproximation, meaning that some expressions are marked as "could"
-- be less than when they actually cannot. The current algorithm returns 'False'
-- when the right-hand side is 0 and 'True' in all other cases except constant
-- expressions @k1 >= k2@.
bvCouldBeLt :: PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvCouldBeLt _ (PExpr_BV [] (BV.BV  0)) = False
bvCouldBeLt e1 e2 | bvEq e1 e2 = False
bvCouldBeLt (PExpr_BV [] (BV.BV k1)) (PExpr_BV [] (BV.BV k2)) = k1 < k2
bvCouldBeLt _ _ = True

-- | Test whether a bitvector expression could potentially be less than another,
-- for some substitution to the free variables. The comparison is signed. This
-- is an overapproximation, meaning that some expressions are marked as "could"
-- be less than when they actually cannot. The current algorithm returns 'True'
-- in all cases except constant expressions @k1 >= k2@.
bvCouldBeSLt :: (1 <= w, KnownNat w) =>
                PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvCouldBeSLt (bvMatchConst -> Just i1) (bvMatchConst -> Just i2) =
  BV.slt knownNat i1 i2
bvCouldBeSLt _ _ = True

-- | Test whether a bitvector expression is less than or equal to another for
-- all substitutions of the free variables. The comparison is unsigned. This is
-- an underapproximation, meaning that it could return 'False' in cases where it
-- is actually 'True'. The current algorithm simply tests if the second
-- epxression 'bvCouldBeLt' the first, and returns the negation of that result.
bvLeq :: (1 <= w, KnownNat w) =>
         PermExpr (BVType w) -> PermExpr (BVType w) -> Bool
bvLeq e1 e2 = not (bvCouldBeLt e2 e1)

-- | Test whether a bitvector expression @e@ is in a 'BVRange' for all
-- substitutions to the free variables. This is an overapproximation, meaning
-- that some expressions are marked as "could" be in the range when they
-- actually cannot. The current algorithm tests if @e - off < len@ using the
-- unsigned comparison 'bvCouldBeLt', where @off@ and @len@ are the offset and
-- length of the 'BVRange'.
bvCouldBeInRange :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> BVRange w -> Bool
bvCouldBeInRange e (BVRange off len) = bvCouldBeLt (bvSub e off) len

-- | Test whether a 'BVProp' holds for all substitutions of the free
-- variables. This is an underapproximation, meaning that some propositions are
-- marked as not holding when they actually do.
bvPropHolds :: (1 <= w, KnownNat w) => BVProp w -> Bool
bvPropHolds (BVProp_Eq e1 e2) = bvEq e1 e2
bvPropHolds (BVProp_Neq e1 e2) = not (bvCouldEqual e1 e2)
bvPropHolds (BVProp_ULt e1 e2) = bvLt e1 e2
bvPropHolds (BVProp_ULeq e1 e2) = bvLeq e1 e2
bvPropHolds (BVProp_ULeq_Diff e1 e2 e3) =
  not (bvCouldBeLt (bvSub e2 e3) e1)

-- | Test whether a 'BVProp' "could" hold for all substitutions of the free
-- variables. This is an overapproximation, meaning that some propositions are
-- marked as "could" hold when they actually cannot.
bvPropCouldHold :: (1 <= w, KnownNat w) => BVProp w -> Bool
bvPropCouldHold (BVProp_Eq e1 e2) = bvCouldEqual e1 e2
bvPropCouldHold (BVProp_Neq e1 e2) = not (bvEq e1 e2)
bvPropCouldHold (BVProp_ULt e1 e2) = bvCouldBeLt e1 e2
bvPropCouldHold (BVProp_ULeq e1 e2) = not (bvLt e2 e1)
bvPropCouldHold (BVProp_ULeq_Diff e1 e2 e3) = not (bvLt (bvSub e2 e3) e1)

-- | Negate a 'BVProp'
bvPropNegate :: BVProp w -> BVProp w
bvPropNegate (BVProp_Eq e1 e2) = BVProp_Neq e1 e2
bvPropNegate (BVProp_Neq e1 e2) = BVProp_Eq e1 e2
bvPropNegate (BVProp_ULt e1 e2) = BVProp_ULeq e2 e1
bvPropNegate (BVProp_ULeq e1 e2) = BVProp_ULt e2 e1
bvPropNegate (BVProp_ULeq_Diff e1 e2 e3) =
  BVProp_ULt (bvSub e2 e3) e1

-- | Build the proposition that @x@ is in the range @[off,off+len)@ as the
-- proposition
--
-- > x-off <u len
bvPropInRange :: (1 <= w, KnownNat w) =>
                 PermExpr (BVType w) -> BVRange w -> BVProp w
bvPropInRange e (BVRange off len) = BVProp_ULt (bvSub e off) len

-- | Build the proposition that @x@ is /not/ in the range @[off,off+len)@ as the
-- negation of 'bvPropInRange'
bvPropNotInRange :: (1 <= w, KnownNat w) =>
                    PermExpr (BVType w) -> BVRange w -> BVProp w
bvPropNotInRange e rng = bvPropNegate $ bvPropInRange e rng

-- | Build the proposition that @[off1,off1+len1)@ is a subset of
-- @[off2,off2+len2)@ as the following pair of propositions:
--
-- > off1 - off2 <=u len2
-- > len1 <=u len2 - (off1 - off2)
--
-- The first one states that the first @off1 - off2@ elements of the range
-- @[off2,off2+len2)@ can be removed to get the range
-- @[off1,off1+(len2-(off1-off2)))@. This also ensures that @len2-(off1- off2)@
-- does not underflow. The second then ensures that removing @off1-off2@
-- elements from the front of the second interval still yields a length that is
-- at least as long as @len1@.
--
-- NOTE: this is technically not complete, because the subset relation should
-- always hold when @len1=0@ while the first proposition above does not always
-- hold in this case, but we are ok with this. Equivalently, this approach views
-- @[off1,off1+len1)@ as always containing @off1@ even when @len1=0@.
--
-- NOTE: we cannot simplify the subtraction @len2 - (off1 - off2)@ because when
-- we translate to SAW core both @len2@ and @(off1 - off2)@ become different
-- arguments to @sliceBVVec@ and @updSliceBVVec@, and SAW core does not simplify
-- the subtraction of these two arguments.
bvPropRangeSubset :: (1 <= w, KnownNat w) =>
                     BVRange w -> BVRange w -> [BVProp w]
bvPropRangeSubset (BVRange off1 len1) (BVRange off2 len2) =
  [BVProp_ULeq (bvSub off1 off2) len2,
   BVProp_ULeq_Diff len1 len2 (bvSub off1 off2)]

-- | Test that one range is a subset of another, by testing that the
-- propositions returned by 'bvPropRangeSubset' all hold (in the sense of
-- 'bvPropHolds')
bvRangeSubset :: (1 <= w, KnownNat w) => BVRange w -> BVRange w -> Bool
bvRangeSubset rng1 rng2 = all bvPropHolds $ bvPropRangeSubset rng1 rng2

-- | Build the proposition that @[off1,off1+len1)@ and @[off2,off2+len2)@ are
-- disjoint as following pair of propositions:
--
-- > len2 <=u off1 - off2
-- > len1 <=u off2 - off1
--
-- These say that each @off@ is not in the other range.
bvPropRangesDisjoint :: (1 <= w, KnownNat w) =>
                        BVRange w -> BVRange w -> [BVProp w]
bvPropRangesDisjoint (BVRange off1 len1) (BVRange off2 len2) =
  [BVProp_ULeq len2 (bvSub off1 off2), BVProp_ULeq len1 (bvSub off2 off1)]

-- | Test if @[off1,off1+len1)@ and @[off2,off2+len2)@ overlap, i.e., share at
-- least one element, by testing that they could not satisfy (in the sense of
-- 'bvPropCouldHold') the results of 'bvPropRangesDisjoint'
bvRangesOverlap :: (1 <= w, KnownNat w) => BVRange w -> BVRange w -> Bool
bvRangesOverlap rng1 rng2 =
  not $ all bvPropCouldHold $ bvPropRangesDisjoint rng1 rng2

-- | Test if @[off1,off1+len1)@ and @[off2,off2+len2)@ could overlap, i.e.,
-- share at least one element, by testing that they do not definitely satisfy
-- (in the sense of 'bvPropHolds') the results of 'bvPropRangesDisjoint'
bvRangesCouldOverlap :: (1 <= w, KnownNat w) => BVRange w -> BVRange w -> Bool
bvRangesCouldOverlap rng1 rng2 =
  not $ all bvPropHolds $ bvPropRangesDisjoint rng1 rng2

-- | Get the ending offset of a range
bvRangeEnd :: (1 <= w, KnownNat w) => BVRange w -> PermExpr (BVType w)
bvRangeEnd (BVRange off len) = bvAdd off len

-- | Take the suffix of a range starting at a given offset, assuming that offset
-- is in the range
bvRangeSuffix :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> BVRange w ->
                 BVRange w
bvRangeSuffix off' (BVRange off len) =
  BVRange off' (bvSub len (bvSub off' off))

-- | Subtract a bitvector word from the offset of a 'BVRange'
bvRangeSub :: (1 <= w, KnownNat w) => BVRange w -> PermExpr (BVType w) ->
              BVRange w
bvRangeSub (BVRange off len) x = BVRange (bvSub off x) len

-- | Build a bitvector expression from an integer
bvInt :: (1 <= w, KnownNat w) => Integer -> PermExpr (BVType w)
bvInt i = PExpr_BV [] $ BV.mkBV knownNat i

-- | Build a bitvector expression of a given size from an integer
bvIntOfSize :: (1 <= sz, KnownNat sz) => prx sz -> Integer -> PermExpr (BVType sz)
bvIntOfSize _ = bvInt

-- | Build a bitvector expression from a Haskell bitvector
bvBV :: (1 <= w, KnownNat w) => BV w -> PermExpr (BVType w)
bvBV i = PExpr_BV [] i

-- | Add two bitvector expressions
bvAdd :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w) ->
         PermExpr (BVType w)
bvAdd (bvMatch -> (factors1, const1)) (bvMatch -> (factors2, const2)) =
  bvNormVar $
  PExpr_BV (bvMergeFactors factors1 factors2) (BV.add knownNat const1 const2)

-- | Multiply a bitvector expression by a bitvector
bvMultBV :: (1 <= w, KnownNat w) => BV.BV w -> PermExpr (BVType w) ->
            PermExpr (BVType w)
bvMultBV i_bv (bvMatch -> (factors, off)) =
  bvNormVar $
  PExpr_BV (map (\(BVFactor j x) ->
                  BVFactor (BV.mul knownNat i_bv j) x) factors)
  (BV.mul knownNat i_bv off)

-- | Multiply a bitvector expression by a constant
bvMult :: (1 <= w, KnownNat w, Integral a) => a -> PermExpr (BVType w) ->
          PermExpr (BVType w)
bvMult i = bvMultBV (BV.mkBV knownNat $ toInteger i)

-- | Negate a bitvector expression
bvNegate :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w)
bvNegate = bvMult (-1 :: Integer)

-- | Subtract one bitvector expression from another
--
-- FIXME: this would be more efficient if we did not use 'bvNegate', which could
-- make very large 'Integer's for negative numbers wrapped around to be positive
bvSub :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> PermExpr (BVType w) ->
         PermExpr (BVType w)
bvSub e1 e2 = bvAdd e1 (bvNegate e2)

-- | Integer division on bitvector expressions, truncating any factors @i*x@
-- where @i@ is not a multiple of the divisor to zero
bvDiv :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> Integer ->
         PermExpr (BVType w)
bvDiv (bvMatch -> (factors, off)) n =
  let n_bv = BV.mkBV knownNat n in
  bvNormVar $
  PExpr_BV (mapMaybe (\(BVFactor i x) ->
                       if BV.urem i n_bv == BV.zero knownNat then
                         Just (BVFactor (BV.uquot i n_bv) x)
                       else Nothing) factors)
  (BV.uquot off n_bv)

-- | Integer Modulus on bitvector expressions, where any factors @i*x@ with @i@
-- not a multiple of the divisor are included in the modulus
bvMod :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> Integer ->
         PermExpr (BVType w)
bvMod (bvMatch -> (factors, off)) n =
  let n_bv = BV.mkBV knownNat n in
  bvNormVar $
  PExpr_BV (mapMaybe (\f@(BVFactor i _) ->
                       if BV.urem i n_bv /= BV.zero knownNat
                       then Just f else Nothing) factors)
  (BV.urem off n_bv)

-- | Given a constant factor @a@, test if a bitvector expression can be written
-- as @a*x+y@ for some constant @y@
bvMatchFactorPlusConst :: (1 <= w, KnownNat w) =>
                          Integer -> PermExpr (BVType w) ->
                          Maybe (PermExpr (BVType w), BV w)
bvMatchFactorPlusConst a e =
  bvMatchConst (bvMod e a) >>= \y -> Just (bvDiv e a, y)

-- | Convert an LLVM pointer expression to a variable + optional offset, if this
-- is possible
asLLVMOffset :: (1 <= w, KnownNat w) => PermExpr (LLVMPointerType w) ->
                Maybe (ExprVar (LLVMPointerType w), PermExpr (BVType w))
asLLVMOffset (PExpr_Var x) = Just (x, bvInt 0)
asLLVMOffset (PExpr_LLVMOffset x off) = Just (x, off)
asLLVMOffset _ = Nothing

-- | Add a word expression to an LLVM pointer expression
addLLVMOffset :: (1 <= w, KnownNat w) =>
                 PermExpr (LLVMPointerType w) -> PermExpr (BVType w) ->
                 PermExpr (LLVMPointerType w)
addLLVMOffset (PExpr_Var x) off = PExpr_LLVMOffset x off
addLLVMOffset (PExpr_LLVMWord e) off = PExpr_LLVMWord $ bvAdd e off
addLLVMOffset (PExpr_LLVMOffset x e) off =
  PExpr_LLVMOffset x $ bvAdd e off

-- | Build a range that contains exactly one index
bvRangeOfIndex :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> BVRange w
bvRangeOfIndex e = BVRange e (bvInt 1)

-- | Add an offset to a 'BVRange'
offsetBVRange :: (1 <= w, KnownNat w) => PermExpr (BVType w) -> BVRange w ->
                 BVRange w
offsetBVRange off (BVRange off' len) = (BVRange (bvAdd off' off) len)


----------------------------------------------------------------------
-- * Permissions
----------------------------------------------------------------------

-- | The Haskell type of permission variables, that is, variables that range
-- over 'ValuePerm's
type PermVar (a :: CrucibleType) = Name (ValuePermType a)

-- | Ranges @[off,off+len)@ of bitvector values @x@ equal to @off+y@ for some
-- unsigned @y < len@. Note that ranges are allowed to wrap around 0, meaning
-- @off+y@ can overflow when testing whether @x@ is in the range. Thus, @x@ is
-- in range @[off,off+len)@ iff @x-off@ is unsigned less than @len@.
data BVRange w = BVRange { bvRangeOffset :: PermExpr (BVType w),
                           bvRangeLength :: PermExpr (BVType w) }
               deriving Eq

-- | Propositions about bitvectors
data BVProp w
    -- | True iff the two expressions are equal
  = BVProp_Eq (PermExpr (BVType w)) (PermExpr (BVType w))
    -- | True iff the two expressions are not equal
  | BVProp_Neq (PermExpr (BVType w)) (PermExpr (BVType w))
    -- | True iff the first expression is unsigned less-than the second
  | BVProp_ULt (PermExpr (BVType w)) (PermExpr (BVType w))
    -- | True iff the first expression is unsigned @<=@ the second
  | BVProp_ULeq (PermExpr (BVType w)) (PermExpr (BVType w))
    -- | True iff the first expression is unsigned @<=@ the difference of the
    -- second minus the third
  | (1 <= w, KnownNat w) =>
    BVProp_ULeq_Diff (PermExpr (BVType w)) (PermExpr (BVType w))
    (PermExpr (BVType w))

deriving instance Eq (BVProp w)

-- | An atomic permission is a value permission that is not one of the compound
-- constructs in the 'ValuePerm' type; i.e., not a disjunction, existential,
-- recursive, or equals permission. These are the permissions that we can put
-- together with separating conjuctions.
data AtomicPerm (a :: CrucibleType) where
  -- | Gives permissions to a single field pointed to by an LLVM pointer
  Perm_LLVMField :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                    LLVMFieldPerm w sz ->
                    AtomicPerm (LLVMPointerType w)

  -- | Gives permissions to an array pointer to by an LLVM pointer
  Perm_LLVMArray :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                    AtomicPerm (LLVMPointerType w)

  -- | Gives read or write access to a memory block, whose contents also give
  -- some permissions
  Perm_LLVMBlock :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                    AtomicPerm (LLVMPointerType w)

  -- | Says that we have permission to free the memory pointed at by this
  -- pointer if we have write permission to @e@ words of size @w@
  Perm_LLVMFree :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                   AtomicPerm (LLVMPointerType w)

  -- | Says that we known an LLVM value is a function pointer whose function has
  -- the given permissions
  Perm_LLVMFunPtr :: (1 <= w, KnownNat w) =>
                     TypeRepr (FunctionHandleType cargs ret) ->
                     ValuePerm (FunctionHandleType cargs ret) ->
                     AtomicPerm (LLVMPointerType w)

  -- | Says that a memory block has a given shape
  Perm_LLVMBlockShape :: (1 <= w, KnownNat w) => PermExpr (LLVMShapeType w) ->
                         AtomicPerm (LLVMBlockType w)

  -- | Says we know an LLVM value is a pointer value, meaning that its block
  -- value is non-zero. Note that this does not say the pointer is allocated.
  Perm_IsLLVMPtr :: (1 <= w, KnownNat w) =>
                    AtomicPerm (LLVMPointerType w)

  -- | A named conjunctive permission
  Perm_NamedConj :: NameSortIsConj ns ~ 'True =>
                    NamedPermName ns args a -> PermExprs args ->
                    PermOffset a -> AtomicPerm a

  -- | Permission to allocate (via @alloca@) on an LLVM stack frame, and
  -- permission to delete that stack frame if we have exclusive permissions to
  -- all the given LLVM pointer objects
  Perm_LLVMFrame :: (1 <= w, KnownNat w) => LLVMFramePerm w ->
                    AtomicPerm (LLVMFrameType w)

  -- | Ownership permission for a lifetime, including an assertion that it is
  -- still current and permission to end that lifetime. A lifetime also
  -- represents a permission "borrow" of some sub-permissions out of some larger
  -- permissions. For example, we might borrow a portion of an array, or a
  -- portion of a larger data structure. When the lifetime is ended, you have to
  -- give back to sub-permissions to get back the larger permissions. Together,
  -- these are a form of permission implication, so we write lifetime ownership
  -- permissions as @lowned(Pin -o Pout)@. Intuitively, @Pin@ must be given back
  -- before the lifetime is ended, and @Pout@ is returned afterwards.
  Perm_LOwned :: LOwnedPerms ps_in -> LOwnedPerms ps_out ->
                 AtomicPerm LifetimeType

  -- | Assertion that a lifetime is current during another lifetime
  Perm_LCurrent :: PermExpr LifetimeType -> AtomicPerm LifetimeType

  -- | A struct permission = a sequence of permissions for each field
  Perm_Struct :: RAssign ValuePerm (CtxToRList ctx) ->
                 AtomicPerm (StructType ctx)

  -- | A function permission
  Perm_Fun :: FunPerm ghosts (CtxToRList cargs) ret ->
              AtomicPerm (FunctionHandleType cargs ret)

  -- | An LLVM permission that asserts a proposition about bitvectors
  Perm_BVProp :: (1 <= w, KnownNat w) => BVProp w ->
                 AtomicPerm (LLVMPointerType w)


-- | A value permission is a permission to do something with a value, such as
-- use it as a pointer. This also includes a limited set of predicates on values
-- (you can think about this as "permission to assume the value satisfies this
-- predicate" if you like).
data ValuePerm (a :: CrucibleType) where

  -- | Says that a value is equal to a known static expression
  ValPerm_Eq :: PermExpr a -> ValuePerm a

  -- | The disjunction of two value permissions
  ValPerm_Or :: ValuePerm a -> ValuePerm a -> ValuePerm a

  -- | An existential binding of a value in a value permission
  --
  -- FIXME: turn the 'KnownRepr' constraint into a normal 'TypeRepr' argument
  ValPerm_Exists :: KnownRepr TypeRepr a =>
                    Binding a (ValuePerm b) ->
                    ValuePerm b

  -- | A named permission
  ValPerm_Named :: NamedPermName ns args a -> PermExprs args ->
                   PermOffset a -> ValuePerm a

  -- | A permission variable plus an offset
  ValPerm_Var :: PermVar a -> PermOffset a -> ValuePerm a

  -- | A separating conjuction of 0 or more atomic permissions, where 0
  -- permissions is the trivially true permission
  ValPerm_Conj :: [AtomicPerm a] -> ValuePerm a


-- | The vacuously true permission is the conjunction of 0 atomic permissions
pattern ValPerm_True :: ValuePerm a
pattern ValPerm_True = ValPerm_Conj []

-- | The conjunction of exactly 1 atomic permission
pattern ValPerm_Conj1 :: AtomicPerm a -> ValuePerm a
pattern ValPerm_Conj1 p = ValPerm_Conj [p]

-- | The conjunction of exactly 1 field permission
pattern ValPerm_LLVMField :: () => (a ~ LLVMPointerType w, 1 <= w, KnownNat w,
                                    1 <= sz, KnownNat sz) =>
                             LLVMFieldPerm w sz -> ValuePerm a
pattern ValPerm_LLVMField fp <- ValPerm_Conj [Perm_LLVMField fp]
  where
    ValPerm_LLVMField fp = ValPerm_Conj [Perm_LLVMField fp]

-- | The conjunction of exactly 1 array permission
pattern ValPerm_LLVMArray :: () => (a ~ LLVMPointerType w, 1 <= w, KnownNat w) =>
                             LLVMArrayPerm w -> ValuePerm a
pattern ValPerm_LLVMArray ap <- ValPerm_Conj [Perm_LLVMArray ap]
  where
    ValPerm_LLVMArray ap = ValPerm_Conj [Perm_LLVMArray ap]

-- | The conjunction of exactly 1 block permission
pattern ValPerm_LLVMBlock :: () => (a ~ LLVMPointerType w, 1 <= w, KnownNat w) =>
                             LLVMBlockPerm w -> ValuePerm a
pattern ValPerm_LLVMBlock bp <- ValPerm_Conj [Perm_LLVMBlock bp]
  where
    ValPerm_LLVMBlock bp = ValPerm_Conj [Perm_LLVMBlock bp]

-- | The conjunction of exactly 1 block shape permission
pattern ValPerm_LLVMBlockShape :: () => (a ~ LLVMBlockType w, b ~ LLVMShapeType w,
                                         1 <= w, KnownNat w) =>
                                  PermExpr b -> ValuePerm a
pattern ValPerm_LLVMBlockShape sh <- ValPerm_Conj [Perm_LLVMBlockShape sh]
  where
    ValPerm_LLVMBlockShape sh = ValPerm_Conj [Perm_LLVMBlockShape sh]

-- | A single @lowned@ permission
pattern ValPerm_LOwned :: () => (a ~ LifetimeType) =>
                          LOwnedPerms ps_in -> LOwnedPerms ps_out -> ValuePerm a
pattern ValPerm_LOwned ps_in ps_out <- ValPerm_Conj [Perm_LOwned ps_in ps_out]
  where
    ValPerm_LOwned ps_in ps_out = ValPerm_Conj [Perm_LOwned ps_in ps_out]

-- | A single @lcurrent@ permission
pattern ValPerm_LCurrent :: () => (a ~ LifetimeType) =>
                            PermExpr LifetimeType -> ValuePerm a
pattern ValPerm_LCurrent l <- ValPerm_Conj [Perm_LCurrent l]
  where
    ValPerm_LCurrent l = ValPerm_Conj [Perm_LCurrent l]

-- | A sequence of value permissions
{-
data ValuePerms as where
  ValPerms_Nil :: ValuePerms RNil
  ValPerms_Cons :: ValuePerms as -> ValuePerm a -> ValuePerms (as :> a)
-}

type ValuePerms = RAssign ValuePerm

pattern ValPerms_Nil :: () => (tps ~ RNil) => ValuePerms tps
pattern ValPerms_Nil = MNil

pattern ValPerms_Cons :: () => (tps ~ (tps' :> a)) =>
                         ValuePerms tps' -> ValuePerm a -> ValuePerms tps
pattern ValPerms_Cons ps p = ps :>: p

{-# COMPLETE ValPerms_Nil, ValPerms_Cons #-}


-- | Fold a function over a 'ValuePerms' list, where
--
-- > foldValuePerms f b ('ValuePermsCons'
-- >                     ('ValuePermsCons' (... 'ValuePermsNil' ...) p2) p1) =
-- > f (f (... b ...) p2) p1
--
-- FIXME: implement more functions on ValuePerms in terms of this
foldValuePerms :: (forall a. b -> ValuePerm a -> b) -> b -> ValuePerms as -> b
foldValuePerms _ b ValPerms_Nil = b
foldValuePerms f b (ValPerms_Cons ps p) = f (foldValuePerms f b ps) p

-- | Build a one-element 'ValuePerms' list from a single permission
singletonValuePerms :: ValuePerm a -> ValuePerms (RNil :> a)
singletonValuePerms = ValPerms_Cons ValPerms_Nil

-- | Build a 'ValuePerms' from an 'RAssign' of permissions
assignToPerms :: RAssign ValuePerm ps -> ValuePerms ps
assignToPerms MNil = ValPerms_Nil
assignToPerms (ps :>: p) = ValPerms_Cons (assignToPerms ps) p

-- | A binding of 0 or more variables, each with permissions
type MbValuePerms ctx = Mb ctx (ValuePerms ctx)

-- | A frame permission is a list of the pointers that have been allocated in
-- the frame and their corresponding allocation sizes in words of size
-- @w@. Write permissions of the given sizes are required to these pointers in
-- order to delete the frame.
type LLVMFramePerm w = [(PermExpr (LLVMPointerType w), Integer)]

-- | An LLVM pointer permission is an 'AtomicPerm' of type 'LLVMPointerType'
type LLVMPtrPerm w = AtomicPerm (LLVMPointerType w)

-- | A permission for a pointer to a specific field of a given size
data LLVMFieldPerm w sz =
  LLVMFieldPerm { llvmFieldRW :: PermExpr RWModalityType,
                  -- ^ Whether this is a read or write permission
                  llvmFieldLifetime :: PermExpr LifetimeType,
                  -- ^ The lifetime during with this field permission is active
                  llvmFieldOffset :: PermExpr (BVType w),
                  -- ^ The offset from the pointer in bytes of this field
                  llvmFieldContents :: ValuePerm (LLVMPointerType sz)
                  -- ^ The permissions we get for the value read from this field
                }
  deriving Eq

-- | Helper to get a 'NatRepr' for the size of an 'LLVMFieldPerm'
llvmFieldSize :: KnownNat sz => LLVMFieldPerm w sz -> NatRepr sz
llvmFieldSize _ = knownNat

-- | Helper type to represent byte offsets
--
-- > 'machineWordBytes' * (stride * ix + fld_num)
--
-- from the beginning of an array permission. Such an expression refers to the
-- array field @fld_num@, which must be a statically-known constant, in array
-- cell @ix@.
data LLVMArrayIndex w =
  LLVMArrayIndex { llvmArrayIndexCell :: PermExpr (BVType w),
                   llvmArrayIndexFieldNum :: Int }

-- NOTE: we need a custom instance of Eq so we can use bvEq on the cell
instance Eq (LLVMArrayIndex w) where
  LLVMArrayIndex e1 i1 == LLVMArrayIndex e2 i2 =
    bvEq e1 e2 && i1 == i2

-- | A single field in an array permission
data LLVMArrayField w =
  forall sz. (1 <= sz, KnownNat sz) => LLVMArrayField (LLVMFieldPerm w sz)

instance Eq (LLVMArrayField w) where
  (LLVMArrayField fp1) == (LLVMArrayField fp2)
    | Just Refl <- testEquality (llvmFieldSize fp1) (llvmFieldSize fp2) =
      fp1 == fp2
  _ == _ = False

-- | Extract the offset from the field permission in an 'LLVMArrayField'
llvmArrayFieldOffset :: LLVMArrayField w -> PermExpr (BVType w)
llvmArrayFieldOffset (LLVMArrayField fp) = llvmFieldOffset fp

-- | Convert an 'LLVMArrayField' to an atomic permission
llvmArrayFieldToAtomicPerm :: (1 <= w, KnownNat w) => LLVMArrayField w ->
                              AtomicPerm (LLVMPointerType w)
llvmArrayFieldToAtomicPerm (LLVMArrayField fp) = Perm_LLVMField fp

-- | Get the length in bytes of an array field
llvmArrayFieldLen :: LLVMArrayField w -> Integer
llvmArrayFieldLen (LLVMArrayField fp) = intValue $ llvmFieldSize fp

-- | A permission to an array of repeated field permissions. An array permission
-- is structured as zero or more cells, each of which are composed of one or
-- more individual fields. The number of cells can be a dynamic expression, but
-- the size in memory of each cell, called the /stride/ of the array, must be
-- statically known and no less than the total size of the fields
data LLVMArrayPerm w =
  LLVMArrayPerm { llvmArrayOffset :: PermExpr (BVType w),
                  -- ^ The offset from the pointer in bytes of this array
                  llvmArrayLen :: PermExpr (BVType w),
                  -- ^ The number of array blocks
                  llvmArrayStride :: Bytes,
                  -- ^ The array stride in bytes
                  llvmArrayFields :: [LLVMArrayField w],
                  -- ^ The fields in each element of this array; should have
                  -- length <= the stride
                  llvmArrayBorrows :: [LLVMArrayBorrow w]
                  -- ^ Indices or index ranges that are missing from this array
                }
  deriving Eq

-- | Get the stride of an array in bits
llvmArrayStrideBits :: LLVMArrayPerm w -> Integer
llvmArrayStrideBits = toInteger . bytesToBits . llvmArrayStride

-- | An index or range of indices that are missing from an array perm
--
-- FIXME: think about calling the just @LLVMArrayIndexSet@
data LLVMArrayBorrow w
  = FieldBorrow (LLVMArrayIndex w)
    -- ^ Borrow a specific field in a specific cell of an array permission
  | RangeBorrow (BVRange w)
    -- ^ Borrow a range of array cells, where each cell is 'llvmArrayStride'
    -- machine words long
  deriving Eq


-- | An LLVM block permission is read or write access to the memory at a given
-- offset with a given length with a given shape
data LLVMBlockPerm w =
  LLVMBlockPerm { llvmBlockRW :: PermExpr RWModalityType,
                  -- ^ Whether this is a read or write block permission
                  llvmBlockLifetime :: PermExpr LifetimeType,
                  -- ^ The lifetime during with this block permission is active
                  llvmBlockOffset :: PermExpr (BVType w),
                  -- ^ The offset of the block from the pointer in bytes
                  llvmBlockLen :: PermExpr (BVType w),
                  -- ^ The length of the block in bytes
                  llvmBlockShape :: PermExpr (LLVMShapeType w)
                  -- ^ The shape of the permissions in the block
                }
  deriving Eq

-- | Convenience function for building a single llvmblock permission
mkLLVMBlockPerm :: (1 <= w, KnownNat w) =>
                   PermExpr RWModalityType -> PermExpr LifetimeType ->
                   PermExpr (BVType w) -> PermExpr (BVType w) ->
                   PermExpr (LLVMShapeType w) -> ValuePerm (LLVMPointerType w)
mkLLVMBlockPerm rw l off len sh =
  ValPerm_Conj1 $ Perm_LLVMBlock $ LLVMBlockPerm rw l off len sh

-- | An LLVM shape for a single pointer field of unknown size
data LLVMFieldShape w =
  forall sz. (1 <= sz, KnownNat sz) =>
  LLVMFieldShape (ValuePerm (LLVMPointerType sz))

instance Eq (LLVMFieldShape w) where
  (LLVMFieldShape p1) == (LLVMFieldShape p2)
    | Just Refl <- testEquality (exprType p1) (exprType p2) = p1 == p2
  _ == _ = False


-- | A form of permission used in lifetime ownership permissions
data LOwnedPerm a where
  LOwnedPermField :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                     PermExpr (LLVMPointerType w) -> LLVMFieldPerm w sz ->
                     LOwnedPerm (LLVMPointerType w)
  LOwnedPermBlock :: (1 <= w, KnownNat w) => PermExpr (LLVMPointerType w) ->
                     LLVMBlockPerm w -> LOwnedPerm (LLVMPointerType w)
  LOwnedPermLifetime :: PermExpr LifetimeType ->
                        LOwnedPerms ps_in -> LOwnedPerms ps_out ->
                        LOwnedPerm LifetimeType

-- | A sequence of 'LOwnedPerm's
type LOwnedPerms = RAssign LOwnedPerm

instance TestEquality LOwnedPerm where
  testEquality (LOwnedPermField e1 fp1) (LOwnedPermField e2 fp2)
    | Just Refl <- testEquality (exprType e1) (exprType e2)
    , Just Refl <- testEquality (llvmFieldSize fp1) (llvmFieldSize fp2)
    , e1 == e2 && fp1 == fp2
    = Just Refl
  testEquality (LOwnedPermField _ _) _ = Nothing
  testEquality (LOwnedPermBlock e1 bp1) (LOwnedPermBlock e2 bp2)
    | Just Refl <- testEquality (exprType e1) (exprType e2)
    , e1 == e2 && bp1 == bp2
    = Just Refl
  testEquality (LOwnedPermBlock _ _) _ = Nothing
  testEquality (LOwnedPermLifetime e1 ps_in1 ps_out1)
    (LOwnedPermLifetime e2 ps_in2 ps_out2)
    | Just Refl <- testEquality ps_in1 ps_in2
    , Just Refl <- testEquality ps_out1 ps_out2
    , e1 == e2
    = Just Refl
  testEquality (LOwnedPermLifetime _ _ _) _ = Nothing

instance Eq (LOwnedPerm a) where
  lop1 == lop2 | Just Refl <- testEquality lop1 lop2 = True
  _ == _ = False

instance Eq1 LOwnedPerm where
  eq1 = (==)

-- | Convert an 'LOwnedPerm' to the expression plus permission it represents
lownedPermExprAndPerm :: LOwnedPerm a -> ExprAndPerm a
lownedPermExprAndPerm (LOwnedPermField e fp) =
  ExprAndPerm e $ ValPerm_LLVMField fp
lownedPermExprAndPerm (LOwnedPermBlock e bp) =
  ExprAndPerm e $ ValPerm_LLVMBlock bp
lownedPermExprAndPerm (LOwnedPermLifetime e ps_in ps_out) =
  ExprAndPerm e $ ValPerm_LOwned ps_in ps_out

-- | Convert an 'LOwnedPerm' to a variable plus permission, if possible
lownedPermVarAndPerm :: LOwnedPerm a -> Maybe (VarAndPerm a)
lownedPermVarAndPerm lop
  | ExprAndPerm (PExpr_Var x) p <- lownedPermExprAndPerm lop =
    Just $ VarAndPerm x p
lownedPermVarAndPerm _ = Nothing

-- | Convert an expression plus permission to an 'LOwnedPerm', if possible
varAndPermLOwnedPerm :: VarAndPerm a -> Maybe (LOwnedPerm a)
varAndPermLOwnedPerm (VarAndPerm x (ValPerm_LLVMField fp)) =
  Just $ LOwnedPermField (PExpr_Var x) fp
varAndPermLOwnedPerm (VarAndPerm x (ValPerm_LLVMBlock bp)) =
  Just $ LOwnedPermBlock (PExpr_Var x) bp
varAndPermLOwnedPerm (VarAndPerm x (ValPerm_LOwned ps_in ps_out)) =
  Just $ LOwnedPermLifetime (PExpr_Var x) ps_in ps_out
varAndPermLOwnedPerm _ = Nothing

-- | Get the expression part of an 'LOwnedPerm'
lownedPermExpr :: LOwnedPerm a -> PermExpr a
lownedPermExpr = exprAndPermExpr . lownedPermExprAndPerm

-- | Convert the expression part of an 'LOwnedPerm' to a variable, if possible
lownedPermVar :: LOwnedPerm a -> Maybe (ExprVar a)
lownedPermVar lop | PExpr_Var x <- lownedPermExpr lop = Just x
lownedPermVar _ = Nothing

-- | Get the permission part of an 'LOwnedPerm'
lownedPermPerm :: LOwnedPerm a -> ValuePerm a
lownedPermPerm = exprAndPermPerm . lownedPermExprAndPerm


-- | A function permission is a set of input and output permissions inside a
-- context of ghost variables
data FunPerm ghosts args ret where
  FunPerm :: CruCtx ghosts -> CruCtx args -> TypeRepr ret ->
             MbValuePerms (ghosts :++: args) ->
             MbValuePerms (ghosts :++: args :> ret) ->
             FunPerm ghosts args ret

-- | Extract the @args@ context from a function permission
funPermArgs :: FunPerm ghosts args ret -> CruCtx args
funPermArgs (FunPerm _ args _ _ _) = args

-- | Extract the @ghosts@ context from a function permission
funPermGhosts :: FunPerm ghosts args ret -> CruCtx ghosts
funPermGhosts (FunPerm ghosts _ _ _ _) = ghosts

-- | Extract the @ghosts@ and @args@ contexts from a function permission
funPermTops :: FunPerm ghosts args ret -> CruCtx (ghosts :++: args)
funPermTops fun_perm =
  appendCruCtx (funPermGhosts fun_perm) (funPermArgs fun_perm)

-- | Extract the return type from a function permission
funPermRet :: FunPerm ghosts args ret -> TypeRepr ret
funPermRet (FunPerm _ _ ret _ _) = ret

-- | Extract the input permissions of a function permission
funPermIns :: FunPerm ghosts args ret -> MbValuePerms (ghosts :++: args)
funPermIns (FunPerm _ _ _ perms_in _) = perms_in

-- | Extract the output permissions of a function permission
funPermOuts :: FunPerm ghosts args ret ->
               MbValuePerms (ghosts :++: args :> ret)
funPermOuts (FunPerm _ _ _ _ perms_out) = perms_out


-- | A function permission that existentially quantifies the @ghosts@ types
data SomeFunPerm args ret where
  SomeFunPerm :: FunPerm ghosts args ret -> SomeFunPerm args ret


-- | The different sorts of name, each of which comes with a 'Bool' flag
-- indicating whether the name can be used as an atomic permission. A recursive
-- sort also comes with a second flag indicating whether it is a reachability
-- permission.
data NameSort = DefinedSort Bool | OpaqueSort Bool | RecursiveSort Bool Bool

type DefinedSort   = 'DefinedSort
type OpaqueSort    = 'OpaqueSort
type RecursiveSort = 'RecursiveSort

-- | Test whether a name of a given 'NameSort' is conjoinable
type family NameSortIsConj (ns::NameSort) :: Bool where
  NameSortIsConj (DefinedSort b) = b
  NameSortIsConj (OpaqueSort b) = b
  NameSortIsConj (RecursiveSort b _) = b

-- | Test whether a name of a given 'NameSort' can be folded / unfolded
type family NameSortCanFold (ns::NameSort) :: Bool where
  NameSortCanFold (DefinedSort _) = 'True
  NameSortCanFold (OpaqueSort _) = 'False
  NameSortCanFold (RecursiveSort b _) = 'True

-- | Test whether a name of a given 'NameSort' is a reachability permission
type family IsReachabilityName (ns::NameSort) :: Bool where
  IsReachabilityName (DefinedSort _) = 'False
  IsReachabilityName (OpaqueSort _) = 'False
  IsReachabilityName (RecursiveSort _ reach) = reach

-- | A singleton representation of 'NameSort'
data NameSortRepr (ns::NameSort) where
  DefinedSortRepr :: BoolRepr b -> NameSortRepr (DefinedSort b)
  OpaqueSortRepr :: BoolRepr b -> NameSortRepr (OpaqueSort b)
  RecursiveSortRepr :: BoolRepr b -> BoolRepr reach ->
                       NameSortRepr (RecursiveSort b reach)

-- | Get a 'BoolRepr' for whether a name sort is conjunctive
nameSortIsConjRepr :: NameSortRepr ns -> BoolRepr (NameSortIsConj ns)
nameSortIsConjRepr (DefinedSortRepr b) = b
nameSortIsConjRepr (OpaqueSortRepr b) = b
nameSortIsConjRepr (RecursiveSortRepr b _) = b

-- | Get a 'BoolRepr' for whether a 'NamedPermName' is conjunctive
nameIsConjRepr :: NamedPermName ns args a -> BoolRepr (NameSortIsConj ns)
nameIsConjRepr = nameSortIsConjRepr . namedPermNameSort

-- | Get a 'BoolRepr' for whether a name sort allows folds / unfolds
nameSortCanFoldRepr :: NameSortRepr ns -> BoolRepr (NameSortCanFold ns)
nameSortCanFoldRepr (DefinedSortRepr _) = TrueRepr
nameSortCanFoldRepr (OpaqueSortRepr _) = FalseRepr
nameSortCanFoldRepr (RecursiveSortRepr _ _) = TrueRepr

-- | Get a 'BoolRepr' for whether a 'NamedPermName' allows folds / unfolds
nameCanFoldRepr :: NamedPermName ns args a -> BoolRepr (NameSortCanFold ns)
nameCanFoldRepr = nameSortCanFoldRepr . namedPermNameSort

-- | Extract to Boolean value out of a 'BoolRepr'
--
-- FIXME: this should probably go in @BoolRepr.hs@
boolVal :: BoolRepr b -> Bool
boolVal TrueRepr = True
boolVal FalseRepr = False

-- | Test whether a name of a given sort can be used as an atomic permission
nameSortIsConj :: NameSortRepr ns -> Bool
nameSortIsConj = boolVal . nameSortIsConjRepr

-- | Get a 'Bool' for whether a 'NamedPermName' allows folds / unfolds
nameCanFold :: NamedPermName ns args a -> Bool
nameCanFold = boolVal . nameCanFoldRepr

instance TestEquality NameSortRepr where
  testEquality (DefinedSortRepr b1) (DefinedSortRepr b2)
    | Just Refl <- testEquality b1 b2 = Just Refl
  testEquality (DefinedSortRepr _) _ = Nothing
  testEquality (OpaqueSortRepr b1) (OpaqueSortRepr b2)
    | Just Refl <- testEquality b1 b2 = Just Refl
  testEquality (OpaqueSortRepr _) _ = Nothing
  testEquality (RecursiveSortRepr b1 reach1) (RecursiveSortRepr b2 reach2)
    | Just Refl <- testEquality b1 b2
    , Just Refl <- testEquality reach1 reach2
    = Just Refl
  testEquality (RecursiveSortRepr _ _) _ = Nothing

-- | A constraint that the last argument of a reachability permission is a
-- permission argument
data NameReachConstr ns args a where
  NameReachConstr :: (IsReachabilityName ns ~ 'True) =>
                     NameReachConstr ns (args :> a) a
  NameNonReachConstr :: (IsReachabilityName ns ~ 'False) =>
                        NameReachConstr ns args a

-- | Extract a 'BoolRepr' from a 'NameReachConstr' for whether the name it
-- constrains is a reachability name
nameReachConstrBool :: NameReachConstr ns args a ->
                       BoolRepr (IsReachabilityName ns)
nameReachConstrBool NameReachConstr = TrueRepr
nameReachConstrBool NameNonReachConstr = FalseRepr

-- | A name for a named permission
data NamedPermName ns args a = NamedPermName {
  namedPermNameName :: String,
  namedPermNameType :: TypeRepr a,
  namedPermNameArgs :: CruCtx args,
  namedPermNameSort :: NameSortRepr ns,
  namedPermNameReachConstr :: NameReachConstr ns args a
  }

-- FIXME: NamedPermNames should maybe say something about which arguments are
-- covariant? Right now we assume lifetime and rwmodalities are covariant
-- w.r.t. their respective orders, and everything else is invariant, but that
-- could potentially change

-- | Test if two 'NamedPermName's of possibly different types are equal
testNamedPermNameEq :: NamedPermName ns1 args1 a1 ->
                       NamedPermName ns2 args2 a2 ->
                       Maybe (ns1 :~: ns2, args1 :~: args2, a1 :~: a2)
testNamedPermNameEq (NamedPermName str1 tp1 ctx1 ns1 _r1)
                    (NamedPermName str2 tp2 ctx2 ns2 _r2)
  | Just Refl <- testEquality tp1 tp2
  , Just Refl <- testEquality ctx1 ctx2
  , Just Refl <- testEquality ns1 ns2
  , str1 == str2 = Just (Refl, Refl, Refl)
testNamedPermNameEq _ _ = Nothing

instance Eq (NamedPermName ns args a) where
  n1 == n2 | Just (Refl, Refl, Refl) <- testNamedPermNameEq n1 n2 = True
  _ == _ = False

-- | An existentially quantified 'NamedPermName'
data SomeNamedPermName where
  SomeNamedPermName :: NamedPermName ns args a -> SomeNamedPermName

instance Eq SomeNamedPermName where
  (SomeNamedPermName n1) == (SomeNamedPermName n2)
    | Just (Refl, Refl, Refl) <- testNamedPermNameEq n1 n2 = True
  _ == _ = False

-- | An existentially quantified conjunctive 'NamedPermName'
data SomeNamedConjPermName where
  SomeNamedConjPermName ::
    NameSortIsConj ns ~ 'True => NamedPermName ns args a ->
    SomeNamedConjPermName

-- | A named LLVM shape is a name, a list of arguments, and a body, where the
-- Boolean flag @b@ determines whether the shape can be unfolded or not
data NamedShape b args w = NamedShape {
  namedShapeName :: String,
  namedShapeArgs :: CruCtx args,
  namedShapeBody :: NamedShapeBody b args w
  }

-- | Test if two 'NamedShapes' of possibly different @b@ and @args@ arguments
-- are equal
namedShapeEq :: NamedShape b1 args1 w -> NamedShape b2 args2 w ->
                Maybe (b1 :~: b2, args1 :~: args2)
namedShapeEq nmsh1 nmsh2
  | Just Refl <- testEquality (namedShapeArgs nmsh1) (namedShapeArgs nmsh2)
  , b1 <- namedShapeCanUnfoldRepr nmsh1
  , b2 <- namedShapeCanUnfoldRepr nmsh2
  , Just Refl <- testEquality b1 b2
  , namedShapeName nmsh1 == namedShapeName nmsh2
  , namedShapeBody nmsh1 == namedShapeBody nmsh2 =
    Just (Refl,Refl)
namedShapeEq _ _ = Nothing

data NamedShapeBody b args w where
  -- | A defined shape is just a definition in terms of the arguments
  DefinedShapeBody :: Mb args (PermExpr (LLVMShapeType w)) ->
                      NamedShapeBody 'True args w

  -- | An opaque shape has no body, just a length and a translation to a type
  OpaqueShapeBody :: Mb args (PermExpr (BVType w)) -> Ident ->
                     NamedShapeBody 'False args w

  -- | A recursive shape body has a one-step unfolding to a shape, which can
  -- refer to the shape itself via the last bound variable; it also has
  -- identifiers for the type it is translated to, along with fold and unfold
  -- functions for mapping to and from this type
  RecShapeBody :: Mb (args :> LLVMShapeType w) (PermExpr (LLVMShapeType w)) ->
                  Ident -> Ident -> Ident ->
                  NamedShapeBody 'True args w

deriving instance Eq (NamedShapeBody b args w)

-- | Test if a 'NamedShape' is recursive
namedShapeIsRecursive :: NamedShape b args w -> Bool
namedShapeIsRecursive (NamedShape _ _ (RecShapeBody _ _ _ _)) = True
namedShapeIsRecursive _ = False

-- | Get a 'BoolRepr' for the Boolean flag for whether a named shape can be
-- unfolded
namedShapeCanUnfoldRepr :: NamedShape b args w -> BoolRepr b
namedShapeCanUnfoldRepr (NamedShape _ _ (DefinedShapeBody _)) = TrueRepr
namedShapeCanUnfoldRepr (NamedShape _ _ (OpaqueShapeBody _ _)) = FalseRepr
namedShapeCanUnfoldRepr (NamedShape _ _ (RecShapeBody _ _ _ _)) = TrueRepr

-- | Whether a 'NamedShape' can be unfolded
namedShapeCanUnfold :: NamedShape b args w -> Bool
namedShapeCanUnfold = boolVal . namedShapeCanUnfoldRepr

-- | An offset that is added to a permission. Only makes sense for llvm
-- permissions (at least for now...?)
data PermOffset a where
  NoPermOffset :: PermOffset a
  -- | NOTE: the invariant is that the bitvector offset is non-zero
  LLVMPermOffset :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                    PermOffset (LLVMPointerType w)

instance Eq (PermOffset a) where
  NoPermOffset == NoPermOffset = True
  (LLVMPermOffset e1) == (LLVMPermOffset e2) = e1 == e2
  _ == _ = False

-- | Smart constructor for 'LLVMPermOffset', that maps a 0 to 'NoPermOffset'
mkLLVMPermOffset :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                    PermOffset (LLVMPointerType w)
mkLLVMPermOffset off | bvIsZero off = NoPermOffset
mkLLVMPermOffset off = LLVMPermOffset off

-- | Test two 'PermOffset's for semantic, not just syntactic, equality
offsetsEq :: PermOffset a -> PermOffset a -> Bool
offsetsEq NoPermOffset NoPermOffset = True
offsetsEq (LLVMPermOffset off) NoPermOffset = bvIsZero off
offsetsEq NoPermOffset (LLVMPermOffset off) = bvIsZero off
offsetsEq (LLVMPermOffset off1) (LLVMPermOffset off2) = bvEq off1 off2

-- | Add a 'PermOffset' to an expression
offsetExpr :: PermOffset a -> PermExpr a -> PermExpr a
offsetExpr NoPermOffset e = e
offsetExpr (LLVMPermOffset off) e = addLLVMOffset e off

-- | Convert an expression to a variable + optional offset, if this is possible
asVarOffset :: PermExpr a -> Maybe (ExprVar a, PermOffset a)
asVarOffset (PExpr_Var x) = Just (x, NoPermOffset)
asVarOffset (PExpr_LLVMOffset x off) = Just (x, LLVMPermOffset off)
asVarOffset _ = Nothing

-- | Negate a 'PermOffset'
negatePermOffset :: PermOffset a -> PermOffset a
negatePermOffset NoPermOffset = NoPermOffset
negatePermOffset (LLVMPermOffset off) = LLVMPermOffset $ bvNegate off

-- | Add two 'PermOffset's
addPermOffsets :: PermOffset a -> PermOffset a -> PermOffset a
addPermOffsets NoPermOffset off = off
addPermOffsets off NoPermOffset = off
addPermOffsets (LLVMPermOffset off1) (LLVMPermOffset off2) =
  mkLLVMPermOffset (bvAdd off1 off2)

-- | Get the @n@th expression in a 'PermExprs' list
nthPermExpr :: PermExprs args -> Member args a -> PermExpr a
nthPermExpr (PExprs_Cons _ arg) Member_Base = arg
nthPermExpr (PExprs_Cons args _) (Member_Step memb) =
  nthPermExpr args memb

-- | Set the @n@th expression in a 'PermExprs' list
setNthPermExpr :: PermExprs args -> Member args a -> PermExpr a ->
                  PermExprs args
setNthPermExpr (PExprs_Cons args _) Member_Base a =
  PExprs_Cons args a
setNthPermExpr (PExprs_Cons args arg) (Member_Step memb) a =
  PExprs_Cons (setNthPermExpr args memb a) arg

-- | Get a list of 'Member' proofs for each expression in a 'PermExprs' list
getPermExprsMembers :: PermExprs args ->
                       [Some (Member args :: CrucibleType -> Type)]
getPermExprsMembers PExprs_Nil = []
getPermExprsMembers (PExprs_Cons args _) =
  map (\case Some memb -> Some (Member_Step memb)) (getPermExprsMembers args)
  ++ [Some Member_Base]

-- | The semantics of a named permission, which can can either be an opaque
-- named permission, a recursive named permission, a defined permission, or an
-- LLVM shape
data NamedPerm ns args a where
  NamedPerm_Opaque :: OpaquePerm b args a -> NamedPerm (OpaqueSort b) args a
  NamedPerm_Rec :: RecPerm b reach args a ->
                   NamedPerm (RecursiveSort b reach) args a
  NamedPerm_Defined :: DefinedPerm b args a -> NamedPerm (DefinedSort b) args a

-- | Extract the name back out of the interpretation of a 'NamedPerm'
namedPermName :: NamedPerm ns args a -> NamedPermName ns args a
namedPermName (NamedPerm_Opaque op) = opaquePermName op
namedPermName (NamedPerm_Rec rp) = recPermName rp
namedPermName (NamedPerm_Defined dp) = definedPermName dp

-- | Extract out the argument context of the name of a 'NamedPerm'
namedPermArgs :: NamedPerm ns args a -> CruCtx args
namedPermArgs = namedPermNameArgs . namedPermName

-- | An opaque named permission is just a name and a SAW core type given by
-- identifier that it is translated to
data OpaquePerm b args a = OpaquePerm {
  opaquePermName :: NamedPermName (OpaqueSort b) args a,
  opaquePermTrans :: Ident
  }

-- | The interpretation of a recursive permission as a reachability permission.
-- Reachability permissions are recursive permissions of the form
--
-- > reach<args,x> = eq(x)  |  p
--
-- where @reach@ occurs exactly once in @p@ in the form @reach<args,x>@ and @x@
-- does not occur at all in @p@. This means their interpretations look like a
-- list type, where the @eq(x)@ is the nil constructor and the @p@ is the
-- cons. To support the transitivity rule, we need an append function for these
-- lists, which is given by the transitivity method listed here, which has type
--
-- > trans : forall args (x y:A), t args x -> t args y -> t args y
--
-- where @args@ are the arguments and @A@ is the translation of type @a@ (which
-- may correspond to 0 or more arguments)
data ReachMethods reach args a where
  ReachMethods :: {
    reachMethodTrans :: Ident
    } -> ReachMethods (args :> a) a 'True
  NoReachMethods :: ReachMethods args a 'False

-- | A recursive permission is a disjunction of 1 or more permissions, each of
-- which can contain the recursive permission itself. NOTE: it is an error to
-- have an empty list of cases. A recursive permission is also associated with a
-- SAW datatype, given by a SAW 'Ident', and each disjunctive permission case is
-- associated with a constructor of that datatype. The @b@ flag indicates
-- whether this recursive permission can be used as an atomic permission, which
-- should be 'True' iff all of the cases are conjunctive permissions as in
-- 'isConjPerm'. If the recursive permission is a reachability permission, then
-- it also has a 'ReachMethods' structure.
data RecPerm b reach args a = RecPerm {
  recPermName :: NamedPermName (RecursiveSort b reach) args a,
  recPermTransType :: Ident,
  recPermFoldFun :: Ident,
  recPermUnfoldFun :: Ident,
  recPermReachMethods :: ReachMethods args a reach,
  recPermCases :: [Mb args (ValuePerm a)]
  }

-- | Get the @trans@ method from a 'RecPerm' for a reachability permission
recPermTransMethod :: RecPerm b 'True args a -> Ident
recPermTransMethod (RecPerm { recPermReachMethods = ReachMethods { .. }}) =
  reachMethodTrans

-- | A defined permission is a name and a permission to which it is
-- equivalent. The @b@ flag indicates whether this permission can be used as an
-- atomic permission, which should be 'True' iff the associated permission is a
-- conjunctive permission as in 'isConjPerm'.
data DefinedPerm b args a = DefinedPerm {
  definedPermName :: NamedPermName (DefinedSort b) args a,
  definedPermDef :: Mb args (ValuePerm a)
}

-- | A pair of a variable and its permission; we give it its own datatype to
-- make certain typeclass instances (like pretty-printing) specific to it
data VarAndPerm a = VarAndPerm (ExprVar a) (ValuePerm a)

-- | A list of "distinguished" permissions to named variables
-- FIXME: just call these VarsAndPerms or something like that...
type DistPerms = RAssign VarAndPerm

-- | Pattern for an empty 'DistPerms'
pattern DistPermsNil :: () => (ps ~ RNil) => DistPerms ps
pattern DistPermsNil = MNil

-- | Pattern for a non-empty 'DistPerms'
pattern DistPermsCons :: () => (ps ~ (ps' :> a)) =>
                         DistPerms ps' -> ExprVar a -> ValuePerm a ->
                         DistPerms ps
pattern DistPermsCons ps x p <- ps :>: (VarAndPerm x p)
  where
    DistPermsCons ps x p = ps :>: VarAndPerm x p

{-# COMPLETE DistPermsNil, DistPermsCons #-}

{-
data DistPerms ps where
  DistPermsNil :: DistPerms RNil
  DistPermsCons :: DistPerms ps -> ExprVar a -> ValuePerm a ->
                   DistPerms (ps :> a)
-}

type MbDistPerms ps = Mb ps (DistPerms ps)

-- | A pair of an epxression and its permission; we give it its own datatype to
-- make certain typeclass instances (like pretty-printing) specific to it
data ExprAndPerm a =
  ExprAndPerm { exprAndPermExpr :: PermExpr a,
                exprAndPermPerm :: ValuePerm a }

-- | A list of expressions and associated permissions; different from
-- 'DistPerms' because the expressions need not be variables
type ExprPerms = RAssign ExprAndPerm

-- | Convert a 'DistPerms' to an 'ExprPerms'
distPermsToExprPerms :: DistPerms ps -> ExprPerms ps
distPermsToExprPerms =
  RL.map (\(VarAndPerm x p) -> ExprAndPerm (PExpr_Var x) p)

-- FIXME: change all of the following functions on DistPerms to use the RAssign
-- combinators

-- | Fold a function over a 'DistPerms' list, where
--
-- > foldDistPerms f b ('DistPermsCons'
-- >                    ('DistPermsCons' (... 'DistPermsNil' ...) x2 p2) x1 p1) =
-- > f (f (... b ...) x2 p2) x1 p1
--
-- FIXME: implement more functions on DistPerms in terms of this
foldDistPerms :: (forall a. b -> ExprVar a -> ValuePerm a -> b) ->
                 b -> DistPerms as -> b
foldDistPerms _ b DistPermsNil = b
foldDistPerms f b (DistPermsCons ps x p) = f (foldDistPerms f b ps) x p

-- | Find all permissions in a 'DistPerms' on a specific variable
varPermsInDistPerms :: ExprVar a -> DistPerms ps -> [ValuePerm a]
varPermsInDistPerms x =
  RL.foldr (\case (VarAndPerm y p) | Just Refl <- testEquality x y -> (p:)
                  _ -> id)
  []

-- | Find all atomic permissions in a 'DistPerms' on a specific variable
varAtomicPermsInDistPerms :: ExprVar a -> DistPerms ps -> [AtomicPerm a]
varAtomicPermsInDistPerms x =
  RL.foldr (\case (VarAndPerm y (ValPerm_Conj ps))
                    | Just Refl <- testEquality x y -> (ps ++)
                  _ -> id)
  []

-- | Combine a list of variable names and a list of permissions into a list of
-- distinguished permissions
valuePermsToDistPerms :: RAssign Name ps -> ValuePerms ps -> DistPerms ps
valuePermsToDistPerms MNil _ = DistPermsNil
valuePermsToDistPerms (ns :>: n) (ps :>: p) =
  DistPermsCons (valuePermsToDistPerms ns ps) n p

-- | Convert a list of permissions inside bindings for variables into a list of
-- distinguished permissions for those variables
mbValuePermsToDistPerms :: MbValuePerms ps -> MbDistPerms ps
mbValuePermsToDistPerms = nuMultiWithElim1 valuePermsToDistPerms

-- | Extract the permissions from a 'DistPerms'
distPermsToValuePerms :: DistPerms ps -> ValuePerms ps
distPermsToValuePerms DistPermsNil = ValPerms_Nil
distPermsToValuePerms (DistPermsCons dperms _ p) =
  ValPerms_Cons (distPermsToValuePerms dperms) p

-- | Extract the permissions-in-binding from a 'DistPerms' in a binding
mbDistPermsToValuePerms :: Mb ctx (DistPerms ps) -> Mb ctx (ValuePerms ps)
mbDistPermsToValuePerms = fmap distPermsToValuePerms

-- | Create a sequence @x1:eq(e1), ..., xn:eq(en)@ of equality permissions
eqDistPerms :: RAssign Name ps -> PermExprs ps -> DistPerms ps
eqDistPerms ns exprs =
  valuePermsToDistPerms ns $ RL.map ValPerm_Eq $ exprsToRAssign exprs

-- | Create a sequence @x1:true, ..., xn:true@ of vacuous permissions
trueDistPerms :: RAssign Name ps -> DistPerms ps
trueDistPerms MNil = DistPermsNil
trueDistPerms (ns :>: n) = DistPermsCons (trueDistPerms ns) n ValPerm_True

-- | A list of "distinguished" permissions with types
type TypedDistPerms = RAssign (Typed VarAndPerm)

-- | Convert a permission list expression to a 'TypedDistPerms', if possible
permListToTypedPerms :: PermExpr PermListType -> Maybe (Some TypedDistPerms)
permListToTypedPerms PExpr_PermListNil = Just $ Some MNil
permListToTypedPerms (PExpr_PermListCons tp (PExpr_Var x) p l)
  | Just (Some perms) <- permListToTypedPerms l =
    Just $ Some $ RL.append (MNil :>: Typed tp (VarAndPerm x p)) perms
permListToTypedPerms _ = Nothing

-- | Convert a 'TypedDistPerms' to a permission list
typedPermsToPermList :: TypedDistPerms ps -> PermExpr PermListType
typedPermsToPermList = flip helper PExpr_PermListNil where
  -- We use an accumulator to reverse as we go, because DistPerms cons to the
  -- right while PermLists cons to the left
  helper :: TypedDistPerms ps' -> PermExpr PermListType -> PermExpr PermListType
  helper MNil accum = accum
  helper (ps :>: Typed tp (VarAndPerm x p)) accum =
    helper ps $ PExpr_PermListCons tp (PExpr_Var x) p accum

-- | Convert a 'TypedDistPerms' to a normal 'DistPerms'
unTypeDistPerms :: TypedDistPerms ps -> DistPerms ps
unTypeDistPerms = RL.map (\(Typed _ v_and_p) -> v_and_p)


instance TestEquality VarAndPerm where
  testEquality (VarAndPerm x1 p1) (VarAndPerm x2 p2)
    | Just Refl <- testEquality x1 x2
    , p1 == p2
    = Just Refl
  testEquality _ _ = Nothing

instance Eq (VarAndPerm a) where
  vp1 == vp2 | Just _ <- testEquality vp1 vp2 = True
  _ == _ = False

instance Eq1 VarAndPerm where
  eq1 = (==)

{-
instance TestEquality DistPerms where
  testEquality DistPermsNil DistPermsNil = Just Refl
  testEquality (DistPermsCons ps1 x1 p1) (DistPermsCons ps2 x2 p2)
    | Just Refl <- testEquality ps1 ps2
    , Just Refl <- testEquality x1 x2
    , p1 == p2
    = Just Refl
  testEquality _ _ = Nothing

instance Eq (DistPerms ps) where
  perms1 == perms2 =
    case testEquality perms1 perms2 of
      Just _ -> True
      Nothing -> False
-}


-- | Build the permission and the variable it applies to that is needed to prove
-- that @l@ is current during @l2@. If @l@ is @always@, this holds vacuously, so
-- return the permission @l2:true@, and otherwise, if @l@ is a variable, return
-- @l:[l2]lcurrent@.
lcurrentPerm :: PermExpr LifetimeType -> ExprVar LifetimeType ->
                (ExprVar LifetimeType, ValuePerm LifetimeType)
lcurrentPerm PExpr_Always l2 = (l2, ValPerm_True)
lcurrentPerm (PExpr_Var l) l2 = (l, ValPerm_LCurrent $ PExpr_Var l2)

-- | A special-purpose 'DistPerms' that specifies a list of permissions needed
-- to prove that a lifetime is current
data LifetimeCurrentPerms ps_l where
  -- | The @always@ lifetime needs no proof that it is current
  AlwaysCurrentPerms :: LifetimeCurrentPerms RNil
  -- | A variable @l@ that is @lowned@ is current, requiring perms
  --
  -- > l:lowned(ps_in -o ps_out)
  LOwnedCurrentPerms :: ExprVar LifetimeType ->
                        LOwnedPerms ps_in -> LOwnedPerms ps_out ->
                        LifetimeCurrentPerms (RNil :> LifetimeType)

  -- | A variable @l@ that is @lcurrent@ during another lifetime @l'@ is
  -- current, i.e., if @ps@ ensure @l'@ is current then we need perms
  --
  -- > ps, l:lcurrent(l')
  CurrentTransPerms :: LifetimeCurrentPerms ps_l -> ExprVar LifetimeType ->
                       LifetimeCurrentPerms (ps_l :> LifetimeType)

-- | Get the lifetime that a 'LifetimeCurrentPerms' is about
lifetimeCurrentPermsLifetime :: LifetimeCurrentPerms ps_l ->
                                PermExpr LifetimeType
lifetimeCurrentPermsLifetime AlwaysCurrentPerms = PExpr_Always
lifetimeCurrentPermsLifetime (LOwnedCurrentPerms l _ _) = PExpr_Var l
lifetimeCurrentPermsLifetime (CurrentTransPerms _ l) = PExpr_Var l

-- | Convert a 'LifetimeCurrentPerms' to the 'DistPerms' it represent
lifetimeCurrentPermsPerms :: LifetimeCurrentPerms ps_l -> DistPerms ps_l
lifetimeCurrentPermsPerms AlwaysCurrentPerms = DistPermsNil
lifetimeCurrentPermsPerms (LOwnedCurrentPerms l ps_in ps_out) =
  DistPermsCons DistPermsNil l $ ValPerm_LOwned ps_in ps_out
lifetimeCurrentPermsPerms (CurrentTransPerms cur_ps l) =
  DistPermsCons (lifetimeCurrentPermsPerms cur_ps) l $
  ValPerm_Conj1 $ Perm_LCurrent $ lifetimeCurrentPermsLifetime cur_ps

-- | Build a lift of proxies for a 'LifetimeCurrentPerms'
mbLifetimeCurrentPermsProxies :: Mb ctx (LifetimeCurrentPerms ps_l) ->
                                 RAssign Proxy ps_l
mbLifetimeCurrentPermsProxies mb_l = case mbMatch mb_l of
  [nuMP| AlwaysCurrentPerms |] -> MNil
  [nuMP| LOwnedCurrentPerms _ _ _ |] -> MNil :>: Proxy
  [nuMP| CurrentTransPerms cur_ps _ |] ->
    mbLifetimeCurrentPermsProxies cur_ps :>: Proxy

-- | A lifetime functor is a function from a lifetime plus a set of 0 or more
-- rwmodalities to a permission that satisfies a number of properties discussed
-- in Issue #62 (FIXME: copy those here). Rather than try to enforce these
-- properties, we syntactically restrict lifetime functors to one of a few forms
-- that are guaranteed to satisfy the properties. The @args@ type lists all
-- arguments (which should all be rwmodalities) other than the lifetime
-- argument.
data LifetimeFunctor args a where
  -- | The functor @\(l,rw) -> [l]ptr((rw,off) |-> p)@
  LTFunctorField :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                    PermExpr (BVType w) -> ValuePerm (LLVMPointerType sz) ->
                    LifetimeFunctor (RNil :> RWModalityType) (LLVMPointerType w)

  -- | The functor @\(l,rw) -> [l]memblock(rw,off,len,sh)
  LTFunctorBlock :: (1 <= w, KnownNat w) =>
                    PermExpr (BVType w) -> PermExpr (BVType w) ->
                    PermExpr (LLVMShapeType w) ->
                    LifetimeFunctor (RNil :> RWModalityType) (LLVMPointerType w)

  -- FIXME: add functors for arrays and named permissions

-- | Apply a functor to its arguments to get out a permission
ltFuncApply :: LifetimeFunctor args a -> PermExprs args ->
               PermExpr LifetimeType -> ValuePerm a
ltFuncApply (LTFunctorField off p) (MNil :>: rw) l =
  ValPerm_LLVMField $ LLVMFieldPerm rw l off p
ltFuncApply (LTFunctorBlock off len sh) (MNil :>: rw) l =
  ValPerm_LLVMBlock $ LLVMBlockPerm rw l off len sh

-- | Apply a functor to its arguments to get out an 'LOwnedPerm' on a variable
ltFuncApplyLOP :: ExprVar a -> LifetimeFunctor args a -> PermExprs args ->
                  PermExpr LifetimeType -> LOwnedPerm a
ltFuncApplyLOP x (LTFunctorField off p) (MNil :>: rw) l =
  LOwnedPermField (PExpr_Var x) $ LLVMFieldPerm rw l off p
ltFuncApplyLOP x (LTFunctorBlock off len sh) (MNil :>: rw) l =
  LOwnedPermBlock (PExpr_Var x) $ LLVMBlockPerm rw l off len sh

-- | Apply a functor to a lifetime and the "minimal" rwmodalities, i.e., with
-- all read permissions
ltFuncMinApply :: LifetimeFunctor args a -> PermExpr LifetimeType -> ValuePerm a
ltFuncMinApply (LTFunctorField off p) l =
  ValPerm_LLVMField $ LLVMFieldPerm PExpr_Read l off p
ltFuncMinApply (LTFunctorBlock off len sh) l =
  ValPerm_LLVMBlock $ LLVMBlockPerm PExpr_Read l off len sh

-- | Apply a functor to a lifetime and the "minimal" rwmodalities, i.e., with
-- all read permissions, getting out an 'LOwnedPerm'  on a variable
ltFuncMinApplyLOP :: ExprVar a -> LifetimeFunctor args a ->
                     PermExpr LifetimeType -> LOwnedPerm a
ltFuncMinApplyLOP x (LTFunctorField off p) l =
  LOwnedPermField (PExpr_Var x) $ LLVMFieldPerm PExpr_Read l off p
ltFuncMinApplyLOP x (LTFunctorBlock off len sh) l =
  LOwnedPermBlock (PExpr_Var x) $ LLVMBlockPerm PExpr_Read l off len sh

-- | Convert a field permission to a lifetime functor and its arguments
fieldToLTFunc :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                 LLVMFieldPerm w sz ->
                 (LifetimeFunctor (RNil :> RWModalityType) (LLVMPointerType w),
                  PermExprs (RNil :> RWModalityType))
fieldToLTFunc fp = (LTFunctorField (llvmFieldOffset fp) (llvmFieldContents fp),
                    MNil :>: llvmFieldRW fp)

-- | Convert a block permission to a lifetime functor and its arguments
blockToLTFunc :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                 (LifetimeFunctor (RNil :> RWModalityType) (LLVMPointerType w),
                  PermExprs (RNil :> RWModalityType))
blockToLTFunc bp =
  (LTFunctorBlock (llvmBlockOffset bp) (llvmBlockLen bp) (llvmBlockShape bp),
   MNil :>: llvmBlockRW bp)

instance Eq (ValuePerm a) where
  (ValPerm_Eq e1) == (ValPerm_Eq e2) = e1 == e2
  (ValPerm_Eq _) == _ = False
  (ValPerm_Or p1 p1') == (ValPerm_Or p2 p2') = p1 == p2 && p1' == p2'
  (ValPerm_Or _ _) == _ = False
  (ValPerm_Exists (p1 :: Binding a1 (ValuePerm a))) ==
   (ValPerm_Exists (p2 :: Binding a2 (ValuePerm a)))
    | Just Refl <-
        testEquality (knownRepr :: TypeRepr a1) (knownRepr :: TypeRepr a2)
    = p1 == p2
  (ValPerm_Exists _) == _ = False
  (ValPerm_Named n1 args1 off1) == (ValPerm_Named n2 args2 off2)
    | Just (Refl, Refl, Refl) <- testNamedPermNameEq n1 n2 =
        args1 == args2 && off1 == off2
  (ValPerm_Named _ _ _) == _ = False
  (ValPerm_Var x1 off1) == (ValPerm_Var x2 off2) = x1 == x2 && off1 == off2
  (ValPerm_Var _ _) == _ = False
  (ValPerm_Conj aps1) == (ValPerm_Conj aps2) = aps1 == aps2
  (ValPerm_Conj _) == _ = False

instance Eq (AtomicPerm a) where
  (Perm_LLVMField fp1) == (Perm_LLVMField fp2)
    | Just Refl <- testEquality (llvmFieldSize fp1) (llvmFieldSize fp2)
    = fp1 == fp2
  (Perm_LLVMField _) == _ = False
  (Perm_LLVMArray ap1) == (Perm_LLVMArray ap2) = ap1 == ap2
  (Perm_LLVMArray _) == _ = False
  (Perm_LLVMBlock bp1) == (Perm_LLVMBlock bp2) = bp1 == bp2
  (Perm_LLVMBlock _) == _ = False
  (Perm_LLVMFree e1) == (Perm_LLVMFree e2) = e1 == e2
  (Perm_LLVMFree _) == _ = False
  (Perm_LLVMFunPtr tp1 p1) == (Perm_LLVMFunPtr tp2 p2)
    | Just Refl <- testEquality tp1 tp2 = p1 == p2
  (Perm_LLVMFunPtr _ _) == _ = False
  Perm_IsLLVMPtr == Perm_IsLLVMPtr = True
  Perm_IsLLVMPtr == _ = False
  (Perm_LLVMBlockShape sh1) == (Perm_LLVMBlockShape sh2) = sh1 == sh2
  (Perm_LLVMBlockShape _) == _ = False
  (Perm_LLVMFrame frame1) == (Perm_LLVMFrame frame2) = frame1 == frame2
  (Perm_LLVMFrame _) == _ = False
  (Perm_LOwned ps_in1 ps_out1) == (Perm_LOwned ps_in2 ps_out2)
    | Just Refl <- testEquality ps_in1 ps_in2
    , Just Refl <- testEquality ps_out1 ps_out2
    = True
  (Perm_LOwned _ _) == _ = False
  (Perm_LCurrent e1) == (Perm_LCurrent e2) = e1 == e2
  (Perm_LCurrent _) == _ = False
  (Perm_Struct ps1) == (Perm_Struct ps2) = ps1 == ps2
  (Perm_Struct _) == _ = False
  (Perm_Fun fperm1) == (Perm_Fun fperm2)
    | Just Refl <- funPermEq fperm1 fperm2 = True
  (Perm_Fun _) == _ = False
  (Perm_NamedConj n1 args1 off1) == (Perm_NamedConj n2 args2 off2)
    | Just (Refl, Refl, Refl) <- testNamedPermNameEq n1 n2 =
      args1 == args2 && off1 == off2
  (Perm_NamedConj _ _ _) == _ = False
  (Perm_BVProp p1) == (Perm_BVProp p2) = p1 == p2
  (Perm_BVProp _) == _ = False

instance Eq1 ValuePerm where
  eq1 = (==)

{-
instance Eq (ValuePerms as) where
  ValPerms_Nil == ValPerms_Nil = True
  (ValPerms_Cons ps1 p1) == (ValPerms_Cons ps2 p2) =
    ps1 == ps2 && p1 == p2
-}

-- | Test if function permissions with different ghost argument lists are equal
funPermEq :: FunPerm ghosts1 args ret -> FunPerm ghosts2 args ret ->
             Maybe (ghosts1 :~: ghosts2)
funPermEq (FunPerm ghosts1 _ _ perms_in1 perms_out1)
  (FunPerm ghosts2 _ _ perms_in2 perms_out2)
  | Just Refl <- testEquality ghosts1 ghosts2
  , perms_in1 == perms_in2 && perms_out1 == perms_out2
  = Just Refl
funPermEq _ _ = Nothing

-- | Test if function permissions with all 3 type args different are equal
funPermEq3 :: FunPerm ghosts1 args1 ret1 -> FunPerm ghosts2 args2 ret2 ->
              Maybe (ghosts1 :~: ghosts2, args1 :~: args2, ret1 :~: ret2)
funPermEq3 (FunPerm ghosts1 args1 ret1 perms_in1 perms_out1)
  (FunPerm ghosts2 args2 ret2 perms_in2 perms_out2)
  | Just Refl <- testEquality ghosts1 ghosts2
  , Just Refl <- testEquality args1 args2
  , Just Refl <- testEquality ret1 ret2
  , perms_in1 == perms_in2 && perms_out1 == perms_out2
  = Just (Refl, Refl, Refl)
funPermEq3 _ _ = Nothing

instance Eq (FunPerm ghosts args ret) where
  fperm1 == fperm2 = isJust (funPermEq fperm1 fperm2)

instance PermPretty (NamedPermName ns args a) where
  permPrettyM (NamedPermName str _ _ _ _) = return $ pretty str

instance PermPretty (ValuePerm a) where
  permPrettyM (ValPerm_Eq e) = ((pretty "eq" <>) . parens) <$> permPrettyM e
  permPrettyM (ValPerm_Or p1 p2) =
    -- FIXME: If we ever fix the SAW lexer to handle "\/"...
    -- (\pp1 pp2 -> hang 2 (pp1 </> string "\\/" <> pp2))
    (\pp1 pp2 -> hang 2 (pp1 <> softline <> pretty "or" <+> pp2))
    <$> permPrettyM p1 <*> permPrettyM p2
  permPrettyM (ValPerm_Exists mb_p) =
    flip permPrettyExprMb mb_p $ \(_ :>: Constant pp_n) ppm ->
    (\pp -> hang 2 (pretty "exists" <+> pp_n <> dot <+> pp)) <$> ppm
  permPrettyM (ValPerm_Named n args off) =
    do n_pp <- permPrettyM n
       args_pp <- permPrettyM args
       off_pp <- permPrettyM off
       return (n_pp <> pretty '<' <>
               align (args_pp <> pretty '>') <> off_pp)
  permPrettyM (ValPerm_Var n off) =
    do n_pp <- permPrettyM n
       off_pp <- permPrettyM off
       return (n_pp <> off_pp)
  permPrettyM ValPerm_True = return $ pretty "true"
  permPrettyM (ValPerm_Conj ps) =
    (hang 2 . encloseSep mempty mempty (pretty "*")) <$> mapM permPrettyM ps

instance PermPrettyF ValuePerm where
  permPrettyMF = permPrettyM

-- | Pretty-print a lifetime @l@ as either the string @[l]@, or as the empty
-- string if @l==always@
permPrettyLifetimePrefix :: PermExpr LifetimeType -> PermPPM (Doc ann)
permPrettyLifetimePrefix PExpr_Always = return emptyDoc
permPrettyLifetimePrefix l = brackets <$> permPrettyM l

-- | Pretty-print an 'LLVMFieldPerm', either by itself as the form
-- @[l]ptr((rw,off) |-> p)@ if the 'Bool' flag is 'False' or as part of an array
-- permission as the form @[l](rw,off) |-> p@ if the 'Bool' flag is 'True'
permPrettyLLVMField :: (KnownNat w, KnownNat sz) =>
                       Bool -> LLVMFieldPerm w sz -> PermPPM (Doc ann)
permPrettyLLVMField in_array (LLVMFieldPerm {..} :: LLVMFieldPerm w sz) =
  do let w = knownNat @w
     let sz = knownNat @sz
     pp_l <- permPrettyLifetimePrefix llvmFieldLifetime
     pp_off <- permPrettyM llvmFieldOffset
     pp_rw <- permPrettyM llvmFieldRW
     let pp_parens =
           parens $
           if intValue sz == intValue w then
             pp_rw <> comma <> pp_off
           else
             pp_rw <> comma <> pp_off <> comma <> pretty (intValue sz)
     pp_contents <- permPrettyM llvmFieldContents
     return (pp_l <>
             (if in_array then id else (pretty "ptr" <>) . parens)
             (hang 2
              (pp_parens <+> pretty "|->" <> softline <> pp_contents)))

instance (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
         PermPretty (LLVMFieldPerm w sz) where
  permPrettyM = permPrettyLLVMField False

instance KnownNat w => PermPretty (LLVMArrayField w) where
  permPrettyM (LLVMArrayField fp) = permPrettyLLVMField True fp

instance (1 <= w, KnownNat w) => PermPretty (LLVMArrayPerm w) where
  permPrettyM (LLVMArrayPerm {..}) =
    do pp_off <- permPrettyM llvmArrayOffset
       pp_len <- permPrettyM llvmArrayLen
       let pp_stride = pretty (show llvmArrayStride)
       pp_flds <- mapM permPrettyM llvmArrayFields
       pp_bs <- mapM permPrettyM llvmArrayBorrows
       return $ PP.group (pretty "array" <>
                          ppEncList True [pp_off, pretty "<" <> pp_len,
                                          pretty "*" <> pp_stride,
                                          ppEncList False pp_flds,
                                          ppEncList False pp_bs])

instance (1 <= w, KnownNat w) => PermPretty (LLVMBlockPerm w) where
  permPrettyM (LLVMBlockPerm {..}) =
    do pp_rw <- permPrettyM llvmBlockRW
       pp_l <- permPrettyLifetimePrefix llvmBlockLifetime
       pp_off <- permPrettyM llvmBlockOffset
       pp_len <- permPrettyM llvmBlockLen
       pp_sh <- permPrettyM llvmBlockShape
       return $ PP.group (pp_l <> pretty "memblock" <>
                          ppEncList True [pp_rw, pp_off, pp_len, pp_sh])

instance PermPretty (AtomicPerm a) where
  permPrettyM (Perm_LLVMField fp) = permPrettyLLVMField False fp
  permPrettyM (Perm_LLVMArray ap) = permPrettyM ap
  permPrettyM (Perm_LLVMBlock bp) = permPrettyM bp
  permPrettyM (Perm_LLVMBlockShape sh) =
    ((pretty "shape" <>) . parens) <$> permPrettyM sh
  permPrettyM (Perm_LLVMFree e) = (pretty "free" <+>) <$> permPrettyM e
  permPrettyM (Perm_LLVMFunPtr _tp fp) =
    (\pp -> pretty "llvmfunptr" <+> parens pp) <$> permPrettyM fp
  permPrettyM Perm_IsLLVMPtr = return (pretty "is_llvmptr")
  permPrettyM (Perm_LLVMFrame fperm) =
    do pps <- mapM (\(e,i) -> (<> (colon <> pretty i)) <$> permPrettyM e) fperm
       return (pretty "llvmframe" <+> ppEncList False pps)
  permPrettyM (Perm_LOwned ps_in ps_out) =
    do pp_in <- permPrettyM ps_in
       pp_out <- permPrettyM ps_out
       return (pretty "lowned" <+> parens (align $
                                           sep [pp_in, pretty "-o", pp_out]))
  permPrettyM (Perm_LCurrent l) = (pretty "lcurrent" <+>) <$> permPrettyM l
  permPrettyM (Perm_Struct ps) =
    ((pretty "struct" <+>) . parens) <$> permPrettyM ps
  permPrettyM (Perm_Fun fun_perm) = permPrettyM fun_perm
  permPrettyM (Perm_BVProp prop) = permPrettyM prop
  permPrettyM (Perm_NamedConj n args off) =
    do n_pp <- permPrettyM n
       args_pp <- permPrettyM args
       off_pp <- permPrettyM off
       return (n_pp <> pretty '<' <> args_pp <> pretty '>' <> off_pp)

instance PermPretty (PermOffset a) where
  permPrettyM NoPermOffset = return mempty
  permPrettyM (LLVMPermOffset e) =
    do e_pp <- permPrettyM e
       return (pretty '@' <> parens e_pp)

instance PermPretty (LOwnedPerm a) where
  permPrettyM = permPrettyM . lownedPermExprAndPerm

instance PermPrettyF LOwnedPerm where
  permPrettyMF = permPrettyM

instance PermPretty (FunPerm ghosts args ret) where
  permPrettyM (FunPerm ghosts args _ mb_ps_in mb_ps_out) =
    let dps_in  = extMb $ mbValuePermsToDistPerms mb_ps_in
        dps_out = mbValuePermsToDistPerms mb_ps_out
        dps = mbMap2 (,) dps_in dps_out in
    fmap mbLift $ strongMbM $
    flip nuMultiWithElim1 dps $ \(ghosts_args_ns :>: ret_n) (ps_in, ps_out) ->
    let (ghosts_ns, args_ns) =
          RL.split Proxy (cruCtxProxies args) ghosts_args_ns in
    local (ppInfoAddExprName "ret" ret_n) $
    local (ppInfoAddExprNames "arg" args_ns) $
    local (ppInfoAddExprNames "ghost" ghosts_ns) $
    do pp_ps_in  <- permPrettyM ps_in
       pp_ps_out <- permPrettyM ps_out
       pp_ghosts <- permPrettyM (RL.map2 VarAndType ghosts_ns $
                                 cruCtxToTypes ghosts)
       return $ align $
         sep [parens pp_ghosts <> dot, pp_ps_in, pretty "-o", pp_ps_out]

instance PermPretty (BVRange w) where
  permPrettyM (BVRange e1 e2) =
    (\pp1 pp2 -> braces (pp1 <> comma <+> pp2))
    <$> permPrettyM e1 <*> permPrettyM e2

instance PermPretty (BVProp w) where
  permPrettyM (BVProp_Eq e1 e2) =
    (\pp1 pp2 -> pp1 <+> equals <+> pp2) <$> permPrettyM e1 <*> permPrettyM e2
  permPrettyM (BVProp_Neq e1 e2) =
    (\pp1 pp2 -> pp1 <+> pretty "/=" <+> pp2) <$> permPrettyM e1 <*> permPrettyM e2
  permPrettyM (BVProp_ULt e1 e2) =
    (\pp1 pp2 -> pp1 <+> pretty "<u" <+> pp2) <$> permPrettyM e1 <*> permPrettyM e2
  permPrettyM (BVProp_ULeq e1 e2) =
    (\pp1 pp2 -> pp1 <+> pretty "<=u" <+> pp2) <$> permPrettyM e1 <*> permPrettyM e2
  permPrettyM (BVProp_ULeq_Diff e1 e2 e3) =
    (\pp1 pp2 pp3 -> pp1 <+> pretty "<=u" <+> pp2 <+> pretty '-' <+> pp3)
    <$> permPrettyM e1 <*> permPrettyM e2 <*> permPrettyM e3

instance PermPretty (LLVMArrayBorrow w) where
  permPrettyM (FieldBorrow (LLVMArrayIndex ix fld_num)) =
    do pp_ix <- permPrettyM ix
       let pp_fld_num = pretty (show fld_num)
       return (parens pp_ix <> pretty "." <> pp_fld_num)
  permPrettyM (RangeBorrow rng) = permPrettyM rng

instance PermPretty (VarAndPerm a) where
  permPrettyM (VarAndPerm x p) =
    (\pp1 pp2 -> pp1 <> colon <> pp2) <$> permPrettyM x <*> permPrettyM p

instance PermPrettyF VarAndPerm where
  permPrettyMF = permPrettyM

{-
instance PermPretty (DistPerms ps) where
  permPrettyM ps = ppCommaSep <$> helper ps where
    helper :: DistPerms ps' -> PermPPM [Doc ann]
    helper DistPermsNil = return []
    helper (DistPermsCons ps x p) =
      do x_pp <- permPrettyM x
         p_pp <- permPrettyM p
         (++ [x_pp <> colon <> p_pp]) <$> helper ps
-}

instance PermPretty (ExprAndPerm a) where
  permPrettyM (ExprAndPerm x p) =
    (\pp1 pp2 -> pp1 <> colon <> pp2) <$> permPrettyM x <*> permPrettyM p

instance PermPrettyF ExprAndPerm where
  permPrettyMF = permPrettyM


$(mkNuMatching [t| forall a . PermExpr a |])
$(mkNuMatching [t| forall a . BVFactor a |])
$(mkNuMatching [t| forall w. BVRange w |])
$(mkNuMatching [t| forall w. BVProp w |])
$(mkNuMatching [t| forall a . AtomicPerm a |])
$(mkNuMatching [t| forall a . ValuePerm a |])
-- $(mkNuMatching [t| forall as. ValuePerms as |])
$(mkNuMatching [t| forall a . VarAndPerm a |])

instance NuMatchingAny1 PermExpr where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 ValuePerm where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 VarAndPerm where
  nuMatchingAny1Proof = nuMatchingProof

$(mkNuMatching [t| forall w sz . LLVMFieldPerm w sz |])
$(mkNuMatching [t| forall w . LLVMArrayPerm w |])
$(mkNuMatching [t| forall w . LLVMBlockPerm w |])
$(mkNuMatching [t| RWModality |])
$(mkNuMatching [t| forall w . LLVMArrayIndex w |])
$(mkNuMatching [t| forall w . LLVMArrayField w |])
$(mkNuMatching [t| forall w . LLVMArrayBorrow w |])
$(mkNuMatching [t| forall w . LLVMFieldShape w |])
$(mkNuMatching [t| forall w . LOwnedPerm w |])
$(mkNuMatching [t| forall ghosts args ret. FunPerm ghosts args ret |])
$(mkNuMatching [t| forall args ret. SomeFunPerm args ret |])
$(mkNuMatching [t| forall ns. NameSortRepr ns |])
$(mkNuMatching [t| forall ns args a. NameReachConstr ns args a |])
$(mkNuMatching [t| forall ns args a. NamedPermName ns args a |])
$(mkNuMatching [t| SomeNamedPermName |])
$(mkNuMatching [t| forall b args w. NamedShape b args w |])
$(mkNuMatching [t| forall b args w. NamedShapeBody b args w |])
$(mkNuMatching [t| forall a. PermOffset a |])
$(mkNuMatching [t| forall ns args a. NamedPerm ns args a |])
$(mkNuMatching [t| forall b args a. OpaquePerm b args a |])
$(mkNuMatching [t| forall args a reach. ReachMethods args a reach |])
$(mkNuMatching [t| forall b reach args a. RecPerm b reach args a |])
$(mkNuMatching [t| forall b args a. DefinedPerm b args a |])
$(mkNuMatching [t| forall args a. LifetimeFunctor args a |])
$(mkNuMatching [t| forall ps. LifetimeCurrentPerms ps |])


instance NuMatchingAny1 LOwnedPerm where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 DistPerms where
  nuMatchingAny1Proof = nuMatchingProof

instance Liftable RWModality where
  mbLift mb_rw = case mbMatch mb_rw of
    [nuMP| Write |] -> Write
    [nuMP| Read |] -> Read

instance Closable RWModality where
  toClosed Write = $(mkClosed [| Write |])
  toClosed Read = $(mkClosed [| Read |])

instance Closable (NameSortRepr ns) where
  toClosed (DefinedSortRepr b) =
    $(mkClosed [| DefinedSortRepr |]) `clApply` toClosed b
  toClosed (OpaqueSortRepr b) =
    $(mkClosed [| OpaqueSortRepr |]) `clApply` toClosed b
  toClosed (RecursiveSortRepr b reach) =
    $(mkClosed [| RecursiveSortRepr |])
    `clApply` toClosed b `clApply` toClosed reach

instance Liftable (NameSortRepr ns) where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable (NameReachConstr ns args a) where
  toClosed NameReachConstr = $(mkClosed [| NameReachConstr |])
  toClosed NameNonReachConstr = $(mkClosed [| NameNonReachConstr |])

instance Liftable (NameReachConstr ns args a) where
  mbLift = unClosed . mbLift . fmap toClosed

instance Liftable (NamedPermName ns args a) where
  mbLift (mbMatch -> [nuMP| NamedPermName n tp args ns r |]) =
    NamedPermName (mbLift n) (mbLift tp) (mbLift args) (mbLift ns) (mbLift r)

instance Liftable SomeNamedPermName where
  mbLift (mbMatch -> [nuMP| SomeNamedPermName rpn |]) =
    SomeNamedPermName $ mbLift rpn

instance Liftable (ReachMethods args a reach) where
  mbLift mb_x = case mbMatch mb_x of
    [nuMP| ReachMethods transIdent |] ->
      ReachMethods (mbLift transIdent)
    [nuMP| NoReachMethods |] -> NoReachMethods

-- | Embed a 'ValuePerm' in a 'PermExpr' - like 'PExpr_ValPerm' but maps
-- 'ValPerm_Var's to 'PExpr_Var's
permToExpr :: ValuePerm a -> PermExpr (ValuePermType a)
permToExpr (ValPerm_Var n NoPermOffset) = PExpr_Var n
permToExpr a = PExpr_ValPerm a

-- | Extract @p1@ from a permission of the form @p1 \/ p2@
orPermLeft :: ValuePerm a -> ValuePerm a
orPermLeft (ValPerm_Or p _) = p
orPermLeft _ = error "orPermLeft"

-- | Extract @p2@ from a permission of the form @p1 \/ p2@
orPermRight :: ValuePerm a -> ValuePerm a
orPermRight (ValPerm_Or _ p) = p
orPermRight _ = error "orPermRight"

-- | Extract the body @p@ from a permission of the form @exists (x:tp).p@
exPermBody :: TypeRepr tp -> ValuePerm a -> Binding tp (ValuePerm a)
exPermBody tp (ValPerm_Exists (p :: Binding tp' (ValuePerm a)))
  | Just Refl <- testEquality tp (knownRepr :: TypeRepr tp') = p
exPermBody _ _ = error "exPermBody"

-- | A representation of a context of types as a sequence of 'KnownRepr'
-- instances
--
-- FIXME: this can go away when existentials take explicit 'TypeRepr's instead
-- of 'KnownRepr TypeRepr' instances, as per issue #79
type KnownCruCtx = RAssign (KnownReprObj TypeRepr)

-- | Convert a 'KnownCruCtx' to a 'CruCtx'
knownCtxToCruCtx :: KnownCruCtx ctx -> CruCtx ctx
knownCtxToCruCtx MNil = CruCtxNil
knownCtxToCruCtx (ctx :>: KnownReprObj) =
  CruCtxCons (knownCtxToCruCtx ctx) knownRepr

-- | Construct 0 or more nested existential permissions
valPermExistsMulti :: KnownCruCtx ctx -> Mb ctx (ValuePerm a) -> ValuePerm a
valPermExistsMulti MNil mb_p = elimEmptyMb mb_p
valPermExistsMulti (ctx :>: KnownReprObj) mb_p =
  valPermExistsMulti ctx (fmap ValPerm_Exists $
                          mbSeparate (MNil :>: Proxy) mb_p)

-- | Test if an 'AtomicPerm' is a field permission
isLLVMFieldPerm :: AtomicPerm a -> Bool
isLLVMFieldPerm (Perm_LLVMField _) = True
isLLVMFieldPerm _ = False

-- | Test if an 'AtomicPerm' is a field permission with the given offset
isLLVMFieldPermWithOffset :: PermExpr (BVType w) ->
                             AtomicPerm (LLVMPointerType w) -> Bool
isLLVMFieldPermWithOffset off (Perm_LLVMField fp) =
  bvEq off (llvmFieldOffset fp)
isLLVMFieldPermWithOffset _ _ = False

-- | Test if an 'AtomicPerm' starts with the given offset
isLLVMAtomicPermWithOffset :: PermExpr (BVType w) ->
                              AtomicPerm (LLVMPointerType w) -> Bool
isLLVMAtomicPermWithOffset off p
  | Just off' <- llvmAtomicPermOffset p = bvEq off off'
isLLVMAtomicPermWithOffset _ _ = False

-- | Get the size of an 'LLVMFieldPerm' as an expression
llvmFieldLen :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                LLVMFieldPerm w sz -> PermExpr (BVType w)
llvmFieldLen fp = exprLLVMTypeBytesExpr $ llvmFieldContents fp

-- | Test if an 'AtomicPerm' is an array permission
isLLVMArrayPerm :: AtomicPerm a -> Bool
isLLVMArrayPerm (Perm_LLVMArray _) = True
isLLVMArrayPerm _ = False

-- | Test if an 'AtomicPerm' is an llvmblock permission
isLLVMBlockPerm :: AtomicPerm a -> Bool
isLLVMBlockPerm (Perm_LLVMBlock _) = True
isLLVMBlockPerm _ = False

-- | Test if an 'AtomicPerm' is a lifetime permission
isLifetimePerm :: AtomicPerm a -> Maybe (a :~: LifetimeType)
isLifetimePerm (Perm_LOwned _ _) = Just Refl
isLifetimePerm (Perm_LCurrent _) = Just Refl
isLifetimePerm _ = Nothing

-- | Test if an 'AtomicPerm' is a struct permission
isStructPerm :: AtomicPerm a -> Bool
isStructPerm (Perm_Struct _) = True
isStructPerm _ = False

-- | Test if an 'AtomicPerm' is a function permission
isFunPerm :: AtomicPerm a -> Bool
isFunPerm (Perm_Fun _) = True
isFunPerm _ = False

-- | Test if an 'AtomicPerm' is a named conjunctive permission
isNamedConjPerm :: AtomicPerm a -> Bool
isNamedConjPerm (Perm_NamedConj _ _ _) = True
isNamedConjPerm _ = False

-- | Test if an 'AtomicPerm' is a foldable named conjunctive permission
isFoldableConjPerm :: AtomicPerm a -> Bool
isFoldableConjPerm (Perm_NamedConj npn _ _) = nameCanFold npn
isFoldableConjPerm _ = False

-- | Test if an 'AtomicPerm' is a defined conjunctive permission
isDefinedConjPerm :: AtomicPerm a -> Bool
isDefinedConjPerm (Perm_NamedConj
                   (namedPermNameSort -> DefinedSortRepr _) _ _) = True
isDefinedConjPerm _ = False

-- | Test if an 'AtomicPerm' is a recursive conjunctive permission
isRecursiveConjPerm :: AtomicPerm a -> Bool
isRecursiveConjPerm (Perm_NamedConj
                     (namedPermNameSort -> RecursiveSortRepr _ _) _ _) = True
isRecursiveConjPerm _ = False

-- | Test that a permission is a conjunctive permission, meaning that it is
-- built inductively using only existentials, disjunctions, conjunctive named
-- permissions, and conjunctions of atomic permissions. Note that an atomic
-- permissions in such a conjunction can itself contain equality permissions;
-- e.g., in LLVM field permissions.
isConjPerm :: ValuePerm a -> Bool
isConjPerm (ValPerm_Eq _) = False
isConjPerm (ValPerm_Or p1 p2) = isConjPerm p1 && isConjPerm p2
isConjPerm (ValPerm_Exists mb_p) = mbLift $ fmap isConjPerm mb_p
isConjPerm (ValPerm_Named n _ _) = nameSortIsConj (namedPermNameSort n)
isConjPerm (ValPerm_Var _ _) = False
isConjPerm (ValPerm_Conj _) = True

-- | Helper function to build a 'Perm_LLVMFunPtr' from a 'FunPerm'
mkPermLLVMFunPtr :: (1 <= w, KnownNat w) => f w -> FunPerm ghosts args ret ->
                    AtomicPerm (LLVMPointerType w)
mkPermLLVMFunPtr (_w :: f w) fun_perm =
  case cruCtxToReprEq (funPermArgs fun_perm) of
    Refl ->
      Perm_LLVMFunPtr (FunctionHandleRepr
                       (cruCtxToRepr $ funPermArgs fun_perm)
                       (funPermRet fun_perm))
      (ValPerm_Conj1 $ Perm_Fun fun_perm)

-- | Helper function to build a 'Perm_LLVMFunPtr' from a list of 'FunPerm's. The
-- list must be non-empty.
mkPermLLVMFunPtrs :: (1 <= w, KnownNat w) => f w -> [SomeFunPerm args ret] ->
                     AtomicPerm (LLVMPointerType w)
mkPermLLVMFunPtrs (_w :: f w) [] = error "mkPermLLVMFunPtrs: empty list"
mkPermLLVMFunPtrs (_w :: f w) fun_perms@(SomeFunPerm fun_perm:_) =
  case cruCtxToReprEq (funPermArgs fun_perm) of
    Refl ->
      Perm_LLVMFunPtr (FunctionHandleRepr
                       (cruCtxToRepr $ funPermArgs fun_perm)
                       (funPermRet fun_perm))
      (ValPerm_Conj $ map (\(SomeFunPerm fp) -> Perm_Fun fp) fun_perms)

-- | Existential permission @x:eq(word(e))@ for some @e@
llvmExEqWord :: (1 <= w, KnownNat w) => prx w ->
                Binding (BVType w) (ValuePerm (LLVMPointerType w))
llvmExEqWord _ = nu $ \e -> ValPerm_Eq (PExpr_LLVMWord $ PExpr_Var e)

{-
-- | Create a field pointer permission with offset 0 and @eq(e)@ permissions
-- with the given read-write modality
llvmFieldContents0Eq :: (1 <= w, KnownNat w) =>
                    RWModality -> PermExpr (LLVMPointerType w) ->
                    LLVMPtrPerm w
llvmFieldContents0Eq rw e =
  Perm_LLVMField $ LLVMFieldPerm { llvmFieldRW = rw,
                                   llvmFieldOffset = bvInt 0,
                                   llvmFieldContents = ValPerm_Eq e }
-}

-- | Create a field permission to read a known value from offset 0 of an LLVM
-- pointer using an existential modality, lifetime, and value
llvmPtr0EqEx :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) => prx sz ->
                Mb (RNil :> RWModalityType :> LifetimeType :> LLVMPointerType sz)
                (LLVMFieldPerm w sz)
llvmPtr0EqEx _ =
  nuMulti (MNil :>: Proxy :>: Proxy :>: Proxy) $ \(_ :>: rw :>: l :>: x) ->
  LLVMFieldPerm { llvmFieldRW = PExpr_Var rw,
                  llvmFieldLifetime = PExpr_Var l,
                  llvmFieldOffset = bvInt 0,
                  llvmFieldContents = ValPerm_Eq (PExpr_Var x) }

-- | Create a permission to read a known value from offset 0 of an LLVM pointer
-- using an existential modality, lifetime, and value, i.e., return the
-- permission @exists rw,l,y.[l]ptr ((0,rw) |-> eq(y))@
llvmPtr0EqExPerm :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) => prx sz ->
                    Mb (RNil :> RWModalityType :> LifetimeType :> LLVMPointerType sz)
                    (ValuePerm (LLVMPointerType w))
llvmPtr0EqExPerm = fmap (ValPerm_Conj1 . Perm_LLVMField) . llvmPtr0EqEx

-- | Create a permission to read a known value from offset 0 of an LLVM pointer
-- in the given lifetime, i.e., return @exists y.[l]ptr ((0,R) |-> eq(e))@
llvmRead0EqPerm :: (1 <= w, KnownNat w) => PermExpr LifetimeType ->
                    PermExpr (LLVMPointerType w) ->
                    ValuePerm (LLVMPointerType w)
llvmRead0EqPerm l e =
  ValPerm_Conj [Perm_LLVMField $
                LLVMFieldPerm { llvmFieldRW = PExpr_Read,
                                llvmFieldLifetime = l,
                                llvmFieldOffset = bvInt 0,
                                llvmFieldContents = ValPerm_Eq e }]

-- | Create a field write permission with offset 0 and @true@ permissions of a
-- given size
llvmSizedFieldWrite0True :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                            f1 w -> f2 sz -> LLVMFieldPerm w sz
llvmSizedFieldWrite0True _ _ =
  LLVMFieldPerm { llvmFieldRW = PExpr_Write,
                  llvmFieldLifetime = PExpr_Always,
                  llvmFieldOffset = bvInt 0,
                  llvmFieldContents = ValPerm_True }

-- | Create a field write permission with offset 0 and @true@ permissions
llvmFieldWrite0True :: (1 <= w, KnownNat w) => LLVMFieldPerm w w
llvmFieldWrite0True = llvmSizedFieldWrite0True Proxy Proxy

-- | Create a field write permission with offset 0 and @true@ permissions
llvmWrite0TruePerm :: (1 <= w, KnownNat w) => ValuePerm (LLVMPointerType w)
llvmWrite0TruePerm = ValPerm_Conj [Perm_LLVMField llvmFieldWrite0True]

-- | Create a field write permission with offset 0 and an @eq(e)@ permission
llvmFieldWrite0Eq :: (1 <= w, KnownNat w) => PermExpr (LLVMPointerType w) ->
                     LLVMFieldPerm w w
llvmFieldWrite0Eq e =
  LLVMFieldPerm { llvmFieldRW = PExpr_Write,
                  llvmFieldLifetime = PExpr_Always,
                  llvmFieldOffset = bvInt 0,
                  llvmFieldContents = ValPerm_Eq e }

-- | Create a field write permission with offset 0 and an @eq(e)@ permission
llvmWrite0EqPerm :: (1 <= w, KnownNat w) => PermExpr (LLVMPointerType w) ->
                    ValuePerm (LLVMPointerType w)
llvmWrite0EqPerm e = ValPerm_Conj [Perm_LLVMField $ llvmFieldWrite0Eq e]

-- | Create a field write permission with offset @e@ and lifetime @l@
llvmFieldWriteTrueL :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                       prx sz -> PermExpr (BVType w) ->
                       PermExpr LifetimeType -> LLVMFieldPerm w sz
llvmFieldWriteTrueL _ off l =
  LLVMFieldPerm { llvmFieldRW = PExpr_Write,
                  llvmFieldLifetime = l,
                  llvmFieldOffset = off,
                  llvmFieldContents = ValPerm_True }

-- | Create a field write permission with offset @e@ and an existential lifetime
llvmWriteTrueExLPerm :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                        prx sz -> PermExpr (BVType w) ->
                        Binding LifetimeType (ValuePerm (LLVMPointerType w))
llvmWriteTrueExLPerm sz off =
  nu $ \l ->
  ValPerm_Conj1 $ Perm_LLVMField $ llvmFieldWriteTrueL sz off (PExpr_Var l)

-- | Create a field permission with offset @e@ and existential lifetime and rw
llvmReadExRWExLPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                       Mb (RNil :> RWModalityType :> LifetimeType)
                       (ValuePerm (LLVMPointerType w))
llvmReadExRWExLPerm (off :: PermExpr (BVType w)) =
  nuMulti (MNil :>: Proxy :>: Proxy) $ \(_ :>: rw :>: l) ->
  ValPerm_Conj1 $ Perm_LLVMField @w @w $
  LLVMFieldPerm { llvmFieldRW = PExpr_Var rw,
                  llvmFieldLifetime = PExpr_Var l,
                  llvmFieldOffset = off,
                  llvmFieldContents = ValPerm_True }

-- | Convert a field permission to a block permission
llvmFieldPermToBlock :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                        LLVMFieldPerm w sz -> LLVMBlockPerm w
llvmFieldPermToBlock fp =
  LLVMBlockPerm
  { llvmBlockRW = llvmFieldRW fp,
    llvmBlockLifetime = llvmFieldLifetime fp,
    llvmBlockOffset = llvmFieldOffset fp,
    llvmBlockLen = llvmFieldLen fp,
    llvmBlockShape = PExpr_FieldShape (LLVMFieldShape $ llvmFieldContents fp) }

-- | Convert an atomic permission to a @memblock@, if possible
llvmAtomicPermToBlock :: AtomicPerm (LLVMPointerType w) ->
                         Maybe (LLVMBlockPerm w)
llvmAtomicPermToBlock (Perm_LLVMField fp) = Just $ llvmFieldPermToBlock fp
llvmAtomicPermToBlock (Perm_LLVMArray ap)
  | [] <- llvmArrayBorrows ap
  , LLVMArrayField fp : _ <- llvmArrayFields ap
  , Just shs <-
      mapM (\case
               LLVMArrayField fp'
                 | llvmFieldRW fp == llvmFieldRW fp'
                 , llvmFieldLifetime fp == llvmFieldLifetime fp' ->
                     Just $ LLVMFieldShape (llvmFieldContents fp')
               _ -> Nothing)
      (llvmArrayFields ap)
  = Just $ LLVMBlockPerm
      { llvmBlockRW = llvmFieldRW fp,
        llvmBlockLifetime = llvmFieldLifetime fp,
        llvmBlockOffset = llvmArrayOffset ap,
        llvmBlockLen = llvmArrayLen ap,
        llvmBlockShape =
          PExpr_ArrayShape (llvmArrayLen ap) (llvmArrayStride ap) shs }
llvmAtomicPermToBlock (Perm_LLVMBlock bp) = Just bp
llvmAtomicPermToBlock _ = Nothing

-- | An 'LLVMBlockPerm' with a proof that its type is valid
data SomeLLVMBlockPerm a where
  SomeLLVMBlockPerm :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                       SomeLLVMBlockPerm (LLVMPointerType w)

-- | Convert an atomic permission whose type is unknown to a @memblock@, if
-- possible, along with a proof that its type is a valid llvm pointer type
llvmAtomicPermToSomeBlock :: AtomicPerm a -> Maybe (SomeLLVMBlockPerm a)
llvmAtomicPermToSomeBlock p@(Perm_LLVMField _) =
  SomeLLVMBlockPerm <$> llvmAtomicPermToBlock p
llvmAtomicPermToSomeBlock p@(Perm_LLVMArray _) =
  SomeLLVMBlockPerm <$> llvmAtomicPermToBlock p
llvmAtomicPermToSomeBlock (Perm_LLVMBlock bp) =
  Just $ SomeLLVMBlockPerm $ bp
llvmAtomicPermToSomeBlock _ = Nothing

-- | Get the lifetime of an atomic permission, if it has one
llvmAtomicPermLifetime :: AtomicPerm a -> Maybe (PermExpr LifetimeType)
llvmAtomicPermLifetime (llvmAtomicPermToSomeBlock ->
                        Just (SomeLLVMBlockPerm bp)) =
  Just $ llvmBlockLifetime bp
llvmAtomicPermLifetime _ = Nothing

-- | Get the offset of an atomic permission, if it has one
llvmAtomicPermOffset :: AtomicPerm (LLVMPointerType w) ->
                        Maybe (PermExpr (BVType w))
llvmAtomicPermOffset = fmap llvmBlockOffset . llvmAtomicPermToBlock

-- | Get the length of an atomic permission, if it has one
llvmAtomicPermLen :: AtomicPerm (LLVMPointerType w) ->
                     Maybe (PermExpr (BVType w))
llvmAtomicPermLen = fmap llvmBlockLen . llvmAtomicPermToBlock

-- | Get the range of offsets of an atomic permission, if it has one. Note that
-- arrays with borrows do not have a well-defined range.
llvmAtomicPermRange :: AtomicPerm (LLVMPointerType w) -> Maybe (BVRange w)
llvmAtomicPermRange p = fmap llvmBlockRange $ llvmAtomicPermToBlock p

-- | Get the range of offsets represented by an 'LLVMBlockPerm'
llvmBlockRange :: LLVMBlockPerm w -> BVRange w
llvmBlockRange bp = BVRange (llvmBlockOffset bp) (llvmBlockLen bp)

-- | Get the ending offset of a block permission
llvmBlockEndOffset :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                      PermExpr (BVType w)
llvmBlockEndOffset = bvRangeEnd . llvmBlockRange

-- | Return the expression for the length of a shape if there is one
llvmShapeLength :: (1 <= w, KnownNat w) => PermExpr (LLVMShapeType w) ->
                   Maybe (PermExpr (BVType w))
llvmShapeLength (PExpr_Var _) = Nothing
llvmShapeLength PExpr_EmptyShape = Just $ bvInt 0
llvmShapeLength (PExpr_NamedShape _ _ nmsh@(NamedShape _ _
                                            (DefinedShapeBody _)) args) =
  llvmShapeLength (unfoldNamedShape nmsh args)
llvmShapeLength (PExpr_NamedShape _ _ (NamedShape _ _
                                       (OpaqueShapeBody mb_len _)) args) =
  Just $ subst (substOfExprs args) mb_len
llvmShapeLength (PExpr_NamedShape _ _ nmsh@(NamedShape _ _
                                            (RecShapeBody _ _ _ _)) args) =
  -- FIXME: if the recursive shape contains itself *not* under a pointer, then
  -- this could diverge
  llvmShapeLength (unfoldNamedShape nmsh args)
llvmShapeLength (PExpr_EqShape _) = Nothing
llvmShapeLength (PExpr_PtrShape _ _ sh)
  | LLVMShapeRepr w <- exprType sh = Just $ bvInt (intValue w `div` 8)
  | otherwise = Nothing
llvmShapeLength (PExpr_FieldShape (LLVMFieldShape p)) =
  Just $ exprLLVMTypeBytesExpr p
llvmShapeLength (PExpr_ArrayShape len _ _) = Just len
llvmShapeLength (PExpr_SeqShape sh1 sh2) =
  liftA2 bvAdd (llvmShapeLength sh1) (llvmShapeLength sh2)
llvmShapeLength (PExpr_OrShape sh1 sh2) =
  -- We cannot represent a max expression, so we have to statically know which
  -- shape is bigger in order to compute the length of an or shape
  do len1 <- llvmShapeLength sh1
     len2 <- llvmShapeLength sh2
     if (bvLeq len1 len2) then return len2 else
       if (bvLeq len2 len1) then return len1
       else Nothing
llvmShapeLength (PExpr_ExShape mb_sh) =
  -- The length of an existential cannot depend on the existential variable, or
  -- we cannot return it
  case mbMatch $ fmap llvmShapeLength mb_sh of
    [nuMP| Just mb_len |] ->
      partialSubst (emptyPSubst $ singletonCruCtx $ knownRepr) mb_len
    _ -> Nothing

-- | Convert an 'LLVMFieldShape' inside (i.e., with all the other components of)
-- a @memblock@ permission to an 'LLVMArrayField' and its length
llvmFieldShapePermToArrayField :: (1 <= w, KnownNat w) => PermExpr RWModalityType ->
                                  PermExpr LifetimeType -> PermExpr (BVType w) ->
                                  LLVMFieldShape w ->
                                  (LLVMArrayField w, PermExpr (BVType w))
llvmFieldShapePermToArrayField rw l off (LLVMFieldShape p) =
  (LLVMArrayField (LLVMFieldPerm rw l off p), exprLLVMTypeBytesExpr p)

-- | Convert a @memblock@ permission with array shape to an array permission
llvmArrayBlockToArrayPerm :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                             LLVMArrayPerm w
llvmArrayBlockToArrayPerm bp
  | PExpr_ArrayShape len stride fshs <- llvmBlockShape bp
  , rw <- llvmBlockRW bp
  , l <- llvmBlockLifetime bp =
    LLVMArrayPerm
    { llvmArrayOffset = llvmBlockOffset bp,
      llvmArrayLen = bvMult (toInteger stride) len,
      llvmArrayStride = stride,
      llvmArrayBorrows = [],
      llvmArrayFields =
        snd $
        foldl (\(off,flds) sh ->
                let (fld, sz) = llvmFieldShapePermToArrayField rw l off sh in
                (bvAdd off sz, flds ++ [fld]))
        (bvInt 0, [])
        fshs }
llvmArrayBlockToArrayPerm _ =
  error "llvmArrayBlockToArrayPerm: block perm not of array shape"

-- | Adjust the read/write and lifetime modalities of a block permission by
-- setting those modalities that are supplied as arguments
llvmBlockAdjustModalities :: Maybe (PermExpr RWModalityType) ->
                             Maybe (PermExpr LifetimeType) ->
                             LLVMBlockPerm w -> LLVMBlockPerm w
llvmBlockAdjustModalities maybe_rw maybe_l bp =
  let rw = maybe (llvmBlockRW bp) id maybe_rw
      l = maybe (llvmBlockLifetime bp) id maybe_l in
  bp { llvmBlockRW = rw, llvmBlockLifetime = l }

-- | Create a field permission for a pointer to a block permission which uses
-- the offset, read/write modality, and lifetime of the block permission; that
-- is, return
--
-- > [l]ptr((rw,off) |-> [l]memblock(rw,0,len,sh))
llvmBlockPtrFieldPerm :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                         LLVMFieldPerm w w
llvmBlockPtrFieldPerm bp =
  LLVMFieldPerm
  { llvmFieldRW = llvmBlockRW bp,
    llvmFieldLifetime = llvmBlockLifetime bp,
    llvmFieldOffset = llvmBlockOffset bp,
    llvmFieldContents = ValPerm_LLVMBlock (bp { llvmBlockOffset = bvInt 0 }) }

-- | Create a pointer atomic permission to a block permission which uses the
-- offset, read/write modality, and lifetime of the block permission; that is,
-- return
--
-- > [l]ptr((rw,off) |-> [l]memblock(rw,0,len,sh))
llvmBlockPtrAtomicPerm :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                          AtomicPerm (LLVMPointerType w)
llvmBlockPtrAtomicPerm bp = Perm_LLVMField $ llvmBlockPtrFieldPerm bp

-- | Create a pointer permission to a block permission which uses the offset,
-- read/write modality, and lifetime of the block permission; that is, return
--
-- > [l]ptr((rw,off) |-> [l]memblock(rw,0,len,sh))
llvmBlockPtrPerm :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                    ValuePerm (LLVMPointerType w)
llvmBlockPtrPerm bp = ValPerm_Conj1 $ llvmBlockPtrAtomicPerm bp

-- | Add the given read/write and lifetime modalities to all top-level pointer
-- shapes in a shape. Top-level here means we do not recurse inside pointer
-- shapes, as pointer shape modalities also apply recursively to the contained
-- shapes. If there are any top-level variables in the shape, then this fails,
-- since there is no way to modalize a variable shape.
--
-- The high-level idea here is that pointer shapes take on the read/write and
-- lifetime modalities of the @memblock@ permission containing them, and
-- 'modalizeShape' folds these modalities into the shape itself.
modalizeShape :: Maybe (PermExpr RWModalityType) ->
                 Maybe (PermExpr LifetimeType) ->
                 PermExpr (LLVMShapeType w) ->
                 Maybe (PermExpr (LLVMShapeType w))
modalizeShape Nothing Nothing sh =
  -- If neither modality is given, it is a no-op
  Just sh
modalizeShape _ _ (PExpr_Var _) =
  -- Variables cannot be modalized; NOTE: we could fix this if necessary by
  -- adding a modalized variable shape constructor
  Nothing
modalizeShape _ _ PExpr_EmptyShape = Just PExpr_EmptyShape
modalizeShape rw l (PExpr_NamedShape rw' l' nmsh args) =
  -- If a named shape already has modalities, they take precedence
  Just $ PExpr_NamedShape (rw' <|> rw) (l' <|> l) nmsh args
modalizeShape _ _ sh@(PExpr_EqShape _) = Just sh
modalizeShape rw l (PExpr_PtrShape rw' l' sh) =
  -- If a pointer shape already has modalities, they take precedence
  Just $ PExpr_PtrShape (rw' <|> rw) (l' <|> l) sh
modalizeShape _ _ sh@(PExpr_FieldShape _) = Just sh
modalizeShape _ _ sh@(PExpr_ArrayShape _ _ _) = Just sh
modalizeShape rw l (PExpr_SeqShape sh1 sh2) =
  PExpr_SeqShape <$> modalizeShape rw l sh1 <*> modalizeShape rw l sh2
modalizeShape rw l (PExpr_OrShape sh1 sh2) =
  PExpr_OrShape <$> modalizeShape rw l sh1 <*> modalizeShape rw l sh2
modalizeShape rw l (PExpr_ExShape mb_sh) =
  PExpr_ExShape <$> mbM (fmap (modalizeShape rw l) mb_sh)

-- | Apply 'modalizeShape' to the shape of a block permission, raising an error
-- if 'modalizeShape' cannot be applied
modalizeBlockShape :: LLVMBlockPerm w -> PermExpr (LLVMShapeType w)
modalizeBlockShape (LLVMBlockPerm {..}) =
  maybe (error "modalizeBlockShape") id $
  modalizeShape (Just llvmBlockRW) (Just llvmBlockLifetime) llvmBlockShape

-- | Unfold a named shape
unfoldNamedShape :: KnownNat w => NamedShape 'True args w -> PermExprs args ->
                    PermExpr (LLVMShapeType w)
unfoldNamedShape (NamedShape _ _ (DefinedShapeBody mb_sh)) args =
  subst (substOfExprs args) mb_sh
unfoldNamedShape sh@(NamedShape _ _ (RecShapeBody mb_sh _ _ _)) args =
  subst (substOfExprs (args :>: PExpr_NamedShape Nothing Nothing sh args)) mb_sh

-- | Unfold a named shape and apply 'modalizeShape' to the result
unfoldModalizeNamedShape :: KnownNat w => Maybe (PermExpr RWModalityType) ->
                            Maybe (PermExpr LifetimeType) ->
                            NamedShape 'True args w -> PermExprs args ->
                            Maybe (PermExpr (LLVMShapeType w))
unfoldModalizeNamedShape rw l nmsh args =
  modalizeShape rw l $ unfoldNamedShape nmsh args

-- | Split a block permission into portions that are before and after a given
-- offset, if possible, assuming the offset is in the block permission
splitLLVMBlockPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                      LLVMBlockPerm w ->
                      Maybe (LLVMBlockPerm w, LLVMBlockPerm w)
splitLLVMBlockPerm off bp
  | bvEq off (llvmBlockOffset bp)
  = Just (bp { llvmBlockLen = bvInt 0, llvmBlockShape = PExpr_EmptyShape },
          bp)
splitLLVMBlockPerm off bp@(LLVMBlockPerm { llvmBlockShape = sh })
  | Just sh_len <- llvmShapeLength sh
  , bvLt sh_len (bvSub off (llvmBlockOffset bp)) =
    -- If we are splitting after the end of the natural length of a shape, then
    -- pad out the block permission to its natural length and fall back to the
    -- sequence shape case below
    splitLLVMBlockPerm off (bp { llvmBlockShape =
                                   PExpr_SeqShape sh PExpr_EmptyShape })
splitLLVMBlockPerm _ (llvmBlockShape -> PExpr_Var _) = Nothing
splitLLVMBlockPerm off bp@(llvmBlockShape -> PExpr_EmptyShape) =
  Just (bp { llvmBlockLen = bvSub off (llvmBlockOffset bp) },
        bp { llvmBlockOffset = off,
             llvmBlockLen = bvSub (llvmBlockLen bp) off })
splitLLVMBlockPerm off bp@(llvmBlockShape ->
                           PExpr_NamedShape maybe_rw maybe_l nmsh args)
  | TrueRepr <- namedShapeCanUnfoldRepr nmsh
  , Just sh' <- unfoldModalizeNamedShape maybe_rw maybe_l nmsh args =
    splitLLVMBlockPerm off (bp { llvmBlockShape = sh' })
splitLLVMBlockPerm _ (llvmBlockShape -> PExpr_NamedShape _ _ _ _) = Nothing
splitLLVMBlockPerm _ (llvmBlockShape -> PExpr_EqShape _) = Nothing
splitLLVMBlockPerm _ (llvmBlockShape -> PExpr_PtrShape _ _ _) = Nothing
splitLLVMBlockPerm _ (llvmBlockShape -> PExpr_FieldShape _) = Nothing
splitLLVMBlockPerm off bp@(llvmBlockShape -> PExpr_ArrayShape len stride flds)
  | Just (ix, BV.BV 0) <-
      bvMatchFactorPlusConst (bytesToInteger stride) (bvSub off $
                                                      llvmBlockOffset bp)
  , off_diff <- bvSub off (llvmBlockOffset bp)
  = Just (bp { llvmBlockLen = off_diff,
               llvmBlockShape = PExpr_ArrayShape ix stride flds },
          bp { llvmBlockOffset = off,
               llvmBlockLen = bvSub (llvmBlockLen bp) off_diff,
               llvmBlockShape = PExpr_ArrayShape (bvSub len ix) stride flds })
splitLLVMBlockPerm off bp@(llvmBlockShape -> PExpr_SeqShape sh1 sh2)
  | Just sh1_len <- llvmShapeLength sh1
  , off_diff <- bvSub off (llvmBlockOffset bp)
  , bvLt off_diff sh1_len
  = splitLLVMBlockPerm off (bp { llvmBlockLen = sh1_len,
                                 llvmBlockShape = sh1 }) >>= \(bp1,bp2) ->
    Just (bp1,
          bp2 { llvmBlockLen = bvSub (llvmBlockLen bp) off_diff,
                llvmBlockShape = PExpr_SeqShape (llvmBlockShape bp2) sh2 })
splitLLVMBlockPerm off bp@(llvmBlockShape -> PExpr_SeqShape sh1 sh2)
  | Just sh1_len <- llvmShapeLength sh1
  = splitLLVMBlockPerm off
    (bp { llvmBlockOffset = bvAdd (llvmBlockOffset bp) sh1_len,
          llvmBlockLen = bvSub (llvmBlockLen bp) sh1_len,
          llvmBlockShape = sh2 }) >>= \(bp1,bp2) ->
    Just (bp1 { llvmBlockOffset = llvmBlockOffset bp,
                llvmBlockLen = bvAdd (llvmBlockLen bp1) sh1_len,
                llvmBlockShape = PExpr_SeqShape sh1 (llvmBlockShape bp1) },
          bp2)
splitLLVMBlockPerm off bp@(llvmBlockShape -> PExpr_OrShape sh1 sh2) =
  do (bp1_L,bp1_R) <- splitLLVMBlockPerm off (bp { llvmBlockShape = sh1 })
     (bp2_L,bp2_R) <- splitLLVMBlockPerm off (bp { llvmBlockShape = sh2 })
     let or_helper bp1 bp2 =
           bp1 { llvmBlockShape =
                   PExpr_OrShape (llvmBlockShape bp1) (llvmBlockShape bp2)}
     Just (or_helper bp1_L bp2_L, or_helper bp1_R bp2_R)
splitLLVMBlockPerm off bp@(llvmBlockShape -> PExpr_ExShape mb_sh) =
  case mbMatch $ fmap (\sh -> splitLLVMBlockPerm off
                                (bp { llvmBlockShape = sh })) mb_sh of
    [nuMP| Just (mb_bp1,mb_bp2) |] ->
      let off_diff = bvSub off (llvmBlockOffset bp) in
      Just (bp { llvmBlockLen = off_diff,
                 llvmBlockShape = PExpr_ExShape (fmap llvmBlockShape mb_bp1) },
            bp { llvmBlockOffset = off,
                 llvmBlockLen = bvSub (llvmBlockLen bp) off_diff,
                 llvmBlockShape = PExpr_ExShape (fmap llvmBlockShape mb_bp2) })
    _ -> Nothing
splitLLVMBlockPerm _ _ = Nothing

-- | Remove a range of offsets from a block permission, if possible, yielding a
-- list of block permissions for the remaining offsets
remLLVMBLockPermRange :: (1 <= w, KnownNat w) => BVRange w -> LLVMBlockPerm w ->
                         Maybe [LLVMBlockPerm w]
remLLVMBLockPermRange rng bp
  | bvRangeSubset (llvmBlockRange bp) rng = Just []
remLLVMBLockPermRange rng bp =
  do (bps_l, bp') <-
       if bvInRange (bvRangeOffset rng) (llvmBlockRange bp) then
         do (bp_l,bp') <- splitLLVMBlockPerm (bvRangeOffset rng) bp
            return ([bp_l],bp')
       else return ([],bp)
     bp_r <-
       if bvInRange (bvRangeEnd rng) (llvmBlockRange bp) then
         snd <$> splitLLVMBlockPerm (bvRangeEnd rng) bp
       else return bp'
     return (bps_l ++ [bp_r])

-- | Convert an array cell number @cell@ to the byte offset for that cell, given
-- by @stride * cell + field_num@
llvmArrayCellToOffset :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                         PermExpr (BVType w) -> PermExpr (BVType w)
llvmArrayCellToOffset ap cell =
  bvMult (bytesToInteger $ llvmArrayStride ap) cell

-- | Convert a range of cell numbers to a range of byte offsets from the
-- beginning of the array permission
llvmArrayCellsToOffsets :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                           BVRange w -> BVRange w
llvmArrayCellsToOffsets ap (BVRange cell num_cells) =
  BVRange (llvmArrayCellToOffset ap cell) (llvmArrayCellToOffset ap num_cells)

-- | Return the clopen range @[0,len)@ of the cells of an array permission
llvmArrayCells :: (1 <= w, KnownNat w) => LLVMArrayPerm w -> BVRange w
llvmArrayCells ap = BVRange (bvInt 0) (llvmArrayLen ap)

-- | Build the 'BVRange' of "absolute" offsets @[off,off+len_bytes)@
llvmArrayAbsOffsets :: (1 <= w, KnownNat w) => LLVMArrayPerm w -> BVRange w
llvmArrayAbsOffsets ap =
  BVRange (llvmArrayOffset ap) (llvmArrayCellToOffset ap $ llvmArrayLen ap)

-- | Return the number of bytes per machine word; @w@ is the number of bits
machineWordBytes :: KnownNat w => f w -> Integer
machineWordBytes w
  | natVal w `mod` 8 /= 0 =
    error "machineWordBytes: word size is not a multiple of 8!"
machineWordBytes w = natVal w `div` 8

-- | Convert bytes to machine words, rounded up, i.e., return @ceil(n/W)@,
-- where @W@ is the number of bytes per machine word
bytesToMachineWords :: KnownNat w => f w -> Integer -> Integer
bytesToMachineWords w n = (n + machineWordBytes w - 1) `div` machineWordBytes w

-- | Return the largest multiple of 'machineWordBytes' less than the input
prevMachineWord :: KnownNat w => f w -> Integer -> Integer
prevMachineWord w n = (bytesToMachineWords w n - 1) * machineWordBytes w

-- | Build the permission that corresponds to a borrow from an array, i.e., that
-- would need to be returned in order to remove this borrow. For 'RangeBorrow's,
-- that is the sub-array permission with no borrows of its own.
permForLLVMArrayBorrow :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                          LLVMArrayBorrow w -> ValuePerm (LLVMPointerType w)
permForLLVMArrayBorrow ap (FieldBorrow ix) =
  ValPerm_Conj1 $ llvmArrayFieldToAtomicPerm $ llvmArrayFieldWithOffset ap ix
permForLLVMArrayBorrow ap (RangeBorrow (BVRange off len)) =
  ValPerm_Conj1 $ Perm_LLVMArray $
  ap { llvmArrayOffset = llvmArrayCellToOffset ap off,
       llvmArrayLen = len,
       llvmArrayBorrows = [] }

-- | Add a borrow to an 'LLVMArrayPerm'
llvmArrayAddBorrow :: LLVMArrayBorrow w -> LLVMArrayPerm w -> LLVMArrayPerm w
llvmArrayAddBorrow b ap = ap { llvmArrayBorrows = b : llvmArrayBorrows ap }

-- | Add a list of borrows to an 'LLVMArrayPerm'
llvmArrayAddBorrows :: [LLVMArrayBorrow w] -> LLVMArrayPerm w -> LLVMArrayPerm w
llvmArrayAddBorrows bs ap = foldr llvmArrayAddBorrow ap bs

-- | Add all borrows from the second array to the first, assuming the one is an
-- offset array as in 'llvmArrayIsOffsetArray'
llvmArrayAddArrayBorrows :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                            LLVMArrayPerm w -> LLVMArrayPerm w
llvmArrayAddArrayBorrows ap sub_ap
  | Just cell_num <- llvmArrayIsOffsetArray ap sub_ap =
    llvmArrayAddBorrows
    (map (cellOffsetLLVMArrayBorrow cell_num) (llvmArrayBorrows sub_ap))
    ap
llvmArrayAddArrayBorrows _ _ = error "llvmArrayAddArrayBorrows"

-- | Find the position in the list of borrows of an 'LLVMArrayPerm' of a
-- specific borrow
llvmArrayFindBorrow :: LLVMArrayBorrow w -> LLVMArrayPerm w -> Int
llvmArrayFindBorrow b ap =
  case findIndex (== b) (llvmArrayBorrows ap) of
    Just i -> i
    Nothing -> error "llvmArrayFindBorrow: borrow not found"

-- | Remove a borrow from an 'LLVMArrayPerm'
llvmArrayRemBorrow :: LLVMArrayBorrow w -> LLVMArrayPerm w -> LLVMArrayPerm w
llvmArrayRemBorrow b ap =
  ap { llvmArrayBorrows =
         deleteNth (llvmArrayFindBorrow b ap) (llvmArrayBorrows ap) }

-- | Remove a sequence of borrows from an 'LLVMArrayPerm'
llvmArrayRemBorrows :: [LLVMArrayBorrow w] -> LLVMArrayPerm w -> LLVMArrayPerm w
llvmArrayRemBorrows bs ap = foldr llvmArrayRemBorrow ap bs

-- | Remove all borrows from the second array to the first, assuming the one is
-- an offset array as in 'llvmArrayIsOffsetArray'
llvmArrayRemArrayBorrows :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                            LLVMArrayPerm w -> LLVMArrayPerm w
llvmArrayRemArrayBorrows ap sub_ap
  | Just cell_num <- llvmArrayIsOffsetArray ap sub_ap =
    llvmArrayRemBorrows
    (map (cellOffsetLLVMArrayBorrow cell_num) (llvmArrayBorrows sub_ap))
    ap
llvmArrayRemArrayBorrows _ _ = error "llvmArrayRemArrayBorrows"

-- | Add a cell offset to an 'LLVMArrayBorrow', meaning we change the borrow to
-- be relative to an array with that many more cells added to the front
cellOffsetLLVMArrayBorrow :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                              LLVMArrayBorrow w -> LLVMArrayBorrow w
cellOffsetLLVMArrayBorrow off (FieldBorrow (LLVMArrayIndex ix fld_num)) =
  FieldBorrow (LLVMArrayIndex (bvAdd ix off) fld_num)
cellOffsetLLVMArrayBorrow off (RangeBorrow rng) =
  RangeBorrow $ offsetBVRange off rng

-- | Convert an array permission into a field permission of the same size with a
-- @true@ permission, if possible
llvmArrayToField :: (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
                    NatRepr sz -> LLVMArrayPerm w -> Maybe (LLVMFieldPerm w sz)
llvmArrayToField sz ap
  | LLVMArrayField fp : _ <- llvmArrayFields ap
  , (rw,l) <- (llvmFieldRW fp, llvmFieldLifetime fp)
  , all (\(LLVMArrayField fp') -> rw == llvmFieldRW fp' &&
                                  l == llvmFieldLifetime fp')
    (llvmArrayFields ap)
  , [] <- llvmArrayBorrows ap
  , bvEq (bvMult (bytesToBits $
                  llvmArrayStride ap) (llvmArrayLen ap)) (bvInt $ intValue sz) =
    Just $ LLVMFieldPerm { llvmFieldRW = rw, llvmFieldLifetime = l,
                           llvmFieldOffset = llvmArrayOffset ap,
                           llvmFieldContents = ValPerm_True }
llvmArrayToField _ _ = Nothing

-- | Test if a byte offset @o@ statically aligns with a field in an array, i.e.,
-- whether
--
-- > o - off = stride*ix + 'llvmFieldOffset' (fields !! fld_num)
--
-- for some @ix@ and @fld_num@, where @off@ is the array offset, @stride@ is the
-- array stride, and @fields@ is the array fields. Return @ix@ and @fld_num@ on
-- success.
matchLLVMArrayField :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                       PermExpr (BVType w) -> Maybe (LLVMArrayIndex w)
matchLLVMArrayField ap o
  | rel_off <- bvSub o (llvmArrayOffset ap) =
    do (ix, fld_off) <-
         bvMatchFactorPlusConst (bytesToInteger $ llvmArrayStride ap) rel_off
       fld_num <-
         findIndex (\case LLVMArrayField fp ->
                            bvEq (llvmFieldOffset fp) (bvBV fld_off))
         (llvmArrayFields ap)
       return $ LLVMArrayIndex ix fld_num

-- | Return a list 'BVProp' stating that the field(s) represented by an array
-- borrow are in the "base" set of fields in an array, before the borrows are
-- considered. We assume that the borrow is statically well-formed for that
-- array, meaning that the static field number of a 'FieldBorrow' refers to a
-- valid field in the array perm.
llvmArrayBorrowInArrayBase :: (1 <= w, KnownNat w) =>
                              LLVMArrayPerm w -> LLVMArrayBorrow w ->
                              [BVProp w]
llvmArrayBorrowInArrayBase ap (FieldBorrow ix)
  | llvmArrayIndexFieldNum ix >= length (llvmArrayFields ap) =
    error "llvmArrayBorrowInArrayBase: invalid index"
llvmArrayBorrowInArrayBase ap (FieldBorrow ix) =
  [bvPropInRange (llvmArrayIndexCell ix) (llvmArrayCells ap)]
llvmArrayBorrowInArrayBase ap (RangeBorrow rng) =
  bvPropRangeSubset rng (llvmArrayCells ap)

-- | Return a list of 'BVProp's stating that two array borrows are disjoint. The
-- empty list is returned if they are trivially disjoint because they refer to
-- statically distinct field numbers.
llvmArrayBorrowsDisjoint :: (1 <= w, KnownNat w) =>
                            LLVMArrayBorrow w -> LLVMArrayBorrow w -> [BVProp w]
llvmArrayBorrowsDisjoint (FieldBorrow ix1) (FieldBorrow ix2)
  | llvmArrayIndexFieldNum ix1 == llvmArrayIndexFieldNum ix2
  = [BVProp_Neq (llvmArrayIndexCell ix1) (llvmArrayIndexCell ix2)]
llvmArrayBorrowsDisjoint (FieldBorrow _) (FieldBorrow _) = []
llvmArrayBorrowsDisjoint (FieldBorrow ix) (RangeBorrow rng) =
  [bvPropNotInRange (llvmArrayIndexCell ix) rng]
llvmArrayBorrowsDisjoint (RangeBorrow rng) (FieldBorrow ix) =
  [bvPropNotInRange (llvmArrayIndexCell ix) rng]
llvmArrayBorrowsDisjoint (RangeBorrow rng1) (RangeBorrow rng2) =
  bvPropRangesDisjoint rng1 rng2

-- | Return a list of propositions stating that the field(s) represented by an
-- array borrow are in the set of fields of an array permission. This takes into
-- account the current borrows on the array permission, which are fields that
-- are /not/ currently in that array permission.
llvmArrayBorrowInArray :: (1 <= w, KnownNat w) =>
                          LLVMArrayPerm w -> LLVMArrayBorrow w -> [BVProp w]
llvmArrayBorrowInArray ap b =
  llvmArrayBorrowInArrayBase ap b ++
  concatMap (llvmArrayBorrowsDisjoint b) (llvmArrayBorrows ap)

-- | Shorthand for 'llvmArrayBorrowInArray' with a single index
llvmArrayIndexInArray :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                         LLVMArrayIndex w -> [BVProp w]
llvmArrayIndexInArray ap ix = llvmArrayBorrowInArray ap (FieldBorrow ix)

-- | Test if all cell numbers in a 'BVRange' are in an array permission and are
-- not currently being borrowed
llvmArrayCellsInArray :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                         BVRange w -> [BVProp w]
llvmArrayCellsInArray ap rng = llvmArrayBorrowInArray ap (RangeBorrow rng)

-- | Test if an array permission @ap2@ is offset by an even multiple of cell
-- sizes from the start of @ap1@, and return that number of cells if so. Note
-- that 'llvmArrayIsOffsetArray' @ap1@ @ap2@ returns the negative of
-- 'llvmArrayIsOffsetArray' @ap2@ @ap1@ whenever either returns a value.
llvmArrayIsOffsetArray :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                          LLVMArrayPerm w -> Maybe (PermExpr (BVType w))
llvmArrayIsOffsetArray ap1 ap2
  | llvmArrayStride ap1 == llvmArrayStride ap2
  , Just (LLVMArrayIndex cell_num 0) <-
      matchLLVMArrayField ap1 (llvmArrayOffset ap2) = Just cell_num
llvmArrayIsOffsetArray _ _ = Nothing

-- | Build a 'BVRange' for the cells of a sub-array @ap2@ in @ap1@
llvmSubArrayRange :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                     LLVMArrayPerm w -> BVRange w
llvmSubArrayRange ap1 ap2
  | Just cell_num <- llvmArrayIsOffsetArray ap1 ap2 =
    BVRange cell_num (llvmArrayLen ap2)
llvmSubArrayRange _ _ = error "llvmSubArrayRange"

-- | Build a 'RangeBorrow' for the cells of a sub-array @ap2@ of @ap1@
llvmSubArrayBorrow :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                      LLVMArrayPerm w -> LLVMArrayBorrow w
llvmSubArrayBorrow ap1 ap2 = RangeBorrow $ llvmSubArrayRange ap1 ap2

-- | Return the propositions stating that the first array permission @ap@
-- contains the second @sub_ap@, meaning that array indices that are in @sub_ap@
-- (in the sense of 'llvmArrayIndexInArray') are in @ap@. This requires that the
-- range of @sub_ap@ be a subset of that of @ap@ and that it be disjoint from
-- all borrows in @ap@ that aren't also in @sub_ap@, i.e., that after removing
-- all borrows in @sub_ap@ from @ap@ we have that the 'llvmArrayCellsInArray'
-- propositions hold for the range of @sub_ap@.
--
-- NOTE: @sub_ap@ must satisfy 'llvmArrayIsOffsetArray', i.e., have the same
-- stride as @ap@ and be at a cell boundary in @ap@, or it is an error
llvmArrayContainsArray :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                          LLVMArrayPerm w -> [BVProp w]
llvmArrayContainsArray ap sub_ap =
  llvmArrayCellsInArray
  (llvmArrayRemArrayBorrows ap sub_ap)
  (llvmSubArrayRange ap sub_ap)

-- | Test if an atomic LLVM permission potentially allows a read or write of a
-- given offset. If so, return a list of the propositions required for the read
-- to be allowed. For LLVM field permissions, the offset of the field must
-- statically match the supplied offset, so the list of propositions will be
-- empty, while for arrays, the offset must only /not/ match any outstanding
-- borrows, and the propositions returned codify that as well as the requirement
-- that the offset is in the array range.
llvmPermContainsOffset :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                          AtomicPerm (LLVMPointerType w) -> Maybe [BVProp w]
llvmPermContainsOffset off (Perm_LLVMField fp)
  | bvEq (llvmFieldOffset fp) off = Just []
llvmPermContainsOffset off (Perm_LLVMArray ap)
  | Just ix <- matchLLVMArrayField ap off
  , props <- llvmArrayIndexInArray ap ix
  , all bvPropCouldHold props =
    Just props
llvmPermContainsOffset off (Perm_LLVMBlock bp)
  | prop <- bvPropInRange off (llvmBlockRange bp)
  , bvPropCouldHold prop =
    Just [prop]
llvmPermContainsOffset _ _ = Nothing

-- | Return the total length of an LLVM array permission in bytes
llvmArrayLengthBytes :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                        PermExpr (BVType w)
llvmArrayLengthBytes ap =
  llvmArrayIndexByteOffset ap (LLVMArrayIndex (llvmArrayLen ap) 0)

-- | Return the byte offset of an array index from the beginning of the array
llvmArrayIndexByteOffset :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                            LLVMArrayIndex w -> PermExpr (BVType w)
llvmArrayIndexByteOffset ap (LLVMArrayIndex cell fld_num) =
  bvAdd (llvmArrayCellToOffset ap cell)
  (llvmArrayFieldOffset (llvmArrayFields ap !! fld_num))

-- | Return the field permission corresponding to the given index an array
-- permission, offset by the array offset plus the byte offset of the field
llvmArrayFieldWithOffset :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                            LLVMArrayIndex w -> LLVMArrayField w
llvmArrayFieldWithOffset ap ix =
  if llvmArrayIndexFieldNum ix < length (llvmArrayFields ap) then
    offsetLLVMArrayField
    (bvAdd (llvmArrayOffset ap) (llvmArrayIndexByteOffset ap ix))
    (llvmArrayFields ap !! llvmArrayIndexFieldNum ix)
  else
    error "llvmArrayFieldWithOffset: index out of bounds"

-- | Get a list of all the fields in cell 0 of an array permission
llvmArrayHeadFields :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                       [LLVMArrayField w]
llvmArrayHeadFields ap =
  map (\i -> llvmArrayFieldWithOffset ap (LLVMArrayIndex (bvInt 0) i)) $
  [0 .. length (llvmArrayFields ap) - 1]

-- | Test if an array permission @ap@ is equivalent to a finite,
-- statically-known list of field permissions. This is the case iff the array
-- permission has a static constant length, in which case its field permissions
-- are all of the permissions returned by 'llvmArrayFieldWithOffset' for array
-- indices that are not borrowed in @ap@.
--
-- In order to make the translation work, we also need there to be at least one
-- complete array cell that is not borrowed.
--
-- If all this is satisfied by @ap@, return the field permissions it is equal
-- to, where those that comprise the un-borrowed cell are returned as the first
-- element of the returned pair and the rest are the second.
llvmArrayAsFields :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                     Maybe ([LLVMArrayField w], [LLVMArrayField w])
-- FIXME: this code is terrible! Simplify it!
llvmArrayAsFields ap
  | Just len <- bvMatchConstInt (llvmArrayLen ap)
  , Just cell <-
      find (\i ->
             not $ any (bvRangesCouldOverlap
                        (llvmArrayBorrowOffsets ap $
                         RangeBorrow $ BVRange (bvInt i) $ bvInt 1)
                        . llvmArrayBorrowOffsets ap) $ llvmArrayBorrows ap)
      [0 .. len-1]
  , fld_nums <- [0 .. length (llvmArrayFields ap) - 1]
  , all_ixs <-
      concatMap (\cell' ->
                  map (LLVMArrayIndex $ bvInt cell') fld_nums) [0 .. len - 1]
  = Just ( map (llvmArrayFieldWithOffset ap) $
           filter (bvEq (bvInt cell) . llvmArrayIndexCell) all_ixs
         , map (llvmArrayFieldWithOffset ap) $
           filter (\ix ->
                    not (bvEq (bvInt cell) (llvmArrayIndexCell ix)) &&
                    not (any (bvRangesCouldOverlap
                              (llvmArrayBorrowOffsets ap $ FieldBorrow ix)
                              . llvmArrayBorrowOffsets ap) $ llvmArrayBorrows ap))
           all_ixs)
llvmArrayAsFields _ = Nothing

-- | Map an offset to a borrow from an array, if possible
offsetToLLVMArrayBorrow :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                           PermExpr (BVType w) -> Maybe (LLVMArrayBorrow w)
offsetToLLVMArrayBorrow ap off = FieldBorrow <$> matchLLVMArrayField ap off

-- | Get the range of byte offsets represented by an array borrow relative to
-- the beginning of the array permission
llvmArrayBorrowOffsets :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                          LLVMArrayBorrow w -> BVRange w
llvmArrayBorrowOffsets ap (FieldBorrow ix) =
  bvRangeOfIndex $ llvmArrayIndexByteOffset ap ix
llvmArrayBorrowOffsets ap (RangeBorrow r) = llvmArrayCellsToOffsets ap r

-- | Get the range of byte offsets represented by an array borrow relative to
-- the variable @x@ that has the supplied array permission. This is equivalent
-- to the addition of 'llvmArrayOffset' to the range of relative offsets
-- returned by 'llvmArrayBorrowOffsets'.
llvmArrayBorrowAbsOffsets :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                             LLVMArrayBorrow w -> BVRange w
llvmArrayBorrowAbsOffsets ap b =
  offsetBVRange (llvmArrayOffset ap) (llvmArrayBorrowOffsets ap b)

-- | Divide an array permission @x:array(off,<len,*1,flds,bs)@ into two arrays,
-- one of length @len'@ starting at @off@ and one of length @len-len'@ starting
-- at offset @off+len'*stride@. All borrows that are definitely (in the sense of
-- 'bvPropHolds') in the first portion of the array are moved to that first
-- portion, and otherwise they are left in the second.
llvmArrayPermDivide :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                       PermExpr (BVType w) -> (LLVMArrayPerm w, LLVMArrayPerm w)
llvmArrayPermDivide ap len =
  let len_bytes = llvmArrayCellToOffset ap len
      borrow_in_first b =
        all bvPropHolds (bvPropRangeSubset
                         (llvmArrayBorrowOffsets ap b)
                         (BVRange (bvInt 0) len_bytes)) in
  (ap { llvmArrayLen = len,
        llvmArrayBorrows = filter borrow_in_first (llvmArrayBorrows ap) }
  ,
   ap { llvmArrayOffset = bvAdd (llvmArrayOffset ap) len_bytes
      , llvmArrayLen = bvSub (llvmArrayLen ap) len
      , llvmArrayBorrows =
          filter (not . borrow_in_first) (llvmArrayBorrows ap) })


{- FIXME HERE: remove these...?

-- | Test if a specific range of byte offsets from the beginning of an array
-- corresponds to a borrow already on an array
llvmArrayRangeIsBorrowed :: (1 <= w, KnownNat w) =>
                            LLVMArrayPerm w -> BVRange w -> Bool
llvmArrayRangeIsBorrowed ap rng =
  elem rng (map (llvmArrayBorrowOffsets ap) $ llvmArrayBorrows ap)

-- | Test if a specific array index and field number correspond to a borrow
-- already on an array
llvmArrayIndexIsBorrowed :: (1 <= w, KnownNat w) => LLVMArrayPerm w ->
                            PermExpr (BVType w) -> Int -> Bool
llvmArrayIndexIsBorrowed ap ix fld_num =
  llvmArrayRangeIsBorrowed ap $ llvmArrayIndexToRange ap ix fld_num

-- | Build 'BVProp's stating that each borrow in an array permission is disjoint
-- from an index or range
llvmArrayBorrowsDisjoint :: (1 <= w, KnownNat w) =>
                            LLVMArrayPerm w -> BVRange w -> [BVProp w]
llvmArrayBorrowsDisjoint ap range =
  map (BVProp_RangesDisjoint range . llvmArrayBorrowOffsets ap) $
  llvmArrayBorrows ap

-- | Search through a list of atomic permissions to see if one of them is an
-- LLVM array permission where the given field has been borrowed. If so, return
-- the index of the array permission in the list, the array permission itself,
-- and the index and field number of the field in the array
findLLVMArrayWithFieldBorrow :: (1 <= w, KnownNat w) => LLVMFieldPerm w ->
                                [AtomicPerm (LLVMPointerType w)] ->
                                Maybe (Int, LLVMArrayPerm w,
                                       PermExpr (BVType w), Int)
findLLVMArrayWithFieldBorrow _ [] = Nothing
findLLVMArrayWithFieldBorrow fp (Perm_LLVMArray ap : _)
  | Just (ix, fromInteger -> fld_num) <-
      bvMatchFactorPlusConst (llvmArrayStride ap)
      (bvSub (llvmFieldOffset fp) (llvmArrayOffset ap))
  , llvmArrayIndexIsBorrowed ap ix fld_num =
    Just (0, ap, ix, fld_num)
findLLVMArrayWithFieldBorrow fp (_ : ps) =
  fmap (\(i, ap, ix, fld_num) -> (i+1, ap, ix, fld_num)) $
  findLLVMArrayWithFieldBorrow fp ps
-}

-- | Create a list of field permissions the cover @N@ bytes:
--
-- > ptr((W,0) |-> true, (W,M) |-> true, (W,2*M) |-> true,
-- >   ..., (W, (i-1)*M, 8*(sz-(i-1)*M)) |-> true)
--
-- where @sz@ is the number of bytes allocated, @M@ is the machine word size in
-- bytes, and @i@ is the greatest natural number such that @(i-1)*M < sz@
llvmFieldsOfSize :: (1 <= w, KnownNat w) => f w -> Integer -> [LLVMArrayField w]
llvmFieldsOfSize (w :: f w) sz
  | sz_last_int <- 8 * (sz - prevMachineWord w sz)
  , Just (Some sz_last) <- someNat sz_last_int
  , Left LeqProof <- decideLeq (knownNat @1) sz_last =
    withKnownNat sz_last $
    map (\i -> LLVMArrayField $
               (llvmFieldWrite0True @w) { llvmFieldOffset =
                                            bvInt (i * machineWordBytes w) })
    [0 .. bytesToMachineWords w sz - 2]
    ++
    [LLVMArrayField $
     (llvmSizedFieldWrite0True w sz_last)
     { llvmFieldOffset =
         bvInt ((bytesToMachineWords w sz - 1) * machineWordBytes w) }]
  | otherwise = error "impossible (sz_last_int is always >= 8)"

-- | Return the permission built from the field permissions returned by
-- 'llvmFieldsOfSize'
llvmFieldsPermOfSize :: (1 <= w, KnownNat w) => f w -> Integer ->
                        ValuePerm (LLVMPointerType w)
llvmFieldsPermOfSize w n =
  ValPerm_Conj $ map llvmArrayFieldToAtomicPerm $ llvmFieldsOfSize w n

-- | Create an 'LLVMArrayPerm' for an array of uninitialized bytes
llvmByteArrayArrayPerm :: (1 <= w, KnownNat w) =>
                          PermExpr (BVType w) -> PermExpr (BVType w) ->
                          PermExpr RWModalityType -> PermExpr LifetimeType ->
                          LLVMArrayPerm w
llvmByteArrayArrayPerm off len rw l =
  LLVMArrayPerm {
  llvmArrayOffset = off,
  llvmArrayLen = len,
  llvmArrayStride = 1,
  llvmArrayFields =
      [LLVMArrayField $ LLVMFieldPerm {
          llvmFieldRW = rw,
          llvmFieldLifetime = l,
          llvmFieldOffset = bvInt 0,
          llvmFieldContents = (ValPerm_True
                               :: ValuePerm (LLVMPointerType 8)) }],
  llvmArrayBorrows = [] }

-- | Create a permission for an array of bytes
llvmByteArrayPerm :: (1 <= w, KnownNat w) =>
                     PermExpr (BVType w) -> PermExpr (BVType w) ->
                     PermExpr RWModalityType -> PermExpr LifetimeType ->
                     ValuePerm (LLVMPointerType w)
llvmByteArrayPerm off len rw l =
  ValPerm_Conj1 $ Perm_LLVMArray $ llvmByteArrayArrayPerm off len rw l

-- | Map an 'LLVMBlockPerm' to a byte array perm with the same components
llvmBlockPermToByteArrayPerm :: (1 <= w, KnownNat w) => LLVMBlockPerm w ->
                                ValuePerm (LLVMPointerType w)
llvmBlockPermToByteArrayPerm (LLVMBlockPerm {..}) =
  llvmByteArrayPerm llvmBlockOffset llvmBlockLen llvmBlockRW llvmBlockLifetime

-- | Create a @memblock(W,0,sz,emptysh)@ permission for a given size @sz@
llvmBlockPermOfSize :: (1 <= w, KnownNat w) => Integer ->
                       ValuePerm (LLVMPointerType w)
llvmBlockPermOfSize sz =
  ValPerm_Conj1 $ Perm_LLVMBlock $
  LLVMBlockPerm { llvmBlockRW = PExpr_Write, llvmBlockLifetime = PExpr_Always,
                  llvmBlockOffset = bvInt 0, llvmBlockLen = bvInt sz,
                  llvmBlockShape = PExpr_EmptyShape }

-- | Add an offset @off@ to an LLVM permission @p@, meaning change @p@ so that
-- it indicates that @x+off@ has permission @p@.
--
-- FIXME: this should be the general-purpose function 'offsetPerm' that recurses
-- through permissions; that would allow other sorts of offsets at other types
offsetLLVMPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                  ValuePerm (LLVMPointerType w) -> ValuePerm (LLVMPointerType w)
offsetLLVMPerm off (ValPerm_Eq e) = ValPerm_Eq $ addLLVMOffset e (bvNegate off)
offsetLLVMPerm off (ValPerm_Or p1 p2) =
  ValPerm_Or (offsetLLVMPerm off p1) (offsetLLVMPerm off p2)
offsetLLVMPerm off (ValPerm_Exists mb_p) =
  ValPerm_Exists $ fmap (offsetLLVMPerm off) mb_p
offsetLLVMPerm off (ValPerm_Named n args off') =
  ValPerm_Named n args (addPermOffsets off' (mkLLVMPermOffset off))
offsetLLVMPerm off (ValPerm_Var x off') =
  ValPerm_Var x $ addPermOffsets off' (mkLLVMPermOffset off)
offsetLLVMPerm off (ValPerm_Conj ps) =
  ValPerm_Conj $ mapMaybe (offsetLLVMAtomicPerm off) ps

-- | Test if an LLVM pointer permission can be offset by the given offset; i.e.,
-- whether 'offsetLLVMAtomicPerm' returns a value
canOffsetLLVMAtomicPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                           LLVMPtrPerm w -> Bool
canOffsetLLVMAtomicPerm off p = isJust $ offsetLLVMAtomicPerm off p

-- | Add an offset to an LLVM pointer permission, returning 'Nothing' for
-- permissions like @free@ and @llvm_funptr@ that cannot be offset
offsetLLVMAtomicPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                        LLVMPtrPerm w -> Maybe (LLVMPtrPerm w)
offsetLLVMAtomicPerm (bvMatchConstInt -> Just 0) p = Just p
offsetLLVMAtomicPerm off (Perm_LLVMField fp) =
  Just $ Perm_LLVMField $ offsetLLVMFieldPerm off fp
offsetLLVMAtomicPerm off (Perm_LLVMArray ap) =
  Just $ Perm_LLVMArray $ offsetLLVMArrayPerm off ap
offsetLLVMAtomicPerm off (Perm_LLVMBlock bp) =
  Just $ Perm_LLVMBlock $ offsetLLVMBlockPerm off bp
offsetLLVMAtomicPerm _ (Perm_LLVMFree _) = Nothing
offsetLLVMAtomicPerm _ (Perm_LLVMFunPtr _ _) = Nothing
offsetLLVMAtomicPerm _ p@Perm_IsLLVMPtr = Just p
offsetLLVMAtomicPerm off (Perm_NamedConj n args off') =
  Just $ Perm_NamedConj n args $ addPermOffsets off' (mkLLVMPermOffset off)
offsetLLVMAtomicPerm _ p@(Perm_BVProp _) = Just p

-- | Add an offset to a field permission
offsetLLVMFieldPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                       LLVMFieldPerm w sz -> LLVMFieldPerm w sz
offsetLLVMFieldPerm off (LLVMFieldPerm {..}) =
  LLVMFieldPerm { llvmFieldOffset = bvAdd llvmFieldOffset off, ..}

-- | Add an offset to an array field
offsetLLVMArrayField :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                        LLVMArrayField w -> LLVMArrayField w
offsetLLVMArrayField off (LLVMArrayField fp) =
  LLVMArrayField $ offsetLLVMFieldPerm off fp

-- | Add an offset to an array permission
offsetLLVMArrayPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                       LLVMArrayPerm w -> LLVMArrayPerm w
offsetLLVMArrayPerm off (LLVMArrayPerm {..}) =
  LLVMArrayPerm { llvmArrayOffset = bvAdd llvmArrayOffset off, ..}

-- | Add an offset to a block permission
offsetLLVMBlockPerm :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                       LLVMBlockPerm w -> LLVMBlockPerm w
offsetLLVMBlockPerm off (LLVMBlockPerm {..}) =
  LLVMBlockPerm { llvmBlockOffset = bvAdd llvmBlockOffset off, ..}

-- | Add a 'PermOffset' to a permission, assuming that it is a conjunctive
-- permission, meaning that it is built inductively using only existentials,
-- disjunctions, conjunctive named permissions, and conjunctions of atomic
-- permissions (though these atomic permissions can contain equality permissions
-- in, e.g., LLVM field permissions)
offsetPerm :: PermOffset a -> ValuePerm a -> ValuePerm a
offsetPerm (LLVMPermOffset off) p = offsetLLVMPerm off p
offsetPerm NoPermOffset p = p

-- | Lens for the atomic permissions in a 'ValPerm_Conj'; it is an error to use
-- this lens with a value permission not of this form
conjAtomicPerms :: Lens' (ValuePerm a) [AtomicPerm a]
conjAtomicPerms =
  lens
  (\p -> case p of
      ValPerm_Conj ps -> ps
      _ -> error "conjAtomicPerms: not a conjuction of atomic permissions")
  (\p ps ->
    case p of
      ValPerm_Conj _ -> ValPerm_Conj ps
      _ -> error "conjAtomicPerms: not a conjuction of atomic permissions")

-- | Lens for the @i@th atomic permission in a 'ValPerm_Conj'; it is an error to
-- use this lens with a value permission not of this form
conjAtomicPerm :: Int -> Lens' (ValuePerm a) (AtomicPerm a)
conjAtomicPerm i =
  lens
  (\p -> if i >= length (p ^. conjAtomicPerms) then
           error "conjAtomicPerm: index out of bounds"
         else (p ^. conjAtomicPerms) !! i)
  (\p pp ->
    -- FIXME: there has got to be a nicer, more lens-like way to do this
    let pps = p ^. conjAtomicPerms in
    if i >= length pps then
      error "conjAtomicPerm: index out of bounds"
    else set conjAtomicPerms (take i pps ++ (pp : drop (i+1) pps)) p)

-- | Add a new atomic permission to the end of the list of those contained in
-- the 'conjAtomicPerms' of a permission
addAtomicPerm :: AtomicPerm a -> ValuePerm a -> ValuePerm a
addAtomicPerm pp = over conjAtomicPerms (++ [pp])

-- | Delete the atomic permission at the given index from the list of those
-- contained in the 'conjAtomicPerms' of a permission
deleteAtomicPerm :: Int -> ValuePerm a -> ValuePerm a
deleteAtomicPerm i =
  over conjAtomicPerms (\pps ->
                         if i >= length pps then
                           error "deleteAtomicPerm: index out of bounds"
                         else take i pps ++ drop (i+1) pps)

-- | Lens for the LLVM pointer permissions in a 'ValPerm_Conj'; it is an error
-- to use this lens with a value permission not of this form
llvmPtrPerms :: Lens' (ValuePerm (LLVMPointerType w)) [LLVMPtrPerm w]
llvmPtrPerms = conjAtomicPerms

-- | Lens for the @i@th LLVM pointer permission of a 'ValPerm_Conj'
llvmPtrPerm :: Int -> Lens' (ValuePerm (LLVMPointerType w)) (LLVMPtrPerm w)
llvmPtrPerm = conjAtomicPerm

-- | Add a new 'LLVMPtrPerm' to the end of the list of those contained in the
-- 'llvmPtrPerms' of a permission
addLLVMPtrPerm :: LLVMPtrPerm w -> ValuePerm (LLVMPointerType w) ->
                  ValuePerm (LLVMPointerType w)
addLLVMPtrPerm pp = over llvmPtrPerms (++ [pp])

-- | Delete the 'LLVMPtrPerm' at the given index from the list of those
-- contained in the 'llvmPtrPerms' of a permission
deleteLLVMPtrPerm :: Int -> ValuePerm (LLVMPointerType w) ->
                     ValuePerm (LLVMPointerType w)
deleteLLVMPtrPerm i =
  over llvmPtrPerms (\pps ->
                      if i >= length pps then
                        error "deleteLLVMPtrPerm: index out of bounds"
                      else take i pps ++ drop (i+1) pps)

-- | Return the index of the last 'LLVMPtrPerm' of a permission
lastLLVMPtrPermIndex :: ValuePerm (LLVMPointerType w) -> Int
lastLLVMPtrPermIndex p =
  let len = length (p ^. llvmPtrPerms) in
  if len > 0 then len - 1 else error "lastLLVMPtrPerms: no pointer perms!"

-- | Create a list of pointer permissions needed in order to deallocate a frame
-- that has the given frame permissions. It is an error if any of the required
-- permissions are for LLVM words instead of pointers.
llvmFrameDeletionPerms :: (1 <= w, KnownNat w) => LLVMFramePerm w ->
                          Some DistPerms
llvmFrameDeletionPerms [] = Some DistPermsNil
llvmFrameDeletionPerms ((asLLVMOffset -> Just (x,_off), sz):fperm')
  | Some del_perms <- llvmFrameDeletionPerms fperm' =
    Some $ DistPermsCons del_perms x $ llvmBlockPermOfSize sz
llvmFrameDeletionPerms _ =
  error "llvmFrameDeletionPerms: unexpected LLVM word allocated in frame"

-- | Build a 'DistPerms' with just one permission
distPerms1 :: ExprVar a -> ValuePerm a -> DistPerms (RNil :> a)
distPerms1 x p = DistPermsCons DistPermsNil x p

-- | Build a 'DistPerms' with two permissions
distPerms2 :: ExprVar a1 -> ValuePerm a1 ->
              ExprVar a2 -> ValuePerm a2 -> DistPerms (RNil :> a1 :> a2)
distPerms2 x1 p1 x2 p2 = DistPermsCons (distPerms1 x1 p1) x2 p2

-- | Build a 'DistPerms' with three permissions
distPerms3 :: ExprVar a1 -> ValuePerm a1 -> ExprVar a2 -> ValuePerm a2 ->
              ExprVar a3 -> ValuePerm a3 -> DistPerms (RNil :> a1 :> a2 :> a3)
distPerms3 x1 p1 x2 p2 x3 p3 = DistPermsCons (distPerms2 x1 p1 x2 p2) x3 p3

-- | Get the first permission in a 'DistPerms'
distPermsHeadPerm :: DistPerms (ps :> a) -> ValuePerm a
distPermsHeadPerm (DistPermsCons _ _ p) = p

-- | Drop the last permission in a 'DistPerms'
distPermsSnoc :: DistPerms (ps :> a) -> DistPerms ps
distPermsSnoc (DistPermsCons ps _ _) = ps

-- | Map a function on permissions across a 'DistPerms'
mapDistPerms :: (forall a. ValuePerm a -> ValuePerm a) ->
                DistPerms ps -> DistPerms ps
mapDistPerms _ DistPermsNil = DistPermsNil
mapDistPerms f (DistPermsCons perms x p) =
  DistPermsCons (mapDistPerms f perms) x (f p)


-- | Create a sequence of @true@ permissions
trueValuePerms :: RAssign any ps -> ValuePerms ps
trueValuePerms MNil = ValPerms_Nil
trueValuePerms (ps :>: _) = ValPerms_Cons (trueValuePerms ps) ValPerm_True

-- | Create a list of @eq(xi)@ permissions from a list of variables @x1,x2,...@
eqValuePerms :: RAssign Name ps -> ValuePerms ps
eqValuePerms MNil = ValPerms_Nil
eqValuePerms (xs :>: x) =
  ValPerms_Cons (eqValuePerms xs) (ValPerm_Eq (PExpr_Var x))

-- | Append two lists of permissions
appendValuePerms :: ValuePerms ps1 -> ValuePerms ps2 -> ValuePerms (ps1 :++: ps2)
appendValuePerms ps1 ValPerms_Nil = ps1
appendValuePerms ps1 (ValPerms_Cons ps2 p) =
  ValPerms_Cons (appendValuePerms ps1 ps2) p

distPermsToProxies :: DistPerms ps -> RAssign Proxy ps
distPermsToProxies (DistPermsNil) = MNil
distPermsToProxies (DistPermsCons ps _ _) = distPermsToProxies ps :>: Proxy

mbDistPermsToProxies :: Mb ctx (DistPerms ps) -> RAssign Proxy ps
mbDistPermsToProxies mb_ps = case mbMatch mb_ps of
  [nuMP| DistPermsNil |] -> MNil
  [nuMP| DistPermsCons ps _ _ |] ->
    mbDistPermsToProxies ps :>: Proxy

-- | Extract the variables in a 'DistPerms'
distPermsVars :: DistPerms ps -> RAssign Name ps
distPermsVars DistPermsNil = MNil
distPermsVars (DistPermsCons ps x _) = distPermsVars ps :>: x

-- | Append two lists of distinguished permissions
appendDistPerms :: DistPerms ps1 -> DistPerms ps2 -> DistPerms (ps1 :++: ps2)
appendDistPerms ps1 DistPermsNil = ps1
appendDistPerms ps1 (DistPermsCons ps2 x p) =
  DistPermsCons (appendDistPerms ps1 ps2) x p

-- | Filter a list of distinguished permissions using a predicate
filterDistPerms :: (forall a. Name a -> ValuePerm a -> Bool) ->
                   DistPerms ps -> Some DistPerms
filterDistPerms _ DistPermsNil = Some DistPermsNil
filterDistPerms pred (DistPermsCons ps x p)
  | pred x p
  , Some ps' <- filterDistPerms pred ps = Some (DistPermsCons ps' x p)
filterDistPerms pred (DistPermsCons ps _ _) = filterDistPerms pred ps

-- | Build a list of distinguished permissions from a list of variables
buildDistPerms :: (forall a. Name a -> ValuePerm a) -> RAssign Name ps ->
                  DistPerms ps
buildDistPerms _ MNil = DistPermsNil
buildDistPerms f (ns :>: n) = DistPermsCons (buildDistPerms f ns) n (f n)

-- | Split a list of distinguished permissions into two
splitDistPerms :: f ps1 -> RAssign g ps2 -> DistPerms (ps1 :++: ps2) ->
                  (DistPerms ps1, DistPerms ps2)
splitDistPerms _ = helper where
  helper :: RAssign g ps2 -> DistPerms (ps1 :++: ps2) ->
            (DistPerms ps1, DistPerms ps2)
  helper MNil perms = (perms, DistPermsNil)
  helper (prxs :>: _) (DistPermsCons ps x p) =
    let (perms1, perms2) = helper prxs ps in
    (perms1, DistPermsCons perms2 x p)

-- | Split a list of value permissions in bindings into two
splitMbValuePerms :: f ps1 -> RAssign g ps2 ->
                     Mb vars (ValuePerms (ps1 :++: ps2)) ->
                     (Mb vars (ValuePerms ps1), Mb vars (ValuePerms ps2))
splitMbValuePerms _ MNil mb_perms =
  (mb_perms, fmap (const ValPerms_Nil) mb_perms)
splitMbValuePerms prx (ps2 :>: _) (mbMatch -> [nuMP| ValPerms_Cons mb_perms p |]) =
  let (ret1, ret2) = splitMbValuePerms prx ps2 mb_perms in
  (ret1, mbMap2 ValPerms_Cons ret2 p)

-- | Lens for the top permission in a 'DistPerms' stack
distPermsHead :: ExprVar a -> Lens' (DistPerms (ps :> a)) (ValuePerm a)
distPermsHead x =
  lens (\(DistPermsCons _ y p) ->
         if x == y then p else error "distPermsHead: incorrect variable name!")
  (\(DistPermsCons pstk y _) p ->
    if x == y then DistPermsCons pstk y p else
      error "distPermsHead: incorrect variable name!")

-- | The lens for the tail of a 'DistPerms' stack
distPermsTail :: Lens' (DistPerms (ps :> a)) (DistPerms ps)
distPermsTail =
  lens (\(DistPermsCons pstk _ _) -> pstk)
  (\(DistPermsCons _ x p) pstk -> DistPermsCons pstk x p)

-- | The lens for the nth permission in a 'DistPerms' stack
nthVarPerm :: Member ps a -> ExprVar a -> Lens' (DistPerms ps) (ValuePerm a)
nthVarPerm Member_Base x = distPermsHead x
nthVarPerm (Member_Step memb') x = distPermsTail . nthVarPerm memb' x

-- | Test if a permission can be copied, i.e., whether @p -o p*p@. This is true
-- iff @p@ does not contain any 'Write' modalities, any frame permissions, or
-- any lifetime ownership permissions. Note that this must be true for all
-- substitutions of free (permission or expression) variables, so free variables
-- can make a permission not copyable as well.
permIsCopyable :: ValuePerm a -> Bool
permIsCopyable (ValPerm_Eq _) = True
permIsCopyable (ValPerm_Or p1 p2) = permIsCopyable p1 && permIsCopyable p2
permIsCopyable (ValPerm_Exists mb_p) = mbLift $ fmap permIsCopyable mb_p
permIsCopyable (ValPerm_Named npn args _) =
  namedPermArgsAreCopyable (namedPermNameArgs npn) args
permIsCopyable (ValPerm_Var _ _) = False
permIsCopyable (ValPerm_Conj ps) = all atomicPermIsCopyable ps

-- | The same as 'permIsCopyable' except for atomic permissions
atomicPermIsCopyable :: AtomicPerm a -> Bool
atomicPermIsCopyable (Perm_LLVMField
                      (LLVMFieldPerm { llvmFieldRW = PExpr_Read,
                                       llvmFieldContents = p })) =
  permIsCopyable p
atomicPermIsCopyable (Perm_LLVMField _) = False
atomicPermIsCopyable (Perm_LLVMArray
                      (LLVMArrayPerm { llvmArrayFields = fs })) =
  all (atomicPermIsCopyable . llvmArrayFieldToAtomicPerm) fs
atomicPermIsCopyable (Perm_LLVMBlock (LLVMBlockPerm {..})) =
  llvmBlockRW == PExpr_Read && shapeIsCopyable llvmBlockRW llvmBlockShape
atomicPermIsCopyable (Perm_LLVMFree _) = True
atomicPermIsCopyable (Perm_LLVMFunPtr _ _) = True
atomicPermIsCopyable Perm_IsLLVMPtr = True
atomicPermIsCopyable (Perm_LLVMBlockShape sh) = shapeIsCopyable PExpr_Write sh
atomicPermIsCopyable (Perm_LLVMFrame _) = False
atomicPermIsCopyable (Perm_LOwned _ _) = False
atomicPermIsCopyable (Perm_LCurrent _) = True
atomicPermIsCopyable (Perm_Struct ps) = and $ RL.mapToList permIsCopyable ps
atomicPermIsCopyable (Perm_Fun _) = True
atomicPermIsCopyable (Perm_BVProp _) = True
atomicPermIsCopyable (Perm_NamedConj n args _) =
  namedPermArgsAreCopyable (namedPermNameArgs n) args

-- | 'permIsCopyable' for the arguments of a named permission
namedPermArgIsCopyable :: TypeRepr a -> PermExpr a -> Bool
namedPermArgIsCopyable RWModalityRepr PExpr_Read = True
namedPermArgIsCopyable RWModalityRepr _ = False
namedPermArgIsCopyable (ValuePermRepr _) (PExpr_ValPerm p) = permIsCopyable p
namedPermArgIsCopyable (ValuePermRepr _) (PExpr_Var _) = False
namedPermArgIsCopyable _ _ = True

-- | 'permIsCopyable' for an argument of a named permission
namedPermArgsAreCopyable :: CruCtx args -> PermExprs args -> Bool
namedPermArgsAreCopyable CruCtxNil PExprs_Nil = True
namedPermArgsAreCopyable (CruCtxCons tps tp) (PExprs_Cons args arg) =
  namedPermArgsAreCopyable tps args && namedPermArgIsCopyable tp arg

-- | Test if an LLVM shape corresponds to a copyable permission relative to the
-- given read/write modality
shapeIsCopyable :: PermExpr RWModalityType -> PermExpr (LLVMShapeType w) -> Bool
shapeIsCopyable _ (PExpr_Var _) = False
shapeIsCopyable _ PExpr_EmptyShape = True
shapeIsCopyable rw (PExpr_NamedShape maybe_rw' _ nmsh args) =
  case namedShapeBody nmsh of
    DefinedShapeBody _ ->
      let rw' = maybe rw id maybe_rw' in
      shapeIsCopyable rw' $ unfoldNamedShape nmsh args
    -- NOTE: we are assuming that opaque shapes are copyable iff their args are
    OpaqueShapeBody _ _ ->
      namedPermArgsAreCopyable (namedShapeArgs nmsh) args
    -- HACK: the real computation we want to perform is to assume nmsh is copyable
    -- and prove it is under that assumption; to accomplish this, we substitute
    -- the empty shape for the recursive shape
    RecShapeBody mb_sh _ _ _ ->
      shapeIsCopyable rw $ subst (substOfExprs (args :>: PExpr_EmptyShape)) mb_sh
shapeIsCopyable _ (PExpr_EqShape _) = True
shapeIsCopyable rw (PExpr_PtrShape maybe_rw' _ sh) =
  let rw' = maybe rw id maybe_rw' in
  rw' == PExpr_Read && shapeIsCopyable rw' sh
shapeIsCopyable _ (PExpr_FieldShape (LLVMFieldShape p)) = permIsCopyable p
shapeIsCopyable _ (PExpr_ArrayShape _ _ flds) =
  all (\(LLVMFieldShape p) -> permIsCopyable p) flds
shapeIsCopyable rw (PExpr_SeqShape sh1 sh2) =
  shapeIsCopyable rw sh1 && shapeIsCopyable rw sh2
shapeIsCopyable rw (PExpr_OrShape sh1 sh2) =
  shapeIsCopyable rw sh1 && shapeIsCopyable rw sh2
shapeIsCopyable rw (PExpr_ExShape mb_sh) =
  mbLift $ fmap (shapeIsCopyable rw) mb_sh


-- FIXME: need a traversal function for RAssign for the following two funs

-- | Convert an 'LOwnedPerms' list to a 'DistPerms'
lownedPermsToDistPerms :: LOwnedPerms ps -> Maybe (DistPerms ps)
lownedPermsToDistPerms MNil = Just MNil
lownedPermsToDistPerms (lops :>: lop) =
  (:>:) <$> lownedPermsToDistPerms lops <*> lownedPermVarAndPerm lop

-- | Convert the expressions of an 'LOwnedPerms' to variables, if possible
lownedPermsVars :: LOwnedPerms ps -> Maybe (RAssign Name ps)
lownedPermsVars MNil = Just MNil
lownedPermsVars (lops :>: lop) =
  (:>:) <$> lownedPermsVars lops <*> lownedPermVar lop

-- | Test if an 'LOwnedPerm' could help prove any of a list of permissions
lownedPermCouldProve :: LOwnedPerm a -> DistPerms ps -> Bool
lownedPermCouldProve (LOwnedPermField (PExpr_Var x) fp) ps =
  any (\case (llvmAtomicPermRange -> Just rng) ->
               bvCouldBeInRange (llvmFieldOffset fp) rng
             _ -> False) $
  varAtomicPermsInDistPerms x ps
lownedPermCouldProve (LOwnedPermBlock (PExpr_Var x) bp) ps =
  any (\case (llvmAtomicPermRange -> Just rng) ->
               bvRangesCouldOverlap (llvmBlockRange bp) rng
             _ -> False) $
  varAtomicPermsInDistPerms x ps
lownedPermCouldProve (LOwnedPermLifetime (PExpr_Var l) _ ps_out) ps =
  any (\case Perm_LOwned _ _ -> True
             _ -> False) (varAtomicPermsInDistPerms l ps) ||
  lownedPermsCouldProve ps_out ps
lownedPermCouldProve _ _ = False

-- | Test if an 'LOwnedPerms' list could help prove any of a list of permissions
lownedPermsCouldProve :: LOwnedPerms ps -> DistPerms ps' -> Bool
lownedPermsCouldProve lops ps =
  RL.foldr (\lop rest -> lownedPermCouldProve lop ps || rest) False lops


-- | Convert a 'FunPerm' in a name-binding to a 'FunPerm' that takes those bound
-- names as additional ghost arguments with the supplied input permissions and
-- no output permissions
mbFunPerm :: CruCtx ctx -> Mb ctx (ValuePerms ctx) ->
             Mb ctx (FunPerm ghosts args ret) ->
             FunPerm (ctx :++: ghosts) args ret
mbFunPerm ctx mb_ps (mbMatch -> [nuMP| FunPerm mb_ghosts mb_args mb_ret ps_in ps_out |]) =
  let ghosts = mbLift mb_ghosts
      args = mbLift mb_args
      ctx_perms = trueValuePerms $ cruCtxToTypes ctx
      arg_types = cruCtxToTypes args
      ghost_types = cruCtxToTypes ghosts
      prxys = mapRAssign (const Proxy) (RL.append ghost_types arg_types) in
  case RL.appendAssoc ctx ghosts arg_types of
    Refl ->
      FunPerm (appendCruCtx ctx ghosts) args (mbLift mb_ret)
      (mbCombine prxys $
       mbMap2 (\ps mb_ps_in -> fmap (RL.append ps) mb_ps_in) mb_ps ps_in)
      (fmap (RL.append ctx_perms) $
       mbCombine (prxys :>: Proxy) ps_out)

-- | Substitute ghost and regular arguments into a function permission to get
-- its input permissions for those arguments, where ghost arguments are given
-- both as variables and expressions to which those variables are instantiated.
-- For a 'FunPerm' of the form @(gctx). xs:ps -o xs:ps'@, return
--
-- > [gs/gctx]xs : [gexprs/gctx]ps, g1:eq(gexpr1), ..., gm:eq(gexprm)
funPermDistIns :: FunPerm ghosts args ret -> RAssign Name ghosts ->
                  PermExprs ghosts -> RAssign Name args ->
                  DistPerms ((ghosts :++: args) :++: ghosts)
funPermDistIns fun_perm ghosts gexprs args =
  appendDistPerms
  (valuePermsToDistPerms (RL.append ghosts args) $
   subst (appendSubsts (substOfExprs gexprs) (substOfVars args)) $
   funPermIns fun_perm)
  (eqDistPerms ghosts gexprs)

-- | Substitute ghost and regular arguments into a function permission to get
-- its input permissions for those arguments, where ghost arguments are given
-- both as variables and expressions to which those variables are instantiated.
-- For a 'FunPerm' of the form @(gctx). xs:ps -o xs:ps'@, return
--
-- > [gs/gctx]xs : [gexprs/gctx]ps'
funPermDistOuts :: FunPerm ghosts args ret -> RAssign Name ghosts ->
                   PermExprs ghosts -> RAssign Name (args :> ret) ->
                   DistPerms (ghosts :++: args :> ret)
funPermDistOuts fun_perm ghosts gexprs args_and_ret =
  valuePermsToDistPerms (RL.append ghosts args_and_ret) $
  subst (appendSubsts (substOfExprs gexprs) (substOfVars args_and_ret)) $
  funPermOuts fun_perm

-- | Unfold a recursive permission given a 'RecPerm' for it
unfoldRecPerm :: RecPerm b reach args a -> PermExprs args -> PermOffset a ->
                 ValuePerm a
unfoldRecPerm rp args off =
  offsetPerm off $ foldr1 ValPerm_Or $ map (subst (substOfExprs args)) $
  recPermCases rp

-- | Unfold a defined permission given arguments
unfoldDefinedPerm :: DefinedPerm b args a -> PermExprs args ->
                     PermOffset a -> ValuePerm a
unfoldDefinedPerm dp args off =
  offsetPerm off $ subst (substOfExprs args) (definedPermDef dp)

-- | Unfold a named permission as long as it is unfoldable
unfoldPerm :: NameSortCanFold ns ~ 'True => NamedPerm ns args a ->
              PermExprs args -> PermOffset a -> ValuePerm a
unfoldPerm (NamedPerm_Defined dp) = unfoldDefinedPerm dp
unfoldPerm (NamedPerm_Rec rp) = unfoldRecPerm rp

-- | Generic function to get free variables
class FreeVars a where
  freeVars :: a -> NameSet CrucibleType

-- | Get the free variables of an expression as an 'RAssign'
freeVarsRAssign :: FreeVars a => a -> Some (RAssign ExprVar)
freeVarsRAssign =
  foldl (\(Some ns) (SomeName n) -> Some (ns :>: n)) (Some MNil) . toList . freeVars

instance FreeVars a => FreeVars (Maybe a) where
  freeVars = maybe NameSet.empty freeVars

instance FreeVars a => FreeVars [a] where
  freeVars = foldr (NameSet.union . freeVars) NameSet.empty

instance (FreeVars a, FreeVars b) => FreeVars (a,b) where
  freeVars (a,b) = NameSet.union (freeVars a) (freeVars b)

instance FreeVars a => FreeVars (Mb ctx a) where
  freeVars = NameSet.liftNameSet . fmap freeVars

instance FreeVars (PermExpr a) where
  freeVars (PExpr_Var x) = NameSet.singleton x
  freeVars PExpr_Unit = NameSet.empty
  freeVars (PExpr_Bool _) = NameSet.empty
  freeVars (PExpr_Nat _) = NameSet.empty
  freeVars (PExpr_String _) = NameSet.empty
  freeVars (PExpr_BV factors _) = freeVars factors
  freeVars (PExpr_Struct elems) = freeVars elems
  freeVars PExpr_Always = NameSet.empty
  freeVars (PExpr_LLVMWord e) = freeVars e
  freeVars (PExpr_LLVMOffset ptr off) =
    NameSet.insert ptr (freeVars off)
  freeVars (PExpr_Fun _) = NameSet.empty
  freeVars PExpr_PermListNil = NameSet.empty
  freeVars (PExpr_PermListCons _ e p l) =
    NameSet.unions [freeVars e, freeVars p, freeVars l]
  freeVars (PExpr_RWModality _) = NameSet.empty
  freeVars PExpr_EmptyShape = NameSet.empty
  freeVars (PExpr_NamedShape rw l nmsh args) =
    NameSet.unions [freeVars rw, freeVars l, freeVars nmsh, freeVars args]
  freeVars (PExpr_EqShape b) = freeVars b
  freeVars (PExpr_PtrShape maybe_rw maybe_l sh) =
    NameSet.unions [freeVars maybe_rw, freeVars maybe_l, freeVars sh]
  freeVars (PExpr_FieldShape fld) = freeVars fld
  freeVars (PExpr_ArrayShape len _ flds) =
    NameSet.union (freeVars len) (freeVars flds)
  freeVars (PExpr_SeqShape sh1 sh2) =
    NameSet.union (freeVars sh1) (freeVars sh2)
  freeVars (PExpr_OrShape sh1 sh2) =
    NameSet.union (freeVars sh1) (freeVars sh2)
  freeVars (PExpr_ExShape mb_sh) = NameSet.liftNameSet $ fmap freeVars mb_sh
  freeVars (PExpr_ValPerm p) = freeVars p

instance FreeVars (BVFactor w) where
  freeVars (BVFactor _ x) = NameSet.singleton x

instance FreeVars (PermExprs as) where
  freeVars PExprs_Nil = NameSet.empty
  freeVars (PExprs_Cons es e) = NameSet.union (freeVars es) (freeVars e)

instance FreeVars (LLVMFieldShape w) where
  freeVars (LLVMFieldShape p) = freeVars p

instance FreeVars (BVRange w) where
  freeVars (BVRange off len) = NameSet.union (freeVars off) (freeVars len)

instance FreeVars (BVProp w) where
  freeVars (BVProp_Eq e1 e2) = NameSet.union (freeVars e1) (freeVars e2)
  freeVars (BVProp_Neq e1 e2) = NameSet.union (freeVars e1) (freeVars e2)
  freeVars (BVProp_ULt e1 e2) = NameSet.union (freeVars e1) (freeVars e2)
  freeVars (BVProp_ULeq e1 e2) = NameSet.union (freeVars e1) (freeVars e2)
  freeVars (BVProp_ULeq_Diff e1 e2 e3) =
    NameSet.unions [freeVars e1, freeVars e2, freeVars e3]

instance FreeVars (AtomicPerm tp) where
  freeVars (Perm_LLVMField fp) = freeVars fp
  freeVars (Perm_LLVMArray ap) = freeVars ap
  freeVars (Perm_LLVMBlock bp) = freeVars bp
  freeVars (Perm_LLVMFree e) = freeVars e
  freeVars (Perm_LLVMFunPtr _ fun_perm) = freeVars fun_perm
  freeVars Perm_IsLLVMPtr = NameSet.empty
  freeVars (Perm_LLVMBlockShape sh) = freeVars sh
  freeVars (Perm_LLVMFrame fperms) = freeVars $ map fst fperms
  freeVars (Perm_LOwned ps_in ps_out) =
    NameSet.union (freeVars ps_in) (freeVars ps_out)
  freeVars (Perm_LCurrent l) = freeVars l
  freeVars (Perm_Struct ps) = NameSet.unions $ RL.mapToList freeVars ps
  freeVars (Perm_Fun fun_perm) = freeVars fun_perm
  freeVars (Perm_BVProp prop) = freeVars prop
  freeVars (Perm_NamedConj _ args off) =
    NameSet.union (freeVars args) (freeVars off)

instance FreeVars (ValuePerm tp) where
  freeVars (ValPerm_Eq e) = freeVars e
  freeVars (ValPerm_Or p1 p2) = NameSet.union (freeVars p1) (freeVars p2)
  freeVars (ValPerm_Exists mb_p) =
    NameSet.liftNameSet $ fmap freeVars mb_p
  freeVars (ValPerm_Named _ args off) =
    NameSet.union (freeVars args) (freeVars off)
  freeVars (ValPerm_Var x off) = NameSet.insert x $ freeVars off
  freeVars (ValPerm_Conj ps) = freeVars ps

instance FreeVars (ValuePerms tps) where
  freeVars ValPerms_Nil = NameSet.empty
  freeVars (ValPerms_Cons ps p) = NameSet.union (freeVars ps) (freeVars p)

instance FreeVars (LLVMFieldPerm w sz) where
  freeVars (LLVMFieldPerm {..}) =
    NameSet.unions [freeVars llvmFieldRW, freeVars llvmFieldLifetime,
                    freeVars llvmFieldOffset, freeVars llvmFieldContents]

instance FreeVars (LLVMArrayField w) where
  freeVars (LLVMArrayField fp) = freeVars fp

instance FreeVars (LLVMArrayPerm w) where
  freeVars (LLVMArrayPerm {..}) =
    NameSet.unions [freeVars llvmArrayOffset,
                    freeVars llvmArrayLen,
                    freeVars llvmArrayFields,
                    freeVars llvmArrayBorrows]

instance FreeVars (LLVMArrayIndex w) where
  freeVars (LLVMArrayIndex cell _) = freeVars cell

instance FreeVars (LLVMArrayBorrow w) where
  freeVars (FieldBorrow ix) = freeVars ix
  freeVars (RangeBorrow rng) = freeVars rng

instance FreeVars (LLVMBlockPerm w) where
  freeVars (LLVMBlockPerm rw l off len sh) =
    NameSet.unions [freeVars rw, freeVars l, freeVars off,
                    freeVars len, freeVars sh]

instance FreeVars (PermOffset tp) where
  freeVars NoPermOffset = NameSet.empty
  freeVars (LLVMPermOffset e) = freeVars e

instance FreeVars (LOwnedPerm a) where
  freeVars (LOwnedPermField e fp) =
    NameSet.unions [freeVars e, freeVars fp]
  freeVars (LOwnedPermBlock e bp) =
    NameSet.unions [freeVars e, freeVars bp]
  freeVars (LOwnedPermLifetime e ps_in ps_out) =
    NameSet.unions [freeVars e, freeVars ps_in, freeVars ps_out]

instance FreeVars (LOwnedPerms ps) where
  freeVars = NameSet.unions . RL.mapToList freeVars

instance FreeVars (FunPerm ghosts args ret) where
  freeVars (FunPerm _ _ _ perms_in perms_out) =
    NameSet.union
    (NameSet.liftNameSet $ fmap freeVars perms_in)
    (NameSet.liftNameSet $ fmap freeVars perms_out)

instance FreeVars (NamedShape b args w) where
  freeVars (NamedShape _ _ body) = freeVars body

instance FreeVars (NamedShapeBody b args w) where
  freeVars (DefinedShapeBody mb_sh) = freeVars mb_sh
  freeVars (OpaqueShapeBody mb_len _) = freeVars mb_len
  freeVars (RecShapeBody mb_sh _ _ _) = freeVars mb_sh


-- | Test if an expression @e@ is a /determining/ expression, meaning that
-- proving @x:eq(e)@ will necessarily determine the values of the free variables
-- of @e@ in the sense of 'determinedVars'.
isDeterminingExpr :: PermExpr a -> Bool
isDeterminingExpr (PExpr_Var _) = True
isDeterminingExpr (PExpr_LLVMWord e) = isDeterminingExpr e
isDeterminingExpr (PExpr_BV [BVFactor _ _] _) =
  -- A linear expression N*x + M lets you solve for x when it is possible
  True
isDeterminingExpr (PExpr_ValPerm (ValPerm_Eq e)) = isDeterminingExpr e
isDeterminingExpr e =
  -- If an expression has no free variables then it vacuously determines all of
  -- its free variables
  NameSet.null $ freeVars e
  -- FIXME: consider adding a case for y &+ e

-- | Generic function to compute the /needed/ variables of a permission, meaning
-- those whose values must be determined before that permission can be
-- proved. This includes, e.g., all the offsets and lengths of field and array
-- permissions.
class NeededVars a where
  neededVars :: a -> NameSet CrucibleType

instance NeededVars a => NeededVars [a] where
  neededVars as = NameSet.unions $ map neededVars as

instance NeededVars (PermExpr a) where
  -- FIXME: need a better explanation of why this is the right answer...
  neededVars e = if isDeterminingExpr e then NameSet.empty else freeVars e

instance NeededVars (ValuePerm a) where
  neededVars (ValPerm_Eq e) = neededVars e
  neededVars (ValPerm_Or p1 p2) = NameSet.union (neededVars p1) (neededVars p2)
  neededVars (ValPerm_Exists mb_p) = NameSet.liftNameSet $ fmap neededVars mb_p
  neededVars p@(ValPerm_Named _ _ _) = freeVars p
  neededVars p@(ValPerm_Var _ _) = freeVars p
  neededVars (ValPerm_Conj ps) = neededVars ps

instance NeededVars (AtomicPerm a) where
  neededVars (Perm_LLVMField fp) = neededVars fp
  neededVars (Perm_LLVMArray ap) = neededVars ap
  neededVars (Perm_LLVMBlock bp) = neededVars bp
  neededVars (Perm_LLVMBlockShape _) = NameSet.empty
  neededVars p@(Perm_LOwned _ _) = freeVars p
  neededVars p = freeVars p

instance NeededVars (LLVMFieldPerm w sz) where
  neededVars (LLVMFieldPerm {..}) =
    NameSet.unions [freeVars llvmFieldOffset, neededVars llvmFieldRW,
                    neededVars llvmFieldLifetime, neededVars llvmFieldContents]

instance NeededVars (LLVMArrayField w) where
  neededVars (LLVMArrayField fp) = neededVars fp

instance NeededVars (LLVMArrayPerm w) where
  neededVars (LLVMArrayPerm {..}) =
    NameSet.unions [freeVars llvmArrayOffset, freeVars llvmArrayLen,
                    freeVars llvmArrayBorrows, neededVars llvmArrayFields]

instance NeededVars (LLVMBlockPerm w) where
  neededVars (LLVMBlockPerm {..}) =
    NameSet.unions [neededVars llvmBlockRW, neededVars llvmBlockLifetime,
                    freeVars llvmBlockOffset, freeVars llvmBlockLen]

instance NeededVars (ValuePerms as) where
  neededVars =
    foldValuePerms (\vars p ->
                     NameSet.union vars (neededVars p)) NameSet.empty

instance NeededVars (DistPerms as) where
  neededVars =
    foldDistPerms (\vars _ p ->
                    NameSet.union vars (neededVars p)) NameSet.empty


-- | Change all pointer shapes that are associated with the current lifetime of
-- that shape (i.e., that are not inside a pointer shape with an explicit
-- lifetime) to 'PExpr_Read'.
readOnlyShape :: PermExpr (LLVMShapeType w) -> PermExpr (LLVMShapeType w)
readOnlyShape e@(PExpr_Var _) = e
readOnlyShape PExpr_EmptyShape = PExpr_EmptyShape
readOnlyShape (PExpr_NamedShape _ l nmsh args) =
  PExpr_NamedShape (Just PExpr_Read) l nmsh args
readOnlyShape e@(PExpr_EqShape _) = e
readOnlyShape e@(PExpr_PtrShape _ (Just _) _) = e
readOnlyShape (PExpr_PtrShape _ Nothing sh) =
  PExpr_PtrShape (Just PExpr_Read) Nothing $ readOnlyShape sh
readOnlyShape e@(PExpr_FieldShape _) = e
readOnlyShape e@(PExpr_ArrayShape _ _ _) =
  -- FIXME: when array shapes contain lists of shapes instead of lists of
  -- permissions, this needs to map readOnlyShape to all of those shapes
  e
readOnlyShape (PExpr_SeqShape sh1 sh2) =
  PExpr_SeqShape (readOnlyShape sh1) (readOnlyShape sh2)
readOnlyShape (PExpr_OrShape sh1 sh2) =
  PExpr_OrShape (readOnlyShape sh1) (readOnlyShape sh2)
readOnlyShape (PExpr_ExShape mb_sh) =
  PExpr_ExShape $ fmap readOnlyShape mb_sh


----------------------------------------------------------------------
-- * Generalized Substitution
----------------------------------------------------------------------

-- FIXME: these two EFQ proofs may no longer be needed...?
noTypesInExprCtx :: forall (ctx :: RList CrucibleType) (a :: Type) b.
                    Member ctx a -> b
noTypesInExprCtx (Member_Step ctx) = noTypesInExprCtx ctx

noExprsInTypeCtx :: forall (ctx :: RList Type) (a :: CrucibleType) b.
                    Member ctx a -> b
noExprsInTypeCtx (Member_Step ctx) = noExprsInTypeCtx ctx
-- No case for Member_Base

-- | Defines a substitution type @s@ that supports substituting into expression
-- and permission variables in a given monad @m@
class MonadBind m => SubstVar s m | s -> m where
  -- extSubst :: s ctx -> ExprVar a -> s (ctx :> a)
  substExprVar :: s ctx -> Mb ctx (ExprVar a) -> m (PermExpr a)

substPermVar :: SubstVar s m => s ctx -> Mb ctx (PermVar a) -> m (ValuePerm a)
substPermVar s mb_x =
  substExprVar s mb_x >>= \e ->
  case e of
    PExpr_Var x -> return $ ValPerm_Var x NoPermOffset
    PExpr_ValPerm p -> return p

-- | Generalized notion of substitution, which says that substitution type @s@
-- supports substituting into type @a@ in monad @m@
class SubstVar s m => Substable s a m where
  genSubst :: s ctx -> Mb ctx a -> m a

-- | A version of 'Substable' for type functors
class SubstVar s m => Substable1 s f m where
  genSubst1 :: s ctx -> Mb ctx (f a) -> m (f a)

instance SubstVar s m => Substable s Integer m where
  genSubst _ mb_i = return $ mbLift mb_i

instance (NuMatching a, Substable s a m) => Substable s [a] m where
  genSubst s as = mapM (genSubst s) (mbList as)

instance (NuMatching a, Substable s a m) => Substable s (NonEmpty a) m where
  genSubst s (mbMatch -> [nuMP| x :| xs |]) =
    (:|) <$> genSubst s x <*> genSubst s xs

instance (Substable s a m, Substable s b m) => Substable s (a,b) m where
  genSubst s ab = (,) <$> genSubst s (fmap fst ab) <*> genSubst s (fmap snd ab)

instance (Substable s a m,
          Substable s b m, Substable s c m) => Substable s (a,b,c) m where
  genSubst s abc =
    (,,) <$> genSubst s (fmap (\(a,_,_) -> a) abc)
    <*> genSubst s (fmap (\(_,b,_) -> b) abc)
    <*> genSubst s (fmap (\(_,_,c) -> c) abc)

instance (Substable s a m, Substable s b m,
          Substable s c m, Substable s d m) => Substable s (a,b,c,d) m where
  genSubst s abcd =
    (,,,) <$> genSubst s (fmap (\(a,_,_,_) -> a) abcd)
          <*> genSubst s (fmap (\(_,b,_,_) -> b) abcd)
          <*> genSubst s (fmap (\(_,_,c,_) -> c) abcd)
          <*> genSubst s (fmap (\(_,_,_,d) -> d) abcd)

instance (NuMatching a, Substable s a m) => Substable s (Maybe a) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| Just a |] -> Just <$> genSubst s a
    [nuMP| Nothing |] -> return Nothing

instance {-# INCOHERENT #-} (Given (RAssign Proxy ctx), Substable s a m, NuMatching a) => Substable s (Mb ctx a) m where
   genSubst = genSubstMb given

instance {-# INCOHERENT #-} (Substable s a m, NuMatching a) => Substable s (Mb RNil a) m where
   genSubst = genSubstMb RL.typeCtxProxies

instance {-# INCOHERENT #-} (Substable s a m, NuMatching a) => Substable s (Binding c a) m where
   genSubst = genSubstMb RL.typeCtxProxies

genSubstMb ::
  Substable s a m =>
  NuMatching a =>
  RAssign Proxy ctx ->
  s ctx' -> Mb ctx' (Mb ctx a) -> m (Mb ctx a)
genSubstMb p s mbmb = mbM (fmap (genSubst s) (mbSwap p mbmb))

instance SubstVar s m => Substable s (Member ctx a) m where
  genSubst _ mb_memb = return $ mbLift mb_memb

instance (NuMatchingAny1 f, Substable1 s f m) =>
         Substable s (RAssign f ctx) m where
  genSubst s mb_xs = case mbMatch mb_xs of
    [nuMP| MNil |] -> return MNil
    [nuMP| xs :>: x |] -> (:>:) <$> genSubst s xs <*> genSubst1 s x

instance (NuMatchingAny1 f, Substable1 s f m) =>
         Substable s (Assignment f ctx) m where
  genSubst s mb_assign =
    case mbMatch $ fmap viewAssign mb_assign of
      [nuMP| AssignEmpty |] -> return $ Ctx.empty
      [nuMP| AssignExtend asgn' x |] ->
        Ctx.extend <$> genSubst s asgn' <*> genSubst1 s x

instance SubstVar s m => Substable s (a :~: b) m where
  genSubst _ = return . mbLift

instance SubstVar s m => Substable1 s ((:~:) a) m where
  genSubst1 _ = return . mbLift

-- | Helper function to substitute into 'BVFactor's
substBVFactor :: SubstVar s m => s ctx -> Mb ctx (BVFactor w) ->
                 m (PermExpr (BVType w))
substBVFactor s (mbMatch -> [nuMP| BVFactor (BV.BV i) x |]) =
  bvMult (mbLift i) <$> substExprVar s x

instance SubstVar s m =>
         Substable s (NatRepr n) m where
  genSubst _ = return . mbLift

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (ExprVar a) m where
  genSubst s mb_x = return $ varSubstVar s mb_x

instance SubstVar PermVarSubst m => Substable1 PermVarSubst ExprVar m where
  genSubst1 = genSubst

instance SubstVar s m => Substable s (PermExpr a) m where
  genSubst s mb_expr = case mbMatch mb_expr of
    [nuMP| PExpr_Var x |] -> substExprVar s x
    [nuMP| PExpr_Unit |] -> return $ PExpr_Unit
    [nuMP| PExpr_Bool b |] -> return $ PExpr_Bool $ mbLift b
    [nuMP| PExpr_Nat n |] -> return $ PExpr_Nat $ mbLift n
    [nuMP| PExpr_String str |] -> return $ PExpr_String $ mbLift str
    [nuMP| PExpr_BV factors off |] ->
      foldr bvAdd (PExpr_BV [] (mbLift off)) <$>
      mapM (substBVFactor s) (mbList factors)
    [nuMP| PExpr_Struct args |] ->
      PExpr_Struct <$> genSubst s args
    [nuMP| PExpr_Always |] -> return PExpr_Always
    [nuMP| PExpr_LLVMWord e |] ->
      PExpr_LLVMWord <$> genSubst s e
    [nuMP| PExpr_LLVMOffset x off |] ->
      addLLVMOffset <$> substExprVar s x <*> genSubst s off
    [nuMP| PExpr_Fun fh |] ->
      return $ PExpr_Fun $ mbLift fh
    [nuMP| PExpr_PermListNil |] ->
      return $ PExpr_PermListNil
    [nuMP| PExpr_PermListCons tp e p l |] ->
      PExpr_PermListCons (mbLift tp) <$> genSubst s e <*> genSubst s p
                                     <*> genSubst s l
    [nuMP| PExpr_RWModality rw |] ->
      return $ PExpr_RWModality $ mbLift rw
    [nuMP| PExpr_EmptyShape |] -> return PExpr_EmptyShape
    [nuMP| PExpr_NamedShape rw l nmsh args |] ->
      PExpr_NamedShape <$> genSubst s rw <*> genSubst s l <*> genSubst s nmsh
                       <*> genSubst s args
    [nuMP| PExpr_EqShape b |] ->
      PExpr_EqShape <$> genSubst s b
    [nuMP| PExpr_PtrShape maybe_rw maybe_l sh |] ->
      PExpr_PtrShape <$> genSubst s maybe_rw <*> genSubst s maybe_l
                     <*> genSubst s sh
    [nuMP| PExpr_FieldShape sh |] ->
      PExpr_FieldShape <$> genSubst s sh
    [nuMP| PExpr_ArrayShape len stride flds |] ->
      PExpr_ArrayShape <$> genSubst s len <*> return (mbLift stride)
                       <*> genSubst s flds
    [nuMP| PExpr_SeqShape sh1 sh2 |] ->
      PExpr_SeqShape <$> genSubst s sh1 <*> genSubst s sh2
    [nuMP| PExpr_OrShape sh1 sh2 |] ->
      PExpr_OrShape <$> genSubst s sh1 <*> genSubst s sh2
    [nuMP| PExpr_ExShape mb_sh |] ->
      PExpr_ExShape <$> genSubstMb RL.typeCtxProxies s mb_sh
    [nuMP| PExpr_ValPerm p |] ->
      PExpr_ValPerm <$> genSubst s p

instance SubstVar s m => Substable1 s PermExpr m where
  genSubst1 = genSubst

instance SubstVar s m => Substable s (BVRange w) m where
  genSubst s (mbMatch -> [nuMP| BVRange e1 e2 |]) =
    BVRange <$> genSubst s e1 <*> genSubst s e2

instance SubstVar s m => Substable s (BVProp w) m where
  genSubst s mb_prop = case mbMatch mb_prop of
    [nuMP| BVProp_Eq e1 e2 |] ->
      BVProp_Eq <$> genSubst s e1 <*> genSubst s e2
    [nuMP| BVProp_Neq e1 e2 |] ->
      BVProp_Neq <$> genSubst s e1 <*> genSubst s e2
    [nuMP| BVProp_ULt e1 e2 |] ->
      BVProp_ULt <$> genSubst s e1 <*> genSubst s e2
    [nuMP| BVProp_ULeq e1 e2 |] ->
      BVProp_ULeq <$> genSubst s e1 <*> genSubst s e2
    [nuMP| BVProp_ULeq_Diff e1 e2 e3 |] ->
      BVProp_ULeq_Diff <$> genSubst s e1 <*> genSubst s e2 <*> genSubst s e3

instance SubstVar s m => Substable s (AtomicPerm a) m where
  genSubst s mb_p = case mbMatch mb_p of
    [nuMP| Perm_LLVMField fp |] -> Perm_LLVMField <$> genSubst s fp
    [nuMP| Perm_LLVMArray ap |] -> Perm_LLVMArray <$> genSubst s ap
    [nuMP| Perm_LLVMBlock bp |] -> Perm_LLVMBlock <$> genSubst s bp
    [nuMP| Perm_LLVMFree e |] -> Perm_LLVMFree <$> genSubst s e
    [nuMP| Perm_LLVMFunPtr tp p |] ->
      Perm_LLVMFunPtr (mbLift tp) <$> genSubst s p
    [nuMP| Perm_IsLLVMPtr |] -> return Perm_IsLLVMPtr
    [nuMP| Perm_LLVMBlockShape sh |] ->
      Perm_LLVMBlockShape <$> genSubst s sh
    [nuMP| Perm_LLVMFrame fp |] -> Perm_LLVMFrame <$> genSubst s fp
    [nuMP| Perm_LOwned ps_in ps_out |] ->
      Perm_LOwned <$> genSubst s ps_in <*> genSubst s ps_out
    [nuMP| Perm_LCurrent e |] -> Perm_LCurrent <$> genSubst s e
    [nuMP| Perm_Struct tps |] -> Perm_Struct <$> genSubst s tps
    [nuMP| Perm_Fun fperm |] -> Perm_Fun <$> genSubst s fperm
    [nuMP| Perm_BVProp prop |] -> Perm_BVProp <$> genSubst s prop
    [nuMP| Perm_NamedConj n args off |] ->
      Perm_NamedConj (mbLift n) <$> genSubst s args <*> genSubst s off

instance SubstVar s m => Substable s (NamedShape b args w) m where
  genSubst s (mbMatch -> [nuMP| NamedShape str args body |]) =
    NamedShape (mbLift str) (mbLift args) <$> genSubstNSB (cruCtxProxies (mbLift args)) s body

genSubstNSB ::
  SubstVar s m =>
  RAssign Proxy args ->
  s ctx -> Mb ctx (NamedShapeBody b args w) -> m (NamedShapeBody b args w)
genSubstNSB px s mb_body = case mbMatch mb_body of
    [nuMP| DefinedShapeBody mb_sh |] ->
      DefinedShapeBody <$> genSubstMb px s mb_sh
    [nuMP| OpaqueShapeBody mb_len trans_id |] ->
      OpaqueShapeBody <$> genSubstMb px s mb_len <*> return (mbLift trans_id)
    [nuMP| RecShapeBody mb_sh trans_id fold_id unfold_id |] ->
      RecShapeBody <$> genSubstMb (px :>: Proxy) s mb_sh
                   <*> return (mbLift trans_id)
                   <*> return (mbLift fold_id)
                   <*> return (mbLift unfold_id)

instance SubstVar s m => Substable s (NamedPermName ns args a) m where
  genSubst _ mb_rpn = return $ mbLift mb_rpn

instance SubstVar s m => Substable s (PermOffset a) m where
  genSubst s mb_off = case mbMatch mb_off of
    [nuMP| NoPermOffset |] -> return NoPermOffset
    [nuMP| LLVMPermOffset e |] -> mkLLVMPermOffset <$> genSubst s e

instance SubstVar s m => Substable s (NamedPerm ns args a) m where
  genSubst s mb_np = case mbMatch mb_np of
    [nuMP| NamedPerm_Opaque  p |] -> NamedPerm_Opaque  <$> genSubst s p
    [nuMP| NamedPerm_Rec     p |] -> NamedPerm_Rec     <$> genSubst s p
    [nuMP| NamedPerm_Defined p |] -> NamedPerm_Defined <$> genSubst s p

instance SubstVar s m => Substable s (OpaquePerm ns args a) m where
  genSubst _ (mbMatch -> [nuMP| OpaquePerm n i |]) =
    return $ OpaquePerm (mbLift n) (mbLift i)

instance SubstVar s m => Substable s (RecPerm ns reach args a) m where
  genSubst s (mbMatch -> [nuMP| RecPerm rpn dt_i f_i u_i reachMeths cases |]) =
    RecPerm (mbLift rpn) (mbLift dt_i) (mbLift f_i) (mbLift u_i)
            (mbLift reachMeths) <$> mapM (genSubstMb (cruCtxProxies (mbLift (fmap namedPermNameArgs rpn))) s) (mbList cases)

instance SubstVar s m => Substable s (DefinedPerm ns args a) m where
  genSubst s (mbMatch -> [nuMP| DefinedPerm n p |]) =
    DefinedPerm (mbLift n) <$> genSubstMb (cruCtxProxies (mbLift (fmap namedPermNameArgs n))) s p

instance SubstVar s m => Substable s (ValuePerm a) m where
  genSubst s mb_p = case mbMatch mb_p of
    [nuMP| ValPerm_Eq e |] -> ValPerm_Eq <$> genSubst s e
    [nuMP| ValPerm_Or p1 p2 |] ->
      ValPerm_Or <$> genSubst s p1 <*> genSubst s p2
    [nuMP| ValPerm_Exists p |] ->
      -- FIXME: maybe we don't need extSubst at all, but can just use the
      -- Substable instance for Mb ctx a from above
      ValPerm_Exists <$> genSubstMb RL.typeCtxProxies s p
      -- nuM (\x -> genSubst (extSubst s x) $ mbCombine p)
    [nuMP| ValPerm_Named n args off |] ->
      ValPerm_Named (mbLift n) <$> genSubst s args <*> genSubst s off
    [nuMP| ValPerm_Var mb_x mb_off |] ->
      offsetPerm <$> genSubst s mb_off <*> substPermVar s mb_x
    [nuMP| ValPerm_Conj aps |] ->
      ValPerm_Conj <$> mapM (genSubst s) (mbList aps)

instance SubstVar s m => Substable1 s ValuePerm m where
  genSubst1 = genSubst

{-
instance SubstVar s m => Substable s (ValuePerms as) m where
  genSubst s mb_ps = case mbMatch mb_ps of
    [nuMP| ValPerms_Nil |] -> return ValPerms_Nil
    [nuMP| ValPerms_Cons ps p |] ->
      ValPerms_Cons <$> genSubst s ps <*> genSubst s p
-}

instance SubstVar s m => Substable s RWModality m where
  genSubst _ mb_rw = case mbMatch mb_rw of
    [nuMP| Write |] -> return Write
    [nuMP| Read |] -> return Read

instance SubstVar s m => Substable s (LLVMFieldPerm w sz) m where
  genSubst s (mbMatch -> [nuMP| LLVMFieldPerm rw ls off p |]) =
    LLVMFieldPerm <$> genSubst s rw <*> genSubst s ls <*>
                      genSubst s off <*> genSubst s p

instance SubstVar s m => Substable s (LLVMArrayField w) m where
  genSubst s (mbMatch -> [nuMP| LLVMArrayField fp |]) =
    LLVMArrayField <$> genSubst s fp

instance SubstVar s m => Substable s (LLVMArrayPerm w) m where
  genSubst s (mbMatch -> [nuMP| LLVMArrayPerm off len stride pps bs |]) =
    LLVMArrayPerm <$> genSubst s off <*> genSubst s len <*>
    return (mbLift stride) <*> mapM (genSubst s) (mbList pps)
    <*> mapM (genSubst s) (mbList bs)

instance SubstVar s m => Substable s (LLVMArrayIndex w) m where
  genSubst s (mbMatch -> [nuMP| LLVMArrayIndex ix fld_num |]) =
    LLVMArrayIndex <$> genSubst s ix <*> return (mbLift fld_num)

instance SubstVar s m => Substable s (LLVMArrayBorrow w) m where
  genSubst s mb_borrow = case mbMatch mb_borrow of
    [nuMP| FieldBorrow ix |] -> FieldBorrow <$> genSubst s ix
    [nuMP| RangeBorrow r |] -> RangeBorrow <$> genSubst s r

instance SubstVar s m => Substable s (LLVMBlockPerm w) m where
  genSubst s (mbMatch -> [nuMP| LLVMBlockPerm rw l off len sh |]) =
    LLVMBlockPerm <$> genSubst s rw <*> genSubst s l <*> genSubst s off
    <*> genSubst s len <*> genSubst s sh

instance SubstVar s m => Substable s (LLVMFieldShape w) m where
  genSubst s (mbMatch -> [nuMP| LLVMFieldShape p |]) =
    LLVMFieldShape <$> genSubst s p

instance SubstVar s m => Substable s (LOwnedPerm a) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| LOwnedPermField e fp |] ->
      LOwnedPermField <$> genSubst s e <*> genSubst s fp
    [nuMP| LOwnedPermBlock e bp |] ->
      LOwnedPermBlock <$> genSubst s e <*> genSubst s bp
    [nuMP| LOwnedPermLifetime e ps_in ps_out |] ->
      LOwnedPermLifetime <$> genSubst s e <*> genSubst s ps_in
                         <*> genSubst s ps_out

instance SubstVar s m => Substable1 s LOwnedPerm m where
  genSubst1 = genSubst

instance SubstVar s m => Substable s (FunPerm ghosts args ret) m where
  genSubst s (mbMatch -> [nuMP| FunPerm ghosts args ret perms_in perms_out |]) =
    let gpx = mbLift ghosts
        apx = mbLift args
        rpx = mbLift ret
        gapx = RL.append (cruCtxProxies gpx) (cruCtxProxies apx) in
    FunPerm gpx apx rpx
    <$> genSubstMb gapx s perms_in
    <*> genSubstMb (gapx :>: Proxy) s perms_out

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (LifetimeCurrentPerms ps) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| AlwaysCurrentPerms |] -> return AlwaysCurrentPerms
    [nuMP| LOwnedCurrentPerms l ps_in ps_out |] ->
      LOwnedCurrentPerms <$> genSubst s l <*> genSubst s ps_in
                         <*> genSubst s ps_out
    [nuMP| CurrentTransPerms ps l |] ->
      CurrentTransPerms <$> genSubst s ps <*> genSubst s l

instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (VarAndPerm a) m where
  genSubst s (mbMatch -> [nuMP| VarAndPerm x p |]) =
    VarAndPerm <$> genSubst s x <*> genSubst s p

instance SubstVar PermVarSubst m => Substable1 PermVarSubst VarAndPerm m where
  genSubst1 = genSubst

instance Substable1 s f m => Substable1 s (Typed f) m where
  genSubst1 s mb_typed =
    Typed (mbLift $ fmap typedType mb_typed) <$>
    genSubst1 s (fmap typedObj mb_typed)

{-
instance SubstVar PermVarSubst m =>
         Substable PermVarSubst (DistPerms ps) m where
  genSubst s mb_dperms = case mbMatch mb_dperms of
    [nuMP| DistPermsNil |] -> return DistPermsNil
    [nuMP| DistPermsCons dperms' x p |] ->
      DistPermsCons <$> genSubst s dperms' <*>
      return (varSubstVar s x) <*> genSubst s p
-}

instance SubstVar s m => Substable s (LifetimeFunctor args a) m where
  genSubst s mb_x = case mbMatch mb_x of
    [nuMP| LTFunctorField off p |] ->
      LTFunctorField <$> genSubst s off <*> genSubst s p
    [nuMP| LTFunctorBlock off len sh |] ->
      LTFunctorBlock <$> genSubst s off <*> genSubst s len <*> genSubst s sh


----------------------------------------------------------------------
-- * Expression Substitutions
----------------------------------------------------------------------

-- | A substitution assigns a permission expression to each bound name in a
-- name-binding context
newtype PermSubst ctx =
  PermSubst { unPermSubst :: RAssign PermExpr ctx }

emptySubst :: PermSubst RNil
emptySubst = PermSubst RL.empty

consSubst :: PermSubst ctx -> PermExpr a -> PermSubst (ctx :> a)
consSubst (PermSubst elems) e = PermSubst (elems :>: e)

singletonSubst :: PermExpr a -> PermSubst (RNil :> a)
singletonSubst e = PermSubst (RL.empty :>: e)

appendSubsts :: PermSubst ctx1 -> PermSubst ctx2 -> PermSubst (ctx1 :++: ctx2)
appendSubsts (PermSubst es1) (PermSubst es2) = PermSubst $ RL.append es1 es2

substOfVars :: RAssign ExprVar ctx -> PermSubst ctx
substOfVars = PermSubst . RL.map PExpr_Var

substOfExprs :: PermExprs ctx -> PermSubst ctx
substOfExprs PExprs_Nil = PermSubst MNil
substOfExprs (PExprs_Cons es e) = consSubst (substOfExprs es) e

-- FIXME: Maybe PermSubst should just be PermExprs?
exprsOfSubst :: PermSubst ctx -> PermExprs ctx
exprsOfSubst (PermSubst MNil) = PExprs_Nil
exprsOfSubst (PermSubst (es :>: e)) =
  PExprs_Cons (exprsOfSubst $ PermSubst es) e

substLookup :: PermSubst ctx -> Member ctx a -> PermExpr a
substLookup (PermSubst m) memb = RL.get memb m

noPermsInCruCtx :: forall (ctx :: RList CrucibleType) (a :: CrucibleType) b.
                   Member ctx (ValuePerm a) -> b
noPermsInCruCtx (Member_Step ctx) = noPermsInCruCtx ctx
-- No case for Member_Base

instance SubstVar PermSubst Identity where
  -- extSubst (PermSubst elems) x = PermSubst $ elems :>: PExpr_Var x
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> return $ substLookup s memb
      Right y -> return $ PExpr_Var y
  {-
  substPermVar s mb_x =
    case mbNameBoundP mb_x of
      Left memb -> noTypesInExprCtx memb
      Right x -> return $ ValPerm_Var x -}

-- | Apply a substitution to an object
subst :: Substable PermSubst a Identity => PermSubst ctx -> Mb ctx a -> a
subst s mb = runIdentity $ genSubst s mb

-- | Substitute a single expression into an object
subst1 :: Substable PermSubst a Identity => PermExpr b -> Binding b a -> a
subst1 e = subst (singletonSubst e)


----------------------------------------------------------------------
-- * Variable Substitutions
----------------------------------------------------------------------

-- FIXME HERE: PermVarSubst and other types should just be instances of a
-- RAssign, except it is annoying to build NuMatching instances for RAssign
-- because there are different ways one might do it, so we need to use
-- OVERLAPPING and/or INCOHERENT pragmas for them

-- | Like a substitution but assigns variables instead of arbitrary expressions
-- to bound variables
data PermVarSubst (ctx :: RList CrucibleType) where
  PermVarSubst_Nil :: PermVarSubst RNil
  PermVarSubst_Cons :: PermVarSubst ctx -> Name tp -> PermVarSubst (ctx :> tp)

emptyVarSubst :: PermVarSubst RNil
emptyVarSubst = PermVarSubst_Nil

singletonVarSubst :: ExprVar a -> PermVarSubst (RNil :> a)
singletonVarSubst x = PermVarSubst_Cons emptyVarSubst x

consVarSubst :: PermVarSubst ctx -> ExprVar a -> PermVarSubst (ctx :> a)
consVarSubst = PermVarSubst_Cons

permVarSubstOfNames :: RAssign Name ctx -> PermVarSubst ctx
permVarSubstOfNames MNil = PermVarSubst_Nil
permVarSubstOfNames (ns :>: n) = PermVarSubst_Cons (permVarSubstOfNames ns) n

permVarSubstToNames :: PermVarSubst ctx -> RAssign Name ctx
permVarSubstToNames PermVarSubst_Nil = MNil
permVarSubstToNames (PermVarSubst_Cons s n) = permVarSubstToNames s :>: n

varSubstLookup :: PermVarSubst ctx -> Member ctx a -> ExprVar a
varSubstLookup (PermVarSubst_Cons _ x) Member_Base = x
varSubstLookup (PermVarSubst_Cons s _) (Member_Step memb) =
  varSubstLookup s memb

appendVarSubsts :: PermVarSubst ctx1 -> PermVarSubst ctx2 ->
                   PermVarSubst (ctx1 :++: ctx2)
appendVarSubsts es1 PermVarSubst_Nil = es1
appendVarSubsts es1 (PermVarSubst_Cons es2 x) =
  PermVarSubst_Cons (appendVarSubsts es1 es2) x

-- | Convert a 'PermVarSubst' to a 'PermSubst'
permVarSubstToSubst :: PermVarSubst ctx -> PermSubst ctx
permVarSubstToSubst s = PermSubst $ RL.map PExpr_Var $ permVarSubstToNames s

varSubstVar :: PermVarSubst ctx -> Mb ctx (ExprVar a) -> ExprVar a
varSubstVar s mb_x =
  case mbNameBoundP mb_x of
    Left memb -> varSubstLookup s memb
    Right x -> x

instance SubstVar PermVarSubst Identity where
  -- extSubst (PermVarSubst elems) x = PermVarSubst $ elems :>: x
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> return $ PExpr_Var $ varSubstLookup s memb
      Right y -> return $ PExpr_Var y
  {-
  substPermVar s mb_x =
    case mbNameBoundP mb_x of
      Left memb -> noTypesInExprCtx memb
      Right x -> return $ ValPerm_Var x -}

-- | Wrapper function to apply a renamionmg to an expression type
varSubst :: Substable PermVarSubst a Identity => PermVarSubst ctx ->
            Mb ctx a -> a
varSubst s mb = runIdentity $ genSubst s mb

-- | Build a list of all possible 'PermVarSubst's of variables in a 'NameMap'
-- for variables listed in a 'CruCtx'
allPermVarSubsts :: NameMap TypeRepr -> CruCtx ctx -> [PermVarSubst ctx]
allPermVarSubsts nmap = helper (NameMap.assocs nmap) where
  helper :: [NameAndElem TypeRepr] -> CruCtx ctx -> [PermVarSubst ctx]
  helper _ CruCtxNil = return emptyVarSubst
  helper ns_ts (CruCtxCons ctx tp) =
    helper ns_ts ctx >>= \sbst ->
    map (consVarSubst sbst) (getVarsOfType ns_ts tp)
  getVarsOfType :: [NameAndElem TypeRepr] -> TypeRepr tp -> [Name tp]
  getVarsOfType [] _ = []
  getVarsOfType (NameAndElem n tp':ns_ts) tp
    | Just Refl <- testEquality tp tp' = n : (getVarsOfType ns_ts tp)
  getVarsOfType (_:ns_ts) tp = getVarsOfType ns_ts tp


----------------------------------------------------------------------
-- * Partial Substitutions
----------------------------------------------------------------------

-- | An element of a partial substitution = maybe an expression
newtype PSubstElem a = PSubstElem { unPSubstElem :: Maybe (PermExpr a) }

-- | Partial substitutions assign expressions to some of the bound names in a
-- context
newtype PartialSubst ctx =
  PartialSubst { unPartialSubst :: RAssign PSubstElem ctx }

-- | Build an empty partial substitution for a given set of variables, i.e., the
-- partial substitution that assigns no expressions to those variables
emptyPSubst :: CruCtx ctx -> PartialSubst ctx
emptyPSubst = PartialSubst . helper where
  helper :: CruCtx ctx -> RAssign PSubstElem ctx
  helper CruCtxNil = MNil
  helper (CruCtxCons ctx' _) = helper ctx' :>: PSubstElem Nothing

-- | Return the set of variables that have been assigned values by a partial
-- substitution inside a binding for all of its variables
psubstMbDom :: PartialSubst ctx -> Mb ctx (NameSet CrucibleType)
psubstMbDom (PartialSubst elems) =
  nuMulti (RL.map (\_-> Proxy) elems) $ \ns ->
  NameSet.fromList $ catMaybes $ RL.toList $
  RL.map2 (\n (PSubstElem maybe_e) ->
            if isJust maybe_e
            then Constant (Just $ SomeName n)
            else Constant Nothing) ns elems

-- | Return the set of variables that have not been assigned values by a partial
-- substitution inside a binding for all of its variables
psubstMbUnsetVars :: PartialSubst ctx -> Mb ctx (NameSet CrucibleType)
psubstMbUnsetVars (PartialSubst elems) =
  nuMulti (RL.map (\_ -> Proxy) elems) $ \ns ->
  NameSet.fromList $ catMaybes $ RL.toList $
  RL.map2 (\n (PSubstElem maybe_e) ->
            if maybe_e == Nothing
            then Constant (Just $ SomeName n)
            else Constant Nothing) ns elems

-- | Set the expression associated with a variable in a partial substitution. It
-- is an error if it is already set.
psubstSet :: Member ctx a -> PermExpr a -> PartialSubst ctx ->
             PartialSubst ctx
psubstSet memb e (PartialSubst elems) =
  PartialSubst $
  RL.modify memb
  (\pse -> case pse of
      PSubstElem Nothing -> PSubstElem $ Just e
      PSubstElem (Just _) -> error "psubstSet: value already set for variable")
  elems

-- | Extend a partial substitution with an unassigned variable
extPSubst :: PartialSubst ctx -> PartialSubst (ctx :> a)
extPSubst (PartialSubst elems) = PartialSubst $ elems :>: PSubstElem Nothing

-- | Shorten a partial substitution
unextPSubst :: PartialSubst (ctx :> a) -> PartialSubst ctx
unextPSubst (PartialSubst (elems :>: _)) = PartialSubst elems

-- | Complete a partial substitution into a total substitution, filling in zero
-- values using 'zeroOfType' if necessary
completePSubst :: CruCtx vars -> PartialSubst vars -> PermSubst vars
completePSubst ctx (PartialSubst pselems) = PermSubst $ helper ctx pselems where
  helper :: CruCtx vars -> RAssign PSubstElem vars -> RAssign PermExpr vars
  helper _ MNil = MNil
  helper (CruCtxCons ctx' tp) (pselems' :>: pse) =
    helper ctx' pselems' :>:
    (fromMaybe (zeroOfType tp) (unPSubstElem pse))

-- | Look up an optional expression in a partial substitution
psubstLookup :: PartialSubst ctx -> Member ctx a -> Maybe (PermExpr a)
psubstLookup (PartialSubst m) memb = unPSubstElem $ RL.get memb m

-- | Append two partial substitutions
psubstAppend :: PartialSubst ctx1 -> PartialSubst ctx2 ->
                PartialSubst (ctx1 :++: ctx2)
psubstAppend (PartialSubst elems1) (PartialSubst elems2) =
  PartialSubst $ RL.append elems1 elems2

instance SubstVar PartialSubst Maybe where
  {-
  extSubst (PartialSubst elems) x =
    PartialSubst $ elems :>: PSubstElem (Just $ PExpr_Var x) -}
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> psubstLookup s memb
      Right y -> return $ PExpr_Var y
  {-
  substPermVar s mb_x =
    case mbNameBoundP mb_x of
      Left memb -> noTypesInExprCtx memb
      Right x -> return $ ValPerm_Var x -}

-- | Wrapper function to apply a partial substitution to an expression type
partialSubst :: Substable PartialSubst a Maybe => PartialSubst ctx ->
                Mb ctx a -> Maybe a
partialSubst = genSubst

-- | Apply a partial substitution, raising an error (with the given string) if
-- this fails
partialSubstForce :: Substable PartialSubst a Maybe => PartialSubst ctx ->
                     Mb ctx a -> String -> a
partialSubstForce s mb msg = fromMaybe (error msg) $ partialSubst s mb


----------------------------------------------------------------------
-- * Abstracting Out Variables
----------------------------------------------------------------------

mbMbApply :: Mb (ctx1 :: RList k1) (Mb (ctx2 :: RList k2) (a -> b)) ->
             Mb ctx1 (Mb ctx2 a) -> Mb ctx1 (Mb ctx2 b)
mbMbApply = mbApply . (fmap mbApply)

clMbMbApplyM :: Monad m =>
                m (Closed (Mb (ctx1 :: RList k1)
                           (Mb (ctx2 :: RList k2) (a -> b)))) ->
                m (Closed (Mb ctx1 (Mb ctx2 a))) ->
                m (Closed (Mb ctx1 (Mb ctx2 b)))
clMbMbApplyM fm am =
  (\f a -> $(mkClosed [| mbMbApply |]) `clApply` f `clApply` a) <$> fm <*> am

absVarsReturnH :: Monad m => RAssign f1 (ctx1 :: RList k1) ->
                  RAssign f2 (ctx2 :: RList k2) ->
                  Closed a -> m (Closed (Mb ctx1 (Mb ctx2 a)))
absVarsReturnH fs1 fs2 cl_a =
  return ( $(mkClosed [| \prxs1 prxs2 a ->
                        nuMulti prxs1 (const $ nuMulti prxs2 $ const a) |])
           `clApply` closedProxies fs1 `clApply` closedProxies fs2
           `clApply` cl_a)

-- | Map an 'RAssign' to a 'Closed' 'RAssign' of 'Proxy' objects
closedProxies :: RAssign f args -> Closed (RAssign Proxy args)
closedProxies = toClosed . mapRAssign (const Proxy)

-- | Class for types that support abstracting out all permission and expression
-- variables. If the abstraction succeeds, we get a closed element of the type
-- inside a binding for those permission and expression variables that are free
-- in the original input.
--
-- NOTE: if a variable occurs more than once, we associate it with the left-most
-- occurrence, i.e., the earliest binding
class AbstractVars a where
  abstractPEVars :: RAssign Name (pctx :: RList Type) ->
                    RAssign Name (ectx :: RList CrucibleType) -> a ->
                    Maybe (Closed (Mb pctx (Mb ectx a)))

-- | Call 'abstractPEVars' with only variables that have 'CrucibleType's
abstractVars :: AbstractVars a =>
                RAssign Name (ctx :: RList CrucibleType) -> a ->
                Maybe (Closed (Mb ctx a))
abstractVars ns a =
  fmap (clApply $(mkClosed [| elimEmptyMb |])) $ abstractPEVars MNil ns a

-- | An expression or other object which the variables have been abstracted out
-- of, along with those variables that were abstracted out of it
data AbsObj a = forall ctx. AbsObj (RAssign ExprVar ctx) (Closed (Mb ctx a))

-- | Find all free variables of an expresssion and abstract them out. Note that
-- this should always succeed, if 'freeVars' is implemented correctly.
abstractFreeVars :: (AbstractVars a, FreeVars a) => a -> AbsObj a
abstractFreeVars a
  | Some ns <- freeVarsRAssign a
  , Just cl_mb_a <- abstractVars ns a = AbsObj ns cl_mb_a
abstractFreeVars _ = error "abstractFreeVars"


-- | Try to close an expression by calling 'abstractPEVars' with an empty list
-- of expression variables
tryClose :: AbstractVars a => a -> Maybe (Closed a)
tryClose a =
  fmap (clApply $(mkClosed [| elimEmptyMb . elimEmptyMb |])) $
  abstractPEVars MNil MNil a

instance AbstractVars (Name (a :: CrucibleType)) where
  abstractPEVars ns1 ns2 (n :: Name a)
    | Just memb <- memberElem n ns2
    = return ( $(mkClosed
                 [| \prxs1 prxs2 memb' ->
                   nuMulti prxs1 (const $ nuMulti prxs2 (RL.get memb')) |])
               `clApply` closedProxies ns1 `clApply` closedProxies ns2
               `clApply` toClosed memb)
  abstractPEVars _ _ _ = Nothing

instance AbstractVars (Name (a :: Type)) where
  abstractPEVars ns1 ns2 (n :: Name a)
    | Just memb <- memberElem n ns1
    = return ( $(mkClosed
                 [| \prxs1 prxs2 memb' ->
                   nuMulti prxs1 $ \ns ->
                   nuMulti prxs2 (const $ RL.get memb' ns) |])
               `clApply` closedProxies ns1 `clApply` closedProxies ns2
               `clApply` toClosed memb)
  abstractPEVars _ _ _ = Nothing

instance AbstractVars a => AbstractVars (Mb (ctx :: RList CrucibleType) a) where
  abstractPEVars ns1 ns2 mb =
    mbLift $
    nuMultiWithElim1
    (\ns a ->
      clApply ( $(mkClosed [| \prxs -> fmap (mbSeparate prxs) |])
                `clApply` closedProxies ns) <$>
      abstractPEVars ns1 (append ns2 ns) a)
    mb

instance AbstractVars a => AbstractVars (Mb (ctx :: RList Type) a) where
  abstractPEVars ns1 ns2 mb =
    mbLift $
    nuMultiWithElim1
    (\ns a ->
      clApply ( $(mkClosed [| \prxs2 prxs -> fmap (mbSwap prxs2) . mbSeparate prxs |])
                `clApply` closedProxies ns2
                `clApply` closedProxies ns) <$>
      abstractPEVars (append ns1 ns) ns2 a)
    mb

instance AbstractVars (RAssign Name (ctx :: RList CrucibleType)) where
  abstractPEVars ns1 ns2 MNil = absVarsReturnH ns1 ns2 $(mkClosed [| MNil |])
  abstractPEVars ns1 ns2 (ns :>: n) =
    absVarsReturnH ns1 ns2 $(mkClosed [| (:>:) |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ns
    `clMbMbApplyM` abstractPEVars ns1 ns2 n

instance AbstractVars Integer where
  abstractPEVars ns1 ns2 i = absVarsReturnH ns1 ns2 (toClosed i)

instance AbstractVars (BV w) where
  abstractPEVars ns1 ns2 bv = absVarsReturnH ns1 ns2 (toClosed bv)

instance AbstractVars Bytes where
  abstractPEVars ns1 ns2 bytes = absVarsReturnH ns1 ns2 (toClosed bytes)

instance AbstractVars Natural where
  abstractPEVars ns1 ns2 n = absVarsReturnH ns1 ns2 (toClosed n)

instance AbstractVars Char where
  abstractPEVars ns1 ns2 c = absVarsReturnH ns1 ns2 (toClosed c)

instance AbstractVars Bool where
  abstractPEVars ns1 ns2 b = absVarsReturnH ns1 ns2 (toClosed b)

instance AbstractVars (Member ctx a) where
  abstractPEVars ns1 ns2 memb = absVarsReturnH ns1 ns2 (toClosed memb)

instance AbstractVars a => AbstractVars (Maybe a) where
  abstractPEVars ns1 ns2 Nothing =
    absVarsReturnH ns1 ns2 $(mkClosed [| Nothing |])
  abstractPEVars ns1 ns2 (Just a) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Just |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 a

instance AbstractVars a => AbstractVars [a] where
  abstractPEVars ns1 ns2 [] =
    absVarsReturnH ns1 ns2 $(mkClosed [| [] |])
  abstractPEVars ns1 ns2 (a:as) =
    absVarsReturnH ns1 ns2 $(mkClosed [| (:) |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 a
    `clMbMbApplyM` abstractPEVars ns1 ns2 as

instance (AbstractVars a, AbstractVars b) => AbstractVars (a,b) where
  abstractPEVars ns1 ns2 (a,b) =
    absVarsReturnH ns1 ns2 $(mkClosed [| (,) |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 a
    `clMbMbApplyM` abstractPEVars ns1 ns2 b

instance AbstractVars (PermExpr a) where
  abstractPEVars ns1 ns2 (PExpr_Var x) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Var |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 x
  abstractPEVars ns1 ns2 PExpr_Unit =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Unit |])
  abstractPEVars ns1 ns2 (PExpr_Bool b) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Bool |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 b
  abstractPEVars ns1 ns2 (PExpr_Nat i) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Nat |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 i
  abstractPEVars ns1 ns2 (PExpr_String str) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_String |])
                            `clApply` toClosed str)
  abstractPEVars ns1 ns2 (PExpr_BV factors k) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_BV |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 factors
    `clMbMbApplyM` abstractPEVars ns1 ns2 k
  abstractPEVars ns1 ns2 (PExpr_Struct es) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Struct |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 es
  abstractPEVars ns1 ns2 PExpr_Always =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_Always |])
  abstractPEVars ns1 ns2 (PExpr_LLVMWord e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_LLVMWord |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (PExpr_LLVMOffset x e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_LLVMOffset |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 x
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (PExpr_Fun fh) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_Fun |]) `clApply` toClosed fh)
  abstractPEVars ns1 ns2 PExpr_PermListNil =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_PermListNil |]))
  abstractPEVars ns1 ns2 (PExpr_PermListCons tp e p l) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_PermListCons |])
                           `clApply` toClosed tp)
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
    `clMbMbApplyM` abstractPEVars ns1 ns2 p
    `clMbMbApplyM` abstractPEVars ns1 ns2 l
  abstractPEVars ns1 ns2 (PExpr_RWModality rw) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_RWModality |])
                            `clApply` toClosed rw)
  abstractPEVars ns1 ns2 PExpr_EmptyShape =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_EmptyShape |])
  abstractPEVars ns1 ns2 (PExpr_NamedShape rw l nmsh args) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_NamedShape |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 rw
    `clMbMbApplyM` abstractPEVars ns1 ns2 l
    `clMbMbApplyM` abstractPEVars ns1 ns2 nmsh
    `clMbMbApplyM` abstractPEVars ns1 ns2 args
  abstractPEVars ns1 ns2 (PExpr_EqShape b) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_EqShape |]))
    `clMbMbApplyM` abstractPEVars ns1 ns2 b
  abstractPEVars ns1 ns2 (PExpr_PtrShape maybe_rw maybe_l sh) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_PtrShape |]))
    `clMbMbApplyM` abstractPEVars ns1 ns2 maybe_rw
    `clMbMbApplyM` abstractPEVars ns1 ns2 maybe_l
    `clMbMbApplyM` abstractPEVars ns1 ns2 sh
  abstractPEVars ns1 ns2 (PExpr_FieldShape fsh) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_FieldShape |]))
    `clMbMbApplyM` abstractPEVars ns1 ns2 fsh
  abstractPEVars ns1 ns2 (PExpr_ArrayShape len stride flds) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| flip PExpr_ArrayShape |])
                           `clApply` toClosed stride)
    `clMbMbApplyM` abstractPEVars ns1 ns2 len
    `clMbMbApplyM` abstractPEVars ns1 ns2 flds
  abstractPEVars ns1 ns2 (PExpr_SeqShape sh1 sh2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_SeqShape |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 sh1
    `clMbMbApplyM` abstractPEVars ns1 ns2 sh2
  abstractPEVars ns1 ns2 (PExpr_OrShape sh1 sh2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_OrShape |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 sh1
    `clMbMbApplyM` abstractPEVars ns1 ns2 sh2
  abstractPEVars ns1 ns2 (PExpr_ExShape mb_sh) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExpr_ExShape |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 mb_sh
  abstractPEVars ns1 ns2 (PExpr_ValPerm p) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| PExpr_ValPerm |]))
    `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars (PermExprs as) where
  abstractPEVars ns1 ns2 PExprs_Nil =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExprs_Nil |])
  abstractPEVars ns1 ns2 (PExprs_Cons es e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| PExprs_Cons |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 es
    `clMbMbApplyM` abstractPEVars ns1 ns2 e

instance AbstractVars (BVFactor w) where
  abstractPEVars ns1 ns2 (BVFactor i x) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVFactor |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 i
    `clMbMbApplyM` abstractPEVars ns1 ns2 x

instance AbstractVars (BVRange w) where
  abstractPEVars ns1 ns2 (BVRange e1 e2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVRange |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e1
    `clMbMbApplyM` abstractPEVars ns1 ns2 e2

instance AbstractVars (BVProp w) where
  abstractPEVars ns1 ns2 (BVProp_Eq e1 e2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_Eq |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e1
    `clMbMbApplyM` abstractPEVars ns1 ns2 e2
  abstractPEVars ns1 ns2 (BVProp_Neq e1 e2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_Neq |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e1
    `clMbMbApplyM` abstractPEVars ns1 ns2 e2
  abstractPEVars ns1 ns2 (BVProp_ULt e1 e2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_ULt |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e1
    `clMbMbApplyM` abstractPEVars ns1 ns2 e2
  abstractPEVars ns1 ns2 (BVProp_ULeq e1 e2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_ULeq |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e1
    `clMbMbApplyM` abstractPEVars ns1 ns2 e2
  abstractPEVars ns1 ns2 (BVProp_ULeq_Diff e1 e2 e3) =
    absVarsReturnH ns1 ns2 $(mkClosed [| BVProp_ULeq_Diff |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e1
    `clMbMbApplyM` abstractPEVars ns1 ns2 e2
    `clMbMbApplyM` abstractPEVars ns1 ns2 e3

instance AbstractVars (AtomicPerm a) where
  abstractPEVars ns1 ns2 (Perm_LLVMField fp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMField |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 fp
  abstractPEVars ns1 ns2 (Perm_LLVMArray ap) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMArray |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ap
  abstractPEVars ns1 ns2 (Perm_LLVMBlock bp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMBlock |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 bp
  abstractPEVars ns1 ns2 (Perm_LLVMFree e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMFree |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (Perm_LLVMFunPtr tp p) =
    absVarsReturnH ns1 ns2
    ($(mkClosed [| Perm_LLVMFunPtr |]) `clApply` toClosed tp)
    `clMbMbApplyM` abstractPEVars ns1 ns2 p
  abstractPEVars ns1 ns2 Perm_IsLLVMPtr =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_IsLLVMPtr |])
  abstractPEVars ns1 ns2 (Perm_LLVMBlockShape sh) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMBlockShape |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 sh
  abstractPEVars ns1 ns2 (Perm_LLVMFrame fp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LLVMFrame |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 fp
  abstractPEVars ns1 ns2 (Perm_LOwned ps_in ps_out) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LOwned |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps_in
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps_out
  abstractPEVars ns1 ns2 (Perm_LCurrent e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_LCurrent |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (Perm_Struct ps) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_Struct |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps
  abstractPEVars ns1 ns2 (Perm_Fun fperm) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_Fun |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 fperm
  abstractPEVars ns1 ns2 (Perm_BVProp prop) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_BVProp |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 prop
  abstractPEVars ns1 ns2 (Perm_NamedConj n args off) =
    absVarsReturnH ns1 ns2 $(mkClosed [| Perm_NamedConj |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 n
    `clMbMbApplyM` abstractPEVars ns1 ns2 args
    `clMbMbApplyM` abstractPEVars ns1 ns2 off

instance AbstractVars (ValuePerm a) where
  abstractPEVars ns1 ns2 (ValPerm_Var x off) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Var |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 x
    `clMbMbApplyM` abstractPEVars ns1 ns2 off
  abstractPEVars ns1 ns2 (ValPerm_Eq e) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Eq |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
  abstractPEVars ns1 ns2 (ValPerm_Or p1 p2) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Or |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 p1
    `clMbMbApplyM` abstractPEVars ns1 ns2 p2
  abstractPEVars ns1 ns2 (ValPerm_Exists p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Exists |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 p
  abstractPEVars ns1 ns2 (ValPerm_Named n args off) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Named |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 n
    `clMbMbApplyM` abstractPEVars ns1 ns2 args
    `clMbMbApplyM` abstractPEVars ns1 ns2 off
  abstractPEVars ns1 ns2 (ValPerm_Conj ps) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerm_Conj |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps

instance AbstractVars (ValuePerms as) where
  abstractPEVars ns1 ns2 ValPerms_Nil =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerms_Nil |])
  abstractPEVars ns1 ns2 (ValPerms_Cons ps p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| ValPerms_Cons |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps
    `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars RWModality where
  abstractPEVars ns1 ns2 Write =
    absVarsReturnH ns1 ns2 $(mkClosed [| Write |])
  abstractPEVars ns1 ns2 Read =
    absVarsReturnH ns1 ns2 $(mkClosed [| Read |])

instance AbstractVars (LLVMFieldPerm w sz) where
  abstractPEVars ns1 ns2 (LLVMFieldPerm rw ls off p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LLVMFieldPerm |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 rw
    `clMbMbApplyM` abstractPEVars ns1 ns2 ls
    `clMbMbApplyM` abstractPEVars ns1 ns2 off
    `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars (LLVMArrayField w) where
  abstractPEVars ns1 ns2 (LLVMArrayField fp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LLVMArrayField |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 fp

instance AbstractVars (LLVMArrayPerm w) where
  abstractPEVars ns1 ns2 (LLVMArrayPerm off len str flds bs) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LLVMArrayPerm |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 off
    `clMbMbApplyM` abstractPEVars ns1 ns2 len
    `clMbMbApplyM` abstractPEVars ns1 ns2 str
    `clMbMbApplyM` abstractPEVars ns1 ns2 flds
    `clMbMbApplyM` abstractPEVars ns1 ns2 bs

instance AbstractVars (LLVMArrayIndex w) where
  abstractPEVars ns1 ns2 (LLVMArrayIndex ix fld_num) =
    absVarsReturnH ns1 ns2 $(mkClosed
                             [| \ix' fld_num' ->
                               LLVMArrayIndex ix' $ fromInteger fld_num' |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ix
    `clMbMbApplyM` abstractPEVars ns1 ns2 (toInteger fld_num)

instance AbstractVars (PermOffset a) where
  abstractPEVars ns1 ns2 NoPermOffset =
    absVarsReturnH ns1 ns2 $(mkClosed [| NoPermOffset |])
  abstractPEVars ns1 ns2 (LLVMPermOffset off) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LLVMPermOffset |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 off

instance AbstractVars (LLVMArrayBorrow w) where
  abstractPEVars ns1 ns2 (FieldBorrow ix) =
    absVarsReturnH ns1 ns2 $(mkClosed [| FieldBorrow |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ix
  abstractPEVars ns1 ns2 (RangeBorrow r) =
    absVarsReturnH ns1 ns2 $(mkClosed [| RangeBorrow |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 r

instance AbstractVars (LLVMFieldShape w) where
  abstractPEVars ns1 ns2 (LLVMFieldShape p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LLVMFieldShape |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars (LLVMBlockPerm w) where
  abstractPEVars ns1 ns2 (LLVMBlockPerm rw l off len sh) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LLVMBlockPerm |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 rw
    `clMbMbApplyM` abstractPEVars ns1 ns2 l
    `clMbMbApplyM` abstractPEVars ns1 ns2 off
    `clMbMbApplyM` abstractPEVars ns1 ns2 len
    `clMbMbApplyM` abstractPEVars ns1 ns2 sh

instance AbstractVars (DistPerms ps) where
  abstractPEVars ns1 ns2 DistPermsNil =
    absVarsReturnH ns1 ns2 $(mkClosed [| DistPermsNil |])
  abstractPEVars ns1 ns2 (DistPermsCons perms x p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| DistPermsCons |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 perms
    `clMbMbApplyM` abstractPEVars ns1 ns2 x `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars (LOwnedPerm a) where
  abstractPEVars ns1 ns2 (LOwnedPermField e fp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LOwnedPermField |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
    `clMbMbApplyM` abstractPEVars ns1 ns2 fp
  abstractPEVars ns1 ns2 (LOwnedPermBlock e bp) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LOwnedPermBlock |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
    `clMbMbApplyM` abstractPEVars ns1 ns2 bp
  abstractPEVars ns1 ns2 (LOwnedPermLifetime e ps_in ps_out) =
    absVarsReturnH ns1 ns2 $(mkClosed [| LOwnedPermLifetime |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 e
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps_in
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps_out

instance AbstractVars (LOwnedPerms ps) where
  abstractPEVars ns1 ns2 MNil =
    absVarsReturnH ns1 ns2 $(mkClosed [| MNil |])
  abstractPEVars ns1 ns2 (ps :>: p) =
    absVarsReturnH ns1 ns2 $(mkClosed [| (:>:) |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 ps
    `clMbMbApplyM` abstractPEVars ns1 ns2 p

instance AbstractVars (FunPerm ghosts args ret) where
  abstractPEVars ns1 ns2 (FunPerm ghosts args ret perms_in perms_out) =
    absVarsReturnH ns1 ns2
    ($(mkClosed [| FunPerm |])
     `clApply` toClosed ghosts `clApply` toClosed args `clApply` toClosed ret)
    `clMbMbApplyM` abstractPEVars ns1 ns2 perms_in
    `clMbMbApplyM` abstractPEVars ns1 ns2 perms_out

instance AbstractVars (NamedShape b args w) where
  abstractPEVars ns1 ns2 (NamedShape nm args body) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| NamedShape |])
                             `clApply` toClosed nm `clApply` toClosed args)
    `clMbMbApplyM` abstractPEVars ns1 ns2 body

instance AbstractVars (NamedShapeBody b args w) where
  abstractPEVars ns1 ns2 (DefinedShapeBody mb_sh) =
    absVarsReturnH ns1 ns2 $(mkClosed [| DefinedShapeBody |])
    `clMbMbApplyM` abstractPEVars ns1 ns2 mb_sh
  abstractPEVars ns1 ns2 (OpaqueShapeBody mb_len trans_id) =
    absVarsReturnH ns1 ns2 ($(mkClosed [| \i l -> OpaqueShapeBody l i |])
                             `clApply` toClosed trans_id)
    `clMbMbApplyM` abstractPEVars ns1 ns2 mb_len
  abstractPEVars ns1 ns2 (RecShapeBody mb_sh trans_id fold_id unfold_id) =
    absVarsReturnH ns1 ns2 ($(mkClosed
                              [| \i1 i2 i3 l -> RecShapeBody l i1 i2 i3 |])
                             `clApply` toClosed trans_id
                             `clApply` toClosed fold_id
                             `clApply` toClosed unfold_id)
    `clMbMbApplyM` abstractPEVars ns1 ns2 mb_sh

instance AbstractVars (NamedPermName ns args a) where
  abstractPEVars ns1 ns2 (NamedPermName n tp args ns reachConstr) =
    absVarsReturnH ns1 ns2
    ($(mkClosed [| NamedPermName |])
     `clApply` toClosed n `clApply` toClosed tp `clApply` toClosed args
     `clApply` toClosed ns`clApply` toClosed reachConstr)


----------------------------------------------------------------------
-- * Abstracting out named shapes
----------------------------------------------------------------------

-- | An existentially quantified, partially defined LLVM shape applied to
-- some arguments
data SomePartialNamedShape w where
  NonRecShape :: String -> CruCtx args -> Mb args (PermExpr (LLVMShapeType w))
              -> SomePartialNamedShape w
  RecShape :: String -> CruCtx args
           -> Mb (args :> LLVMShapeType w) (PermExpr (LLVMShapeType w))
           -> SomePartialNamedShape w

-- | An existentially quantified LLVM shape applied to some arguments
data SomeNamedShapeApp w where
  SomeNamedShapeApp :: String -> CruCtx args -> PermExprs args ->
                       NatRepr w -> SomeNamedShapeApp w

class AbstractNamedShape w a where
  abstractNSM :: a -> ReaderT (SomeNamedShapeApp w) Maybe
                              (Binding (LLVMShapeType w) a)

abstractNS :: (KnownNat w, AbstractNamedShape w a) =>
              String -> CruCtx args -> PermExprs args ->
              a -> Maybe (Binding (LLVMShapeType w) a)
abstractNS nsh args_ctx args x = runReaderT (abstractNSM x) nshApp
  where nshApp = SomeNamedShapeApp nsh args_ctx args knownNat

pureBindingM :: Monad m => b -> m (Binding a b)
pureBindingM = pure . nu . const

instance (NuMatching a, AbstractNamedShape w a) =>
         AbstractNamedShape w (Mb ctx a) where
  abstractNSM = fmap (mbSwap RL.typeCtxProxies) . mbM . fmap abstractNSM

instance AbstractNamedShape w Integer where
  abstractNSM = pureBindingM

instance AbstractNamedShape w a => AbstractNamedShape w (Maybe a) where
  abstractNSM (Just x) = fmap Just <$> abstractNSM x
  abstractNSM Nothing = pureBindingM Nothing

instance AbstractNamedShape w a => AbstractNamedShape w [a] where
  abstractNSM [] = pureBindingM []
  abstractNSM (x:xs) = mbMap2 (:) <$> abstractNSM x <*> abstractNSM xs

instance (AbstractNamedShape w a, AbstractNamedShape w b) =>
         AbstractNamedShape w (a, b) where
  abstractNSM (x,y) = mbMap2 (,) <$> abstractNSM x <*> abstractNSM y

instance AbstractNamedShape w (PermExpr a) where
  abstractNSM (PExpr_Var x) = pureBindingM (PExpr_Var x)
  abstractNSM PExpr_Unit = pureBindingM PExpr_Unit
  abstractNSM (PExpr_Bool b) = pureBindingM (PExpr_Bool b)
  abstractNSM (PExpr_Nat n) = pureBindingM (PExpr_Nat n)
  abstractNSM (PExpr_String s) = pureBindingM (PExpr_String s)
  abstractNSM (PExpr_BV fs c) = pureBindingM (PExpr_BV fs c)
  abstractNSM (PExpr_Struct es) = fmap PExpr_Struct <$> abstractNSM es
  abstractNSM PExpr_Always = pureBindingM PExpr_Always
  abstractNSM (PExpr_LLVMWord e) = fmap PExpr_LLVMWord <$> abstractNSM e
  abstractNSM (PExpr_LLVMOffset x e) = fmap (PExpr_LLVMOffset x) <$> abstractNSM e
  abstractNSM (PExpr_Fun fh) = pureBindingM (PExpr_Fun fh)
  abstractNSM PExpr_PermListNil = pureBindingM PExpr_PermListNil
  abstractNSM (PExpr_PermListCons tp e p l) =
    mbMap3 (PExpr_PermListCons tp) <$> abstractNSM e <*> abstractNSM p <*> abstractNSM l
  abstractNSM (PExpr_RWModality rw) = pureBindingM (PExpr_RWModality rw)
  abstractNSM PExpr_EmptyShape = pureBindingM PExpr_EmptyShape
  abstractNSM e@(PExpr_NamedShape maybe_rw maybe_l nmsh args) =
    do SomeNamedShapeApp nm_abs args_ctx_abs args_abs w_abs <- ask
       case namedShapeName nmsh == nm_abs of
         True | Just Refl <- testEquality (namedShapeArgs nmsh) args_ctx_abs
              , True <- args == args_abs
              , Nothing <- maybe_rw, Nothing <- maybe_l
              , Just Refl <- testEquality w_abs (shapeLLVMTypeWidth e)
              -> pure $ nu PExpr_Var
         True -> fail "named shape not applied to its arguments"
         False -> pureBindingM (PExpr_NamedShape maybe_rw maybe_l nmsh args)
  abstractNSM (PExpr_EqShape b) = fmap PExpr_EqShape <$> abstractNSM b
  abstractNSM (PExpr_PtrShape rw l sh) =
    mbMap3 PExpr_PtrShape <$> abstractNSM rw <*> abstractNSM l <*> abstractNSM sh
  abstractNSM (PExpr_FieldShape fsh) = fmap PExpr_FieldShape <$> abstractNSM fsh
  abstractNSM (PExpr_ArrayShape len s flds) =
    mbMap3 PExpr_ArrayShape <$> abstractNSM len <*> pureBindingM s <*> abstractNSM flds
  abstractNSM (PExpr_SeqShape sh1 sh2) =
    mbMap2 PExpr_SeqShape <$> abstractNSM sh1 <*> abstractNSM sh2
  abstractNSM (PExpr_OrShape sh1 sh2) =
    mbMap2 PExpr_OrShape <$> abstractNSM sh1 <*> abstractNSM sh2
  abstractNSM (PExpr_ExShape mb_sh) = fmap PExpr_ExShape <$> abstractNSM mb_sh
  abstractNSM (PExpr_ValPerm p) = fmap PExpr_ValPerm <$> abstractNSM p

instance AbstractNamedShape w (PermExprs as) where
  abstractNSM PExprs_Nil = pureBindingM PExprs_Nil
  abstractNSM (PExprs_Cons es e) =
    mbMap2 PExprs_Cons <$> abstractNSM es <*> abstractNSM e

instance AbstractNamedShape w' (LLVMFieldShape w) where
  abstractNSM (LLVMFieldShape p) = fmap LLVMFieldShape <$> abstractNSM p

instance AbstractNamedShape w (ValuePerm a) where
  abstractNSM (ValPerm_Eq e) = fmap ValPerm_Eq <$> abstractNSM e
  abstractNSM (ValPerm_Or p1 p2) =
    mbMap2 ValPerm_Or <$> abstractNSM p1 <*> abstractNSM p2
  abstractNSM (ValPerm_Exists p) = fmap ValPerm_Exists <$> abstractNSM p
  abstractNSM (ValPerm_Named n args off) =
    mbMap2 (ValPerm_Named n) <$> abstractNSM args <*> abstractNSM off
  abstractNSM (ValPerm_Var x off) =
    fmap (ValPerm_Var x) <$> abstractNSM off
  abstractNSM (ValPerm_Conj aps) = fmap ValPerm_Conj <$> abstractNSM aps

instance AbstractNamedShape w (PermOffset a) where
  abstractNSM NoPermOffset = pureBindingM NoPermOffset
  abstractNSM (LLVMPermOffset e) = fmap LLVMPermOffset <$> abstractNSM e

instance AbstractNamedShape w (AtomicPerm a) where
  abstractNSM (Perm_LLVMField fp) = fmap Perm_LLVMField <$> abstractNSM fp
  abstractNSM (Perm_LLVMArray ap) = fmap Perm_LLVMArray <$> abstractNSM ap
  abstractNSM (Perm_LLVMBlock bp) = fmap Perm_LLVMBlock <$> abstractNSM bp
  abstractNSM (Perm_LLVMFree e) = fmap Perm_LLVMFree <$> abstractNSM e
  abstractNSM (Perm_LLVMFunPtr tp p) = fmap (Perm_LLVMFunPtr tp) <$> abstractNSM p
  abstractNSM (Perm_LLVMBlockShape sh) = fmap Perm_LLVMBlockShape <$> abstractNSM sh
  abstractNSM Perm_IsLLVMPtr = pureBindingM Perm_IsLLVMPtr
  abstractNSM (Perm_NamedConj n args off) = 
    mbMap2 (Perm_NamedConj n) <$> abstractNSM args <*> abstractNSM off
  abstractNSM (Perm_LLVMFrame fp) = fmap Perm_LLVMFrame <$> abstractNSM fp
  abstractNSM (Perm_LOwned ps_in ps_out) =
    mbMap2 Perm_LOwned <$> abstractNSM ps_in <*> abstractNSM ps_out
  abstractNSM (Perm_LCurrent e) = fmap Perm_LCurrent <$> abstractNSM e
  abstractNSM (Perm_Struct ps) = fmap Perm_Struct <$> abstractNSM ps
  abstractNSM (Perm_Fun fp) = fmap Perm_Fun <$> abstractNSM fp
  abstractNSM (Perm_BVProp prop) = pureBindingM (Perm_BVProp prop)

instance AbstractNamedShape w' (LLVMFieldPerm w sz) where
  abstractNSM (LLVMFieldPerm rw l off p) =
    mbMap4 LLVMFieldPerm <$> abstractNSM rw <*> abstractNSM l
                         <*> abstractNSM off <*> abstractNSM p

instance AbstractNamedShape w' (LLVMArrayPerm w) where
  abstractNSM (LLVMArrayPerm off len s pps bs) =
    mbMap5 LLVMArrayPerm <$> abstractNSM off <*> abstractNSM len
                         <*> pureBindingM s <*> abstractNSM pps
                         <*> abstractNSM bs

instance AbstractNamedShape w' (LLVMArrayField w) where
  abstractNSM (LLVMArrayField fp) = fmap LLVMArrayField <$> abstractNSM fp

instance AbstractNamedShape w' (LLVMArrayBorrow w) where
  abstractNSM (FieldBorrow (LLVMArrayIndex e i)) =
    fmap (\e' -> FieldBorrow (LLVMArrayIndex e' i)) <$> abstractNSM e
  abstractNSM (RangeBorrow rng) = pureBindingM (RangeBorrow rng)

instance AbstractNamedShape w' (LLVMBlockPerm w) where
  abstractNSM (LLVMBlockPerm rw l off len sh) =
    mbMap5 LLVMBlockPerm <$> abstractNSM rw <*> abstractNSM l
                         <*> abstractNSM off <*> abstractNSM len
                         <*> abstractNSM sh

instance AbstractNamedShape w (LOwnedPerms ps) where
  abstractNSM MNil = pureBindingM MNil
  abstractNSM (fp :>: fps) = mbMap2 (:>:) <$> abstractNSM fp <*> abstractNSM fps

instance AbstractNamedShape w (LOwnedPerm a) where
  abstractNSM (LOwnedPermField e fp) =
    mbMap2 LOwnedPermField <$> abstractNSM e <*> abstractNSM fp
  abstractNSM (LOwnedPermBlock e bp) =
    mbMap2 LOwnedPermBlock <$> abstractNSM e <*> abstractNSM bp
  abstractNSM (LOwnedPermLifetime e ps_in ps_out) =
    mbMap3 LOwnedPermLifetime <$> abstractNSM e <*> abstractNSM ps_in
                              <*> abstractNSM ps_out

instance AbstractNamedShape w (ValuePerms as) where
  abstractNSM ValPerms_Nil = pureBindingM ValPerms_Nil
  abstractNSM (ValPerms_Cons ps p) =
    mbMap2 ValPerms_Cons <$> abstractNSM ps <*> abstractNSM p

instance AbstractNamedShape w (FunPerm ghosts args ret) where
  abstractNSM (FunPerm ghosts args ret perms_in perms_out) =
    mbMap2 (FunPerm ghosts args ret) <$> abstractNSM perms_in
                                     <*> abstractNSM perms_out


----------------------------------------------------------------------
-- * Permission Environments
----------------------------------------------------------------------

-- | An entry in a permission environment that associates a permission and
-- corresponding SAW identifier with a Crucible function handle
data PermEnvFunEntry where
  PermEnvFunEntry :: args ~ CtxToRList cargs => FnHandle cargs ret ->
                     FunPerm ghosts args ret -> Ident ->
                     PermEnvFunEntry

-- | An existentially quantified 'NamedPerm'
data SomeNamedPerm where
  SomeNamedPerm :: NamedPerm ns args a -> SomeNamedPerm

-- | An existentially quantified LLVM shape with arguments
data SomeNamedShape where
  SomeNamedShape :: (1 <= w, KnownNat w) => NamedShape b args w ->
                    SomeNamedShape

-- | An entry in a permission environment that associates a 'GlobalSymbol' with
-- a permission and a translation of that permission
data PermEnvGlobalEntry where
  PermEnvGlobalEntry :: (1 <= w, KnownNat w) => GlobalSymbol ->
                        ValuePerm (LLVMPointerType w) -> [OpenTerm] ->
                        PermEnvGlobalEntry

-- | The different sorts hints for blocks
data BlockHintSort args where
  -- | This hint specifies the ghost args and input permissions for a block
  BlockEntryHintSort ::
    CruCtx top_args -> CruCtx ghosts ->
    MbValuePerms ((top_args :++: CtxToRList args) :++: ghosts) ->
    BlockHintSort args

  -- | This hint says that the input perms for a block should be generalized
  GenPermsHintSort :: BlockHintSort args

  -- | This hint says that a block should be a join point
  JoinPointHintSort :: BlockHintSort args

-- | A hint for a block
data BlockHint blocks init ret args where
  BlockHint :: FnHandle init ret -> Assignment CtxRepr blocks ->
               BlockID blocks args -> BlockHintSort args ->
               BlockHint blocks init ret args

-- | Get the 'BlockHintSort' for a 'BlockHint'
blockHintSort :: BlockHint blocks init ret args -> BlockHintSort args
blockHintSort (BlockHint _ _ _ sort) = sort

-- | Test if a 'BlockHintSort' is a block entry hint
isBlockEntryHint :: BlockHintSort args -> Bool
isBlockEntryHint (BlockEntryHintSort _ _  _) = True
isBlockEntryHint _ = False

-- | Test if a 'BlockHintSort' is a generalization hint
isGenPermsHint :: BlockHintSort args -> Bool
isGenPermsHint GenPermsHintSort = True
isGenPermsHint _ = False

-- | Test if a 'BlockHintSort' is a generalization hint
isJoinPointHint :: BlockHintSort args -> Bool
isJoinPointHint JoinPointHintSort = True
isJoinPointHint _ = False

-- FIXME: all the per-block hints 

-- | A "hint" from the user for type-checking
data Hint where
  Hint_Block :: BlockHint blocks init ret args -> Hint

-- | A permission environment that maps function names, permission names, and
-- 'GlobalSymbols' to their respective permission structures
data PermEnv = PermEnv {
  permEnvFunPerms :: [PermEnvFunEntry],
  permEnvNamedPerms :: [SomeNamedPerm],
  permEnvNamedShapes :: [SomeNamedShape],
  permEnvGlobalSyms :: [PermEnvGlobalEntry],
  permEnvHints :: [Hint]
  }

$(mkNuMatching [t| forall ctx. PermVarSubst ctx |])
$(mkNuMatching [t| PermEnvFunEntry |])
$(mkNuMatching [t| SomeNamedPerm |])
$(mkNuMatching [t| SomeNamedShape |])
$(mkNuMatching [t| PermEnvGlobalEntry |])
$(mkNuMatching [t| forall args. BlockHintSort args |])
$(mkNuMatching [t| forall blocks init ret args.
                BlockHint blocks init ret args |])
$(mkNuMatching [t| Hint |])
$(mkNuMatching [t| PermEnv |])

-- | The empty 'PermEnv'
emptyPermEnv :: PermEnv
emptyPermEnv = PermEnv [] [] [] [] []

-- | Add a 'NamedPerm' to a permission environment
permEnvAddNamedPerm :: PermEnv -> NamedPerm ns args a -> PermEnv
permEnvAddNamedPerm env np =
  env { permEnvNamedPerms = SomeNamedPerm np : permEnvNamedPerms env }

-- | Add a 'NamedShape' to a permission environment
permEnvAddNamedShape :: (1 <= w, KnownNat w) =>
                        PermEnv -> NamedShape b args w -> PermEnv
permEnvAddNamedShape env ns =
  env { permEnvNamedShapes = SomeNamedShape ns : permEnvNamedShapes env }

-- | Add an opaque named permission to a 'PermEnv'
permEnvAddOpaquePerm :: PermEnv -> String -> CruCtx args -> TypeRepr a ->
                        Ident -> PermEnv
permEnvAddOpaquePerm env str args tp i =
  let n = NamedPermName str tp args (OpaqueSortRepr
                                     TrueRepr) NameNonReachConstr in
  permEnvAddNamedPerm env $ NamedPerm_Opaque $ OpaquePerm n i

-- | Add a recursive named permission to a 'PermEnv', assuming that the
-- 'recPermCases' and the fold and unfold functions depend recursively on the
-- recursive named permission being defined. This is handled by adding a
-- "temporary" version of the named permission to the environment to be used to
-- compute the 'recPermCases' and the fold and unfold functions and then passing
-- the expanded environment with this temporary named permission to the supplied
-- functions for computing these values. This temporary named permission has its
-- 'recPermCases' and its fold and unfold functions undefined, so the supplied
-- functions cannot depend on these values being defined, which makes sense
-- because they are defining them! Note that the function for computing the
-- 'recPermCases' can be called multiple times, so should not perform any
-- non-idempotent mutation in the monad @m@.
permEnvAddRecPermM :: Monad m => PermEnv -> String -> CruCtx args ->
                      TypeRepr a -> Ident ->
                      (forall b. NameReachConstr (RecursiveSort b reach) args a) ->
                      (forall b. NamedPermName (RecursiveSort b reach) args a ->
                       PermEnv -> m [Mb args (ValuePerm a)]) ->
                      (forall b. NamedPermName (RecursiveSort b reach) args a ->
                       [Mb args (ValuePerm a)] -> PermEnv -> m (Ident, Ident)) ->
                      (forall b. NamedPermName (RecursiveSort b reach) args a ->
                       PermEnv -> m (ReachMethods args a reach)) ->
                      m PermEnv
permEnvAddRecPermM env nm args tp trans_ident reachC casesF foldIdentsF reachMethsF =
  -- NOTE: we start by assuming nm is conjoinable, and then, if it's not, we
  -- call casesF again, and thereby compute a fixed-point
  do let reach = nameReachConstrBool reachC
     let mkTmpEnv :: NamedPermName (RecursiveSort b reach) args a -> PermEnv
         mkTmpEnv npn =
           permEnvAddNamedPerm env $ NamedPerm_Rec $
           RecPerm npn trans_ident
           (error "Analyzing recursive perm cases before it is defined!")
           (error "Folding recursive perm before it is defined!")
           (error "Using reachability methods for recursive perm before it is defined!")
           (error "Unfolding recursive perm before it is defined!")
         mkRealEnv :: Monad m => NamedPermName (RecursiveSort b reach) args a ->
                      [Mb args (ValuePerm a)] ->
                      (PermEnv -> m (Ident, Ident)) ->
                      (PermEnv -> m (ReachMethods args a reach)) ->
                      m PermEnv
         mkRealEnv npn cases identsF rmethsF =
           do let tmp_env = mkTmpEnv npn
              (fold_ident, unfold_ident) <- identsF tmp_env
              reachMeths <- rmethsF tmp_env
              return $ permEnvAddNamedPerm env $ NamedPerm_Rec $
                RecPerm npn trans_ident fold_ident unfold_ident reachMeths cases
     let npn1 = NamedPermName nm tp args (RecursiveSortRepr TrueRepr reach) reachC
     cases1 <- casesF npn1 (mkTmpEnv npn1)
     case someBool $ all (mbLift . fmap isConjPerm) cases1 of
       Some TrueRepr -> mkRealEnv npn1 cases1 (foldIdentsF npn1 cases1) (reachMethsF npn1)
       Some FalseRepr ->
         do let npn2 = NamedPermName nm tp args (RecursiveSortRepr
                                                 FalseRepr reach) reachC
            cases2 <- casesF npn2 (mkTmpEnv npn2)
            mkRealEnv npn2 cases2 (foldIdentsF npn2 cases2) (reachMethsF npn2)


-- | Add a defined named permission to a 'PermEnv'
permEnvAddDefinedPerm :: PermEnv -> String -> CruCtx args -> TypeRepr a ->
                         Mb args (ValuePerm a) -> PermEnv
permEnvAddDefinedPerm env str args tp p =
  case someBool $ mbLift $ fmap isConjPerm p of
    Some b ->
      let n = NamedPermName str tp args (DefinedSortRepr b) NameNonReachConstr
          np = NamedPerm_Defined (DefinedPerm n p) in
      env { permEnvNamedPerms = SomeNamedPerm np : permEnvNamedPerms env }

-- | Add a defined LLVM shape to a permission environment
permEnvAddDefinedShape :: (1 <= w, KnownNat w) => PermEnv -> String ->
                          CruCtx args -> Mb args (PermExpr (LLVMShapeType w)) ->
                          PermEnv
permEnvAddDefinedShape env nm args mb_sh =
  env { permEnvNamedShapes =
          SomeNamedShape (NamedShape nm args $
                          DefinedShapeBody mb_sh) : permEnvNamedShapes env }

-- | Add a global symbol with a function permission to a 'PermEnv'
permEnvAddGlobalSymFun :: (1 <= w, KnownNat w) => PermEnv -> GlobalSymbol ->
                          f w -> FunPerm ghosts args ret -> OpenTerm -> PermEnv
permEnvAddGlobalSymFun env sym (w :: f w) fun_perm t =
  let p = ValPerm_Conj1 $ mkPermLLVMFunPtr w fun_perm in
  env { permEnvGlobalSyms =
          PermEnvGlobalEntry sym p [t] : permEnvGlobalSyms env }

-- | Add a global symbol with 0 or more function permissions to a 'PermEnv'
permEnvAddGlobalSymFunMulti :: (1 <= w, KnownNat w) => PermEnv ->
                               GlobalSymbol -> f w ->
                               [(SomeFunPerm args ret, OpenTerm)] -> PermEnv
permEnvAddGlobalSymFunMulti env sym (w :: f w) ps_ts =
  let p = ValPerm_Conj1 $ mkPermLLVMFunPtrs w $ map fst ps_ts in
  env { permEnvGlobalSyms =
          PermEnvGlobalEntry sym p (map snd ps_ts) : permEnvGlobalSyms env }

-- | Add some 'PermEnvGlobalEntry's to a 'PermEnv'
permEnvAddGlobalSyms :: PermEnv -> [PermEnvGlobalEntry] -> PermEnv
permEnvAddGlobalSyms env entries = env { permEnvGlobalSyms =
                                           entries ++ permEnvGlobalSyms env }

-- | Add a 'Hint' to a 'PermEnv'
permEnvAddHint :: PermEnv -> Hint -> PermEnv
permEnvAddHint env hint = env { permEnvHints = hint : permEnvHints env }

-- | Look up a 'FnHandle' by name in a 'PermEnv'
lookupFunHandle :: PermEnv -> String -> Maybe SomeHandle
lookupFunHandle env str =
  case find (\(PermEnvFunEntry h _ _) ->
              handleName h == fromString str) (permEnvFunPerms env) of
    Just (PermEnvFunEntry h _ _) -> Just (SomeHandle h)
    Nothing -> Nothing

-- | Look up the function permission and SAW translation for a 'FnHandle'
lookupFunPerm :: PermEnv -> FnHandle cargs ret ->
                 Maybe (SomeFunPerm (CtxToRList cargs) ret, Ident)
lookupFunPerm env = helper (permEnvFunPerms env) where
  helper :: [PermEnvFunEntry] -> FnHandle cargs ret ->
            Maybe (SomeFunPerm (CtxToRList cargs) ret, Ident)
  helper [] _ = Nothing
  helper ((PermEnvFunEntry h' fun_perm ident):_) h
    | Just Refl <- testEquality (handleType h') (handleType h)
    , h' == h
    = Just (SomeFunPerm fun_perm, ident)
  helper (_:entries) h = helper entries h

-- | Look up a 'NamedPermName' by name in a 'PermEnv'
lookupNamedPermName :: PermEnv -> String -> Maybe SomeNamedPermName
lookupNamedPermName env str =
  case find (\(SomeNamedPerm np) ->
              namedPermNameName (namedPermName np) == str) (permEnvNamedPerms env) of
    Just (SomeNamedPerm np) -> Just (SomeNamedPermName (namedPermName np))
    Nothing -> Nothing

-- | Look up a conjunctive 'NamedPermName' by name in a 'PermEnv'
lookupNamedConjPermName :: PermEnv -> String -> Maybe SomeNamedConjPermName
lookupNamedConjPermName env str =
  case find (\(SomeNamedPerm np) ->
              namedPermNameName (namedPermName np) == str)
       (permEnvNamedPerms env) of
    Just (SomeNamedPerm np)
      | TrueRepr <- nameIsConjRepr $ namedPermName np ->
        Just (SomeNamedConjPermName (namedPermName np))
    _ -> Nothing

-- | Look up the 'NamedPerm' for a 'NamedPermName' in a 'PermEnv'
lookupNamedPerm :: PermEnv -> NamedPermName ns args a ->
                   Maybe (NamedPerm ns args a)
lookupNamedPerm env = helper (permEnvNamedPerms env) where
  helper :: [SomeNamedPerm] -> NamedPermName ns args a ->
            Maybe (NamedPerm ns args a)
  helper [] _ = Nothing
  helper (SomeNamedPerm rp:_) rpn
    | Just (Refl, Refl, Refl) <- testNamedPermNameEq (namedPermName rp) rpn
    = Just rp
  helper (_:rps) rpn = helper rps rpn

-- | Look up an LLVM shape by name in a 'PermEnv' and cast it to a given width
lookupNamedShape :: PermEnv -> String -> Maybe SomeNamedShape
lookupNamedShape env nm =
  find (\case SomeNamedShape nmsh ->
                nm == namedShapeName nmsh) (permEnvNamedShapes env)

-- | Look up the permissions and translation for a 'GlobalSymbol' at a
-- particular machine word width
lookupGlobalSymbol :: PermEnv -> GlobalSymbol -> NatRepr w ->
                      Maybe (ValuePerm (LLVMPointerType w), [OpenTerm])
lookupGlobalSymbol env = helper (permEnvGlobalSyms env) where
  helper :: [PermEnvGlobalEntry] -> GlobalSymbol -> NatRepr w ->
            Maybe (ValuePerm (LLVMPointerType w), [OpenTerm])
  helper  (PermEnvGlobalEntry sym'
            (p :: ValuePerm (LLVMPointerType w')) t:_) sym w
    | sym' == sym
    , Just Refl <- testEquality w (knownNat :: NatRepr w') =
      Just (p, t)
  helper (_:entries) sym w = helper entries sym w
  helper [] _ _ = Nothing

-- | Look up all hints associated with a 'BlockID' in a function
lookupBlockHints :: PermEnv -> FnHandle init ret -> Assignment CtxRepr blocks ->
                    BlockID blocks args -> [BlockHintSort args]
lookupBlockHints env h blocks blkID =
  mapMaybe (\hint -> case hint of
               Hint_Block (BlockHint h' blocks' blkID' sort)
                 | Just Refl <- testEquality (handleID h') (handleID h)
                 , Just Refl <- testEquality blocks' blocks
                 , Just Refl <- testEquality blkID blkID' ->
                   return sort
               _ -> Nothing) $
  permEnvHints env

-- | Look up all hints with sort 'BlockEntryHintSort' for a given function
lookupBlockEntryHints :: PermEnv -> FnHandle init ret ->
                         Assignment CtxRepr blocks ->
                         [Some (BlockHint blocks init ret)]
lookupBlockEntryHints env h blocks =
  mapMaybe (\hint -> case hint of
               Hint_Block blk_hint@(BlockHint h' blocks' _blkID'
                                    (BlockEntryHintSort _ _ _))
                 | Just Refl <- testEquality (handleID h') (handleID h)
                 , Just Refl <- testEquality blocks' blocks ->
                   return $ Some blk_hint
               _ -> Nothing) $
  permEnvHints env

-- | Test if a 'BlockID' in a 'CFG' has a hint with sort 'GenPermsHintSort'
lookupBlockGenPermsHint :: PermEnv -> FnHandle init ret ->
                           Assignment CtxRepr blocks -> BlockID blocks args ->
                           Bool
lookupBlockGenPermsHint env h blocks blkID =
  any (\case GenPermsHintSort -> True
             _ -> False) $
  lookupBlockHints env h blocks blkID

-- | Test if a 'BlockID' in a 'CFG' has a hint with sort 'JoinPointHintSort'
lookupBlockJoinPointHint :: PermEnv -> FnHandle init ret ->
                            Assignment CtxRepr blocks -> BlockID blocks args ->
                            Bool
lookupBlockJoinPointHint env h blocks blkID =
  any (\case JoinPointHintSort -> True
             _ -> False) $
  lookupBlockHints env h blocks blkID


----------------------------------------------------------------------
-- * Permission Sets
----------------------------------------------------------------------

-- FIXME: revisit all the operations in this section and remove those that we no
-- longer need

-- | A permission set associates permissions with expression variables, and also
-- has a stack of "distinguished permissions" that are used for intro rules
data PermSet ps = PermSet { _varPermMap :: NameMap ValuePerm,
                            _distPerms :: DistPerms ps }

makeLenses ''PermSet

-- | Get all variables that have permissions set in a 'PermSet'
permSetVars :: PermSet ps -> [SomeName CrucibleType]
permSetVars =
  map (\case (NameAndElem n _) ->
               SomeName n) . NameMap.assocs . view varPermMap

-- | Build a 'PermSet' with only distinguished permissions
distPermSet :: DistPerms ps -> PermSet ps
distPermSet perms = PermSet NameMap.empty perms

-- NOTE: this instance would require a NuMatching instance for NameMap...
-- $(mkNuMatching [t| forall ps. PermSet ps |])

-- | The lens for the permissions associated with a given variable
varPerm :: ExprVar a -> Lens' (PermSet ps) (ValuePerm a)
varPerm x =
  lens
  (\(PermSet nmap _) ->
    case NameMap.lookup x nmap of
      Just p -> p
      Nothing -> ValPerm_True)
  (\(PermSet nmap ps) p -> PermSet (NameMap.insert x p nmap) ps)

-- | Set the primary permission for a variable, assuming it is currently the
-- trivial permission @true@
setVarPerm :: ExprVar a -> ValuePerm a -> PermSet ps -> PermSet ps
setVarPerm x p =
  over (varPerm x) $ \p' ->
  case p' of
    ValPerm_True -> p
    _ -> error "setVarPerm: permission for variable already set!"

-- | Get a permission list for multiple variables
varPermsMulti :: RAssign Name ns -> PermSet ps -> DistPerms ns
varPermsMulti MNil _ = DistPermsNil
varPermsMulti (ns :>: n) ps =
  DistPermsCons (varPermsMulti ns ps) n (ps ^. varPerm n)

-- | Get a permission list for all variable permissions
permSetAllVarPerms :: PermSet ps -> Some DistPerms
permSetAllVarPerms perm_set =
  foldr (\(NameAndElem x p) (Some perms) -> Some (DistPermsCons perms x p))
  (Some DistPermsNil) (NameMap.assocs $ _varPermMap perm_set)

-- | A determined vars clause says that the variable on the right-hand side is
-- determined (as in the description of 'determinedVars') if all those on the
-- left-hand side are. Note that this is an if and not an iff, as there may be
-- other ways to mark that RHS variable determined.
data DetVarsClause =
  DetVarsClause (NameSet CrucibleType) (SomeName CrucibleType)

-- | Union a 'NameSet' to the left-hand side of a 'DetVarsClause'
detVarsClauseAddLHS :: NameSet CrucibleType -> DetVarsClause -> DetVarsClause
detVarsClauseAddLHS names (DetVarsClause lhs rhs) =
  DetVarsClause (NameSet.union lhs names) rhs

-- | Add a single variable to the left-hand side of a 'DetVarsClause'
detVarsClauseAddLHSVar :: ExprVar a -> DetVarsClause -> DetVarsClause
detVarsClauseAddLHSVar n (DetVarsClause lhs rhs) =
  DetVarsClause (NameSet.insert n lhs) rhs

-- | Generic function to compute the 'DetVarsClause's for a permission
class GetDetVarsClauses a where
  getDetVarsClauses ::
    a -> ReaderT (PermSet ps) (State (NameSet CrucibleType)) [DetVarsClause]

instance GetDetVarsClauses a => GetDetVarsClauses [a] where
  getDetVarsClauses l = concat <$> mapM getDetVarsClauses l

instance GetDetVarsClauses (ExprVar a) where
  -- If x has not been visited yet, then return a clause stating that x is
  -- determined and add all variables that are potentially determined by the
  -- current permissions on x
  getDetVarsClauses x =
    do seen_vars <- get
       perms <- ask
       if NameSet.member x seen_vars then return [] else
         do modify (NameSet.insert x)
            perm_clauses <- getDetVarsClauses (perms ^. varPerm x)
            return (DetVarsClause NameSet.empty (SomeName x) :
                    map (detVarsClauseAddLHSVar x) perm_clauses)

instance GetDetVarsClauses (PermExpr a) where
  getDetVarsClauses e
    | isDeterminingExpr e =
      concat <$> mapM (\(SomeName n) ->
                        getDetVarsClauses n) (NameSet.toList $ freeVars e)
  getDetVarsClauses _ = return []


instance GetDetVarsClauses (PermExprs as) where
  getDetVarsClauses PExprs_Nil = return []
  getDetVarsClauses (PExprs_Cons es e) =
    (++) <$> getDetVarsClauses es <*> getDetVarsClauses e

instance GetDetVarsClauses (ValuePerm a) where
  getDetVarsClauses (ValPerm_Eq e) = getDetVarsClauses e
  getDetVarsClauses (ValPerm_Conj ps) = concat <$> mapM getDetVarsClauses ps
  -- FIXME: For named perms, we currently require the offset to have no free
  -- vars, as a simplification, but this could maybe be loosened...?
  getDetVarsClauses (ValPerm_Named _ args off)
    | NameSet.null (freeVars off) = getDetVarsClauses args
  getDetVarsClauses _ = return []

instance GetDetVarsClauses (ValuePerms as) where
  getDetVarsClauses ValPerms_Nil = return []
  getDetVarsClauses (ValPerms_Cons ps p) =
    (++) <$> getDetVarsClauses ps <*> getDetVarsClauses p

instance GetDetVarsClauses (AtomicPerm a) where
  getDetVarsClauses (Perm_LLVMField fp) = getDetVarsClauses fp
  getDetVarsClauses (Perm_LLVMArray ap) = getDetVarsClauses ap
  getDetVarsClauses (Perm_LLVMBlock bp) = getDetVarsClauses bp
  getDetVarsClauses (Perm_LLVMBlockShape sh) = getDetVarsClauses sh
  getDetVarsClauses (Perm_LLVMFrame frame_perm) =
    concat <$> mapM (getDetVarsClauses . fst) frame_perm
  getDetVarsClauses (Perm_LOwned _ _) = return []
  getDetVarsClauses _ = return []

instance (1 <= w, KnownNat w, 1 <= sz, KnownNat sz) =>
         GetDetVarsClauses (LLVMFieldPerm w sz) where
  getDetVarsClauses (LLVMFieldPerm {..}) =
    map (detVarsClauseAddLHS (freeVars llvmFieldOffset)) <$> concat <$>
    sequence [getDetVarsClauses llvmFieldRW,
              getDetVarsClauses llvmFieldLifetime,
              getDetVarsClauses llvmFieldContents]

instance (1 <= w, KnownNat w) => GetDetVarsClauses (LLVMArrayField w) where
  getDetVarsClauses (LLVMArrayField fp) = getDetVarsClauses fp

instance (1 <= w, KnownNat w) => GetDetVarsClauses (LLVMArrayPerm w) where
  getDetVarsClauses (LLVMArrayPerm {..}) =
    map (detVarsClauseAddLHS $
         NameSet.unions [freeVars llvmArrayOffset, freeVars llvmArrayLen,
                         freeVars llvmArrayBorrows]) <$>
    concat <$> mapM getDetVarsClauses llvmArrayFields

instance (1 <= w, KnownNat w) => GetDetVarsClauses (LLVMBlockPerm w) where
  getDetVarsClauses (LLVMBlockPerm {..}) =
    map (detVarsClauseAddLHS $
         NameSet.unions [freeVars llvmBlockOffset, freeVars llvmBlockLen]) <$>
    concat <$> sequence [getDetVarsClauses llvmBlockRW,
                         getDetVarsClauses llvmBlockLifetime,
                         getShapeDetVarsClauses llvmBlockShape]

instance GetDetVarsClauses (LLVMFieldShape w) where
  getDetVarsClauses (LLVMFieldShape p) = getDetVarsClauses p

-- | Compute the 'DetVarsClause's for a block permission with the given shape
getShapeDetVarsClauses ::
  (1 <= w, KnownNat w) => PermExpr (LLVMShapeType w) ->
  ReaderT (PermSet ps) (State (NameSet CrucibleType)) [DetVarsClause]
getShapeDetVarsClauses (PExpr_Var x) =
  getDetVarsClauses x
getShapeDetVarsClauses (PExpr_NamedShape _ _ _ args) =
  -- FIXME: maybe also include the variables determined by the modalities?
  getDetVarsClauses args
getShapeDetVarsClauses (PExpr_EqShape e) = getDetVarsClauses e
getShapeDetVarsClauses (PExpr_PtrShape _ _ sh) =
  -- FIXME: maybe also include the variables determined by the modalities?
  getShapeDetVarsClauses sh
getShapeDetVarsClauses (PExpr_FieldShape fldsh) = getDetVarsClauses fldsh
getShapeDetVarsClauses (PExpr_ArrayShape len _ fldshs) =
  map (detVarsClauseAddLHS (freeVars len)) <$>
  getDetVarsClauses fldshs
getShapeDetVarsClauses (PExpr_SeqShape sh1 sh2)
  | isJust $ llvmShapeLength sh1 =
    (++) <$> getDetVarsClauses sh1 <*> getDetVarsClauses sh2
getShapeDetVarsClauses _ = return []


-- | Compute all the variables whose values are /determined/ by the permissions
-- on the given input variables, other than those variables themselves. The
-- intuitive idea is that permission @x:p@ determines the value of @y@ iff there
-- is always a uniquely determined value of @y@ for any proof of @exists y.x:p@.
determinedVars :: PermSet ps -> RAssign ExprVar ns -> [SomeName CrucibleType]
determinedVars top_perms vars =
  let vars_set = NameSet.fromList $ mapToList SomeName vars
      multigraph =
        evalState (runReaderT (getDetVarsClauses (distPermsToValuePerms $
                                                  varPermsMulti vars top_perms))
                   top_perms)
        vars_set in
  evalState (determinedVarsForGraph multigraph) vars_set
  where
    -- Find all variables that are not already marked as determined in our
    -- NameSet state but that are determined given the current determined
    -- variables, mark these variables as determiend, and then repeat, returning
    -- all variables that are found in order
    determinedVarsForGraph :: [DetVarsClause] ->
                              State (NameSet CrucibleType) [SomeName CrucibleType]
    determinedVarsForGraph graph =
      do det_vars <- concat <$> mapM determinedVarsForClause graph
         if det_vars == [] then return [] else
           (det_vars ++) <$> determinedVarsForGraph graph

    -- If the LHS of a clause has become determined but its RHS is not, return
    -- its RHS, otherwise return nothing
    determinedVarsForClause :: DetVarsClause ->
                               State (NameSet CrucibleType) [SomeName CrucibleType]
    determinedVarsForClause (DetVarsClause lhs_vars (SomeName rhs_var)) =
      do det_vars <- get
         if not (NameSet.member rhs_var det_vars) &&
            nameSetIsSubsetOf lhs_vars det_vars
           then modify (NameSet.insert rhs_var) >> return [SomeName rhs_var]
           else return []

-- | Compute the transitive free variables of the permissions on some input list
-- @ns@ of variables, which includes all variables @ns1@ that are free in the
-- permissions associated with @ns@, all the variables @ns2@ free in the
-- permissions of @ns1@, etc. Every variable in the returned list is guaranteed
-- to be listed /after/ (i.e., to the right of where) it is used.
varPermsTransFreeVars :: RAssign ExprVar ns -> PermSet ps ->
                         Some (RAssign ExprVar)
varPermsTransFreeVars =
  helper NameSet.empty . mapToList SomeName
  where
    helper :: NameSet CrucibleType -> [SomeName CrucibleType] -> PermSet ps ->
              Some (RAssign ExprVar)
    helper seen_vars ns perms =
      let seen_vars' =
            foldr (\(SomeName n) -> NameSet.insert n) seen_vars ns
          free_vars =
            NameSet.unions $
            map (\(SomeName n) -> freeVars (perms ^. varPerm n)) ns
          new_vars = NameSet.difference free_vars seen_vars' in
      case toList new_vars of
        [] -> Some MNil
        new_ns ->
          case (namesListToNames new_ns, helper seen_vars' new_ns perms) of
            (SomeRAssign ns', Some rest) ->
              Some $ append ns' rest

-- | Initialize the primary permission of a variable to @true@ if it is not set
initVarPerm :: ExprVar a -> PermSet ps -> PermSet ps
initVarPerm x =
  over varPermMap $ \nmap ->
  if NameMap.member x nmap then nmap else NameMap.insert x ValPerm_True nmap

-- | Set the primary permissions for a sequence of variables to @true@
initVarPerms :: RAssign Name (as :: RList CrucibleType) -> PermSet ps ->
                PermSet ps
initVarPerms MNil perms = perms
initVarPerms (ns :>: n) perms = initVarPerms ns $ initVarPerm n perms

-- | The lens for a particular distinguished perm, checking that it is indeed
-- associated with the given variable
distPerm :: Member ps a -> ExprVar a -> Lens' (PermSet ps) (ValuePerm a)
distPerm memb x = distPerms . nthVarPerm memb x

-- | The lens for the distinguished perm at the top of the stack, checking that
-- it has the given variable
topDistPerm :: ExprVar a -> Lens' (PermSet (ps :> a)) (ValuePerm a)
topDistPerm x = distPerms . distPermsHead x

-- | Modify the distinguished permission stack of a 'PermSet'
modifyDistPerms :: (DistPerms ps1 -> DistPerms ps2) ->
                   PermSet ps1 -> PermSet ps2
modifyDistPerms f (PermSet perms dperms) = PermSet perms $ f dperms

-- | Get all the permissions in the permission set as a sequence of
-- distinguished permissions
getAllPerms :: PermSet ps -> Some DistPerms
getAllPerms perms = helper (NameMap.assocs $ perms ^. varPermMap) where
  helper :: [NameAndElem ValuePerm] -> Some DistPerms
  helper [] = Some DistPermsNil
  helper (NameAndElem x p : xps) =
    case helper xps of
      Some ps -> Some $ DistPermsCons ps x p

-- | Delete permission @x:p@ from the permission set, assuming @x@ has precisely
-- permissions @p@, replacing it with @x:true@
deletePerm :: ExprVar a -> ValuePerm a -> PermSet ps -> PermSet ps
deletePerm x p =
  over (varPerm x) $ \p' ->
  if p' == p then ValPerm_True else error "deletePerm"

-- | Push a new distinguished permission onto the top of the stack
pushPerm :: ExprVar a -> ValuePerm a -> PermSet ps -> PermSet (ps :> a)
pushPerm x p (PermSet nmap ps) = PermSet nmap (DistPermsCons ps x p)

-- | Pop the top distinguished permission off of the stack
popPerm :: ExprVar a -> PermSet (ps :> a) -> (PermSet ps, ValuePerm a)
popPerm x (PermSet nmap pstk) =
  (PermSet nmap (pstk ^. distPermsTail), pstk ^. distPermsHead x)

-- | Drop the top distinguished permission on the stack
dropPerm :: ExprVar a -> PermSet (ps :> a) -> PermSet ps
dropPerm x = fst . popPerm x
