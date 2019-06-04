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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE EmptyCase #-}

module SAWScript.Heapster.Permissions2 where

import Data.List
import Data.Binding.Hobbits
import GHC.TypeLits

import Data.Binding.Hobbits.NameMap (NameMap)
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty)
import Data.Parameterized.NatRepr

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core


----------------------------------------------------------------------
-- * Expressions for Permissions
----------------------------------------------------------------------

-- | The Haskell type of expression variables
type PermVar a = Name (PermExpr a)

-- | Expressions that represent "fractions" of a write permission
data SplittingExpr
  = SplExpr_All
  | SplExpr_L SplittingExpr
  | SplExpr_R SplittingExpr
  | SplExpr_Star SplittingExpr SplittingExpr
  | SplExpr_Var (PermVar SplittingType)

-- | Crucible type for splitting expressions; we give them a Crucible type so
-- they can be existentially bound in the same way as other Crucible objects
type SplittingType = IntrinsicType "Splitting" EmptyCtx

-- | The object-level representation of 'SplittingType'
splittingTypeRepr :: TypeRepr SplittingType
splittingTypeRepr = knownRepr


-- | Expressions that are considered "pure" for use in permissions. Note that
-- these are in a normal form, that makes them easier to analyze.
data PermExpr (a :: CrucibleType) where
  PExpr_Var :: PermVar a -> PermExpr a
  -- ^ A variable of any type

  PExpr_BV :: (1 <= w, KnownNat w) =>
              [BVFactor w] -> Integer -> PermExpr (BVType w)
  -- ^ A bitvector expression is a linear expression in @N@ variables, i.e., sum
  -- of constant times variable factors plus a constant

  PExpr_Struct :: PermExprs args -> PermExpr (StructType args)
  -- ^ A struct expression is an expression for each argument of the struct type

  PExpr_LLVMWord :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
                    PermExpr (LLVMPointerType w)
  -- ^ An LLVM value that represents a word, i.e., whose region identifier is 0

  PExpr_LLVMOffset :: (1 <= w, KnownNat w) =>
                      PermVar (LLVMPointerType w) ->
                      PermExpr (BVType w) ->
                      PermExpr (LLVMPointerType w)
  -- ^ An LLVM value built by adding an offset to an LLVM variable

  PExpr_Spl :: SplittingExpr -> PermExpr SplittingType
  -- ^ An expression that represents a permission splitting


-- | A sequence of permission expressions
data PermExprs (as :: Ctx CrucibleType) where
  PExprs_Nil :: PermExprs EmptyCtx
  PExprs_Cons :: PermExprs as -> PermExpr a -> PermExprs (as ::> a)

-- | A bitvector variable, possibly multiplied by a constant
data BVFactor w where
  BVFactor :: (1 <= w, KnownNat w) => Integer ->
              Name (PermExpr (BVType w)) ->
              BVFactor w
    -- ^ A variable of type @'BVType' w@ multiplied by a constant


$(mkNuMatching [t| SplittingExpr |])
$(mkNuMatching [t| forall a . PermExpr a |])
$(mkNuMatching [t| forall a . BVFactor a |])
$(mkNuMatching [t| forall as . PermExprs as |])

instance Eq SplittingExpr where
  SplExpr_All == SplExpr_All = True
  SplExpr_All == _ = False

  (SplExpr_L spl1) == (SplExpr_L spl2) = spl1 == spl2
  (SplExpr_L _) == _ = False

  (SplExpr_R spl1) == (SplExpr_R spl2) = spl1 == spl2
  (SplExpr_R _) == _ = False

  (SplExpr_Star spl1_l spl1_r) == (SplExpr_Star spl2_l spl2_r) =
    spl1_l == spl2_l && spl1_r == spl2_r
  (SplExpr_Star _ _) == _ = False

  (SplExpr_Var x1) == (SplExpr_Var x2) = x1 == x2
  (SplExpr_Var _) == _ = False


instance Eq (PermExpr a) where
  (PExpr_Var x1) == (PExpr_Var x2) = x1 == x2
  (PExpr_Var _) == _ = False

  (PExpr_BV factors1 const1) == (PExpr_BV factors2 const2) =
    const1 == const2 && eqFactors factors1 factors2
    where
      eqFactors :: [BVFactor w] -> [BVFactor w] -> Bool
      eqFactors [] [] = True
      eqFactors (f : factors1) factors2
        | elem f factors2 = eqFactors factors1 (delete f factors2)
      eqFactors _ _ = False
  (PExpr_BV _ _) == _ = False

  (PExpr_Struct args1) == (PExpr_Struct args2) = args1 == args2 where
  (PExpr_Struct _) == _ = False

  (PExpr_LLVMWord e1) == (PExpr_LLVMWord e2) = e1 == e2
  (PExpr_LLVMWord _) == _ = False

  (PExpr_LLVMOffset x1 e1) == (PExpr_LLVMOffset x2 e2) =
    x1 == x2 && e1 == e2
  (PExpr_LLVMOffset _ _) == _ = False

  (PExpr_Spl spl1) == (PExpr_Spl spl2) = spl1 == spl2
  (PExpr_Spl _) == _ = False


instance Eq (PermExprs as) where
  PExprs_Nil == PExprs_Nil = True
  (PExprs_Cons es1 e1) == (PExprs_Cons es2 e2) = es1 == es2 && e1 == e2


instance Eq (BVFactor w) where
  (BVFactor i1 x1) == (BVFactor i2 x2) = i1 == i2 && x1 == x2


-- | Multiply a 'BVFactor' by a constant
multFactor :: Integer -> BVFactor w -> BVFactor w
multFactor i (BVFactor j x) = BVFactor (i*j) x

-- | Multiply a 'BVFactor' by a constant
multExpr :: (1 <= w, KnownNat w) => Integer -> PermExpr (BVType w) ->
            PermExpr (BVType w)
multExpr i (PExpr_Var x) = PExpr_BV [BVFactor i x] 0
multExpr i (PExpr_BV factors off) =
  PExpr_BV (map (multFactor i) factors) (i*off)

-- | Convert a bitvector expression to a sum of factors plus a constant
matchBVExpr :: (1 <= w, KnownNat w) => PermExpr (BVType w) ->
               ([BVFactor w], Integer)
matchBVExpr (PExpr_Var x) = ([BVFactor 1 x], 0)
matchBVExpr (PExpr_BV factors const) = (factors, const)

-- | Add two bitvector expressions
-- FIXME: normalize factors with the same variable!
addBVExprs :: (1 <= w, KnownNat w) =>
              PermExpr (BVType w) -> PermExpr (BVType w) ->
              PermExpr (BVType w)
addBVExprs (matchBVExpr -> (factors1, const1)) (matchBVExpr ->
                                                (factors2, const2)) =
  PExpr_BV (factors1 ++ factors2) (const1 + const2)

-- | Add a word expression to an LLVM pointer expression
addLLVMOffset :: (1 <= w, KnownNat w) =>
                 PermExpr (LLVMPointerType w) -> PermExpr (BVType w) ->
                 PermExpr (LLVMPointerType w)
addLLVMOffset (PExpr_Var x) off = PExpr_LLVMOffset x off
addLLVMOffset (PExpr_LLVMWord e) off = PExpr_LLVMWord $ addBVExprs e off
addLLVMOffset (PExpr_LLVMOffset x e) off =
  PExpr_LLVMOffset x $ addBVExprs e off

-- | Build a "default" expression for a given type
zeroOfType :: TypeRepr tp -> PermExpr tp
zeroOfType (BVRepr w) = withKnownNat w $ PExpr_BV [] 0
zeroOfType (testEquality splittingTypeRepr -> Just Refl) =
  PExpr_Spl SplExpr_All
zeroOfType _ = error "zeroOfType"


----------------------------------------------------------------------
-- * Permissions
----------------------------------------------------------------------

-- | A value permission is a permission to do something with a value, such as
-- use it as a pointer. This also includes a limited set of predicates on values
-- (you can think about this as "permission to assume the value satisfies this
-- predicate" if you like).
data ValuePerm (a :: CrucibleType) where
  -- | The trivial value perm
  ValPerm_True :: ValuePerm a

  -- | Says that a value is equal to a known static expression
  ValPerm_Eq :: PermExpr a -> ValuePerm a

  -- | The disjunction of two value permissions
  ValPerm_Or :: ValuePerm a -> ValuePerm a -> ValuePerm a

  -- | An existential binding of a value in a value permission
  ValPerm_Exists :: KnownRepr TypeRepr a =>
                    Binding (PermExpr a) (ValuePerm b) ->
                    ValuePerm b

  -- | A recursive / least fixed-point permission
  ValPerm_Mu :: Binding (ValuePerm a) (ValuePerm a) -> ValuePerm a

  -- | A value permission variable, for use in recursive permissions; note that
  -- we use names of type 'ValuePerm' and /not/ of type 'PermExpr', so that
  -- permission variables cannot be bound as expressions and vice-versa.
  ValPerm_Var :: Name (ValuePerm a) -> ValuePerm a

  -- | Says that an LLVM word is a pointer, i.e., with a non-zero block, where
  -- the memory pointed to has the given shape, and optionally we have
  -- permission to free the memory if we have write perms to @N@ words
  ValPerm_LLVMPtr :: (1 <= w, KnownNat w) =>
                     LLVMPtrPerm w -> ValuePerm (LLVMPointerType w)


-- | A permission to the memory referenced by an LLVM pointer
data LLVMPtrPerm w
  = LLVMFieldPerm { llvmFieldOffset :: PermExpr (BVType w),
                    llvmFieldSplitting :: SplittingExpr,
                    llvmFieldPerm :: ValuePerm (LLVMPointerType w) }
  | LLVMArrayPerm { llvmArrayOffset :: PermExpr (BVType w),
                    llvmArrayLen :: PermExpr (BVType w),
                    llvmArrayStride :: Integer,
                    llvmArraySplitting :: SplittingExpr,
                    llvmArrayPtrPerm :: LLVMPtrPerm w }
  | LLVMStarPerm (LLVMPtrPerm w) (LLVMPtrPerm w)
  | LLVMFreePerm (PermExpr (BVType w))


$(mkNuMatching [t| forall a . ValuePerm a |])
$(mkNuMatching [t| forall w . LLVMPtrPerm w |])


----------------------------------------------------------------------
-- * Substitutions
----------------------------------------------------------------------

-- | Workaround for the fact that Hobbits currently only support name and
-- bindings of kind star
data SubstElem (a :: *) where
  SubstElem :: PermExpr a -> SubstElem (PermExpr a)

unSubstElem :: SubstElem (PermExpr a) -> PermExpr a
unSubstElem (SubstElem e) = e

-- | A substitution assigns a permission expression to each bound name in a
-- name-binding context
newtype PermSubst ctx =
  PermSubst { unPermSubst :: MapRList SubstElem ctx }

emptySubst :: PermSubst RNil
emptySubst = PermSubst empty

extSubst :: PermSubst ctx -> PermExpr a -> PermSubst (ctx :> PermExpr a)
extSubst (PermSubst elems) e = PermSubst $ elems :>: SubstElem e

substLookup :: PermSubst ctx -> Member ctx (PermExpr a) -> PermExpr a
substLookup (PermSubst m) memb = unSubstElem $ mapRListLookup memb m

noPermsInSubst :: PermSubst ctx -> Member ctx (ValuePerm a) -> b
noPermsInSubst (PermSubst elems) memb =
  case mapRListLookup memb elems of { }

substVar :: PermSubst ctx -> Mb ctx (Name (PermExpr a)) -> PermExpr a
substVar s x =
  case mbNameBoundP x of
    Left memb -> substLookup s memb
    Right y -> PExpr_Var y

substBVFactor :: PermSubst ctx -> Mb ctx (BVFactor w) -> PermExpr (BVType w)
substBVFactor s [nuP| BVFactor i x |] = multExpr (mbLift i) (substVar s x)

class Substable a where
  subst :: PermSubst ctx -> Mb ctx a -> a

instance Substable SplittingExpr where
  subst s [nuP| SplExpr_All |] = SplExpr_All
  subst s [nuP| SplExpr_L spl |] = SplExpr_L $ subst s spl
  subst s [nuP| SplExpr_R spl |] = SplExpr_R $ subst s spl
  subst s [nuP| SplExpr_Star spl1 spl2 |] =
    SplExpr_Star (subst s spl1) (subst s spl2)
  subst s [nuP| SplExpr_Var x |] =
    case substVar s x of
      PExpr_Var y -> SplExpr_Var y
      PExpr_Spl spl -> spl

instance Substable (PermExpr a) where
  subst s [nuP| PExpr_Var x |] = substVar s x
  subst s [nuP| PExpr_BV factors off |] =
    foldr addBVExprs (PExpr_BV [] (mbLift off)) $
    map (substBVFactor s) $ mbList factors
  subst s [nuP| PExpr_Struct args |] =
    PExpr_Struct (subst s args)
  subst s [nuP| PExpr_LLVMWord e |] =
    PExpr_LLVMWord (subst s e)
  subst s [nuP| PExpr_LLVMOffset x off |] =
    addLLVMOffset (substVar s x) (subst s off)
  subst s [nuP| PExpr_Spl spl |] =
    PExpr_Spl (subst s spl)

instance Substable (PermExprs as) where
  subst s [nuP| PExprs_Nil |] = PExprs_Nil
  subst s [nuP| PExprs_Cons es e |] = PExprs_Cons (subst s es) (subst s e)

instance Substable (ValuePerm a) where
  subst s [nuP| ValPerm_True |] = ValPerm_True
  subst s [nuP| ValPerm_Eq e |] = ValPerm_Eq $ subst s e
  subst s [nuP| ValPerm_Or p1 p2 |] = ValPerm_Or (subst s p1) (subst s p2)
  subst s [nuP| ValPerm_Exists p |] =
    ValPerm_Exists $ nu $ \x -> subst (extSubst s $ PExpr_Var x) $ mbCombine p
  subst s [nuP| ValPerm_Mu p |] =
    ValPerm_Mu $ fmap (subst s) $ mbSwap p
  subst s [nuP| ValPerm_Var x |] =
    case mbNameBoundP x of
      Left memb -> noPermsInSubst s memb
      Right y -> ValPerm_Var y
  subst s [nuP| ValPerm_LLVMPtr p |] = ValPerm_LLVMPtr $ subst s p

instance Substable (LLVMPtrPerm a) where
  subst s [nuP| LLVMFieldPerm off spl p |] =
    LLVMFieldPerm (subst s off) (subst s spl) (subst s p)
  subst s [nuP| LLVMArrayPerm off len stride spl p |] =
    LLVMArrayPerm (subst s off) (subst s len) (mbLift stride)
    (subst s spl) (subst s p)
  subst s [nuP| LLVMStarPerm p1 p2 |] = LLVMStarPerm (subst s p1) (subst s p2)
  subst s [nuP| LLVMFreePerm len |] = LLVMFreePerm (subst s len)
