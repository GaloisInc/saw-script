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

module SAWScript.Heapster.Permissions where

import Data.Maybe
import Data.List
import Data.Binding.Hobbits
import GHC.TypeLits
import Control.Monad.Identity
import Control.Lens hiding ((:>))

import Data.Binding.Hobbits.NameMap (NameMap)
import qualified Data.Binding.Hobbits.NameMap as NameMap

import Data.Parameterized.Context hiding ((:>), empty)
import Data.Parameterized.NatRepr

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core


----------------------------------------------------------------------
-- * Monads that Support Name-Binding
----------------------------------------------------------------------

-- FIXME HERE: move this to Hobbits!
class Monad m => MonadBind m where
  mbM :: NuMatching a => Mb ctx (m a) -> m (Mb ctx a)

nuM :: (MonadBind m, NuMatching b) => (Name a -> m b) -> m (Binding a b)
nuM = mbM . nu

instance MonadBind Identity where
  mbM = Identity . fmap runIdentity

instance MonadBind Maybe where
  mbM [nuP| Just x |] = return x
  mbM [nuP| Nothing |] = Nothing


----------------------------------------------------------------------
-- * Expressions for Permissions
----------------------------------------------------------------------

-- | The Haskell type of expression variables
type ExprVar a = Name (PermExpr a)

-- | Expressions that represent "fractions" of a write permission
data SplittingExpr
  = SplExpr_All
  | SplExpr_L SplittingExpr
  | SplExpr_R SplittingExpr
  | SplExpr_Star SplittingExpr SplittingExpr
  | SplExpr_Var (ExprVar SplittingType)

-- | Crucible type for splitting expressions; we give them a Crucible type so
-- they can be existentially bound in the same way as other Crucible objects
type SplittingType = IntrinsicType "Splitting" EmptyCtx

-- | The object-level representation of 'SplittingType'
splittingTypeRepr :: TypeRepr SplittingType
splittingTypeRepr = knownRepr


-- | Expressions that are considered "pure" for use in permissions. Note that
-- these are in a normal form, that makes them easier to analyze.
data PermExpr (a :: CrucibleType) where
  PExpr_Var :: ExprVar a -> PermExpr a
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
                      ExprVar (LLVMPointerType w) ->
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
  BVFactor :: (1 <= w, KnownNat w) => Integer -> ExprVar (BVType w) ->
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

-- | The type of variables for use in value permissions. Note that we use names
-- of type 'ValuePerm' and /not/ of type 'PermExpr', so that permission
-- variables cannot be bound as expressions and vice-versa.
type PermVar a = Name (ValuePerm a)

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

  -- | A value permission variable, for use in recursive permissions
  ValPerm_Var :: PermVar a -> ValuePerm a

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


-- | Test if a permission is an equality permission
isEqPerm :: ValuePerm a -> Bool
isEqPerm (ValPerm_Eq _) = True
isEqPerm _ = False

-- | Extract @p1@ from a permission of the form @p1 \/ p2@
orPermLeft :: ValuePerm a -> ValuePerm a
orPermLeft (ValPerm_Or p _) = p
orPermLeft _ = error "orPermLeft"

-- | Extract @p2@ from a permission of the form @p1 \/ p2@
orPermRight :: ValuePerm a -> ValuePerm a
orPermRight (ValPerm_Or _ p) = p
orPermRight _ = error "orPermRight"

-- | Extract the body @p@ from a permission of the form @exists (x:tp).p@
exPermBody :: TypeRepr tp -> ValuePerm a -> Binding (PermExpr tp) (ValuePerm a)
exPermBody tp (ValPerm_Exists (p :: Binding (PermExpr tp') (ValuePerm a)))
  | Just Refl <- testEquality tp (knownRepr :: TypeRepr tp') = p
exPermBody _ _ = error "exPermBody"


----------------------------------------------------------------------
-- * Contexts of Crucible Types
----------------------------------------------------------------------

-- | FIXME: 'CruType' should have kind @'CrucibleType' -> *@ instead of @* -> *@
-- as it does here; this is a workaround for the fact that Hobbits currently
-- only supports name and bindings of kind star
data CruType a where
  CruType :: KnownRepr TypeRepr a => (CruType (PermExpr a))

-- | A context of Crucible types
newtype CruCtx ctx = CruCtx { unCruCtx :: MapRList CruType ctx }

-- | The empty context
emptyCruCtx :: CruCtx RNil
emptyCruCtx = CruCtx empty

-- | Add an element to the end of a context
extCruCtx :: KnownRepr TypeRepr a => CruCtx ctx -> CruCtx (ctx :> PermExpr a)
extCruCtx (CruCtx tps) = CruCtx (tps :>: CruType)


----------------------------------------------------------------------
-- * Generalized Substitution
----------------------------------------------------------------------

-- | Defines a substitution type @s@ that supports substituting into expression
-- and permission variables in a given monad @m@
class MonadBind m => SubstVar s m | s -> m where
  extSubst :: s ctx -> PermExpr a -> s (ctx :> PermExpr a)
  substExprVar :: s ctx -> Mb ctx (ExprVar a) -> m (PermExpr a)
  substPermVar :: s ctx -> Mb ctx (PermVar a) -> m (ValuePerm a)

-- | Generalized notion of substitution, which says that substitution type @s@
-- supports substituting into type @a@ in monad @m@
class SubstVar s m => Substable s a m where
  genSubst :: s ctx -> Mb ctx a -> m a

instance SubstVar s m => Substable s SplittingExpr m where
  genSubst s [nuP| SplExpr_All |] = return SplExpr_All
  genSubst s [nuP| SplExpr_L spl |] = SplExpr_L <$> genSubst s spl
  genSubst s [nuP| SplExpr_R spl |] = SplExpr_R <$> genSubst s spl
  genSubst s [nuP| SplExpr_Star spl1 spl2 |] =
    SplExpr_Star <$> genSubst s spl1 <*> genSubst s spl2
  genSubst s [nuP| SplExpr_Var x |] =
    substExprVar s x >>= \e ->
    case e of
      PExpr_Var y -> return $ SplExpr_Var y
      PExpr_Spl spl -> return spl

-- | Helper function to substitute into 'BVFactor's
substBVFactor :: SubstVar s m => s ctx -> Mb ctx (BVFactor w) ->
                 m (PermExpr (BVType w))
substBVFactor s [nuP| BVFactor i x |] =
  multExpr (mbLift i) <$> substExprVar s x

instance SubstVar s m => Substable s (PermExpr a) m where
  genSubst s [nuP| PExpr_Var x |] = substExprVar s x
  genSubst s [nuP| PExpr_BV factors off |] =
    foldr addBVExprs (PExpr_BV [] (mbLift off)) <$>
    mapM (substBVFactor s) (mbList factors)
  genSubst s [nuP| PExpr_Struct args |] =
    PExpr_Struct <$> genSubst s args
  genSubst s [nuP| PExpr_LLVMWord e |] =
    PExpr_LLVMWord <$> genSubst s e
  genSubst s [nuP| PExpr_LLVMOffset x off |] =
    addLLVMOffset <$> substExprVar s x <*> genSubst s off
  genSubst s [nuP| PExpr_Spl spl |] =
    PExpr_Spl <$> genSubst s spl

instance SubstVar s m => Substable s (PermExprs as) m where
  genSubst s [nuP| PExprs_Nil |] = return PExprs_Nil
  genSubst s [nuP| PExprs_Cons es e |] =
    PExprs_Cons <$> genSubst s es <*> genSubst s e

instance SubstVar s m => Substable s (ValuePerm a) m where
  genSubst s [nuP| ValPerm_True |] = return ValPerm_True
  genSubst s [nuP| ValPerm_Eq e |] = ValPerm_Eq <$> genSubst s e
  genSubst s [nuP| ValPerm_Or p1 p2 |] =
    ValPerm_Or <$> genSubst s p1 <*> genSubst s p2
  genSubst s [nuP| ValPerm_Exists p |] =
    ValPerm_Exists <$>
    nuM (\x -> genSubst (extSubst s $ PExpr_Var x) $ mbCombine p)
  genSubst s [nuP| ValPerm_Mu p |] =
    ValPerm_Mu <$> mbM (fmap (genSubst s) $ mbSwap p)
  genSubst s [nuP| ValPerm_Var x |] = substPermVar s x
  genSubst s [nuP| ValPerm_LLVMPtr p |] = ValPerm_LLVMPtr <$> genSubst s p

instance SubstVar s m => Substable s (LLVMPtrPerm a) m where
  genSubst s [nuP| LLVMFieldPerm off spl p |] =
    LLVMFieldPerm <$> genSubst s off <*> genSubst s spl <*> genSubst s p
  genSubst s [nuP| LLVMArrayPerm off len stride spl p |] =
    LLVMArrayPerm <$> genSubst s off <*> genSubst s len <*>
    return (mbLift stride) <*> genSubst s spl <*> genSubst s p
  genSubst s [nuP| LLVMStarPerm p1 p2 |] =
    LLVMStarPerm <$> genSubst s p1 <*> genSubst s p2
  genSubst s [nuP| LLVMFreePerm len |] = LLVMFreePerm <$> genSubst s len


----------------------------------------------------------------------
-- * Expression Substitutions
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

substLookup :: PermSubst ctx -> Member ctx (PermExpr a) -> PermExpr a
substLookup (PermSubst m) memb = unSubstElem $ mapRListLookup memb m

noPermsInSubst :: PermSubst ctx -> Member ctx (ValuePerm a) -> b
noPermsInSubst (PermSubst elems) memb =
  case mapRListLookup memb elems of { }

instance SubstVar PermSubst Identity where
  extSubst (PermSubst elems) e = PermSubst $ elems :>: SubstElem e
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> return $ substLookup s memb
      Right y -> return $ PExpr_Var y
  substPermVar s x =
    case mbNameBoundP x of
      Left memb -> noPermsInSubst s memb
      Right y -> return $ ValPerm_Var y

-- | Wrapper function to apply a substitution to an expression type
subst :: Substable PermSubst a Identity => PermSubst ctx -> Mb ctx a -> a
subst s mb = runIdentity $ genSubst s mb


----------------------------------------------------------------------
-- * Partial Substitutions
----------------------------------------------------------------------

-- | An element of a partial substitution = maybe an expression
data PSubstElem a where
  PSE_Just :: PermExpr a -> PSubstElem (PermExpr a)
  PSE_Nothing :: PSubstElem (PermExpr a)

unPSubstElem :: PSubstElem (PermExpr a) -> Maybe (PermExpr a)
unPSubstElem (PSE_Just e) = Just e
unPSubstElem PSE_Nothing = Nothing

-- | Partial substitutions assign expressions to some of the bound names in a
-- context
newtype PartialSubst ctx =
  PartialSubst { unPartialSubst :: MapRList PSubstElem ctx }

-- | Build an empty partial substitution for a given set of variables, i.e., the
-- partial substitution that assigns no expressions to those variables
emptyPSubst :: CruCtx ctx -> PartialSubst ctx
emptyPSubst = PartialSubst . mapMapRList (\CruType -> PSE_Nothing) . unCruCtx

-- | Extend a partial substitution with an unassigned variable
extPSubst :: PartialSubst ctx -> PartialSubst (ctx :> PermExpr a)
extPSubst (PartialSubst elems) = PartialSubst $ elems :>: PSE_Nothing

-- | Look up an optional expression in a partial substitution
psubstLookup :: PartialSubst ctx -> Member ctx (PermExpr a) ->
                Maybe (PermExpr a)
psubstLookup (PartialSubst m) memb = unPSubstElem $ mapRListLookup memb m

-- | "Proof" that there are no permissions in a partial substitution
noPermsInPSubst :: PartialSubst ctx -> Member ctx (ValuePerm a) -> b
noPermsInPSubst (PartialSubst elems) memb =
  case mapRListLookup memb elems of { }

instance SubstVar PartialSubst Maybe where
  extSubst (PartialSubst elems) e = PartialSubst $ elems :>: PSE_Just e
  substExprVar s x =
    case mbNameBoundP x of
      Left memb -> psubstLookup s memb
      Right y -> return $ PExpr_Var y
  substPermVar s x =
    case mbNameBoundP x of
      Left memb -> noPermsInPSubst s memb
      Right y -> return $ ValPerm_Var y

-- | Wrapper function to apply a partial substitution to an expression type
psubst :: Substable PartialSubst a Maybe => PartialSubst ctx -> Mb ctx a ->
          Maybe a
psubst s mb = genSubst s mb


----------------------------------------------------------------------
-- * Permission Sets
----------------------------------------------------------------------

-- | FIXME: workaround for the fact that Hobbits only support name types of kind
-- star
data PermsList (a :: *) where
  PermsList :: [ValuePerm a] -> PermsList (PermExpr a)

-- | A permission set associates a (possibly empty) list of permissions with
-- each expression variable in scope
newtype PermSet = PermSet { unPermSet :: NameMap PermsList }

-- | The lens for the permissions associated with a given variable
varPerms :: ExprVar a -> Lens' PermSet [ValuePerm a]
varPerms x =
  lens
  (\(PermSet nmap) ->
    case NameMap.lookup x nmap of
      Just (PermsList ps) -> ps
      Nothing -> [])
  (\(PermSet nmap) ps -> PermSet $ NameMap.insert x (PermsList ps) nmap)

-- | A location in a 'PermSet' of a specific permission on a variable
data PermLoc a = PermLoc (ExprVar a) Int

-- | The lens for the permission at a specific location in a 'PermSet'
varPerm :: PermLoc a -> Lens' PermSet (ValuePerm a)
varPerm (PermLoc x i) =
  -- FIXME: there is probably a nicer way in the Haskell lens library of
  -- handling the partiality here
  lens
  (\perms ->
    case perms ^? (varPerms x . element i) of
      Just p -> p
      Nothing -> error ("varPerm: no permission at position " ++ show i))
  (\perms p ->
    over (varPerms x)
    (\ps ->
      if i < length ps then (element i .~ p) ps else
        error ("varPerm: no permission at position " ++ show i))
    perms)

-- | Find all permissions of the form @x:eq(e)@ in a permission set, returning
-- both locations and the associated expressions for each such permission
findEqPerms :: ExprVar a -> PermSet -> [(PermLoc a, PermExpr a)]
findEqPerms x perms =
  map (\i ->
        case perms ^. varPerm (PermLoc x i) of
          ValPerm_Eq e -> (PermLoc x i, e)) $
  findIndices isEqPerm $ perms ^. varPerms x

-- | Replace an or permission at a given location with its left disjunct
permsElimOrLeft :: PermLoc a -> PermSet -> PermSet
permsElimOrLeft l = over (varPerm l) orPermLeft

-- | Replace an or permission at a given location with its right disjunct
permsElimOrRight :: PermLoc a -> PermSet -> PermSet
permsElimOrRight l = over (varPerm l) orPermRight

-- | Replace an existential permission at a given location with its body
permsElimExists :: PermLoc a -> TypeRepr tp -> PermSet ->
                   Binding (PermExpr tp) PermSet
permsElimExists l tp perms =
  nuWithElim1
  (\_ p_body -> set (varPerm l) p_body perms)
  (exPermBody tp $ perms ^. varPerm l)
