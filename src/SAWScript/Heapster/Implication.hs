{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SAWScript.Heapster.Implication where

import Data.Maybe
import Data.List
import Data.Kind as Kind
import Data.Functor.Product
import Data.Functor.Compose
import GHC.TypeLits
import Control.Lens hiding ((:>))
import Control.Monad
import Data.Functor.Identity
import Control.Applicative hiding (empty)
import qualified Control.Applicative as Applicative
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Trans.Maybe

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.CFG.Core

import Data.Binding.Hobbits
import SAWScript.Heapster.CruUtil
import SAWScript.Heapster.Permissions


----------------------------------------------------------------------
-- * Permission Implications
----------------------------------------------------------------------

-- FIXME: add error messages to Impl_Fail, for debugging by the user

-- | A simple implication is an implication that does not introduce any
-- variables or act on the 'varPermMap' part of a permission set. (Compare to
-- the more general 'PermImpl'.) It has the form
--
-- > P1 * ... * Pn -o P1' * ... * Pm'
--
-- where the types of @P1@ through @Pn@ are given by the first type argument
-- @ps_in@ and those of @P1'@ through @Pm'@ are given by the second, @ps_out@.
data SimplImpl ps_in ps_out where
  Simpl_Drop :: ExprVar a -> ValuePerm a -> SimplImpl (RNil :> a) RNil
  -- ^ Drop a permission, i.e., forget about it:
  --
  -- > x:p -o .

  SImpl_IntroOrL :: ExprVar a -> ValuePerm a -> ValuePerm a ->
                    SimplImpl (RNil :> a) (RNil :> a)
  -- ^ @SImpl_IntroOrL x p1 p2@ applies left disjunction introduction:
  --
  -- > x:p1 -o x:(p1 \/ p2)

  SImpl_IntroOrR :: ExprVar a -> ValuePerm a -> ValuePerm a ->
                    SimplImpl (RNil :> a) (RNil :> a)
  -- ^ @SImpl_IntroOrR x p1 p2 pf@ applies right disjunction introduction:
  --
  -- > x:p2 -o x:(p1 \/ p2)

  SImpl_IntroExists :: KnownRepr TypeRepr tp => ExprVar a -> PermExpr tp ->
                       Binding tp (ValuePerm a) ->
                       SimplImpl (RNil :> a) (RNil :> a)
  -- ^ @SImpl_IntroExists x e p@ applies existential introduction:
  --
  -- > x:[e/z]p -o x:(exists z.p)

  SImpl_Cast :: ExprVar a -> ExprVar a -> ValuePerm a ->
                SimplImpl (RNil :> a :> a) (RNil :> a)
  -- ^ Cast a proof of @y:p@ to one of @x:p@ using @x:eq(y)@:
  --
  -- > x:eq(y) * y:p -o x:p

  SImpl_IntroEqRefl :: ExprVar a -> SimplImpl RNil (RNil :> a)
  -- ^ Introduce a proof that @x:eq(x)@:
  --
  -- > . -o x:eq(x)

  SImpl_IntroConj :: ExprVar a -> SimplImpl RNil (RNil :> a)
  -- ^ Introduce an empty conjunction on @x@, i.e.:
  --
  -- > . -o x:true

  SImpl_ExtractConj :: ExprVar a -> [AtomicPerm a] -> Int ->
                       SimplImpl (RNil :> a) (RNil :> a :> a)
  -- ^ Extract the @i@th atomic permission out of a conjunct, putting it below
  -- that conjunct on the stack:
  --
  -- > x:(p1 * ... * pn) -o x:pi * x:(p1 * ... p(i-1) * ... * pn)

  SImpl_CopyConj :: ExprVar a -> [AtomicPerm a] -> Int ->
                    SimplImpl (RNil :> a) (RNil :> a :> a)
  -- ^ Copy the @i@th atomic permission out of a conjunct, assuming it is
  -- copyable, putting it below that conjunct on the stack:
  --
  -- > x:(p1 * ... * pn) -o x:pi * x:(p1 * ... * pn)

  SImpl_InsertConj :: ExprVar a -> AtomicPerm a -> [AtomicPerm a] -> Int ->
                      SimplImpl (RNil :> a :> a) (RNil :> a)
  -- ^ Insert an atomic permission below the top of the stack at the @i@th
  -- position in the conjunct on the top of the stack:
  --
  -- > x:p * x:(p1 * ... * pn)
  -- >   -o x:(p1 * ... * p(i-1) * p * pi * ... * pn)

  SImpl_CastLLVMWord ::
    ExprVar (LLVMPointerType w) ->
    PermExpr (BVType w) -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Cast a proof of @x:eq(word(e1))@ to one of @x:eq(word(e2))@ using an
  -- equality permission @e1=e2@ on top of the stack:
  --
  -- > x:eq(word(e1)) * x:prop(e1=e2) -o x:eq(word(e2))

  SImpl_CastLLVMPtr ::
    ExprVar (LLVMPointerType w) -> [AtomicPerm (LLVMPointerType w)] ->
    PermExpr (BVType w) -> ExprVar (LLVMPointerType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Cast a conjunction @y:(p1 * ... * pn)@ of LLVM type on the top of the
  -- stack to @x:(p1 - off * ... * pn - off)@ using a proof of @x:eq(y+off)@
  -- just below it on the stack:
  --
  -- > x:eq(y+off) * y:(p1 * ... * pn) -o x:(p1 - off * ... * pn - off)

  SImpl_CastLLVMFree ::
    ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
    PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Cast a proof of @x:free(e1)@ to one of @x:free(e2)@ using an equality
  -- permission @e1=e2@ on top of the stack:
  --
  -- > x:free(e1) * x:prop(e1=e2) -o x:free(e2)

  SImpl_CastLLVMFieldOffset ::
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Cast the offset of a field permission from @off@ to @off'@ using an
  -- equality permission @off=off'@ on the top of the stack:
  --
  -- > x:ptr((rw,off) |-> p) * x:prop(off=offf') -o x:ptr((rw,off') |-> p)

  SImpl_IntroLLVMFieldContents ::
    ExprVar (LLVMPointerType w) -> ExprVar (LLVMPointerType w) ->
    SimplImpl (RNil :> (LLVMPointerType w) :> (LLVMPointerType w))
    (RNil :> (LLVMPointerType w))
  -- ^ Combine proofs of @x:ptr((rw,off) |-> eq(y))@ and @y:p@ on the top of the
  -- permission stack into a proof of @x:ptr((rw,off) |-> p)@:
  --
  -- > x:ptr((rw,off) |-> eq(y)) * y:p -o x:ptr((rw,off) |-> p)

  Simpl_AddLLVMFieldLifetime ::
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w -> PermExpr LifetimeType ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)
  -- ^ Add a lifetime to a field permission:
  --
  -- > x:[ls]ptr((rw,off) |-> p) -o [l,ls]x:ptr((rw,off) |-> p)

  Simpl_RemoveLLVMFieldLifetime ::
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w -> PermExpr LifetimeType ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)
  -- ^ Remove a lifetime from a field permission if it is contained by another
  -- lifetime already on this field:
  --
  -- > x:[l,ls]ptr((rw,off) |-> p) * li:lcontains(l) -o [ls]x:ptr((rw,off) |-> p)

  Simpl_DemoteLLVMFieldWrite ::
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)
  -- ^ Demote an LLVM field permission from write to read:
  --
  -- > x:[ls]ptr((W,off) |-> p) -o [ls]x:ptr((R,off) |-> p)

  Simpl_CastLLVMFieldOffset ::
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LifetimeType)
    (RNil :> LLVMPointerType w)
  -- ^ Cast the offset of an LLVM field permission below the top of the stack
  -- cusing an equality permission on the top of the stack:
  --
  -- > x:[ls]ptr((rw,off) |-> p) * x:prop(off=off')
  -- >   -o [ls]x:ptr((rw,off') |-> p)

  Simpl_ShrinkLLVMArray ::
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    PermExpr (BVType w) -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Shrink the range of an array permission to the given offset and length,
  -- using a range subset permission on the top of the stack:
  --
  -- > x:array(off,<len,*stride,fps,bs) * x:prop([off',len') <= [off,len))
  -- >   -o x:array(off',<len',*stride,fps,bs)

  Simpl_LLVMArrayBorrow ::
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    PermExpr (BVType w) -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w :> LLVMPointerType w)
  -- ^ Borrow a range of an array permission at the given offset and length,
  -- adding a borrow to the original array permission and putting the new array
  -- permission just below the top of the stack. Requires a conjunction of
  -- propositional permissions stating that the given offset and length form a
  -- subset of the original offset and length and do not overlap with any of the
  -- existing borrows.
  --
  -- > x:array(off,<len,*stride,fps,bs)
  -- > * x:(prop([off',len') <= [off,len)) * disjoint(bs,[off',len')))
  -- >   -o x:array(off',<len',*stride,fps,[])
  -- >      * x:array(off,<len,*stride,fps,[off',len'):bs)

  Simpl_LLVMArrayReturn ::
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    PermExpr (BVType w) -> PermExpr (BVType w) ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Return a borrowed range of an array permission, undoing a borrow:
  --
  -- > x:array(off',<len',*stride,fps,[])
  -- > * x:array(off,<len,*stride,fps,[off',len'):bs)
  -- >   -o x:array(off,<len,*stride,fps,bs)

  Simpl_LLVMArrayIndex ::
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    PermExpr (BVType w) -> Int ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Extract out the @j@th field permission of the @i@th element of an array
  -- permission, where @j@ is a static 'Int' and @i@ is an expression. Requires
  -- a proposition permission on the top of the stack stating that @i@ is in the
  -- range of the array and that the specified field permission does not overlap
  -- with any of the existing borrows:
  --
  -- > x:array(off,<len,*stride,fps,bs)
  -- > * x:(prop(i \in [off,len)) * disjoint(bs,i*stride+j))
  -- >   -o x:(fp_j + offset i*stride)

  Simpl_LLVMArrayIndexBorrow ::
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    PermExpr (BVType w) -> Int ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Borrow the @j@th field permission of the @i@th element of an array
  -- permission, where @j@ is a static 'Int' and @i@ is an expression. Requires
  -- a proposition permission on the top of the stack stating that @i@ is in the
  -- range of the array and that the specified field permission does not overlap
  -- with any of the existing borrows, and adds a borrow of the given field:
  --
  -- > x:array(off,<len,*stride,fps,bs)
  -- > * x:(prop(i \in [off,len)) * disjoint(bs,i*stride+j))
  -- >   -o x:(fp_j + offset i*stride)
  -- >      * x:array(off,<len,*stride,fps,(i*stride+j):bs)

  Simpl_LLVMArrayIndexReturn ::
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    PermExpr (BVType w) -> Int ->
    SimplImpl (RNil :> LLVMPointerType w :> LLVMPointerType w)
    (RNil :> LLVMPointerType w)
  -- ^ Return the @j@th field permission of the @i@th element of an array
  -- permission, where @j@ is a static 'Int' and @i@ is an expression, undoing a
  -- borrow:
  --
  -- > x:(fp_j + offset i*stride)
  -- > * x:array(off,<len,*stride,fps,(i*stride+j):bs)
  -- >   -o x:array(off,<len,*stride,fps,bs)

  Simpl_LLVMArrayContents ::
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w -> [LLVMFieldPerm w] ->
    IsLLVMPointerTypeList w f_ps ->
    PermImpl ((:~:) f_ps) f_ps ->
    SimplImpl (RNil :> LLVMPointerType w) (RNil :> LLVMPointerType w)
  -- ^ FIXME HERE: describe this rule

  Simpl_SplitLifetime ::
    ExprVar a -> ValuePerm a -> PermExpr LifetimeType ->
    SimplImpl (RNil :> a :> LifetimeType)
    (RNil :> a :> LifetimeType)
  -- ^ Save a permission for later by adding the current lifetime to its type
  -- and storing the permission in the current lifetime for retrieval later:
  --
  -- > x:p * l:lowned(ps) -o x:[l]p * l:lowned(x:p, ps)

  Simpl_LContainsRefl :: ExprVar LifetimeType ->
                         SimplImpl RNil (RNil :> LifetimeType)
  -- ^ Reflexivity for @lcontains@ proofs:
  --
  -- > . -o l:lcontains(l)

  Simpl_LContainsAlways :: ExprVar LifetimeType ->
                           SimplImpl RNil (RNil :> LifetimeType)
  -- ^ Every lifetime is contained by @always@:
  --
  -- > . -o always:lcontains(l)

  Simpl_LContainsTrans :: ExprVar LifetimeType -> ExprVar LifetimeType ->
                          ExprVar LifetimeType ->
                          SimplImpl (RNil :> LifetimeType :> LifetimeType)
                          (RNil :> LifetimeType)
  -- ^ Transitively combine @lcontains@ proofs:
  --
  -- > l1:lcontains(l2) * l2:lcontains(l3) -o l1:lcontains(l3)

  Simpl_FoldMu :: ExprVar a -> Binding (ValuePerm a) (ValuePerm a) ->
                  SimplImpl (RNil :> a) (RNil :> a)
  -- ^ Fold a mu permission:
  --
  -- > x:[mu X.p / X]p -o x:(mu X.p)

  Simpl_UnfoldMu :: ExprVar a -> Binding (ValuePerm a) (ValuePerm a) ->
                    SimplImpl (RNil :> a) (RNil :> a)
  -- ^ Unfold a mu permission:
  --
  -- > x:(mu X.p) -o x:[mu X.p / X]p

  Simpl_Mu ::
    ExprVar (LLVMPointerType w) -> Binding (ValuePerm a) (ValuePerm a) ->
    PermImpl ((:~:) (RNil :> a)) (RNil :> a) ->
    SimplImpl (RNil :> a) (RNil :> a)
  -- ^ FIXME HERE: describe this rule


data PermImpl1 ps_in ps_outs where
  Impl1_Fail :: PermImpl1 ps RNil

  Impl1_Catch :: PermImpl1 ps (RNil :> '(RNil, ps) :> '(RNil, ps))

  Impl1_Push :: ExprVar a -> ValuePerm a ->
                PermImpl1 ps (RNil :> '(RNil, ps :> a))

  Impl1_Pop :: ExprVar a -> ValuePerm a ->
               PermImpl1 (ps :> a) (RNil :> '(RNil, ps))

  Impl1_ElimOr :: ExprVar a -> ValuePerm a -> ValuePerm a ->
                  PermImpl1 (ps :> a)
                  (RNil :> '(RNil, ps :> a) :> '(RNil, ps :> a))

  Impl1_ElimExists :: KnownRepr TypeRepr tp => ExprVar a ->
                      Binding tp (ValuePerm a) ->
                      PermImpl1 (ps :> a) (RNil :> '(RNil :> tp, ps :> a))

  Impl1_Simpl :: SimplImpl ps_in ps_out ->
                 PermImpl1 ps_in (RNil :> '(RNil, ps_out))

  Impl1_ElimLLVMFieldContents ::
    ExprVar (LLVMPointerType w) -> LLVMFieldPerm w ->
    PermImpl1 (ps :> LLVMPointerType w)
    (RNil :> '(RNil :> LLVMPointerType w, ps :> LLVMPointerType w))

  Impl1_TryProveBVProp ::
    ExprVar (LLVMPointerType w) -> BVProp w ->
    PermImpl1 ps (RNil :> '(RNil, ps :> LLVMPointerType w) :> '(RNil, ps))


data PermImpl r ps where
  PermImpl_Done :: r ps -> PermImpl r ps
  PermImpl_Step :: PermImpl1 ps_in ps_outs ->
                   MapRList (MbPermImpl r) ps_outs ->
                   PermImpl r ps_in


type family Fst (p :: (k1,k2)) :: k1 where
  Fst '(x,_) = x

type family Snd (p :: (k1,k2)) :: k2 where
  Snd '(_,y) = y

newtype MbPermImpl r bs_ps =
  MbPermImpl { unMbPermImpl :: Mb (Fst bs_ps) (PermImpl r (Snd bs_ps)) }

type IsLLVMPointerTypeList w ps = MapRList ((:~:) (LLVMPointerType w)) ps

simplImplIn :: SimplImpl ps_in ps_out -> MapRList ValuePerm ps_in
simplImplIn = error "FIXME HERE NOW"

simplImplOut :: SimplImpl ps_in ps_out -> MapRList ValuePerm ps_out
simplImplOut = error "FIXME HERE NOW"

applySimplImpl :: Proxy ps -> SimplImpl ps_in ps_out ->
                  PermSet (ps :++: ps_in) -> PermSet (ps :++: ps_out)
applySimplImpl = error "FIXME HERE NOW"


newtype MbPermSet bs_ps = MbPermSet (Mb (Fst bs_ps) (PermSet (Snd bs_ps)))

applyImpl1 :: PermImpl1 ps_in ps_outs -> PermSet ps_in ->
              MapRList MbPermSet ps_outs
applyImpl1 = error "FIXME HERE NOW"


-- | A @'PermImpl' r ls@ is a proof tree of the judgment
--
-- > Gamma | Pl * P |- (Gamma1 | Pl1 * P1) \/ ... \/ (Gamman | Pln * Pn)
--
-- that contains an element of type @r@ at each leaf of the proof tree. Each
-- disjunct on the right of the judgment corresponds to a different leaf in the
-- tree, while each @Gammai@ denotes the variables that are bound on the path
-- from the root to that leaf. The @ls@ argument captures the form of the
-- "distinguished" left-hand side permissions @Pl@.
--
-- FIXME: explain that @Pl@ is like a stack, and that intro rules apply to the
-- top of the stack
--
-- FIXME: it would be nice to have PermImpl r ps_out ps_in, where ps_out is
-- guaranteed to be the stack shape at any Impl_Done, but this would make our
-- generalized monad below more complicated...

{-
data PermImpl (r :: Ctx CrucibleType -> Type) ps where
  Impl_Done :: r ps -> PermImpl r ps
  -- ^ The proof is finished; i.e., implements the rule
  --
  -- > -------------------------------
  -- > Gin | Pl * Pin |- . | Pin

  Impl_Fail :: PermImpl r ps
  -- ^ The empty tree, with no disjunctive possibilities; i.e., implements the
  -- rule
  --
  -- > ------------------------------
  -- > Gin | Pl * Pin |- anything

  Impl_Catch :: PermImpl r ps -> PermImpl r ps -> PermImpl r ps
  -- ^ Copy the same permissions into two different elimination trees, where an
  -- 'Impl_Fail' in the first tree "calls" the second tree, just like a
  -- try-catch block for exceptions. This implements the rule:
  --
  -- > pf1 = Gin | Pl * Pin |- rets1    pf2 = Gin | Pl * Pin |- rets2
  -- > --------------------------------------------------------------
  -- > Gin | Pl * Pin |- rets1, rets2

  Impl_Push :: ExprVar a -> ValuePerm a -> PermImpl r (ps :> a) ->
               PermImpl r ps
  -- ^ "Push" all of the permissions in the permission set for a variable, which
  -- should be equal to the supplied permission, after deleting those
  -- permissions from the input permission set:
  --
  -- > Gin | Pl,x:p * Pin |- rets
  -- > ---------------------------
  -- > Gin | Pl * Pin, x:p |- rets

  Impl_Pop :: ExprVar a -> ValuePerm a -> PermImpl r ps ->
              PermImpl r (ps :> a)
  -- ^ "Pop" an @x:p@ permission from the top of the permission stack back to
  -- the primary permission for @x@, assuming that the primary permission for
  -- @x@ is currently equal to @true@
  --
  -- > Gin | Pl * Pin, x:p |- rets
  -- > ----------------------------------
  -- > Gin | Pl,x:p * Pin, x:true |- rets

  Impl_ElimOr :: ExprVar a -> PermImpl r (ps :> a) -> PermImpl r (ps :> a) ->
                 PermImpl r (ps :> a)
  -- ^ Eliminate a 'ValPerm_Or' on the top of the stack, replacing it with the
  -- left- and right-hand sides in the two sub-eliminations
  --
  -- > pf1 = Gin | Pl, x:p1 * Pin |- GsPs1  pf2 = Gin | Pl, x:p2 * Pin |- GsPs2
  -- > -------------------------------------------------------------------------
  -- > Gin | Pl, x:(p1 \/ p2) * Pin |- GsPs1, GsPs2

  Impl_ElimExists :: KnownRepr TypeRepr tp => ExprVar a ->
                     Binding tp (PermImpl r ps) ->
                     PermImpl r ps
  -- ^ Eliminate an existential, i.e., a 'ValPerm_Exists', on the given variable
  --
  -- pf = Gin, z:tp | Pl, x:p * Pin |- rets
  -- ------------------------------------------------------
  -- Gin | Pl, x:(exists z:tp. p) * Pin |- rets

  Impl_ElimLLVMFieldContents ::
    ExprVar (LLVMPointerType w) ->
    Binding (LLVMPointerType w) (PermImpl r (ps :> LLVMPointerType w :>
                                             LLVMPointerType w)) ->
    PermImpl r (ps :> LLVMPointerType w)
  -- ^ Eliminate a field permission @x:ptr((rw,off) |-> p)@ into a permission
  -- @x:ptr((rw,off) |-> eq(y))@ that the field contains a fresh variable @y@ and
  -- a permission @y:p@ on @y@:
  --
  -- > Gin | Pl, x:ptr(pps1, (rw,off) |-> eq(y), pps2), y:p * Pin |- rets
  -- > -----------------------------------------------------------------
  -- > Gin | Pl, x:ptr(pps1, (rw,off) |-> p, pps2) * Pin |- rets

  Impl_TryProveBVProp :: ExprVar (LLVMPointerType w) -> BVProp w ->
                         PermImpl r (ps :> LLVMPointerType w) ->
                         PermImpl r ps
                         PermImpl r ps
  -- ^ Try to prove a bitvector proposition using a dynamic check, passing a
  -- proof of that proposition to the left branch on success and calling the
  -- right branch on failure:
  --
  -- > Gin | Pl,x:prop(p) * Pin |- rets      Gin | Pl * Pin |- rets
  -- > ------------------------------------------------------------
  -- > Gin | Pl * Pin |- rets

  Impl_IntroLLVMArrayContents ::
    ExprVar (LLVMPointerType w) -> LLVMArrayPerm w ->
    LLVMFieldPerms w f_ps ->
    PermImpl UnitF f_ps ->
    PermImpl r (ps :> LLVMPointerType w) ->
    PermImpl r (ps :> LLVMPointerType w)
  -- ^ Prove one array permission from another by proving that the fields of the
  -- first imply those of the second:
  --

  Impl_Simpl :: Proxy ps -> SimplImpl ps_in ps_out ->
                PermImpl r (ps :++: ps_out) ->
                PermImpl r (ps :++: ps_in)
  -- ^ Apply a simple implication to the top permissions on the stack:
  --
  -- > Gin | Pl,ps_out * Pin |- rets      ps_in -o ps_out
  -- > --------------------------------------------------
  -- > Gin | Pl,ps_in * Pin |- rets


$(mkNuMatching [t| forall ps_in ps_out. SimplImpl ps_in ps_out |])
$(mkNuMatching [t| forall r ps. NuMatchingAny1 r => PermImpl r ps |])


----------------------------------------------------------------------
-- * Generalized Monads
----------------------------------------------------------------------

-- | A generalized monad has additional "input" and "output" types, that
-- sequence together "backwards" through the generalized bind operation. Mostly
-- this is to support 'GenContM', below.
--
-- Note that a generalized monad @m@ should always be a standard monad when the
-- input and output types are the same; i.e., @m r r@ should always be a
-- monad. I do not know a nice way to encode this in Haskell, however...
class GenMonad (m :: k -> k -> Kind.* -> Kind.*) where
  -- | Generalized return
  greturn :: a -> m r r a
  -- | Generalized bind, that passes the output of @f@ to the input of @m@
  (>>>=) :: m r2 r3 a -> (a -> m r1 r2 b) -> m r1 r3 b

infixl 1 >>>=
infixl 1 >>>

(>>>) :: GenMonad m => m r2 r3 () -> m r1 r2 a -> m r1 r3 a
m1 >>> m2 = m1 >>>= \() -> m2

class GenMonadT (t :: (k1 -> k1 -> Kind.* -> Kind.*) ->
                 k2 -> k2 -> Kind.* -> Kind.*) p1 p2 q1 q2 |
  t q1 q2 -> p1 p2 , t q1 p2 -> q2 p1 , t p1 q2 -> p2 q1 where
  glift :: GenMonad m => m p1 p2 a -> t m q1 q2 a


-- | The generalized continuation transformer, which can have different types
-- for the input vs output continuations
newtype GenContM rin rout a =
  GenContM { runGenContM :: (a -> rin) -> rout }

liftGenContM :: Monad m => m a -> GenContM (m b) (m b) a
liftGenContM m = GenContM $ \k -> m >>= k

instance Functor (GenContM r r) where
  fmap f m = m >>= return . f

instance Applicative (GenContM r r) where
  pure = return
  (<*>) = ap

instance Monad (GenContM r r) where
  return x = GenContM $ \k -> k x
  GenContM m >>= f = GenContM $ \k -> m $ \a -> runGenContM (f a) k

instance GenMonad GenContM where
  greturn x = GenContM $ \k -> k x
  (GenContM m) >>>= f = GenContM $ \k -> m $ \a -> runGenContM (f a) k

{-
-- | Change the return type constructor @r@ by mapping the new input type to the
-- old and mapping the old output type to the new
withAltContM :: (r2 pin2 -> r1 pin1) -> (r1 pout1 -> r2 pout2) ->
                GenContM r1 pin1 pout1 a -> GenContM r2 pin2 pout2 a
withAltContM f_in f_out (GenContM m) =
  GenContM $ \k -> f_out (m (f_in . k))
-}

-- | Typeclass for generalized monads that allow a pure capture of the CC
class GenMonad m => GenMonadCaptureCC rin rout m p1 p2 |
  m p1 -> rin , m p2 -> rout , m p1 rout -> p2 , m p2 rin -> p1 where
  gcaptureCC :: ((a -> rin) -> rout) -> m p1 p2 a

instance GenMonadCaptureCC r1 r2 GenContM r1 r2 where
  gcaptureCC f = GenContM f

instance GenMonadCaptureCC rin rout m q1 q2 =>
         GenMonadCaptureCC rin rout (GenStateT m) '(s,q1) '(s,q2) where
  gcaptureCC f = glift $ gcaptureCC f

gmapRet :: GenMonadCaptureCC rin rout m p1 p2 => (rin -> rout) -> m p1 p2 ()
gmapRet f_ret =
  gcaptureCC $ \k -> f_ret $ k ()

-- | Name-binding in the generalized continuation monad (FIXME: explain)
gopenBinding :: (GenMonadCaptureCC rin rout m p1 p2, TypeCtx ctx) =>
                (Mb ctx rin -> rout) -> Mb ctx a ->
                m p1 p2 (MapRList Name ctx, a)
gopenBinding f_ret mb_a =
  gcaptureCC $ \k ->
  f_ret $ flip nuMultiWithElim1 mb_a $ \names a ->
  k (names, a)

gopenBinding1 :: GenMonadCaptureCC rin rout m p1 p2 =>
                 (Binding a rin -> rout) -> Binding a b ->
                 m p1 p2 (Name a, b)
gopenBinding1 f_ret mb_b =
  gopenBinding f_ret mb_b >>>= \(_ :>: nm, b) -> greturn (nm,b)


{-
class GenMonad m => GenMonadShift r m | m -> r where
  gshift :: ((a -> m p1 p1 (r p2)) -> m p3 p4 (r p3)) -> m p2 p4 a

instance GenMonadShift r (GenContM r) where
  gshift f = GenContM $ \k -> runGenContM (f (\a -> greturn (k a))) id
-}


-- | Running generalized computations in "parallel"
class GenMonad m => GenMonadPar r m p1 p2 | m p1 p2 -> r where
  gparallel :: (r -> r -> r) -> m p1 p2 a -> m p1 p2 a -> m p1 p2 a

instance GenMonadPar r2 GenContM r1 r2 where
  gparallel f (GenContM m1) (GenContM m2) =
    GenContM $ \k -> f (m1 k) (m2 k)

instance GenMonadPar r m q1 q2 =>
         GenMonadPar r (GenStateT m) '(s1,q1) '(s2,q2) where
  gparallel f m1 m2 =
    GenStateT $ \s ->
    gparallel f
    (unGenStateT m1 s) (unGenStateT m2 s)

-- | The generalized state monad. Don't get confused: the parameters are
-- reversed, so @p2@ is the /input/ state param type and @p1@ is the /output/.
newtype GenStateT (m :: k -> k -> Kind.* -> Kind.*) p1 p2 a =
  GenStateT { unGenStateT :: Fst p2 -> m (Snd p1) (Snd p2) (a, Fst p1) }

-- | This version of 'unGenStateT' tells GHC to make the parameters into actual
-- type-level pairs, i.e., it makes GHC reason extensionally about pairs
runGenStateT :: GenStateT m '(s1,q1) '(s2,q2) a -> s2 -> m q1 q2 (a, s1)
runGenStateT = unGenStateT

instance Monad (m (Snd p) (Snd p)) => Functor (GenStateT m p p) where
  fmap f m = m >>= return . f

instance Monad (m (Snd p) (Snd p)) => Applicative (GenStateT m p p) where
  pure = return
  (<*>) = ap

instance Monad (m (Snd p) (Snd p)) => Monad (GenStateT m p p) where
  return x = GenStateT $ \s -> return (x, s)
  (GenStateT m) >>= f =
    GenStateT $ \s -> m s >>= \(a, s') -> unGenStateT (f a) s'

instance GenMonadT GenStateT q1 q2 '(s,q1) '(s,q2) where
  glift m = GenStateT $ \s -> m >>>= \a -> greturn (a, s)

instance GenMonad m => GenMonad (GenStateT m) where
  greturn x = GenStateT $ \s -> greturn (x, s)
  (GenStateT m) >>>= f =
    GenStateT $ \s -> m s >>>= \(a, s') -> unGenStateT (f a) s'

-- | FIXME: documentation
gliftGenStateT :: (GenMonad m) =>
                  m q1 q2 a -> GenStateT m '(s, q1) '(s, q2) a
gliftGenStateT m = glift m

-- | Run a generalized state computation with a different state type @s2@ inside
-- one with state type @s1@, using a lens-like pair of a getter function to
-- extract out the starting inner @s2@ state from the outer @s1@ state and an
-- update function to update the resulting outer @s1@ state with the final inner
-- @s2@ state.
withAltStateM :: GenMonad m => (s2' -> s2) -> (s2' -> s1 -> s1') ->
                 GenStateT m '(s1,q1) '(s2,q2) a ->
                 GenStateT m '(s1',q1) '(s2',q2) a
withAltStateM s_get s_update m =
  gget >>>= \s ->
  gput (s_get s) >>>
  m >>>= \a ->
  gget >>>= \s' ->
  gput (s_update s s') >>>
  greturn a

instance (Monad (m (Snd p) (Snd p)), s ~ Fst p) =>
         MonadState s (GenStateT m p p) where
  get = GenStateT $ \s -> return (s, s)
  put s = GenStateT $ \_ -> return ((), s)

class GenMonad m => GenMonadGet s m p | m p -> s where
  gget :: m p p s

class GenMonad m => GenMonadPut s m p1 p2 | m p1 p2 -> s where
  gput :: s -> m p1 p2 ()

instance GenMonad m => GenMonadGet s (GenStateT m) '(s,q) where
  gget = GenStateT $ \s -> greturn (s, s)

instance GenMonad m =>
         GenMonadPut s1 (GenStateT m) '(s1,q) '(s2,q) where
  gput s = GenStateT $ \_ -> greturn ((), s)

gmodify :: (GenMonadGet s1 m p2, GenMonadPut s2 m p1 p2) =>
           (s1 -> s2) -> m p1 p2 ()
gmodify f =
  gget >>>= \s -> gput (f s)

{-
class GenMonad m =>
      GenMonadState (s :: sk -> Type) (m :: k -> k -> Type -> Type) | m -> s where
  type GStateParam m (p :: k) :: sk
  gget :: m p p (s (GStateParam m p))
  gput :: s (GStateParam m p) -> m p p ()

instance GenMonad m => GenMonadState s (GenStateT s m) where
  type GStateParam (GenStateT s m) p = Fst p
  gget = GenStateT $ \s -> greturn (s, s)
  gput s = GenStateT $ \_ -> greturn ((), s)
-}


-- | The generalized state-continuation monad
type GenStateContM s1 r1 s2 r2 = GenStateT GenContM '(s1,r1) '(s2,r2)

{-
-- | Change both the state and return types for the state-continuation monad
withAltContStateM :: (r2 qin -> r1 qin) -> (r1 qout -> r2 qout) ->
                     (s2 pout -> s1 pout) -> (s2 pout -> s1 pin -> s2 pin) ->
                     GenStateContM s1 r1 pin qin pout qout a ->
                     GenStateContM s2 r2 pin qin pout qout a
withAltContStateM f_in f_out s_get s_update m =
  gget >>>= \s ->
  glift (withAltContM f_in f_out $
         runGenStateT m $ s_get s) >>>= \(a,s') ->
  gput (s_update s s') >>>
  greturn a
-}

-- | Map both the state and return types for the state-continuation monad
gmapRetAndState :: (s2 -> s1) -> (r1 -> r2) -> GenStateContM s1 r1 s2 r2 ()
gmapRetAndState f_st f_ret =
  gmodify f_st >>> gmapRet f_ret

-- | Abort the current state-continuation computation and just return an @r2@
--
-- FIXME: figure out how to write this with something like 'gcaptureCC'...? The
-- problem is that 'gcaptureCC' will not allow us to change the state type...
gabortM :: r2 -> GenStateContM s1 r1 s2 r2 a
gabortM ret = GenStateT $ \_ -> GenContM $ \_ -> ret


----------------------------------------------------------------------
-- * Permission Implication Monad
----------------------------------------------------------------------

data ImplState vars ps =
  ImplState { _implStatePerms :: PermSet ps,
              _implStateVars :: CruCtx vars,
              _implStatePSubst :: PartialSubst vars,
              _implStateLifetimes :: [ExprVar LifetimeType]
              -- ^ Stack of active lifetimes, where the first element is the
              -- current lifetime (we should have an @lowned@ permission for it)
              -- and each lifetime contains (i.e., has an @lcontains@ permission
              -- for) the next lifetime in the stack
            }
makeLenses ''ImplState

mkImplState :: CruCtx vars -> PermSet ps -> ImplState vars ps
mkImplState vars perms =
  ImplState { _implStateVars = vars,
              _implStatePerms = perms,
              _implStatePSubst = emptyPSubst vars,
              _implStateLifetimes = [] }

extImplState :: KnownRepr TypeRepr tp => ImplState vars ps ->
                ImplState (vars :> tp) ps
extImplState s =
  s { _implStateVars = extCruCtx (_implStateVars s),
      _implStatePSubst = extPSubst (_implStatePSubst s) }

unextImplState :: ImplState (vars :> a) ps -> ImplState vars ps
unextImplState s =
  s { _implStateVars = unextCruCtx (_implStateVars s),
      _implStatePSubst = unextPSubst (_implStatePSubst s) }

-- | The implication monad is the permission monad that uses 'ImplState'
type ImplM vars r ps_out ps_in =
  GenStateContM (ImplState vars ps_out) (PermImpl r ps_out)
  (ImplState vars ps_in) (PermImpl r ps_in)


-- | Run an 'ImplM' computation by passing it a @vars@ context, a starting
-- permission set, and an @r@
runImplM :: CruCtx vars -> PermSet ps_in -> r ps_out ->
            ImplM vars r ps_out ps_in () -> PermImpl r ps_in
runImplM vars perms r m =
  runGenContM (runGenStateT m (mkImplState vars perms)) (const $ Impl_Done r)


----------------------------------------------------------------------
-- * Permissions Operations in a Permission Monad
----------------------------------------------------------------------

-- | Look up the current partial substitution
getPSubst :: ImplM vars r ps ps (PartialSubst vars)
getPSubst = view implStatePSubst <$> gget

-- | Apply the current partial substitution to an expression, raising an error
-- with the given string if the partial substitution is not complete enough
partialSubstForceM :: Substable PartialSubst a Maybe => Mb vars a -> String ->
                      ImplM vars r ps ps a
partialSubstForceM mb_e msg =
  getPSubst >>>= \psubst ->
  greturn (partialSubstForce psubst mb_e msg)

-- | Modify the current partial substitution
modifyPSubst :: (PartialSubst vars -> PartialSubst vars) ->
                ImplM vars r ps ps ()
modifyPSubst f = gmodify (over implStatePSubst f)

-- | Set the value for an existential variable in the current substitution,
-- raising an error if it is already set
setVarM :: Member vars a -> PermExpr a -> ImplM vars r ps ps ()
setVarM x e = modifyPSubst (psubstSet x e)

-- | Run an implication computation with one more existential variable,
-- returning the optional expression it was bound to in the current partial
-- substitution when it is done
withExtVarsM :: KnownRepr TypeRepr tp =>
                ImplM (vars :> tp) r ps1 ps2 a ->
                ImplM vars r ps1 ps2 (a, Maybe (PermExpr tp))
withExtVarsM m =
  withAltStateM extImplState (const unextImplState) $
  (m >>>= \a ->
    getPSubst >>>= \psubst ->
    greturn (a, psubstLookup psubst Member_Base))

-- | Get the current lifetime
getCurLifetime :: ImplM vars r ps ps (ExprVar LifetimeType)
getCurLifetime =
  (view implStateLifetimes <$> gget) >>>= \ls ->
  case ls of
    l:_ -> greturn l
    [] -> error "getCurLifetime: no current lifetime!"

-- | Push a lifetime onto the lifetimes stack
pushLifetime :: ExprVar LifetimeType -> ImplM vars r ps ps ()
pushLifetime l = gmodify (over implStateLifetimes (l:))

-- | Pop a lifetime off of the lifetimes stack
popLifetime :: ImplM vars r ps ps (ExprVar LifetimeType)
popLifetime =
  getCurLifetime >>>= \l ->
  gmodify (over implStateLifetimes tail) >>>
  greturn l

-- | Get the current 'PermSet'
getPerms :: ImplM vars r ps ps (PermSet ps)
getPerms = view implStatePerms <$> gget

-- | Look up the current permission for a given variable
getPerm :: ExprVar a -> ImplM vars r ps ps (ValuePerm a)
getPerm x = view (implStatePerms . varPerm x) <$> gget

-- | Get the pointer permissions for a variable @x@, assuming @x@ has LLVM
-- pointer permissions
getLLVMPtrPerms :: ExprVar (LLVMPointerType w) ->
                   ImplM vars r ps ps [LLVMPtrPerm w]
getLLVMPtrPerms x =
  view (implStatePerms . varPerm x . llvmPtrPerms) <$> gget

-- | Get the distinguished permission stack
getDistPerms :: ImplM vars r ps ps (DistPerms ps)
getDistPerms = view (implStatePerms . distPerms) <$> gget

-- | Get the top permission in the stack
getTopDistPerm :: ExprVar a -> ImplM vars r (ps :> a) (ps :> a) (ValuePerm a)
getTopDistPerm x = view (implStatePerms . topDistPerm x) <$> gget

{-

-- | Get the index of the last 'LLVMPtrPerm' in the @x:ptr(pps)@ permission on
-- the top of the stack
getTopPermLastLLVMIx :: ExprVar (LLVMPointerType w) ->
                        ImplM vars r (ps :> LLVMPointerType w)
                        (ps :> LLVMPointerType w) Int
getTopPermLastLLVMIx x =
  getTopDistPerm x >>>= \p ->
  let ret = length (p ^. llvmPtrPerms) - 1 in
  if ret >= 0 then greturn ret else
    error "getTopPermLastLLVMIx"
-}

-- | Set the current 'PermSet'
setPerms :: PermSet ps -> ImplM vars r ps ps ()
setPerms perms = modify $ set (implStatePerms) perms

-- | Set the current permission for a given variable
setPerm :: ExprVar a -> ValuePerm a -> ImplM vars r ps ps ()
setPerm x p = modify $ set (implStatePerms . varPerm x) p

-- | Map the final return value and the current permissions
gmapRetAndPerms :: (PermSet ps2 -> PermSet ps1) ->
                   (PermImpl r ps1 -> PermImpl r ps2) ->
                   ImplM vars r ps1 ps2 ()
gmapRetAndPerms f_perms f_impl =
  gmapRetAndState (over implStatePerms f_perms) f_impl

-- | Terminate the current proof branch with a failure
implFailM :: ImplM vars r ps_any ps a
implFailM = gabortM Impl_Fail

{- FIXME: this should be part of the run method for ImplM...?
-- | Finish the current proof branch successfully with an 'Impl_Done'
implDoneM :: ImplM vars r ps ps ()
implDoneM = gmapRetAndState id Impl_Done
-}

-- | "Push" all of the permissions in the permission set for a variable, which
-- should be equal to the supplied permission, after deleting those permissions
-- from the input permission set. This is like a simple "proof" of @x:p@.
implPushM :: ExprVar a -> ValuePerm a -> ImplM vars r (ps :> a) ps ()
implPushM x p =
  gmapRetAndPerms (pushPerm x p . deletePerm x p) (Impl_Push x p)

-- | Call 'implPushM' for multiple @x:p@ permissions
implPushMultiM :: DistPerms ps -> ImplM vars r ps RNil ()
implPushMultiM DistPermsNil = greturn ()
implPushMultiM (DistPermsCons ps x p) =
  implPushMultiM ps >>> implPushM x p

-- | Pop a permission from the top of the stack back to the primary permission
-- for a variable, assuming that the primary permission for that variable is
-- empty, i.e., is the @true@ permission
implPopM :: ExprVar a -> ValuePerm a -> ImplM vars r ps (ps :> a) ()
implPopM x p =
  gmapRetAndPerms
  (\ps -> let (ps', p') = popPerm x ps in
    if p == p' then
      setVarPerm x p' ps'
    else error "implPopM: current and expected permissions don't agree!")
  (Impl_Pop x p)

-- | Drop a permission from the top of the stack
implDropM :: ExprVar a -> ValuePerm a -> ImplM vars r ps (ps :> a) ()
implDropM x p =
  gmapRetAndPerms (dropPerm x) (Impl_Simpl Proxy $ Simpl_Drop x p)

-- | Produce a branching proof tree, that performs the first implication and, if
-- that one fails, falls back on the second
implCatchM :: ImplM vars r ps1 ps2 () -> ImplM vars r ps1 ps2 () ->
              ImplM vars r ps1 ps2 ()
implCatchM m1 m2 = gparallel Impl_Catch m1 m2

-- FIXME: maybe this isn't useful...
-- | Apply a simple implication rule to the top permissions on the stack
implSimplM :: TypeCtx ps_in => Proxy ps -> SimplImpl ps_in ps_out ->
              (DistPerms ps_in -> DistPerms ps_out) ->
              ImplM vars r (ps :++: ps_out) (ps :++: ps_in) ()
implSimplM prx simpl f =
  gmapRetAndPerms
  (modifyDistPerms $ \ps ->
    let (ps1, ps2) = splitDistPerms prx ps in
    appendDistPerms ps1 (f ps2))
  (Impl_Simpl prx simpl)

-- | Apply the left or-introduction rule to the top of the permission stack,
-- changing it from @x:p1@ to @x:(p1 \/ p2)@
introOrLM :: ExprVar a -> ValuePerm a -> ValuePerm a ->
             ImplM vars r (ps :> a) (ps :> a) ()
introOrLM x p1 p2 =
  gmapRetAndPerms (introOrL x p2) (Impl_Simpl Proxy $ SImpl_IntroOrL x p1 p2)

-- | Apply the right or-introduction rule to the top of the permission stack,
-- changing it from @x:p2@ to @x:(p1 \/ p2)@
introOrRM :: ExprVar a -> ValuePerm a -> ValuePerm a ->
             ImplM vars r (ps :> a) (ps :> a) ()
introOrRM x p1 p2 =
  gmapRetAndPerms (introOrR x p1) (Impl_Simpl Proxy $ SImpl_IntroOrR x p1 p2)

-- | Apply existential introduction to the top of the permission stack, changing
-- it from @[e/x]p@ to @exists (x:tp).p@
--
-- FIXME: is there some way we could "type-check" this, to ensure that the
-- permission on the top of the stack really equals @[e/x]p@?
introExistsM :: KnownRepr TypeRepr tp => ExprVar a -> PermExpr tp ->
                Binding tp (ValuePerm a) ->
                ImplM vars r (ps :> a) (ps :> a) ()
introExistsM x e p_body =
  gmapRetAndPerms (introExists x e p_body)
  (Impl_Simpl Proxy $ SImpl_IntroExists x e p_body)

-- | Eliminate a disjunctive permission @x:(p1 \/ p2)@, building proof trees
-- that proceed with both @x:p1@ and @x:p2@
elimOrM :: ExprVar a -> ImplM vars r (ps :> a) (ps :> a) ()
elimOrM x =
  gparallel (\impl1 impl2 -> Impl_ElimOr x impl1 impl2)
  (modify (over (implStatePerms . varPerm x) orPermLeft))
  (modify (over (implStatePerms . varPerm x) orPermRight))

-- | Eliminate an existential permission @x:(exists (y:tp).p)@ in the current
-- permission set
elimExistsM :: (KnownRepr TypeRepr tp, NuMatchingAny1 r) => ExprVar a -> f tp ->
               ImplM vars r (ps :> a) (ps :> a) ()
elimExistsM x (_ :: f tp) =
  getPerms >>>= \perms ->
  gopenBinding1 (Impl_ElimExists x) (elimExists x (knownRepr :: TypeRepr tp)
                                     perms) >>>= \(_nm, perms') ->
  setPerms perms'

-- | Eliminate disjunctives and existentials on the top of the stack and return
-- the resulting permission
elimOrsExistsM :: NuMatchingAny1 r => ExprVar a ->
                  ImplM vars r (ps :> a) (ps :> a) (ValuePerm a)
elimOrsExistsM x =
  getTopDistPerm x >>>= \p ->
  case p of
    ValPerm_Or _ _ -> elimOrM x >>> elimOrsExistsM x
    ValPerm_Exists (_ :: Binding a _) ->
      elimExistsM x (knownRepr :: TypeRepr a) >>> elimOrsExistsM x
    _ -> greturn p

-- | Introduce a proof of @x:true@ onto the top of the stack, which is the same
-- as an empty conjunction
introConjM :: ExprVar a -> ImplM vars r (ps :> a) ps ()
introConjM x =
  gmapRetAndPerms (introConj x) (Impl_Simpl Proxy $ SImpl_IntroConj x)

-- | Introduce a proof of @x:eq(x)@ onto the top of the stack
introEqReflM :: ExprVar a -> ImplM vars r (ps :> a) ps ()
introEqReflM x =
  gmapRetAndPerms (introEqRefl x)
  (Impl_Simpl Proxy $ SImpl_IntroEqRefl x)

-- | Copy an @x:eq(e)@ permission on the top of the stack
introEqCopyM :: ExprVar a -> PermExpr a ->
                ImplM vars r (ps :> a :> a) (ps :> a) ()
introEqCopyM x e =
  gmapRetAndPerms (introEqCopy x e) (Impl_Simpl Proxy $ SImpl_CopyEq x e)

-- | Cast a @y:p@ perm on the top of the stack to an @x:p@ perm using an
-- @x:eq(y)@ just below it on the stack
introCastM :: ExprVar a -> ExprVar a -> ValuePerm a ->
              ImplM vars r (ps :> a) (ps :> a :> a) ()
introCastM x y p =
  gmapRetAndPerms (castVarPerm x y p) (Impl_Simpl Proxy $ SImpl_Cast x y p)

-- | Delete the @i@th atomic permission in the conjunct on the top of the stack,
-- assuming that conjunction contains the given atomic permissions, and put the
-- extracted atomic permission just below the top of the stack
implExtractConjM :: ExprVar a -> [AtomicPerm a] -> Int ->
                    ImplM vars r (ps :> a :> a) (ps :> a) ()
implExtractConjM x ps i =
  gmapRetAndPerms (extractConj x ps i)
  (Impl_Simpl Proxy $ SImpl_ExtractConj x ps i)

-- | Combine the two conjunctive permissions on the top of the stack
implCombineConjM :: ExprVar a -> [AtomicPerm a] -> [AtomicPerm a] ->
                    ImplM vars r (ps :> a) (ps :> a :> a) ()
implCombineConjM x ps1 ps2 =
  gmapRetAndPerms (combineConj x ps1 ps2)
  (Impl_Simpl Proxy $ SImpl_CombineConj x ps1 ps2)

-- | Cast a proof of @x:eq(LLVMWord(e1))@ to @x:eq(LLVMWord(e2))@ on the top of
-- the stack
castLLVMWordEqM ::
  ExprVar (LLVMPointerType w) -> PermExpr (BVType w) -> PermExpr (BVType w) ->
  ImplM vars r (ps :> LLVMPointerType w) (ps :> LLVMPointerType w) ()
castLLVMWordEqM x e1 e2 =
  gmapRetAndPerms (castLLVMWordEq x e1 e2) (Impl_TryCastLLVMWord x e1 e2)


-- | Cast a @y:ptr(pps)@ on the top of the stack to @x:ptr(pps - off)@ using a
-- proof of @x:eq(y+off)@ just below it on the stack
castLLVMPtrM :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                ExprVar (LLVMPointerType w) ->
                ImplM vars r (ps :> LLVMPointerType w)
                (ps :> LLVMPointerType w :> LLVMPointerType w) ()
castLLVMPtrM y off x =
  gmapRetAndPerms (castLLVMPtr y off x)
  (Impl_Simpl Proxy $ SImpl_CastLLVMPtr y off x)

introCopyLLVMFreeM :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                      ImplM vars r (ps :> LLVMPointerType w :> LLVMPointerType w)
                      (ps :> LLVMPointerType w) ()
introCopyLLVMFreeM x e =
  gmapRetAndPerms (copyLLVMFree x e)
  (Impl_Simpl Proxy $ SImpl_CopyLLVMFree x e)


{-

-- | Copy an LLVM free permission @free(e)@ from the current
-- @x:ptr(pps1,free(e),pps2)@ permission into the @x:ptr(pps)@ permission on the
-- top of the stack, where the 'Int' index gives the size of @pps1@.
introLLVMFreeM :: ExprVar (LLVMPointerType w) -> Int ->
                  ImplM vars r (ps :> LLVMPointerType w)
                  (ps :> LLVMPointerType w) ()
introLLVMFreeM x i =
  gmapRetAndPerms (introLLVMFree x i) (Impl_IntroLLVMFree x i)

-- | Cast a proof of @x:ptr(pps1, free(e1), pps2)@ on the top of the stack to
-- one of @x:ptr(pps1, free(e2), pps2)@
castLLVMFreeM :: ExprVar (LLVMPointerType w) -> Int ->
                 PermExpr (BVType w) -> PermExpr (BVType w) ->
                 ImplM vars r (ps :> LLVMPointerType w)
                 (ps :> LLVMPointerType w) ()
castLLVMFreeM x i e1 e2 =
  gmapRetAndPerms (castLLVMFree x i e1 e2) (Impl_CastLLVMFree x i e1 e2)

-- | Move a field permission of the form @(off,All) |-> eq(e)@ to the
-- @x:ptr(pps)@ permission on the top of of the stack
introLLVMFieldAllM :: ExprVar (LLVMPointerType w) -> Int ->
                      ImplM vars r (ps :> LLVMPointerType w)
                      (ps :> LLVMPointerType w) ()
introLLVMFieldAllM x i =
  gmapRetAndPerms (introLLVMFieldAll x i) (Impl_IntroLLVMFieldAll x i)

-- | Split a field permission @(off,spl) |-> eq(e)@ into two, leaving the left
-- half in the current permission stack and moving the right half to the top of
-- of the stack
introLLVMFieldSplitM :: ExprVar (LLVMPointerType w) -> Int -> SplittingExpr ->
                        ImplM vars r (ps :> LLVMPointerType w)
                        (ps :> LLVMPointerType w) ()
introLLVMFieldSplitM x i spl =
  gmapRetAndPerms (introLLVMFieldSplit x i spl)
  (Impl_IntroLLVMFieldSplit x i spl)

-- | Combine proofs of @x:ptr(pps,(off,spl) |-> eq(y))@ and @y:p@ on the top of
-- the permission stack into a proof of @x:ptr(pps,(off,spl |-> p))@
introLLVMFieldContentsM ::
  ExprVar (LLVMPointerType w) ->
  ExprVar (LLVMPointerType w) ->
  ImplM vars r (ps :> LLVMPointerType w)
  (ps :> LLVMPointerType w :> LLVMPointerType w) ()
introLLVMFieldContentsM x y =
  gmapRetAndPerms (introLLVMFieldContents x y) (Impl_IntroLLVMFieldContents x y)

-- | Eliminate a permission @x:ptr(pps1,(off,S) |-> p,pps2)@ into permissions
-- @x:ptr(pps1,(off,S) |-> eq(y),pps2)@ and @y:p@ for a fresh variable @y@,
-- returning the fresh variable @y@
elimLLVMFieldContentsM :: NuMatchingAny1 r => ExprVar (LLVMPointerType w) ->
                          Int -> ImplM vars r ps ps (ExprVar (LLVMPointerType w))
elimLLVMFieldContentsM x i =
  getPerms >>>= \perms ->
  case elimLLVMFieldContents x i perms of
    Left y -> greturn y
    Right mb_perms' ->
      gopenBinding1 (Impl_ElimLLVMFieldContents x i) mb_perms' >>>= \(y,perms') ->
      setPerms perms' >>> greturn y

-- | Divide an array permission @x:ptr((off,*stride,<len,S) |-> p)@ into two
-- arrays, one of length @e@ starting at @off@ and one of length @len-e@
-- starting at offset @off+e*stride@. The latter permission (at offset
-- @off+e*stride@) stays at the same index, while the former (at the original
-- offset) is moved to the end of the field permissions for @x@.
divideLLVMArrayM :: ExprVar (LLVMPointerType w) -> Int -> PermExpr (BVType w) ->
                    ImplM vars r ps ps ()
divideLLVMArrayM x i arr_ix =
  gmapRetAndPerms (divideLLVMArray x i arr_ix) (Impl_DivideLLVMArray x i arr_ix)

-- | Perform an array indexing of the first cell of an array, by separating an
-- array permission @x:ptr((off,*stride,<len,S) |-> pps)@ into one array cell,
-- containing a copy of the pointer permissions @pps@ starting at offset @off@,
-- along with the remaining array @x:ptr((off+1,*stride,<len,S) |->
-- pps)@. Return the new permission set along with the indices of the new @pps@
-- pointer permissions.
indexLLVMArrayM :: ExprVar (LLVMPointerType w) -> Int ->
                   ImplM vars r ps ps [(Int, LLVMFieldPerm w)]
indexLLVMArrayM x i =
  getPerms >>>= \perms ->
  gmapRetAndPerms (const $ fst $
                   indexLLVMArray x i perms) (Impl_IndexLLVMArray x i) >>>
  greturn (snd $ indexLLVMArray x i perms)

-- | Assert that @off = off'@ at bitvector type, and cast the last pointer
-- permission at the top of the stack from @(off,S) |-> p@ to @(off',S) |-> p@
castLLVMFieldOffsetM :: ExprVar (LLVMPointerType w) -> PermExpr (BVType w) ->
                        PermExpr (BVType w) ->
                        ImplM vars r (ps :> LLVMPointerType w)
                        (ps :> LLVMPointerType w) ()
castLLVMFieldOffsetM x off off' =
  gmapRetAndPerms (castLLVMFieldOffset x off off')
  (Impl_CastLLVMFieldOffsetM x off off')
-}

----------------------------------------------------------------------
-- * Proving Equality Permissions
----------------------------------------------------------------------

-- | Build a proof on the top of the stack that @x:eq(e)@. Assume that all @x@
-- permissions are on the top of the stack and given by argument @p@, and pop
-- them back to the primary permission for @x@ at the end of the proof.
proveVarEq :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
              Mb vars (PermExpr a) -> ImplM vars r (ps :> a) (ps :> a) ()
proveVarEq x p mb_e =
  getPSubst >>>= \psubst ->
  proveVarEqH x p psubst mb_e

-- | Main helper function for 'proveVarEq'
proveVarEqH :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
               PartialSubst vars -> Mb vars (PermExpr a) ->
               ImplM vars r (ps :> a) (ps :> a) ()

-- Prove x:eq(z) for evar z by setting z=x
proveVarEqH x p psubst [nuP| PExpr_Var z |]
  | Left memb <- mbNameBoundP z
  , Nothing <- psubstLookup psubst memb
  = setVarM memb (PExpr_Var x) >>> implPopM x p >>> introEqReflM x

-- Prove x:eq(x) by reflexivity
proveVarEqH x p psubst mb_e
  | Just (PExpr_Var y) <- partialSubst psubst mb_e
  , x == y
  = implPopM x p >>> introEqReflM x

-- Prove x:eq(e) |- x:eq(e) using introEqCopyM
proveVarEqH x p@(ValPerm_Eq e) psubst mb_e
  | Just e' <- partialSubst psubst mb_e
  , e' == e
  = introEqCopyM x e >>> implPopM x p

-- Prove x:eq(word(e)) |- x:eq(word(z)) by setting z=e
proveVarEqH x p@(ValPerm_Eq
                 (PExpr_LLVMWord e)) psubst [nuP| PExpr_LLVMWord (PExpr_Var z) |]
  | Left memb <- mbNameBoundP z
  , Nothing <- psubstLookup psubst memb
  = setVarM memb e >>> introEqCopyM x (PExpr_LLVMWord e) >>> implPopM x p

-- Prove x:eq(word(e')) |- x:eq(word(e)) by first proving x:eq(word(e')) and
-- then casting e' to e
proveVarEqH x p@(ValPerm_Eq
                 (PExpr_LLVMWord e')) psubst [nuP| PExpr_LLVMWord mb_e |]
  | Just e <- partialSubst psubst mb_e =
    introEqCopyM x (PExpr_LLVMWord e') >>> implPopM x p >>>
    castLLVMWordEqM x e' e

-- Eliminate disjunctive and/or existential permissions
proveVarEqH x (ValPerm_Or _ _) _ mb_e =
  elimOrsExistsM x >>>= \p -> proveVarEq x p mb_e

-- Eliminate disjunctive and/or existential permissions
proveVarEqH x (ValPerm_Exists _) _ mb_e =
  elimOrsExistsM x >>>= \p -> proveVarEq x p mb_e

-- Otherwise give up!
proveVarEqH _ _ _ _ = implFailM

----------------------------------------------------------------------
-- * Proving Field Permissions
----------------------------------------------------------------------

-- | FIXME: documentation
proveVarFieldImpl :: NuMatchingAny1 r => ExprVar (LLVMPointerType w) ->
                     [LLVMPtrPerm w] -> LLVMFieldMatch w ->
                     PermExpr (BVType w) -> Mb vars (LLVMFieldPerm w) ->
                     ImplM vars r (ps :> LLVMPointerType w)
                     (ps :> LLVMPointerType w) ()
proveVarFieldImpl x ps match off mb_fp = error "FIXME HERE NOW"


{-
-- | Attempt to prove @x:ptr(pps', off |-> (S,p))@ on the top of the stack from
-- the current permissions @x:ptr(pps)@ for @x@, assuming that @x:ptr(pps')@ is
-- already on the top of the stack.
--
-- FIXME: update this documentation
proveVarField :: NuMatchingAny1 r => ExprVar (LLVMPointerType w) ->
                 LLVMFieldMatch w ->
                 PermExpr (BVType w) -> Mb vars (LLVMFieldPerm w) ->
                 ImplM vars r (ps :> LLVMPointerType w)
                 (ps :> LLVMPointerType w) ()

-- Case for x:ptr((off',All) |-> p') |- x:ptr((off,All) |-> p)
proveVarField x (FieldMatchField
                 is_def i fp) off [nuP| LLVMFieldPerm _ SplExpr_All mb_p |]
  | SplExpr_All <- llvmFieldSplitting fp =
    -- NOTE: If we need "All" and don't have it, we fail, because we have set
    -- things up to ensure that we cannot "piece together" an All from multiple
    -- different pointer permissions: specifically, we make sure that the
    -- pointer permissions in the permission have overlapping splittings. That
    -- is why this case requires the splitting in fp to be "All".
    elimLLVMFieldContentsM x i >>>= \y ->
    introLLVMFieldAllM x i >>>
    proveVarImpl y mb_p >>>
    introLLVMFieldContentsM x y >>>
    if is_def then greturn () else
      castLLVMFieldOffsetM x (llvmFieldOffset fp) off

-- Case for x:ptr((off',spl') |-> p') |- x:ptr((off,z) |-> p), setting z=R(spl')
proveVarField x (FieldMatchField
                 is_def i fp) off [nuP| LLVMFieldPerm _ (SplExpr_Var z) mb_p |]
  | Left memb <- mbNameBoundP z =
    elimLLVMFieldContentsM x i >>>= \y ->
    introLLVMFieldSplitM x i (llvmFieldSplitting fp) >>>
    setVarM memb (PExpr_Spl $ SplExpr_R $ llvmFieldSplitting fp) >>>
    proveVarImpl y mb_p >>>
    introLLVMFieldContentsM x y >>>
    if is_def then greturn () else
      castLLVMFieldOffsetM x (llvmFieldOffset fp) off

proveVarField x (FieldMatchArray _ i ap arr_ix fld_i) off mb_fld =
  (if bvEq off (llvmArrayOffset ap) then greturn () else
     divideLLVMArrayM x i arr_ix) >>>
  indexLLVMArrayM x i >>>= \is_flds ->
  proveVarField x (FieldMatchField True (fst (is_flds !! fld_i))
                   (snd (is_flds !! fld_i))) off mb_fld
-}


----------------------------------------------------------------------
-- * Proving Atomic Permissions
----------------------------------------------------------------------

proveVarAtomicImpl :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] ->
                      Mb vars (AtomicPerm a) ->
                      ImplM vars r (ps :> a) (ps :> a) ()

proveVarAtomicImpl x ps [nuP| Perm_LLVMField mb_fp |] =
  partialSubstForceM (fmap llvmFieldOffset mb_fp)
  "proveVarPtrPerms: incomplete psubst: LLVM field offset" >>>= \off ->
  let matches = findFieldMatches off ps in
  case find fieldMatchDefinite matches of
    Just match -> proveVarFieldImpl x ps match off mb_fp
    Nothing ->
      foldr (\match rest ->
              implCatchM (proveVarFieldImpl x ps match off mb_fp) rest)
      implFailM
      matches

proveVarAtomicImpl _x _ps [nuP| Perm_LLVMArray mb_ap |] =
  partialSubstForceM (fmap llvmArrayOffset mb_ap)
  "proveVarPtrPerms: incomplete psubst: LLVM array offset" >>>= \_off ->
  error "FIXME HERE NOW: prove array perms!"
-- IDEA: maybe an "array match" is a sequence of perms in order that we use to
-- prove the array perm... or possibly a tree of options?

proveVarAtomicImpl x ps [nuP| Perm_LLVMFree mb_e |] =
  partialSubstForceM mb_e
  "proveVarAtomicImpl: incomplete psubst: LLVM free size" >>>= \e ->
  case findFreePerm ps of
    Just (i, e') ->
      let ps' = take i ps ++ drop (i+1) ps in
      implExtractConjM x ps i >>>
      implPopM x (ValPerm_Conj ps') >>>
      introCopyLLVMFreeM x e' >>>
      implPushM x (ValPerm_Conj ps') >>>
      implCombineConjM x [Perm_LLVMFree e'] ps' >>>
      implPopM x (ValPerm_Conj (e' : ps')) >>>
      castLLVMFreeM x e' e
    _ -> implFailM

proveVarAtomicImpl _x _ps [nuP| Perm_LLVMFrame _mb_fp |] =
  error "FIXME HERE NOW: prove frame perms!"

proveVarAtomicImpl _x _ps [nuP| Perm_LOwned _mb_ps |] =
  error "FIXME HERE NOW: prove lowned perms!"
-- IDEA: have a case for an existential var of type PermSetType

proveVarAtomicImpl _x _ps [nuP| Perm_LContains _mb_l |] =
  error "FIXME HERE NOW: prove lcontains perms!"
-- IDEA: go through the lifetime stack

proveVarAtomicImpl _x _ps [nuP| Perm_Fun _mb_fun_perm |] =
  error "FIXME HERE NOW: prove fun perms!"
-- IDEA: for function variables we just need to find an equal fun perm; for
-- function constants (which will show up in the eq(e) |- fun_perm case) we will
-- need an environment to look up function types and we will need a SimplImpl
-- rule that just asserts those types and we can look them up at translation
-- time


proveVarConjImpl :: NuMatchingAny1 r => ExprVar a -> [AtomicPerm a] ->
                    Mb vars [AtomicPerm a] ->
                    ImplM vars r (ps :> a) (ps :> a) ()
proveVarConjImpl x ps [nuP| [] |] = implPopM x p >>> introConjM x
proveVarConjImpl x ps [nuP| mb_p : mb_ps |] =
  proveVarAtomicImpl x ps mb_p >>>
  proveVarImpl x (fmap ValPerm_Conj mb_ps) >>>
  partialSubstForceM mb_p
  "Incomplete psubst: mb_p in proveVarConjImpl" >>>= \p ->
  partialSubstForceM mb_ps
  "Incomplete psubst: mb_ps in proveVarConjImpl" >>>= \ps ->
  implCombineConjM x [p] ps


----------------------------------------------------------------------
-- * Proving Permission Implications
----------------------------------------------------------------------

-- | Prove @x:p'@, where @p@ may have existentially-quantified variables in it
proveVarImpl :: NuMatchingAny1 r => ExprVar a -> Mb vars (ValuePerm a) ->
                ImplM vars r (ps :> a) ps ()
proveVarImpl x mb_p =
  getPerm x >>>= \p ->
  implPushM x p >>>
  proveVarImplH x p mb_p

-- | Prove @x:p'@ assuming that the primary permissions for @x@ have all been
-- pushed to the top of the stack and are equal to @p@. Pop the remaining
-- permissions for @x@ back to its primary permission when we are finished.
proveVarImplH :: NuMatchingAny1 r => ExprVar a -> ValuePerm a ->
                 Mb vars (ValuePerm a) ->
                 ImplM vars r (ps :> a) (ps :> a) ()

-- Eliminate any disjunctions and existentials on the left
proveVarImplH x (ValPerm_Or _ _) mb_p =
  elimOrsExistsM x >>>= \p -> proveVarImplH x p mb_p

-- Eliminate any disjunctions and existentials on the left
proveVarImplH x (ValPerm_Exists _) mb_p =
  elimOrsExistsM x >>>= \p -> proveVarImplH x p mb_p

-- Prove x:(p1 \/ p2) by trying to prove x:p1 and x:p2 in two branches
proveVarImplH x p [nuP| ValPerm_Or mb_p1 mb_p2 |] =
  implCatchM
  (proveVarImplH x p mb_p1 >>>
   partialSubstForceM mb_p1
   "proveVarImpl: incomplete psubst: introOrL" >>>= \p1 ->
    partialSubstForceM mb_p2
   "proveVarImpl: incomplete psubst: introOrL"  >>>= \p2 ->
    introOrLM x p1 p2)
  (proveVarImplH x p mb_p2 >>>
   partialSubstForceM mb_p1
   "proveVarImpl: incomplete psubst: introOrR" >>>= \p1 ->
    partialSubstForceM mb_p2
    "proveVarImpl: incomplete psubst: introOrR"  >>>= \p2 ->
    introOrRM x p1 p2)

-- Prove x:exists (z:tp).p by proving x:p in an extended vars context
proveVarImplH x p [nuP| ValPerm_Exists mb_p |] =
  withExtVarsM (proveVarImplH x p $ mbCombine mb_p) >>>= \((), maybe_e) ->
  let e = fromMaybe (zeroOfType knownRepr) maybe_e in
  partialSubstForceM mb_p "proveVarImpl: incomplete psubst: introExists" >>>=
  introExistsM x e

-- Prove x:eq(e) by calling proveVarEq; note that we do not eliminate
-- disjunctive permissions because some trivial equalities do not require any eq
-- permissions on the left
proveVarImplH x p [nuP| ValPerm_Eq e |] = proveVarEq x p e

-- Prove an empty conjunction trivially
proveVarImplH x p [nuP| ValPerm_Conj [] |] = implPopM x p >>> introConjM x

-- Prove x:p from x:eq(y) by first proving y:p and then casting
proveVarImplH x p@(ValPerm_Eq (PExpr_Var y)) mb_p =
  introEqCopyM x (PExpr_Var y) >>>
  implPopM x p >>>
  proveVarImpl y mb_p >>>
  partialSubstForceM mb_p1
  "proveVarImpl: incomplete psubst: introCast" >>>= \p' ->
  introCastM x y p'

-- Prove x:(p1 * .. * pn) from x:eq(y+off) by proving y:(p1 + off * ...) and
-- then casting the result
proveVarImplH x p@(ValPerm_Eq
                   e@(PExpr_LLVMOffset y off)) [nuP| ValPerm_Conj mb_ps |] =
  introEqCopyM x e >>>
  implPopM x p >>>
  proveVarImpl y (nuWithElim1
                  (\_ ps -> ValPerm_Conj $ map (offsetLLVMAtomicPerm off) ps)
                  mb_ps) >>>
  castLLVMPtrM y off x

-- If x:eq(LLVMword(e)) then we cannot prove any pointer permissions for it
proveVarImplH x (ValPerm_Eq (PExpr_LLVMWord _)) [nuP| ValPerm_Conj _ |] =
  implFailM

proveVarImplH _ (ValPerm_Eq _) [nuP| ValPerm_Conj _ |] =
  error "FIXME HERE NOW: finish the proveVarImplH cases for x:eq(e) |- x:pps"

proveVarImplH x (ValPerm_Conj ps) [nuP| ValPerm_Conj mb_ps |] =
  proveVarConjImpl x ps $ mbList mb_ps

-- We do not yet handle mu
proveVarImplH _ _ [nuP| ValPerm_Mu _ |] = implFailM

-- We do not yet handle permission variables
proveVarImplH _ _ [nuP| ValPerm_Var _ |] = implFailM

-- Fail if nothing else matched
proveVarImplH _ _ _ = implFailM

-- | A list of distinguished permissions with existential variables
data ExDistPerms vars ps where
  ExDistPermsNil :: ExDistPerms vars RNil
  ExDistPermsCons :: ExDistPerms vars ps -> ExprVar a -> Mb vars (ValuePerm a) ->
                     ExDistPerms vars (ps :> a)

$(mkNuMatching [t| forall vars ps. ExDistPerms vars ps |])

-- | Existentially quantify a list of distinguished permissions over the empty
-- set of existential variables
distPermsToExDistPerms :: DistPerms ps -> ExDistPerms RNil ps
distPermsToExDistPerms DistPermsNil = ExDistPermsNil
distPermsToExDistPerms (DistPermsCons ps x p) =
  ExDistPermsCons (distPermsToExDistPerms ps) x (emptyMb p)

-- | Prove a list of existentially-quantified distinguished permissions
proveVarsImpl :: NuMatchingAny1 r => ExDistPerms vars as ->
                 ImplM vars r as RNil ()
proveVarsImpl ExDistPermsNil = return ()
proveVarsImpl (ExDistPermsCons ps x p) = proveVarsImpl ps >>> proveVarImpl x p

-- | Like 'proveVarsImpl' but the starting permission set need not be empty, and
-- so is appended to
proveVarsImplAppend :: NuMatchingAny1 r => ExDistPerms vars ps' ->
                       ImplM vars r (ps :++: ps') ps ()
proveVarsImplAppend ExDistPermsNil = return ()
proveVarsImplAppend (ExDistPermsCons ps x p) =
  proveVarsImplAppend ps >>> proveVarImpl x p


----------------------------------------------------------------------
-- * Recombining Permissions
----------------------------------------------------------------------

{-


-- | Recombine the distinguished permission @p_dist@ on @x@ back into the
-- existing permission @p@ on @x@
recombinePerm :: ExprVar a -> ValuePerm a -> ValuePerm a ->
                 ImplM RNil r as (as :> a) ()
recombinePerm x ValPerm_True _ = recombineTrueM x
recombinePerm _ _ _ = error "FIXME HERE: finish recombinePerm!"

-- | Recombine the distinguished permissions back into the permission set
recombinePerms :: ImplM RNil r RNil as ()
recombinePerms =
  getDistPerms >>>= \stack ->
  case stack of
    DistPermsNil -> greturn ()
    DistPermsCons _ x p_dist ->
      getPerm x >>>= \p_x -> recombinePerm x p_dist p_x >>> recombinePerms
-}
-}
