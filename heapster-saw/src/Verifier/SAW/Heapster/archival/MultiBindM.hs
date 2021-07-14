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
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE EmptyDataDecls #-}

module Verifier.SAW.Heapster.MultiBindM where

import Data.Kind
import Data.Functor.Compose
import Data.Functor.Product
import Control.Applicative
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Identity
import Control.Monad.Trans.Cont (evalContT)

import Data.Parameterized.Some

import Data.Binding.Hobbits
import Data.Type.RList (RList(..), RAssign(..), (:++:), append, memberElem,
                        mapRAssign, mapToList)
import qualified Data.Type.RList as RL
import Data.Binding.Hobbits.Mb (mbMap2)
import Data.Binding.Hobbits.Closed
import Data.Binding.Hobbits.Liftable
import Data.Binding.Hobbits.MonadBind as MB
import Data.Binding.Hobbits.NameMap (NameMap, NameAndElem(..))
import qualified Data.Binding.Hobbits.NameMap as NameMap
import Data.Binding.Hobbits.NameSet (NameSet, SomeName(..), toList)
import qualified Data.Binding.Hobbits.NameSet as NameSet
import Data.Binding.Hobbits.NuMatching
import Data.Binding.Hobbits.NuMatchingInstances

import Verifier.SAW.Heapster.CruUtil


-- * The untyped lambda-calculus with modules

data LCTag
type LCVar = Name LCTag
type LCBinding = Binding LCTag

data LC
  = LC_Var LCVar
  | LC_App LC LC
  | LC_Lam (LCBinding LC)
  | LC_Let LC (LCBinding LC)
  deriving (Show)

data LCModule
  = LCModNil
  | LCModCons String LC (LCBinding LCModule)

$(mkNuMatching [t| LC |])
$(mkNuMatching [t| LCModule |])

class NuMatching a => MaybeLiftable a where
  mbMaybeLift :: Mb ctx a -> Maybe a

mbForceLift :: MaybeLiftable a => Mb ctx a -> a
mbForceLift mb_a | Just a <- mbMaybeLift mb_a = a
mbForceLift _ = error "mbForceLift"

class NuMatchingAny1 f => MaybeLiftableAny1 f where
  mbMaybeLift1 :: Mb ctx (f a) -> Maybe (f a)

instance MaybeLiftable () where
  mbMaybeLift _ = Just ()

instance MaybeLiftable String where
  mbMaybeLift = Just . mbLift

instance (MaybeLiftable a, MaybeLiftable b) => MaybeLiftable (a,b) where
  mbMaybeLift mb_ab =
    (,) <$> mbMaybeLift (fmap fst mb_ab) <*> mbMaybeLift (fmap snd mb_ab)

instance MaybeLiftable a => MaybeLiftable (Mb ctx a) where
  mbMaybeLift mb_mb_a
    | [nuP| Just mb_a |] <- fmap mbMaybeLift $ mbSwap mb_mb_a = Just mb_a
  mbMaybeLift _ = Nothing

mbMaybe :: NuMatching a => Mb ctx (Maybe a) -> Maybe (Mb ctx a)
mbMaybe [nuP| Just mb_a |] = Just mb_a
mbMaybe [nuP| Nothing |] = Nothing

instance MaybeLiftable LC where
  mbMaybeLift [nuP| LC_Var mb_x |]
    | Right x <- mbNameBoundP mb_x = Just $ LC_Var x
  mbMaybeLift [nuP| LC_Var _ |] = Nothing
  mbMaybeLift [nuP| LC_App t1 t2 |] =
    LC_App <$> mbMaybeLift t1 <*> mbMaybeLift t2
  mbMaybeLift [nuP| LC_Lam mb_mb_body |] =
    LC_Lam <$> mbMaybe (fmap mbMaybeLift $ mbSwap mb_mb_body)
  mbMaybeLift [nuP| LC_Let mb_rhs mb_mb_body |] =
    LC_Let <$> mbMaybeLift mb_rhs <*>
    mbMaybe (fmap mbMaybeLift $ mbSwap mb_mb_body)

instance MaybeLiftable LCModule where
  mbMaybeLift [nuP| LCModNil |] = Just LCModNil
  mbMaybeLift [nuP| LCModCons mb_str mb_def mb_mb_rest |] =
    LCModCons (mbLift mb_str) <$> mbMaybeLift mb_def <*>
    mbMaybe (fmap mbMaybeLift $ mbSwap mb_mb_rest)

-- * Yet another approach based on a single continuation monad with "binding
-- commands"

-- | A function that binds a context in an @r@ by showing how to map in @r@ in a
-- binding to one not in a binding. Binding functions are parameterized by an
-- argument that we can try to lift.
data BindingFun ctx r =
  forall arg. MaybeLiftable arg => BindingFun (Closed (arg -> Mb ctx r -> r)) arg

$(mkNuMatching [t| forall ctx r. BindingFun ctx r |])

instance MaybeLiftable (BindingFun ctx r) where
  mbMaybeLift [nuP| BindingFun mb_cl_f mb_arg |] =
    BindingFun (mbLift mb_cl_f) <$> mbMaybeLift mb_arg

-- | A return value @a@ inside a sequence of "binding functions"
data BindingCmds k rs a where
  BindingCmdsNil :: a -> BindingCmds k rs a
  BindingCmdsCons :: Member rs r ->
                     BindingFun (ctx :: RList k) r ->
                     Mb (ctx :: RList k) (BindingCmds k rs a) ->
                     BindingCmds k rs a

instance Functor (BindingCmds k rs) where
  fmap f (BindingCmdsNil x) = BindingCmdsNil $ f x
  fmap f (BindingCmdsCons memb bindF mb_cmds) =
    BindingCmdsCons memb bindF (fmap (fmap f) mb_cmds)

instance Applicative (BindingCmds k rs) where
  pure x = BindingCmdsNil x
  liftA2 f (BindingCmdsNil r1) cmds2 = fmap (f r1) cmds2
  liftA2 f (BindingCmdsCons memb bindF mb_cmds1) cmds2 =
    BindingCmdsCons memb bindF $ fmap (\cmds1 -> liftA2 f cmds1 cmds2) mb_cmds1

instance Monad (BindingCmds k rs) where
  return = pure
  (BindingCmdsNil x) >>= f = f x
  (BindingCmdsCons memb bindF mb_cmds) >>= f =
    BindingCmdsCons memb bindF $ fmap (>>= f) mb_cmds

$(mkNuMatching [t| forall k rs r. NuMatching r => BindingCmds k rs r |])

bindingCmdsM :: MonadStrongBind m => BindingCmds k rs (m a) ->
                m (BindingCmds k rs a)
bindingCmdsM (BindingCmdsNil m) = BindingCmdsNil <$> m
bindingCmdsM (BindingCmdsCons memb bindF mb_cmds) =
  BindingCmdsCons memb bindF <$> strongMbM (fmap bindingCmdsM mb_cmds)

-- | Apply a binding function in a binding to an argument in an extended binding
mbApplyBindFun :: RAssign prx' ctx' -> Mb ctx (BindingFun ctx' r) ->
                  Mb (ctx :++: ctx') r -> Mb ctx r
mbApplyBindFun ctx' [nuP| BindingFun mb_bindF mb_arg |] mb_r =
  fmap unClosed mb_bindF `mbApply` mb_arg `mbApply`
  mbSeparate ctx' mb_r

-- | Helper function for 'runInnerBindingCmds'
runMbInnerBindingCmds :: NuMatching r => (Mb ctx r -> r) ->
                         Mb (ctx :: RList k) (BindingCmds k (rs :> r) r) ->
                         BindingCmds k rs r
runMbInnerBindingCmds bindF [nuP| BindingCmdsNil mb_r |] =
  BindingCmdsNil $ bindF mb_r
runMbInnerBindingCmds bindF [nuP| BindingCmdsCons Member_Base bindF' cmds |] =
  let prxs = mbLift (fmap mbToProxy cmds) in
  runMbInnerBindingCmds (bindF . mbApplyBindFun prxs bindF') (mbCombine cmds)
runMbInnerBindingCmds bindF [nuP| BindingCmdsCons (Member_Step memb) bindF' cmds |] =
  BindingCmdsCons (mbLift memb) (mbForceLift bindF')
  (fmap (runMbInnerBindingCmds bindF) $ mbSwap cmds)

-- | "Run" the innermost level of binding commands in a 'BindingCmds' sequence,
-- to get a sequence of binding commands with one fewer level
runInnerBindingCmds :: NuMatching r => BindingCmds k (rs :> r) r ->
                       BindingCmds k rs r
runInnerBindingCmds = runMbInnerBindingCmds elimEmptyMb . emptyMb

-- | "Run" a list of binding commands with no levels by just returning its contents
runTopBindingCmds :: BindingCmds k RNil a -> a
runTopBindingCmds (BindingCmdsNil a) = a

-- | The monad transformer for building an @r@ inside multiple levels of
-- bindings for names of kind @k@
type BuilderT k rs r m = ContT (BindingCmds k rs r) m

-- | Run a 'BuilderT'
runBuilderT :: Monad m => BuilderT k RNil r m r -> m r
runBuilderT m = runTopBindingCmds <$> runContT m (return . BindingCmdsNil)

-- | The builder monad
type Builder k rs r = BuilderT k rs r Identity

-- | Run a 'Builder'
runBuilder :: Builder k RNil r r -> r
runBuilder = runIdentity . runBuilderT

-- | Run a computation inside a binding that we can account for in one of the
-- levels with a binding command
openBinding :: MonadStrongBind m => Member rs r' ->
               BindingFun (ctx :: RList k) r' -> Mb ctx a ->
               BuilderT k rs r m a
openBinding memb bindF mb_a =
  ContT $ \k ->
  BindingCmdsCons memb bindF <$> strongMbM (fmap k mb_a)

-- | Run a computation locally with a new level
withLevelM :: (MonadStrongBind m, NuMatching r) =>
              BuilderT k (rs :> r) r m r ->
              BuilderT k rs r' m r
withLevelM m =
  ContT $ \k ->
  (runInnerBindingCmds <$> runContT m (return . BindingCmdsNil)) >>= \cmds ->
  fmap join (bindingCmdsM (fmap k cmds))


-- | The 'BindingFun' for let-binding a lambda-calculus term
letBindingFun :: LC -> BindingFun (RNil :> LCTag) LC
letBindingFun rhs = BindingFun $(mkClosed [| LC_Let |]) rhs

-- | The 'BindingFun' for lambda
lambdaBindingFun :: BindingFun (RNil :> LCTag) LC
lambdaBindingFun = BindingFun $(mkClosed [| const LC_Lam |]) ()

-- | The 'BindingFun' for module cons
modConsBindingFun :: String -> LC -> BindingFun (RNil :> LCTag) LCModule
modConsBindingFun str rhs =
  BindingFun $(mkClosed [| \(str,rhs) -> LCModCons str rhs |]) (str,rhs)

-- | Let-bind a value at the current binding level
letBind :: LC -> Builder Type (rs :> LC) LC LC
letBind rhs =
  openBinding Member_Base (letBindingFun rhs) (nu $ \x -> LC_Var x)

-- | Create a lambda
mkLam :: (LC -> Builder Type (rs :> LC) LC LC) -> Builder Type rs r LC
mkLam f =
  withLevelM
  (openBinding Member_Base lambdaBindingFun (nu $ \x -> LC_Var x) >>= f)

class HasModule rs where
  moduleMember :: Member rs LCModule

instance HasModule (rs :> LCModule) where
  moduleMember = Member_Base

instance HasModule rs => HasModule (rs :> LC) where
  moduleMember = Member_Step moduleMember

moduleBind :: HasModule rs => String -> LC -> Builder Type rs r LC
moduleBind str rhs =
  openBinding moduleMember (modConsBindingFun str rhs) (nu $ \x -> LC_Var x)


example1 :: LCModule
example1 =
  runBuilder $ withLevelM $
  do foo1_def <- mkLam (\x -> mkLam $ \y -> return $ LC_App x y)
     foo1 <- moduleBind "foo1" foo1_def
     foo3_def <- mkLam (\x ->
                         do foo2_def <- mkLam return
                            foo2 <- moduleBind "foo2" foo2_def
                            return $ LC_App foo2 x)
     foo2 <- moduleBind "foo3" foo3_def
     return LCModNil


-- * Another approach based on a single continuation monad with "binding commands"

data CmdSteps cmd r where
  CmdStepsNil :: r -> CmdSteps cmd r
  CmdStepsCons :: NuMatching a => cmd a -> (a -> CmdSteps cmd r) -> CmdSteps cmd r

data BindingCmd3 rs a where
  BindingCmd3 :: (MaybeLiftable arg, MaybeLiftable a) => Member rs r ->
                 Closed (arg -> Mb ctx r -> r) -> arg -> Mb ctx a ->
                 BindingCmd3 rs a

$(mkNuMatching [t| forall cmd r. (NuMatchingAny1 cmd,
                                  NuMatching r) => CmdSteps cmd r |])
$(mkNuMatching [t| forall rs a. BindingCmd3 rs a |])

instance NuMatchingAny1 (BindingCmd3 rs) where
  nuMatchingAny1Proof = nuMatchingProof

-- NOTE: can't do this because we can't maybe-lift the continuation, only force
-- lift it (which maybe is ok...?)
instance (MaybeLiftable r, MaybeLiftableAny1 cmd) =>
         MaybeLiftable (CmdSteps cmd r) where
  mbMaybeLift [nuP| CmdStepsNil mb_r |] = CmdStepsNil <$> mbMaybeLift mb_r
  mbMaybeLift [nuP| CmdStepsCons mb_cmd mb_k |] =
    CmdStepsCons <$> mbMaybeLift1 mb_cmd <*>
    return (\a -> mbForceLift $ fmap ($ a) mb_k)

instance MaybeLiftable (BindingCmd3 rs a) where
  mbMaybeLift [nuP| BindingCmd3 mb_memb mb_bindF mb_arg mb_mb_a |]
    | Just mb_a <- mbMaybeLift mb_mb_a
    , Just arg <- mbMaybeLift mb_arg =
      Just $ BindingCmd3 (mbLift mb_memb) (mbLift mb_bindF) arg mb_a
  mbMaybeLift _ = Nothing

{-
liftCmdStepsBC3 :: NuMatching r => CmdSteps (BindingCmd3 (rs :> r)) r ->
                   CmdSteps (BindingCmd3 rs) r
liftCmdStepsBC3 (CmdStepsNil r) = CmdStepsNil r
liftCmdStepsBC3 (CmdStepsCons
                  (BindingCmd3 Member_Base bindF arg mb_a)
                  k) =
  

openBindingBC3 :: NuMatching r => (Mb ctx r -> r) -> Mb ctx a ->
                  (a -> CmdSteps (BindingCmd3 (rs :> r)) r) ->
                  CmdSteps (BindingCmd3 rs) r
openBindingBC3 bindF mb_a k
  | [nuP| CmdStepsNil mb_r |] <- fmap k mb_a = CmdStepsNil $ bindF mb_r
openBindingBC3 bindF mb_a k
  | [nuP| CmdStepsCons
        (BindingCmd3 Member_Base mb_bindF' mb_arg mb_b) mb_k' |] <- fmap k mb_a
  = bindF $ mbApply mb_k' _


(Mb ctx r -> r) -> Mb ctx (CmdSteps (BindingCmd3 (rs :> r)) r) ->
CmdSteps (BindingCmd3 rs) r


liftBindingBC3 :: FreeM (BindingCmd3 (rs :> r)) r -> FreeM (BindingCmd3 rs) r
liftBindingBC3 m =
  runFreeM m Left (\case
                      CmdStep (BindingCmd3 Member_Base bindF arg mb_a) k
                        | 
                        )
-}


-- * An approach based on a single continuation monad with "binding commands"

data BindingCmd2 rs where
  BindingCmd2 :: MaybeLiftable a => Member rs r ->
                 Closed (a -> Mb ctx r -> r) -> a ->
                 BindingCmd2 rs

$(mkNuMatching [t| forall rs. BindingCmd2 rs |])

instance MaybeLiftable (BindingCmd2 rs) where
  mbMaybeLift [nuP| BindingCmd2 mb_memb mb_f mb_a |]
    | Just a <- mbMaybeLift mb_a =
      Just $ BindingCmd2 (mbLift mb_memb) (mbLift mb_f) a
  mbMaybeLift _ = Nothing


type BC2Builder rs r = Cont (BindingCmd2 rs, r)

{-
openTopBinding :: (Mb ctx r -> r) -> Mb ctx a -> BC2Builder rs r a
openTopBinding bindF mb_a =
  cont $ \k ->
-}


-- * An approach based on free monads

data CmdStep cmd r where
  CmdStep :: cmd a -> (a -> r) -> CmdStep cmd r

newtype FreeM cmd a =
  FreeM { runFreeM :: forall r. (a -> r) -> (CmdStep cmd r -> r) -> r }

instance Monad (FreeM f) where
  return x = FreeM $ \kpure _ -> kpure x
  FreeM m >>= f =
    FreeM (\kpure kcmd -> m (\a -> runFreeM (f a) kpure kcmd) kcmd)

instance Functor (FreeM f) where
  fmap f (FreeM g) = FreeM (\kpure -> g (kpure . f))

instance Applicative (FreeM f) where
  pure = return
  FreeM f <*> FreeM g = FreeM (\kpure kcmd -> f (\a -> g (kpure . a) kcmd) kcmd)

applyCmd :: cmd a -> FreeM cmd a
applyCmd cmd = FreeM $ \kpure kcmd -> kcmd $ CmdStep cmd kpure

data BindingCmd rs a where
  BindingCmd :: Member rs r -> (Mb ctx r -> r) -> Mb ctx a ->
                BindingCmd rs a


liftBindingFreeM :: FreeM (BindingCmd (rs :> r)) r -> FreeM (BindingCmd rs) r
liftBindingFreeM = error "FIXME: this is not writeable!"



-- * An approach based on multiple levels of continuation transformers

type Cont2T r1 r2 = ContT r1 (Cont r2)

mbCont2T :: Liftable r2 => Mb ctx (Cont2T r1 r2 a) ->
            Cont2T r1 r2 (Mb ctx a)
mbCont2T mb_m =
  error "FIXME: this doesn't work!"


-- openBindingCont2T :: Liftable r2 => (Mb ctx r1 -> r1) -> Mb ctx a ->
--                      Cont2T r1 r2 a



-- * An approach based on prompts and multiple continuations

-- | A "multi-continuation"
data MultiCont r_out rs r_in where
  MultiContNil :: MultiCont r RNil r
  MultiContCons ::
    MultiCont r_out rs r -> (r_in -> r) ->
    MultiCont r_out (rs :> r) r_in

applyMultiCont :: MultiCont r_out rs a -> a -> r_out
applyMultiCont MultiContNil a = a
applyMultiCont (MultiContCons k f) a = applyMultiCont k (f a)


data MultiContSplit r_out rs r r_in where
  MultiContSplit :: MultiCont r_out rs1 r -> MultiCont r rs2 r_in ->
                    MultiContSplit r_out (rs1 :++: rs2) r r_in

-- | Split a 'MultiCont' into the parts before and after a particular type
splitMultiCont :: Member rs r -> MultiCont r_out rs r_in ->
                  MultiContSplit r_out rs r r_in
splitMultiCont Member_Base (MultiContCons k f) =
  MultiContSplit k (MultiContCons MultiContNil f)
splitMultiCont (Member_Step memb) (MultiContCons k' f) =
  case splitMultiCont memb k' of
    MultiContSplit k1 k2 ->
      MultiContSplit k1 $ MultiContCons k2 f

-- | Append two 'MultiCont's
appendMultiCont ::
  MultiCont r_out rs1 r ->
  MultiCont r rs2 r_in ->
  MultiCont r_out (rs1 :++: rs2) r_in
appendMultiCont k1 MultiContNil = k1
appendMultiCont k1 (MultiContCons k2 f) =
  MultiContCons (appendMultiCont k1 k2) f

newtype MultiContT r_out rs m a =
  MultiContT { unMultiContT :: MultiCont (m r_out) rs a -> m r_out }

instance Monad m => Monad (MultiContT r_out rs m) where
  return x = MultiContT $ \k -> applyMultiCont k x
  m >>= f =
    error "FIXME: bind does not work here!"
    {-
    MultiContT $ \k ->
    unMultiContT m $ \a ->
    unMultiContT (f a) k
   -}

instance Monad m => Functor (MultiContT r_out rs m) where
  fmap f xs = xs >>= return . f

instance Monad m => Applicative (MultiContT r_out rs m) where
  pure = return
  (<*>) = ap

openBindingMultiContT :: Member rs r -> (Mb ctx r -> r) ->
                         Mb ctx a -> MultiContT r_out rs m a
openBindingMultiContT memb bindF mb_a =
  MultiContT $ \k ->
  case splitMultiCont memb k of
    MultiContSplit k2 k1 ->
      applyMultiCont k2 $ bindF $ fmap (applyMultiCont k1) mb_a


-- * An approach based on the continuation monad that returns multiple functions
-- that map between binding contexts

-- | Typeclass for types whose free variables can be abstracted out
class AbstractVars k a where
  abstractVars :: RAssign Name (ctx :: RList k) -> a ->
                  Maybe (Closed (Mb ctx a))

-- | A "contextual multi-continuation"
{-
data MultiCont (ctx_out :: RList k) rs ctx_in where
  MultiContNil :: MultiCont ctx RNil ctx
  MultiCont1 :: (Mb ctx_in r -> Mb ctx_out r) ->
                MultiCont ctx_out (RNil :> r) ctx_in
  MultiContCons :: MultiCont ctx_out (rs :> r) ctx ->
                   (Mb ctx_in r_in -> Mb ctx r) ->
                   MultiCont ctx_out (rs :> r :> r_in) ctx_in
-}

-- | A "contextual multi-continuation"
data CtxMultiCont (ctx_out :: RList k) rs ctx_in where
  CtxMultiContNil :: CtxMultiCont ctx '(r,RNil,r) ctx
  CtxMultiContCons ::
    CtxMultiCont ctx_out '(r_out,rs,r) ctx ->
    (Mb ctx_in r_in -> Mb ctx r) ->
    CtxMultiCont ctx_out '(r_out,rs :> r,r_in) ctx_in

{-
-- | The existential return type for splitting a 'CtxMultiCont'
data CtxMultiContSplit ctx_out rs ctx_in where
  CtxMultiContSplit ::
    CtxMultiCont ctx_out '(r_out,rs1,r) ctx ->
    CtxMultiCont ctx '(r,rs2,r_in) ctx_in ->
    CtxMultiContSplit ctx_out '(r_out, rs1 :++: rs2, r_in) ctx_in

-- | Split a 'CtxMultiCont' into the parts before and after a particular type
splitCtxMultiCont :: Member rs r ->
                     CtxMultiCont ctx_out '(r_out,rs,r_in) ctx_in ->
                     CtxMultiContSplit ctx_out '(r_out,rs,r_in) ctx_in
splitCtxMultiCont Member_Base (CtxMultiContCons k f) =
  CtxMultiContSplit k (CtxMultiContCons CtxMultiContNil f)
splitCtxMultiCont (Member_Step memb) (CtxMultiContCons k' f) =
  case splitCtxMultiCont memb k' of
    CtxMultiContSplit k1 k2 ->
      CtxMultiContSplit k1 $ CtxMultiContCons k2 f
-}

data CtxMultiContSplit ctx_out r_out rs1 rs2 r_in ctx_in where
  CtxMultiContSplit ::
    CtxMultiCont ctx_out '(r_out,rs1,r) ctx ->
    CtxMultiCont ctx '(r,rs2,r_in) ctx_in ->
    CtxMultiContSplit ctx_out r_out rs1 rs2 r_in ctx_in

-- | Split a 'CtxMultiCont' into the parts before and after a particular type
splitCtxMultiCont :: prx1 rs1 -> RAssign prx2 rs2 ->
                     CtxMultiCont ctx_out '(r_out,rs1 :++: rs2,r_in) ctx_in ->
                     CtxMultiContSplit ctx_out r_out rs1 rs2 r_in ctx_in
splitCtxMultiCont _ MNil k =
  CtxMultiContSplit k CtxMultiContNil
splitCtxMultiCont rs1 (rs2' :>: _) (CtxMultiContCons k' f) =
  case splitCtxMultiCont rs1 rs2' k' of
    CtxMultiContSplit k1 k2 ->
      CtxMultiContSplit k1 $ CtxMultiContCons k2 f

-- | Append two 'CtxMultiCont's
appendCtxMultiCont ::
  CtxMultiCont ctx_out '(r_out,rs1,r) ctx ->
  CtxMultiCont ctx '(r,rs2,r_in) ctx_in ->
  CtxMultiCont ctx_out '(r_out, rs1 :++: rs2, r_in) ctx_in
appendCtxMultiCont k1 CtxMultiContNil = k1
appendCtxMultiCont k1 (CtxMultiContCons k2 f) =
  CtxMultiContCons (appendCtxMultiCont k1 k2) f

-- | A multi-binding plus a 'CtxMultiCont' to map it to a final result type
data CMCBuilderRet rs where
  CMCBuilderRet :: Closed (CtxMultiCont RNil '(r_out,rs,r) ctx) -> Mb ctx r ->
                   CMCBuilderRet '(r_out,rs,r)

-- | Remove a level from a 'CMCBuilderRet'
remLevelCMCBuilderRet :: CMCBuilderRet '(r_out, rs :> r, r') ->
                         CMCBuilderRet '(r_out, rs, r)
remLevelCMCBuilderRet (CMCBuilderRet [clP| CtxMultiContCons k f |] mb_r') =
  CMCBuilderRet k $ unClosed f mb_r'

-- | Add a level to a 'CMCBuilderRet' using an initial mapping
{-
addLevelCMCBuilderRet :: Closed (r' -> r) -> (r -> r -> r) ->
                         CMCBuilderRet '(r_out, rs, r) ->
                         CMCBuilderRet '(r_out, rs :> r, r')
addLevelCMCBuilderRet cl_f_r' f_r (CMCBuilderRet cl_k mb_r) =
  CMCBuilderRet ($(mkClosed [| \f_r k -> CtxMultiContCons k $ fmap f_r |]))
-}

-- | A monad for building expressions in multiple levels of binders
type CMCBuilder rs = Cont (CMCBuilderRet rs)

-- NOTE: this is not possible
-- addLevelM :: CMCBuilder '(r_out, rs, r) a -> CMCBuilder '(r_out, rs:>r, r') a

{-
-- | Run a computation locally with another level
withLevelM  :: Closed (r' -> r) -> CMCBuilder '(r_out,rs :> r, r') r' ->
               CMCBuilder '(r_out,rs,r) r
withLevelM f_r m =
  cont $ \k ->
  remLevelCMCBuilderRet $ runCont m (error "FIXME")
-}

-- | Run a computation inside a name-binding
openBindingCMCBuilder :: (Mb ctx (CMCBuilderRet rs) -> CMCBuilderRet rs) ->
                         Mb ctx a -> CMCBuilder rs a
openBindingCMCBuilder f_out mb_a =
  cont $ \k -> f_out $ fmap k mb_a


-- * A name-binding monad with state-monad-like structure

-- | Commuting existentials with name-bindings
mbSome :: Mb ctx (Some f) -> Some (Compose (Mb ctx) f)
mbSome = error "FIXME HERE NOW"

class GetProxies w where
  getProxies :: w ctx -> RAssign Proxy ctx

newtype BindStRet ctx w a ctx' =
  BindStRet { unBindStRet :: Mb ctx' (w (ctx :++: ctx'), a) }

mbBindStRetProxy :: Mb ctx1 (BindStRet ctx2 w a ctx3) -> Proxy ctx3
mbBindStRetProxy _ = Proxy

class CtxAssocProof (w :: RList k -> Type) where
  ctxAssocProof :: f1 ctx1 -> f2 ctx2 -> f3 ctx3 ->
                   w ((ctx1 :++: ctx2) :++: ctx3) ->
                   ((ctx1 :++: ctx2) :++: ctx3) :~: (ctx1 :++: (ctx2 :++: ctx3))

mbSomeBindStRet :: CtxAssocProof w => f1 ctx1 -> f2 ctx2 ->
                   Mb ctx2 (Some (BindStRet (ctx1 :++: ctx2) w a)) ->
                   Some (BindStRet ctx1 w a)
mbSomeBindStRet ctx1 ctx2 mb =
  case mbSome mb of
    Some (Compose mb_mb_ret)
      | ctx3 <- mbBindStRetProxy mb_mb_ret
      , mb_w_a <- mbCombine $ fmap unBindStRet mb_mb_ret
      , Refl <- mbLift $ fmap (ctxAssocProof ctx1 ctx2 ctx3 . fst) mb_w_a ->
        Some (BindStRet mb_w_a)

newtype BindStT (w :: RList k -> Type) m a =
  BindStT { unBindStT :: forall ctx. w ctx -> m (Some (BindStRet ctx w a)) }

instance (MonadStrongBind m, CtxAssocProof w) => Monad (BindStT w m) where
  return x = BindStT $ \w -> return $ Some $ BindStRet (emptyMb (w, x))
  m >>= f =
    BindStT $ \w1 ->
    do Some (BindStRet mb1) <- unBindStT m w1
       mbSomeBindStRet Proxy Proxy <$> strongMbM (fmap (\(w2, a) -> unBindStT (f a) w2) mb1)

instance (MonadStrongBind m, CtxAssocProof w) => Functor (BindStT w m) where
  fmap f xs = xs >>= return . f

instance (MonadStrongBind m, CtxAssocProof w) => Applicative (BindStT w m) where
  pure = return
  m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))


{-
-- newtype BindT2 m a = BindT2 { unBindT2 :: Some (Flip Mb (m a)) }
data BindT2 w m a = forall ctx. BindT2 (w ctx) (Mb ctx (m a))

someifyBindT2 :: BindT2 w m a -> Some (Product w (Flip Mb (m a)))
someifyBindT2 (BindT2 w mb_m) = Some (Pair w (Flip mb_m))

mbBindT2 :: BindMonoid w => w ctx -> Mb ctx (BindT2 m a) -> BindT2 w m a
mbBindT2 w1 mb_m =
  case mbSome (fmap somifyBindT2 mb_m) of
    Some (Compose mb_prod_flip) ->
      let mb_w2 = fmap (\(Pair w2 _) -> w2) mb_prod_flip
          mb_mb_m = fmap (\(Pair _ (Flip mb_m))) mb_prod_flip in
      BindT2 (bmappend w1 mb_w2) (mbCombine mb_mb_m)

instance (BindMonoid w, Monad m) => Monad (BindT2 m) where
  return x = BindT $ emptyMb $ return x
  (BindT2 w1 mb_m) >>= f =
    BindT $
    do Some (Pair w1 (Flip mb_a)) <- unBindT m
       Some (Compose mb_w2_mb_b) <-
         mbSome <$> strongMbM (fmap (unBindT . f) mb_a)
       let mb_w2 = fmap (\(Pair w2 _) -> w2) mb_w2_mb_b
       let mb_b = mbCombine $ fmap (\(Pair _ (Flip b)) -> b) mb_w2_mb_b
       return $ BindRet (bmappend w1 mb_w2) mb_b

instance (BindMonoid w, Monad m) => Functor (BindT2 w m) where
  fmap f xs = xs >>= return . f

instance (BindMonoid w, Monad m) => Applicative (BindT w m) where
  pure = return
  m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))
-}



-- * A name-binding monad with writer-monad-like structure

newtype Flip f a b = Flip { unFlip :: f b a }

type BindRet w a = Some (Product w (Flip Mb a))

pattern BindRet w mb_a = Some (Pair w (Flip mb_a))

instance LiftableAny1 f => Liftable (Some f) where
  mbLift [nuP| Some x |] = Some $ mbLiftAny1 x

class BindMonoid (w :: RList k -> Type) where
  bmempty :: w RNil
  bmappend :: w ctx1 -> Mb ctx1 (w ctx2) -> w (ctx1 :++: ctx2)

newtype BindT (w :: RList k -> Type) m a =
  BindT { unBindT :: m (BindRet w a) }

instance (MonadStrongBind m, BindMonoid w) => Monad (BindT w m) where
  return x = BindT $ return $ BindRet bmempty (emptyMb x)
  m >>= f =
    BindT $
    do Some (Pair w1 (Flip mb_a)) <- unBindT m
       Some (Compose mb_w2_mb_b) <-
         mbSome <$> strongMbM (fmap (unBindT . f) mb_a)
       let mb_w2 = fmap (\(Pair w2 _) -> w2) mb_w2_mb_b
       let mb_b = mbCombine $ fmap (\(Pair _ (Flip b)) -> b) mb_w2_mb_b
       return $ BindRet (bmappend w1 mb_w2) mb_b

instance (MonadStrongBind m, BindMonoid w) => Functor (BindT w m) where
  fmap f xs = xs >>= return . f

instance (MonadStrongBind m, BindMonoid w) => Applicative (BindT w m) where
  pure = return
  m1 <*> m2 = m1 >>= (\x1 -> m2 >>= (\x2 -> return (x1 x2)))

data UnbindFun r (ctx :: RList k) =
  UnbindFun (RAssign Proxy ctx) (Mb ctx r -> r)

appUnbindFun :: UnbindFun r ctx -> Mb ctx r -> r
appUnbindFun (UnbindFun _ f) = f

unbindFunCtx :: UnbindFun r ctx -> RAssign Proxy ctx
unbindFunCtx (UnbindFun ctx _) = ctx

mbUnbindFunCtx :: Mb ctx' (UnbindFun r ctx) -> RAssign Proxy ctx
mbUnbindFunCtx = mbLift . fmap unbindFunCtx

instance BindMonoid (UnbindFun r) where
  bmempty = UnbindFun MNil elimEmptyMb
  bmappend f1 mb_f2 =
    UnbindFun
    (RL.append (unbindFunCtx f1) (mbUnbindFunCtx mb_f2))
    (appUnbindFun f1 . mbApply (fmap appUnbindFun mb_f2)
     . mbSeparate (mbUnbindFunCtx mb_f2))

-- type LCBuilder = BindT (UnbindFun LCModule) (BindT (UnbindFun LC) Identity)


-- * Ideas about a partially closed / "un-binding" type

newtype UnMb (reg :: Type) a = UnMb { reMb :: a }

unMbCombine :: UnMb reg1 (UnMb reg2 a) -> UnMb (reg1,reg2) a
unMbCombine (UnMb (UnMb a)) = UnMb a

unMbSplit :: UnMb (reg1,reg2) a -> UnMb reg1 (UnMb reg2 a)
unMbSplit (UnMb a) = UnMb (UnMb a)

unMbSwap :: UnMb (reg1,reg2) a -> UnMb (reg2,reg1) a
unMbSwap (UnMb a) = UnMb a

unMbApply :: UnMb reg (a -> b) -> UnMb reg a -> UnMb reg b
unMbApply (UnMb f) (UnMb x) = UnMb (f x)

unMbClosed :: Closed a -> UnMb reg a
unMbClosed = UnMb . unClosed

applyWithUnMb :: (forall reg. Mb ctx (UnMb reg a -> (UnMb reg b, c))) ->
                 a -> (b, Mb ctx c)
applyWithUnMb f a = undefined
