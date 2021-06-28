{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module Verifier.SAW.Heapster.IRTTranslation (
  translateCompletePermIRTTyVars,
  translateCompleteShapeIRTTyVars,
  IRTVarTree(..), pattern IRTVar, IRTVarIdxs,
  translateCompleteIRTDesc,
  translateCompleteIRTDef,
  translateCompleteIRTFoldFun,
  translateCompleteIRTUnfoldFun,
  -- * Useful functions
  completeOpenTermTyped,
  listSortOpenTerm,
  askExprCtxTerms
  ) where

import Numeric.Natural
import Data.Foldable
import Data.Functor.Const
import GHC.TypeLits
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import qualified Data.Type.RList as RL
import Data.Binding.Hobbits
import Data.Parameterized.BoolRepr
import Data.Reflection

import Lang.Crucible.Types
import Verifier.SAW.OpenTerm
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.SAWTranslation


-- | "Complete" an 'OpenTerm' to a closed 'TypedTerm' or 'fail' on
-- type-checking error
-- TODO Move this to OpenTerm.hs?
completeOpenTermTyped :: SharedContext -> OpenTerm -> IO TypedTerm
completeOpenTermTyped sc (OpenTerm termM) =
  either (fail . show) return =<<
  runTCM termM sc Nothing []

-- | Build an element of type ListSort from a list of types
-- TODO Move this to OpenTerm.hs?
listSortOpenTerm :: [OpenTerm] -> OpenTerm
listSortOpenTerm [] = ctorOpenTerm "Prelude.LS_Nil" []
listSortOpenTerm (tp:tps) =
  ctorOpenTerm "Prelude.LS_Cons" [tp, listSortOpenTerm tps]

-- | Get the result of applying 'exprCtxToTerms' to the current expression
-- translation context
-- TODO Move this to SAWTranslation.hs?
askExprCtxTerms :: TransInfo info => TransM info ctx [OpenTerm]
askExprCtxTerms = exprCtxToTerms <$> infoCtx <$> ask


----------------------------------------------------------------------
-- The monad for translating IRT type variables
----------------------------------------------------------------------

data IRTRecName args where
  IRTRecPermName :: NamedPermName ns args tp -> IRTRecName args
  IRTRecShapeName :: NatRepr w -> NamedShape 'True args w -> IRTRecName args

data IRTTyVarsTransCtx args ext =
  IRTTyVarsTransCtx
  {
    irtTRecName :: IRTRecName args,
    irtTArgsCtx :: RAssign (Const [OpenTerm]) args,
    irtTExtCtx  :: RAssign Proxy ext,
    irtTPermEnv :: PermEnv
  }

-- | The monad for translating IRT type variables
type IRTTyVarsTransM args ext =
  ReaderT (IRTTyVarsTransCtx args ext) (Either String)

runIRTTyVarsTransM :: PermEnv -> IRTRecName args -> CruCtx args ->
                      IRTTyVarsTransM args RNil a ->
                      Either String a
runIRTTyVarsTransM env n_rec argsCtx m = runReaderT m ctx
  where args_trans = RL.map (\tp -> Const $ typeTransTypes $
                               runNilTypeTransM (translateClosed tp) env)
                            (cruCtxToTypes argsCtx)
        ctx = IRTTyVarsTransCtx n_rec args_trans MNil env

-- | Run an IRT type variables translation computation in an extended context
inExtIRTTyVarsTransM :: IRTTyVarsTransM args (ext :> tp) a ->
                        IRTTyVarsTransM args ext a
inExtIRTTyVarsTransM = withReaderT $
  \ctx -> ctx { irtTExtCtx = irtTExtCtx ctx :>: Proxy }

-- | Combine a binding inside an @args :++: ext@ binding into a single
-- @args :++: ext'@ binding
irtTMbCombine ::
  forall args ext c a.
  Mb (args :++: ext) (Binding c a) ->
  IRTTyVarsTransM args ext (Mb (args :++: (ext :> c)) a)
irtTMbCombine x =
  do ext <- irtTExtCtx <$> ask
     return $
       mbCombine (ext :>: Proxy) $
       fmap (mbCombine RL.typeCtxProxies ) $
       mbSeparate @_ @args ext x

-- | Create an @args :++: ext@ binding
irtNus :: (RAssign Name args -> RAssign Name ext -> b) ->
          IRTTyVarsTransM args ext (Mb (args :++: ext) b)
irtNus f = 
  do args <- irtTArgsCtx <$> ask
     ext  <- irtTExtCtx  <$> ask
     return $ mbCombine ext (nus (RL.map (\_->Proxy) args) (nus ext . f))

-- | Turn an @args :++: ext@ binding into just an @args@ binding using
-- 'partialSubst'
irtTSubstExt :: (Substable PartialSubst a Maybe, NuMatching a) =>
                Mb (args :++: ext) a ->
                IRTTyVarsTransM args ext (Mb args a)
irtTSubstExt x =
  do ext <- irtTExtCtx <$> ask
     let x' = mbSwap ext (mbSeparate ext x)
         emptyPS = PartialSubst $ RL.map (\_ -> PSubstElem Nothing) ext
     args <- RL.map (const Proxy) . irtTArgsCtx <$> ask
     case give args (partialSubst emptyPS x') of
       Just x'' -> return x''
       Nothing -> throwError $ "non-array permission in a recursive perm body"
                               ++ " depends on an existential variable!"


----------------------------------------------------------------------
-- Trees for keeping track of IRT variable indices
----------------------------------------------------------------------

data IRTVarTree a = IRTVarsNil
                  | IRTVarsCons a (IRTVarTree a)
                  | IRTVarsAppend (IRTVarTree a) (IRTVarTree a)
                  | IRTVarsConcat [IRTVarTree a]
                  | IRTRecVar -- the recursive case
                  deriving (Show, Eq, Functor, Foldable, Traversable)

pattern IRTVar :: a -> IRTVarTree a
pattern IRTVar ix = IRTVarsCons ix IRTVarsNil

type IRTVarTreeShape = IRTVarTree ()
type IRTVarIdxs      = IRTVarTree Natural

-- | Fill in all the leaves of an 'IRTVarTree' with sequential indices
setIRTVarIdxs :: IRTVarTreeShape -> IRTVarIdxs
setIRTVarIdxs tree = evalState (mapM (\_ -> nextIdx) tree) 0
  where nextIdx :: State Natural Natural
        nextIdx = state (\i -> (i,i+1))


----------------------------------------------------------------------
-- Translating IRT type variables
----------------------------------------------------------------------

-- | Given the name of a recursive permission being defined and its argument
-- content, translate the permission's body to a SAW core list of its IRT type
-- variables and an 'IRTVarIdxs', which is used to get indices into the list
-- when calling 'translateCompleteIRTDesc'
translateCompletePermIRTTyVars :: SharedContext -> PermEnv ->
                                  NamedPermName ns args tp -> CruCtx args ->
                                  Mb args (ValuePerm a) ->
                                  IO (TypedTerm, IRTVarIdxs)
translateCompletePermIRTTyVars sc env npn_rec args p =
  case runIRTTyVarsTransM env (IRTRecPermName npn_rec) args (irtTyVars p) of
    Left err -> fail err
    Right (tps, ixs) ->
      do tm <- completeOpenTermTyped sc $
               runNilTypeTransM (lambdaExprCtx args $
                                  listSortOpenTerm <$> sequence tps) env
         return (tm, setIRTVarIdxs ixs)

-- | Given the a recursive shape being defined, translate the shape's body to
-- a SAW core list of its IRT type variables and an 'IRTVarIdxs', which is
-- used to get indices into the list when calling 'translateCompleteIRTDesc'
translateCompleteShapeIRTTyVars :: KnownNat w => SharedContext -> PermEnv ->
                                   NamedShape 'True args w ->
                                   IO (TypedTerm, IRTVarIdxs)
translateCompleteShapeIRTTyVars sc env nmsh_rec =
  let args = namedShapeArgs nmsh_rec
      body = unfoldNamedShape nmsh_rec <$>
               nus (cruCtxProxies args) namesToExprs in
  case runIRTTyVarsTransM env (IRTRecShapeName knownNat nmsh_rec)
                              args (irtTyVars body) of
    Left err -> fail err
    Right (tps, ixs) ->
      do tm <- completeOpenTermTyped sc $
               runNilTypeTransM (lambdaExprCtx args $
                                  listSortOpenTerm <$> sequence tps) env
         return (tm, setIRTVarIdxs ixs)

-- | Types from which we can get IRT type variables, e.g. ValuePerm
class IRTTyVars a where
  irtTyVars :: Mb (args :++: ext) a ->
               IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                         IRTVarTreeShape)

-- | Get all IRT type variables in a value perm
instance IRTTyVars (ValuePerm a) where
  irtTyVars mb_p = case mbMatch mb_p of
    [nuMP| ValPerm_Eq _ |] -> return ([], IRTVarsNil)
    [nuMP| ValPerm_Or p1 p2 |] ->
      do (tps1, ixs1) <- irtTyVars p1
         (tps2, ixs2) <- irtTyVars p2
         return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
    [nuMP| ValPerm_Exists p |] -> irtTyVars p -- see the instance for Binding!
    [nuMP| ValPerm_Named npn args off |] ->
      namedPermIRTTyVars mb_p npn args off
    [nuMP| ValPerm_Var x _ |] ->
      irtTTranslateVar mb_p x
    [nuMP| ValPerm_Conj ps |] -> irtTyVars ps

-- | Get all IRT type variables in a binding, including any type variables
-- from the bound variable
instance (KnownRepr TypeRepr tp, IRTTyVars a) => IRTTyVars (Binding tp a) where
  irtTyVars mb_x =
    do let tp = mbBindingType mb_x
           tp_trans = typeTransTupleType <$> translateClosed tp
       xCbn <- irtTMbCombine mb_x
       (tps, ixs) <- inExtIRTTyVarsTransM (irtTyVars xCbn)
       return (tp_trans : tps, IRTVarsCons () ixs)

-- | Get all IRT type variables in a named permission application. The first
-- argument must be either 'ValPerm_Named' or 'Perm_NamedConj' applied to the
-- remaining arguments.
namedPermIRTTyVars :: forall args ext a tr ns args' tp.
                      (Translate TypeTransInfo args a (TypeTrans tr),
                       Substable PartialSubst a Maybe, NuMatching a) =>
                      Mb (args :++: ext) a ->
                      Mb (args :++: ext) (NamedPermName ns args' tp) ->
                      Mb (args :++: ext) (PermExprs args') ->
                      Mb (args :++: ext) (PermOffset tp) ->
                      IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                                IRTVarTreeShape)
namedPermIRTTyVars p npn args off =
  do npn_args <- irtNus (\ns _ -> namesToExprs ns)
     npn_off  <- irtNus (\_  _ -> NoPermOffset @tp)
     n_rec <- irtTRecName <$> ask
     case n_rec of
       IRTRecPermName npn_rec
         | [nuMP| Just (Refl, Refl, Refl) |]
             <- mbMatch $ testNamedPermNameEq npn_rec <$> npn
         , npn_args == args, npn_off == off
         -> return ([], IRTRecVar)
       IRTRecPermName _
         -> throwError $ "recursive permission applied to different"
                         ++ " arguments in its definition!"
       _ -> do env <- irtTPermEnv <$> ask
               case lookupNamedPerm env (mbLift npn) of
                 Just (NamedPerm_Defined dp) ->
                   irtTyVars (mbMap2 (unfoldDefinedPerm dp) args off)
                 _ -> do p' <- irtTSubstExt p
                         let p_trans = typeTransTupleType <$> translate p'
                         return ([p_trans], IRTVar ())

-- | Return a singleton list with the type corresponding to the given variable
-- if the variable has a type translation - otherwise this function returns
-- the empty list. The first argument must be either 'PExpr_Var' or
-- @(\x -> 'ValPerm_Var' x off)@ applied to the second argument.
irtTTranslateVar :: (IsTermTrans tr, Translate TypeTransInfo args a tr,
                     Substable PartialSubst a Maybe, NuMatching a) =>
                    Mb (args :++: ext) a -> Mb (args :++: ext) (ExprVar tp) ->
                    IRTTyVarsTransM args ext ([TypeTransM args OpenTerm],
                                              IRTVarTreeShape)
irtTTranslateVar p x =
  do p' <- irtTSubstExt p
     let tm_trans = transTerms <$> translate p'
     -- because of 'irtTSubstExt' above, we know x must be a member of args,
     --  so we can safely look up its type translation
     argsCtx <- irtTArgsCtx <$> ask
     extCtx  <- irtTExtCtx  <$> ask
     let err _ = error "arguments to irtTTranslateVar do not match"
         memb = mbLift $ fmap (either id err . mbNameBoundP)
                              (mbSwap extCtx (mbSeparate extCtx x))
         tp_trans = getConst $ RL.get memb argsCtx
     -- if x (and thus also p) has no translation, return an empty list
     case tp_trans of
       [] -> return ([], IRTVarsNil)
       _  -> return ([tupleOfTypes <$> tm_trans], IRTVar ())

-- | Get all IRT type variables in a list
instance (NuMatching a, IRTTyVars a) => IRTTyVars [a] where
  irtTyVars mb_xs =
    do (tps, ixs) <- unzip <$> mapM irtTyVars (mbList mb_xs)
       return (concat tps, IRTVarsConcat ixs)

-- | Get all IRT type variables in an atomic perm
instance IRTTyVars (AtomicPerm a) where
  irtTyVars mb_p = case mbMatch mb_p of
    [nuMP| Perm_LLVMField fld |] ->
      irtTyVars (fmap llvmFieldContents fld)
    [nuMP| Perm_LLVMArray mb_ap |] ->
         irtTyVars $ fmap (fmap llvmArrayFieldToAtomicPerm . llvmArrayFields)
                          mb_ap
    [nuMP| Perm_LLVMBlock bp |] ->
      irtTyVars (fmap llvmBlockShape bp)
    [nuMP| Perm_LLVMFree _ |] -> return ([], IRTVarsNil)
    [nuMP| Perm_LLVMFunPtr _ p |] ->
      irtTyVars p
    [nuMP| Perm_IsLLVMPtr |] -> return ([], IRTVarsNil)
    [nuMP| Perm_LLVMBlockShape sh |] ->
      irtTyVars sh
    [nuMP| Perm_NamedConj npn args off |] ->
      namedPermIRTTyVars mb_p npn args off
    [nuMP| Perm_LLVMFrame _ |] -> return ([], IRTVarsNil)
    [nuMP| Perm_LOwned _ _ |] ->
      throwError "lowned permission in an IRT definition!"
    [nuMP| Perm_LCurrent _ |] -> return ([], IRTVarsNil)
    [nuMP| Perm_Struct ps |] -> irtTyVars ps
    [nuMP| Perm_Fun _ |] ->
      throwError "fun perm in an IRT definition!"
    [nuMP| Perm_BVProp _ |] ->
      throwError "BVProp in an IRT definition!"

-- | Get all IRT type variables in a shape expression
instance IRTTyVars (PermExpr (LLVMShapeType w)) where
  irtTyVars mb_sh = case mbMatch mb_sh of
    [nuMP| PExpr_Var x |] -> irtTTranslateVar mb_sh x
    [nuMP| PExpr_EmptyShape |] -> return ([], IRTVarsNil)
    [nuMP| PExpr_NamedShape maybe_rw maybe_l nmsh args |] ->
      do args_rec <- irtNus (\ns _ -> namesToExprs ns)
         n_rec <- irtTRecName <$> ask
         case n_rec of
           IRTRecShapeName w_rec nmsh_rec
             | mbLift $ (namedShapeName nmsh_rec ==) . namedShapeName <$> nmsh
             , [nuMP| Just Refl |] <- mbMatch $
                 testEquality w_rec . shapeLLVMTypeWidth <$> mb_sh
             , [nuMP| Just Refl |] <- mbMatch $
                 testEquality (namedShapeArgs nmsh_rec) . namedShapeArgs <$> nmsh
             , [nuMP| Just Refl |] <- mbMatch $
                 testEquality TrueRepr . namedShapeCanUnfoldRepr <$> nmsh
             , args_rec == args
             , [nuMP| Nothing |] <- mbMatch maybe_rw
             , [nuMP| Nothing |] <- mbMatch maybe_l
             -> return ([], IRTRecVar)
           IRTRecShapeName _ nmsh_rec
             | mbLift $ (namedShapeName nmsh_rec ==) . namedShapeName <$> nmsh
               -> throwError $ "recursive shape applied to different"
                               ++ " arguments in its definition!"
           _ -> case mbMatch $ namedShapeBody <$> nmsh of
                  [nuMP| DefinedShapeBody _ |] ->
                    irtTyVars (mbMap2 unfoldNamedShape nmsh args)
                  _ -> do sh' <- irtTSubstExt mb_sh
                          let sh_trans = transTupleTerm <$> translate sh'
                          return ([sh_trans], IRTVar ())
    [nuMP| PExpr_EqShape _ |] -> return ([], IRTVarsNil)
    [nuMP| PExpr_PtrShape _ _ sh |] -> irtTyVars sh
    [nuMP| PExpr_FieldShape fsh |] -> irtTyVars fsh
    [nuMP| PExpr_ArrayShape _ _ fshs |] -> irtTyVars fshs
    [nuMP| PExpr_SeqShape sh1 sh2 |] ->
      do (tps1, ixs1) <- irtTyVars sh1
         (tps2, ixs2) <- irtTyVars sh2
         return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
    [nuMP| PExpr_OrShape sh1 sh2 |] ->
      do (tps1, ixs1) <- irtTyVars sh1
         (tps2, ixs2) <- irtTyVars sh2
         return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)
    [nuMP| PExpr_ExShape sh |] -> irtTyVars sh -- see the instance for Binding!

-- | Get all IRT type variables in a field shape
instance IRTTyVars (LLVMFieldShape w) where
  irtTyVars (mbMatch -> [nuMP| LLVMFieldShape p |]) = irtTyVars p

-- | Get all IRT type variables in a set of value perms
instance IRTTyVars (RAssign ValuePerm ps) where
  irtTyVars mb_ps = case mbMatch mb_ps of
    [nuMP| ValPerms_Nil |] -> return ([], IRTVarsNil)
    [nuMP| ValPerms_Cons ps p |] ->
      do (tps1, ixs1) <- irtTyVars ps
         (tps2, ixs2) <- irtTyVars p
         return (tps1 ++ tps2, IRTVarsAppend ixs1 ixs2)


----------------------------------------------------------------------
-- The IRTDesc translation monad
----------------------------------------------------------------------

-- | Contextual info for translating IRT type descriptions
data IRTDescTransInfo ctx =
  IRTDescTransInfo { irtDExprCtx :: ExprTransCtx ctx,
                     irtDPermEnv :: PermEnv,
                     irtDTyVars  :: OpenTerm
                   }

-- | Build an empty 'IRTDescTransInfo' from a 'PermEnv' and type var 'Ident',
-- setting 'irtDTyVars' to 'globalOpenTerm' of the given 'Ident'
emptyIRTDescTransInfo :: PermEnv -> Ident -> IRTDescTransInfo RNil
emptyIRTDescTransInfo env tyVarsIdent =
  IRTDescTransInfo MNil env (globalOpenTerm tyVarsIdent)

-- | Apply the current 'irtDTyVars' to the current context using
-- 'applyOpenTermMulti' - intended to be used only in the args context and
-- when the trans info is 'emptyIRTDescTransInfo' (see its usage in
-- 'translateCompleteIRTDesc').
-- The result of calling this function appropriately is that 'irtDTyVars' now
-- contains a term which is the type variables identifier applied to its
-- arguments, no matter how much 'IRTDescTransM's context is extended. This
-- term is then used whenever an IRTDesc constructor is applied, see
-- 'irtCtorOpenTerm' and 'irtCtor'.
irtDInArgsCtx :: IRTDescTransM args OpenTerm -> IRTDescTransM args OpenTerm
irtDInArgsCtx m =
  do args <- askExprCtxTerms
     flip local m $ \info ->
       info { irtDTyVars = applyOpenTermMulti (irtDTyVars info) args }

instance TransInfo IRTDescTransInfo where
  infoCtx = irtDExprCtx
  infoEnv = irtDPermEnv
  extTransInfo etrans (IRTDescTransInfo {..}) =
    IRTDescTransInfo
    { irtDExprCtx = irtDExprCtx :>: etrans
    , .. }

-- | The monad for translating IRT type descriptions
type IRTDescTransM = TransM IRTDescTransInfo

-- | Apply the given IRT constructor to the given arguments, using the
-- type variable identifier applied to its arguments from the current
-- 'IRTDescTransInfo' for the first argument
irtCtorOpenTerm :: Ident -> [OpenTerm] -> IRTDescTransM ctx OpenTerm
irtCtorOpenTerm c all_args =
  do tyVarsTm <- irtDTyVars <$> ask
     return $ ctorOpenTerm c (tyVarsTm : all_args)

-- | Like 'tupleOfTypes' but with @IRT_prod@
irtProd :: [OpenTerm] -> IRTDescTransM ctx OpenTerm
irtProd [x] = return x
irtProd xs =
  do irtUnit <- irtCtorOpenTerm "Prelude.IRT_unit" []
     foldrM (\x xs' -> irtCtorOpenTerm "Prelude.IRT_prod" [x, xs'])
            irtUnit xs

-- | A singleton list containing the result of 'irtCtorOpenTerm'
irtCtor :: Ident -> [OpenTerm] -> IRTDescTransM ctx [OpenTerm]
irtCtor c all_args =
  do tm <- irtCtorOpenTerm c all_args
     return [tm]


----------------------------------------------------------------------
-- Translating IRT type descriptions
----------------------------------------------------------------------

-- | Given an identifier whose definition in the shared context is the first
-- result of calling 'translateCompletePermIRTTyVars' or
-- 'translateCompleteShapeIRTTyVars' on the same argument context and
-- recursive permission/shape body given here, and an 'IRTVarIdxs' which is
-- the second result of the same call to 'translateCompletePermIRTTyVars',
-- translate the given recursive permission body to an IRT type description
translateCompleteIRTDesc :: IRTDescs a => SharedContext -> PermEnv -> 
                            Ident -> CruCtx args ->
                            Mb args a -> IRTVarIdxs -> IO TypedTerm
translateCompleteIRTDesc sc env tyVarsIdent args p ixs =
  do tm <- completeOpenTerm sc $
           runTransM (lambdaExprCtx args . irtDInArgsCtx $
                        do in_mu <- irtDesc p ixs
                           irtCtorOpenTerm "Prelude.IRT_mu" [in_mu])
                     (emptyIRTDescTransInfo env tyVarsIdent)
     -- we manually give the type because we want to keep 'tyVarsIdent' folded
     let irtDescOpenTerm ectx = return $
           dataTypeOpenTerm "Prelude.IRTDesc"
             [ applyOpenTermMulti (globalOpenTerm tyVarsIdent)
                                  (exprCtxToTerms ectx) ]
     tp <- completeOpenTerm sc $
           runNilTypeTransM (translateClosed args >>= \tptrans ->
                              piTransM "e" tptrans irtDescOpenTerm) env
     return $ TypedTerm tm tp

-- | Types from which we can get IRT type descriptions, e.g. ValuePerm
class IRTDescs a where
  irtDescs :: Mb ctx a -> IRTVarIdxs -> IRTDescTransM ctx [OpenTerm]

-- | Like 'irtDescs', but returns the single IRTDesc associated to the input.
-- This function simply applies 'irtProd' to the output of 'irtDescs'.
irtDesc :: IRTDescs a => Mb ctx a -> IRTVarIdxs -> IRTDescTransM ctx OpenTerm
irtDesc x ixs = irtDescs x ixs >>= irtProd

-- | Get the IRTDescs associated to a value perm
instance IRTDescs (ValuePerm a) where
  irtDescs mb_p ixs = case (mbMatch mb_p, ixs) of
    ([nuMP| ValPerm_Eq _ |], _) -> return []
    ([nuMP| ValPerm_Or p1 p2 |], IRTVarsAppend ixs1 ixs2) ->
      do x1 <- irtDesc p1 ixs1
         x2 <- irtDesc p2 ixs2
         irtCtor "Prelude.IRT_Either" [x1, x2]
    ([nuMP| ValPerm_Exists p |], IRTVarsCons ix ixs') ->
      do let tp = mbBindingType p
         tp_trans <- tupleTypeTrans <$> translateClosed tp
         xf <- lambdaTransM "x_irt" tp_trans (\x -> inExtTransM x $
                 irtDesc (mbCombine RL.typeCtxProxies p) ixs')
         irtCtor "Prelude.IRT_sigT" [natOpenTerm ix, xf]
    ([nuMP| ValPerm_Named npn args off |], _) ->
      namedPermIRTDescs npn args off ixs
    ([nuMP| ValPerm_Var _ _ |], _) -> irtVarTDesc ixs
    ([nuMP| ValPerm_Conj ps |], _) -> irtDescs ps ixs
    _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to a named perm
namedPermIRTDescs :: Mb ctx (NamedPermName ns args tp) ->
                     Mb ctx (PermExprs args) ->
                     Mb ctx (PermOffset tp) -> IRTVarIdxs ->
                     IRTDescTransM ctx [OpenTerm]
namedPermIRTDescs npn args off ixs = case ixs of
  IRTRecVar -> irtCtor "Prelude.IRT_varD" [natOpenTerm 0]
  _ -> do env <- infoEnv <$> ask
          case (lookupNamedPerm env (mbLift npn), ixs) of
            (Just (NamedPerm_Defined dp), _) ->
              irtDescs (mbMap2 (unfoldDefinedPerm dp) args off) ixs
            (_, IRTVar ix) -> irtCtor "Prelude.IRT_varT" [natOpenTerm ix]
            _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to a variable
irtVarTDesc :: IRTVarIdxs -> IRTDescTransM ctx [OpenTerm]
irtVarTDesc ixs = case ixs of
  IRTVarsNil -> return []
  IRTVar ix -> irtCtor "Prelude.IRT_varT" [natOpenTerm ix]
  _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to a list
instance (NuMatching a, IRTDescs a) => IRTDescs [a] where
  irtDescs mb_xs ixs = case ixs of
    IRTVarsConcat ixss -> concat <$> zipWithM irtDescs (mbList mb_xs) ixss
    _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to an atomic perm
instance IRTDescs (AtomicPerm a) where
  irtDescs mb_p ixs = case (mbMatch mb_p, ixs) of
    ([nuMP| Perm_LLVMField fld |], _) ->
      irtDescs (fmap llvmFieldContents fld) ixs
    ([nuMP| Perm_LLVMArray mb_ap |], _) ->
      do let w = natVal2 mb_ap
             w_term = natOpenTerm w
         len_term <- translate1 (fmap llvmArrayLen mb_ap)
         let mb_flds = fmap (fmap llvmArrayFieldToAtomicPerm . llvmArrayFields)
                            mb_ap
         xs_term <- irtDesc mb_flds ixs
         irtCtor "Prelude.IRT_BVVec" [w_term, len_term, xs_term]
    ([nuMP| Perm_LLVMBlock bp |], _) ->
      irtDescs (fmap llvmBlockShape bp) ixs
    ([nuMP| Perm_LLVMFree _ |], _) -> return []
    ([nuMP| Perm_LLVMFunPtr _ p |], _) ->
      irtDescs p ixs
    ([nuMP| Perm_IsLLVMPtr |], _) -> return []
    ([nuMP| Perm_LLVMBlockShape sh |], _) ->
      irtDescs sh ixs
    ([nuMP| Perm_NamedConj npn args off |], _) ->
      namedPermIRTDescs npn args off ixs
    ([nuMP| Perm_LLVMFrame _ |], _) -> return []
    ([nuMP| Perm_LOwned _ _ |], _) ->
      error "lowned permission made it to IRTDesc translation"
    ([nuMP| Perm_LCurrent _ |], _) -> return []
    ([nuMP| Perm_Struct ps |], _) ->
      irtDescs ps ixs
    ([nuMP| Perm_Fun _ |], _) ->
      error "fun perm made it to IRTDesc translation"
    ([nuMP| Perm_BVProp _ |], _) ->
      error "BVProp made it to IRTDesc translation"

-- | Get the IRTDescs associated to a shape expression
instance IRTDescs (PermExpr (LLVMShapeType w)) where
  irtDescs mb_expr ixs = case (mbMatch mb_expr, ixs) of
    ([nuMP| PExpr_Var _ |], _) -> irtVarTDesc ixs
    ([nuMP| PExpr_EmptyShape |], _) -> return []
    ([nuMP| PExpr_EqShape _ |], _) -> return []
    ([nuMP| PExpr_NamedShape _ _ nmsh args |], _) ->
      case (mbMatch $ namedShapeBody <$> nmsh, ixs) of
        (_, IRTRecVar) ->
          irtCtor "Prelude.IRT_varD" [natOpenTerm 0]
        ([nuMP| DefinedShapeBody _ |], _) ->
          irtDescs (mbMap2 unfoldNamedShape nmsh args) ixs
        (_, IRTVar ix) -> irtCtor "Prelude.IRT_varT" [natOpenTerm ix]
        _ -> error $ "malformed IRTVarIdxs: " ++ show ixs
    ([nuMP| PExpr_PtrShape _ _ sh |], _) ->
      irtDescs sh ixs
    ([nuMP| PExpr_FieldShape fsh |], _) ->
      irtDescs fsh ixs
    ([nuMP| PExpr_ArrayShape mb_len _ mb_fshs |], _) ->
      do let w = natVal4 mb_len
             w_term = natOpenTerm w
         len_term <- translate1 mb_len
         xs_term <- irtDesc mb_fshs ixs
         irtCtor "Prelude.IRT_BVVec" [w_term, len_term, xs_term]
    ([nuMP| PExpr_SeqShape sh1 sh2 |], IRTVarsAppend ixs1 ixs2) ->
      do x1 <- irtDesc sh1 ixs1
         x2 <- irtDesc sh2 ixs2
         irtCtor "Prelude.IRT_prod" [x1, x2]
    ([nuMP| PExpr_OrShape sh1 sh2 |], IRTVarsAppend ixs1 ixs2) ->
      do x1 <- irtDesc sh1 ixs1
         x2 <- irtDesc sh2 ixs2
         irtCtor "Prelude.IRT_Either" [x1, x2]
    ([nuMP| PExpr_ExShape mb_sh |], IRTVarsCons ix ixs') ->
      do let tp = mbBindingType mb_sh
         tp_trans <- tupleTypeTrans <$> translateClosed tp
         xf <- lambdaTransM "x_irt" tp_trans (\x -> inExtTransM x $
                 irtDesc (mbCombine RL.typeCtxProxies mb_sh) ixs')
         irtCtor "Prelude.IRT_sigT" [natOpenTerm ix, xf]
    _ -> error $ "malformed IRTVarIdxs: " ++ show ixs

-- | Get the IRTDescs associated to a field shape
instance IRTDescs (LLVMFieldShape w) where
  irtDescs (mbMatch -> [nuMP| LLVMFieldShape p |]) ixs = irtDescs p ixs

-- | Get the IRTDescs associated to a set of value perms
instance IRTDescs (RAssign ValuePerm ps) where
  irtDescs mb_ps ixs = case (mbMatch mb_ps, ixs) of
    ([nuMP| ValPerms_Nil |], _) -> return []
    ([nuMP| ValPerms_Cons ps p |], IRTVarsAppend ixs1 ixs2) ->
      do xs <- irtDescs ps ixs1
         x  <- irtDescs p ixs2
         return $ xs ++ x
    _ -> error $ "malformed IRTVarIdxs: " ++ show ixs


----------------------------------------------------------------------
-- Translating IRT definitions
----------------------------------------------------------------------

-- | Given identifiers whose definitions in the shared context are the results
-- of corresponding calls to 'translateCompleteIRTDesc' and
-- 'translateCompletePermIRTTyVars' or 'translateCompleteShapeIRTTyVars',
-- return a term which is @IRT@ applied to these identifiers
translateCompleteIRTDef :: SharedContext -> PermEnv -> 
                           Ident -> Ident -> CruCtx args ->
                           IO TypedTerm
translateCompleteIRTDef sc env tyVarsIdent descIdent args =
  completeOpenTermTyped sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtDefinition tyVarsIdent descIdent) env

-- | Given identifiers whose definitions in the shared context are the results
-- of corresponding calls to 'translateCompleteIRTDef',
-- 'translateCompleteIRTDesc', and 'translateCompletePermIRTTyVars' or
-- 'translateCompleteShapeIRTTyVars', return a term which is @foldIRT@ applied
-- to these identifiers
translateCompleteIRTFoldFun :: SharedContext -> PermEnv -> 
                               Ident -> Ident -> Ident -> CruCtx args ->
                               IO Term
translateCompleteIRTFoldFun sc env tyVarsIdent descIdent _ args =
  completeOpenTerm sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtFoldFun tyVarsIdent descIdent) env

-- | Given identifiers whose definitions in the shared context are the results
-- of corresponding calls to 'translateCompleteIRTDef',
-- 'translateCompleteIRTDesc', and 'translateCompletePermIRTTyVars' or
-- 'translateCompleteShapeIRTTyVars', return a term which is @unfoldIRT@
-- applied to these identifiers
translateCompleteIRTUnfoldFun :: SharedContext -> PermEnv -> 
                                 Ident -> Ident -> Ident -> CruCtx args ->
                                 IO Term
translateCompleteIRTUnfoldFun sc env tyVarsIdent descIdent _ args =
  completeOpenTerm sc $
  runNilTypeTransM (lambdaExprCtx args $
                     irtUnfoldFun tyVarsIdent descIdent) env

-- | Get the terms for the arguments to @IRT@, @foldIRT@, and @unfoldIRT@
-- given the appropriate identifiers
irtDefArgs :: Ident -> Ident -> TypeTransM args (OpenTerm, OpenTerm, OpenTerm)
irtDefArgs tyVarsIdent descIdent = 
  do args <- askExprCtxTerms
     let tyVars = applyOpenTermMulti (globalOpenTerm tyVarsIdent) args
         substs = ctorOpenTerm "Prelude.IRTs_Nil" [tyVars]
         desc   = applyOpenTermMulti (globalOpenTerm descIdent) args
     return (tyVars, substs, desc)

irtDefinition :: Ident -> Ident -> TypeTransM args OpenTerm
irtDefinition tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ dataTypeOpenTerm "Prelude.IRT" [tyVars, substs, desc]

irtFoldFun :: Ident -> Ident -> TypeTransM args OpenTerm
irtFoldFun tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.foldIRT")
                                 [tyVars, substs, desc]

irtUnfoldFun :: Ident -> Ident -> TypeTransM args OpenTerm
irtUnfoldFun tyVarsIdent descIdent = 
  do (tyVars, substs, desc) <- irtDefArgs tyVarsIdent descIdent
     return $ applyOpenTermMulti (globalOpenTerm "Prelude.unfoldIRT")
                                 [tyVars, substs, desc]
