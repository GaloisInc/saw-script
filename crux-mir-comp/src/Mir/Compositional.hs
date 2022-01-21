{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}

module Mir.Compositional
where

import Data.Parameterized.Context (pattern Empty, pattern (:>))
import Data.Parameterized.NatRepr
import Data.Text (Text)
import qualified Data.Text as Text

import Lang.Crucible.Backend
import Lang.Crucible.CFG.Core
import Lang.Crucible.Simulator

import qualified What4.Expr.Builder as W4

import Crux

import Mir.DefId
import Mir.Generator (CollectionState)
import Mir.Intrinsics

import Mir.Compositional.Builder (builderNew)
import Mir.Compositional.Clobber (clobberGlobalsOverride)


compositionalOverrides ::
    forall sym p t st fs args ret blocks rtp a r .
    (IsSymInterface sym, sym ~ W4.ExprBuilder t st fs) =>
    Maybe (SomeOnlineSolver sym) ->
    CollectionState ->
    Text ->
    CFG MIR blocks args ret ->
    Maybe (OverrideSim (p sym) sym MIR rtp a r ())
compositionalOverrides _symOnline cs name cfg

  | (normDefId "crucible::method_spec::raw::builder_new" <> "::_inst") `Text.isPrefixOf` name
  , Empty <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_new" MethodSpecBuilderRepr $ do
        msb <- builderNew cs (textId name)
        return $ MethodSpecBuilder msb

  | (normDefId "crucible::method_spec::raw::builder_add_arg" <> "::_inst") `Text.isPrefixOf` name
  , Empty :> MethodSpecBuilderRepr :> MirReferenceRepr _tpr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_add_arg" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)
            :> RegEntry (MirReferenceRepr tpr) argRef) <- getOverrideArgs
        msb' <- msbAddArg tpr argRef msb
        return $ MethodSpecBuilder msb'

  | (normDefId "crucible::method_spec::raw::builder_set_return" <> "::_inst") `Text.isPrefixOf` name
  , Empty :> MethodSpecBuilderRepr :> MirReferenceRepr _tpr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_set_return" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)
            :> RegEntry (MirReferenceRepr tpr) argRef) <- getOverrideArgs
        msb' <- msbSetReturn tpr argRef msb
        return $ MethodSpecBuilder msb'

  | normDefId "crucible::method_spec::raw::builder_gather_assumes" == name
  , Empty :> MethodSpecBuilderRepr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_gather_assumes" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)) <- getOverrideArgs
        msb' <- msbGatherAssumes msb
        return $ MethodSpecBuilder msb'

  | normDefId "crucible::method_spec::raw::builder_gather_asserts" == name
  , Empty :> MethodSpecBuilderRepr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_gather_asserts" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)) <- getOverrideArgs
        msb' <- msbGatherAsserts msb
        return $ MethodSpecBuilder msb'

  | normDefId "crucible::method_spec::raw::builder_finish" == name
  , Empty :> MethodSpecBuilderRepr <- cfgArgTypes cfg
  , MethodSpecRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_finish" MethodSpecRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)) <- getOverrideArgs
        msbFinish msb


  | normDefId "crucible::method_spec::raw::clobber_globals" == name
  , Empty <- cfgArgTypes cfg
  , UnitRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_clobber_globals" UnitRepr $ do
        clobberGlobalsOverride cs


  | normDefId "crucible::method_spec::raw::spec_pretty_print" == name
  , Empty :> MethodSpecRepr <- cfgArgTypes cfg
  , MirSliceRepr (BVRepr w) <- cfgReturnType cfg
  , Just Refl <- testEquality w (knownNat @8)
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_spec_pretty_print" (MirSliceRepr $ BVRepr $ knownNat @8) $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpec ms _)) <- getOverrideArgs
        msPrettyPrint ms

  | normDefId "crucible::method_spec::raw::spec_enable" == name
  , Empty :> MethodSpecRepr <- cfgArgTypes cfg
  , UnitRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_spec_enable" UnitRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpec ms _)) <- getOverrideArgs
        msEnable ms


  | otherwise = Nothing

