{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}

module Mir.Compositional
where

import Data.Parameterized.Context (Ctx(..), pattern Empty, pattern (:>), Assignment)
import Data.Parameterized.NatRepr
import Data.Text (Text)
import qualified Data.Text as Text

import Lang.Crucible.Backend
import Lang.Crucible.CFG.Core
import Lang.Crucible.Simulator
import Lang.Crucible.Simulator.OverrideSim
import Lang.Crucible.Simulator.RegMap

import Crux
import Crux.Types

import Mir.DefId
import Mir.Intrinsics
import Mir.Language (BindExtraOverridesFn)


compositionalOverrides ::
    forall args ret blocks sym rtp a r .
    (IsSymInterface sym) =>
    Maybe (SomeOnlineSolver sym) -> Text -> CFG MIR blocks args ret ->
    Maybe (OverrideSim (Model sym) sym MIR rtp a r ())
compositionalOverrides symOnline name cfg

  | (normDefId "crucible::method_spec::raw::builder_new" <> "::_inst") `Text.isPrefixOf` name
  , Empty <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_new" MethodSpecBuilderRepr $ do
        error "TODO method_spec_builder_new requires a MethodSpecBuilderImpl instance"

  | (normDefId "crucible::method_spec::raw::builder_add_arg" <> "::_inst") `Text.isPrefixOf` name
  , Empty :> MethodSpecBuilderRepr :> MirReferenceRepr tpr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_add_arg" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)
            :> RegEntry (MirReferenceRepr tpr) argRef) <- getOverrideArgs
        msb' <- msbAddArg tpr argRef msb
        return $ MethodSpecBuilder msb'

  | (normDefId "crucible::method_spec::raw::builder_set_return" <> "::_inst") `Text.isPrefixOf` name
  , Empty :> MethodSpecBuilderRepr :> MirReferenceRepr tpr <- cfgArgTypes cfg
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

