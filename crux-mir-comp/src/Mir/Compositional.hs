{-# Language RankNTypes #-}
{-# Language PatternSynonyms #-}
{-# Language TypeApplications #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language OverloadedStrings #-}
{-# Language TypeOperators #-}

module Mir.Compositional
where

import Control.Lens ((^.), at)
import Data.Parameterized.Context (pattern Empty, pattern (:>))
import Data.Text (Text)
import qualified Prettyprinter as PP

import Lang.Crucible.Backend
import Lang.Crucible.CFG.Core
import Lang.Crucible.Simulator

import Crux

import Mir.DefId
import Mir.Generator (CollectionState, collection)
import Mir.Intrinsics
import Mir.Mir (Intrinsic, Substs(..), inSubsts, intrInst, intrinsics)
import Mir.TransTy (tyToRepr)

import Mir.Compositional.Builder (builderNew)
import Mir.Compositional.Clobber (clobberGlobalsOverride)
import Mir.Compositional.DefId (hasInstPrefix)
import Mir.Compositional.State


compositionalOverrides ::
    forall sym bak p t fs args ret blocks rtp a r .
    (IsSymInterface sym, sym ~ MirSym t fs) =>
    Maybe (SomeOnlineSolver sym bak) ->
    CollectionState ->
    Text ->
    CFG MIR blocks args ret ->
    Maybe (OverrideSim (p sym) sym MIR rtp a r ())
compositionalOverrides _symOnline cs name cfg

  | hasInstPrefix ["crucible", "method_spec", "raw", "builder_new"] explodedName
  , Empty <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_new" MethodSpecBuilderRepr $ do
        msb <- builderNew cs (textId name)
        return $ MethodSpecBuilder msb

  | hasInstPrefix ["crucible", "method_spec", "raw", "builder_add_arg"] explodedName
  , Empty :> MethodSpecBuilderRepr :> MirReferenceRepr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_add_arg" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)
            :> RegEntry MirReferenceRepr argRef) <- getOverrideArgs
        -- The TypeRepr for the reference's pointee type cannot be obtained from
        -- getOverrideArgs, so we must compute it indirectly by looking at the
        -- type substitution in the instantiated function.
        Some tpr <- substedTypeRepr nameIntrinsic
        msb' <- msbAddArg tpr argRef msb
        return $ MethodSpecBuilder msb'

  | hasInstPrefix ["crucible", "method_spec", "raw", "builder_set_return"] explodedName
  , Empty :> MethodSpecBuilderRepr :> MirReferenceRepr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_set_return" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)
            :> RegEntry MirReferenceRepr argRef) <- getOverrideArgs
        -- The TypeRepr for the reference's pointee type cannot be obtained from
        -- getOverrideArgs, so we must compute it indirectly by looking at the
        -- type substitution in the instantiated function.
        Some tpr <- substedTypeRepr nameIntrinsic
        msb' <- msbSetReturn tpr argRef msb
        return $ MethodSpecBuilder msb'

  | ["crucible", "method_spec", "raw", "builder_gather_assumes"] == explodedName
  , Empty :> MethodSpecBuilderRepr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_gather_assumes" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)) <- getOverrideArgs
        msb' <- msbGatherAssumes msb
        return $ MethodSpecBuilder msb'

  | ["crucible", "method_spec", "raw", "builder_gather_asserts"] == explodedName
  , Empty :> MethodSpecBuilderRepr <- cfgArgTypes cfg
  , MethodSpecBuilderRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_gather_asserts" MethodSpecBuilderRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)) <- getOverrideArgs
        msb' <- msbGatherAsserts msb
        return $ MethodSpecBuilder msb'

  | ["crucible", "method_spec", "raw", "builder_finish"] == explodedName
  , Empty :> MethodSpecBuilderRepr <- cfgArgTypes cfg
  , MethodSpecRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_builder_finish" MethodSpecRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpecBuilder msb)) <- getOverrideArgs
        msbFinish msb


  | ["crucible", "method_spec", "raw", "clobber_globals"] == explodedName
  , Empty <- cfgArgTypes cfg
  , MirAggregateRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_clobber_globals" MirAggregateRepr $ do
        clobberGlobalsOverride cs
        mirAggregate_zstSim


  | ["crucible", "method_spec", "raw", "spec_pretty_print"] == explodedName
  , Empty :> MethodSpecRepr <- cfgArgTypes cfg
  , MirSliceRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_spec_pretty_print" MirSliceRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpec ms _)) <- getOverrideArgs
        msPrettyPrint ms

  | ["crucible", "method_spec", "raw", "spec_enable"] == explodedName
  , Empty :> MethodSpecRepr <- cfgArgTypes cfg
  , MirAggregateRepr <- cfgReturnType cfg
  = Just $ bindFnHandle (cfgHandle cfg) $ UseOverride $
    mkOverride' "method_spec_spec_enable" MirAggregateRepr $ do
        RegMap (Empty :> RegEntry _tpr (MethodSpec ms _)) <- getOverrideArgs
        msEnable ms
        mirAggregate_zstSim


  | otherwise = Nothing
  where
    col = cs ^. collection
    explodedName = textIdKey name
    nameId = textId name
    nameIntrinsic =
      case col ^. intrinsics . at nameId of
        Nothing ->
          panic $ "Could not look up DefId: " ++ show nameId
        Just intr -> intr

    -- Given an Intrinsic for an instantiation of a polymorphic function with
    -- exactly one type argument, look in the Intrinsic's Substs and convert the
    -- substituted type to a TypeRepr. This function will panic if the supplied
    -- Intrinsic has a Subst with a number of type substitutions other than one.
    substedTypeRepr :: Intrinsic -> OverrideSim (p sym) sym MIR rtp a r (Some TypeRepr)
    substedTypeRepr intr =
      let instSubstTy =
            case intr ^. intrInst . inSubsts of
              Substs [ty] -> ty
              Substs tys ->
                panic $
                  "Expected Substs value with a single type, but found: " ++
                  show (PP.pretty tys) in

      case tyToRepr col instSubstTy of
        Left err -> fail ("Type not supported: " ++ err)
        Right x -> pure x

    panic :: String -> a
    panic msg = error $ "compositionalOverrides: " ++ msg
