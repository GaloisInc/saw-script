{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}

module SAWScript.Crucible.LLVM.Skeleton where

import Control.Lens.TH

import Control.Monad
import Control.Lens

import Data.Maybe
import Data.List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Parameterized.Some

import qualified Text.LLVM as LLVM

import Lang.Crucible.LLVM.ArraySizeProfile

import Verifier.SAW.TypedTerm

import SAWScript.Options
import SAWScript.Value
import SAWScript.Crucible.Common.MethodSpec
import SAWScript.Crucible.LLVM.Builtins
import SAWScript.Crucible.LLVM.MethodSpecIR
import SAWScript.Crucible.LLVM.Boilerplate

type Skeleton = BPFun LLVM.Type

data SkeletonState = SkeletonState
  { _skelArgs :: [(TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)]
  }
makeLenses ''SkeletonState

llvm_skeleton ::
  Some LLVMModule ->
  [Profile] ->
  String ->
  TopLevel Skeleton
llvm_skeleton m profs nm
  | Just skel <- find (\fun -> fun ^. bpFunName == Text.pack nm)
                 $ extractDefines (viewSome modAST m) profs
  = pure skel
  | otherwise = fail $ mconcat
    [ "No function named \""
    , nm
    , "\" defined in LLVM module."
    ]

skeleton_resize_arg_index ::
  Skeleton ->
  Int ->
  Int ->
  TopLevel Skeleton
skeleton_resize_arg_index skel idx sz = pure (skel & bpFunArgs . ix idx . bpArgBufSize .~ Just sz)

skeleton_resize_arg ::
  Skeleton ->
  String ->
  Int ->
  TopLevel Skeleton
skeleton_resize_arg skel nm sz
  | Just idx <- skelArgIndex skel nm
  = skeleton_resize_arg_index skel idx sz
  | otherwise = fail $ mconcat
    [ "No argument named \""
    , nm
    , "\" (enabling debug symbols when compiling might help)"
    ]

skeleton_prestate ::
  BuiltinContext ->
  Options ->
  Skeleton ->
  LLVMCrucibleSetupM SkeletonState
skeleton_prestate bic opts skel = do
  _skelArgs <- mapM (uncurry $ buildArg bic opts) $ zip (skel ^. bpFunArgs) [1,2..]
  pure $ SkeletonState{..}

skeleton_exec ::
  BuiltinContext ->
  Options ->
  SkeletonState ->
  LLVMCrucibleSetupM ()
skeleton_exec bic opts prestate =
  crucible_execute_func bic opts
  $ (prestate ^. skelArgs) <&> \(val, mptr, _) -> fromMaybe (anySetupTerm val) mptr

skeleton_poststate ::
  BuiltinContext ->
  Options ->
  Skeleton ->
  SkeletonState ->
  LLVMCrucibleSetupM SkeletonState
skeleton_poststate bic opts skel prestate = do
  _skelArgs <- zipWithM (rebuildArg bic opts)
    (zip (skel ^. bpFunArgs) (prestate ^. skelArgs))
    [1,2..]
  pure $ SkeletonState{..}

skeleton_arg_index ::
  BuiltinContext ->
  Options ->
  SkeletonState ->
  Int ->
  LLVMCrucibleSetupM TypedTerm
skeleton_arg_index _bic _opts state idx
  | idx < length (state ^. skelArgs)
  , (t, _, _) <- (state ^. skelArgs) !! idx
  = pure t
  | otherwise = fail $ mconcat
    [ "No argument at index "
    , show idx
    ]

skeleton_arg ::
  BuiltinContext ->
  Options ->
  SkeletonState ->
  String ->
  LLVMCrucibleSetupM TypedTerm
skeleton_arg bic opts state nm
  | Just idx <- stateArgIndex state nm
  = skeleton_arg_index bic opts state idx
  | otherwise = fail $ mconcat
    [ "No argument named \""
    , nm
    , "\" (enabling debug symbols when compiling might help)"
    ]

skeleton_arg_index_pointer ::
  BuiltinContext ->
  Options ->
  SkeletonState ->
  Int ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
skeleton_arg_index_pointer _bic _opts state idx
  | idx < length (state ^. skelArgs)
  , (_, mp, _) <- (state ^. skelArgs) !! idx
  = case mp of
      Just p -> pure p
      Nothing -> fail $ mconcat
        [ "Argument at index "
        , show idx
        , " is not a pointer or array"
        ]
  | otherwise = fail $ mconcat
    [ "No argument at index "
    , show idx
    ]

skeleton_arg_pointer ::
  BuiltinContext ->
  Options ->
  SkeletonState ->
  String ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
skeleton_arg_pointer bic opts state nm
  | Just idx <- stateArgIndex state nm
  = skeleton_arg_index_pointer bic opts state idx
  | otherwise = fail $ mconcat
    [ "No argument named \""
    , nm
    , "\" (enabling debug symbols when compiling might help)"
    ]

-------------------------------------------------------------------------------

buildArg ::
  BuiltinContext ->
  Options ->
  BPArg LLVM.Type ->
  Int ->
  LLVMCrucibleSetupM (TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)
buildArg bic opts arg idx
  | LLVM.PtrTo pt <- arg ^. bpArgType
  = let t = case arg ^. bpArgBufSize of
              Nothing -> pt
              Just s -> LLVM.Array (fromIntegral s) pt
    in do
      ptr <- crucible_alloc bic opts t
      val <- crucible_fresh_var bic opts ident t
      crucible_points_to True bic opts ptr (anySetupTerm val)
      pure (val, Just ptr, arg ^. bpArgName)
  | otherwise
  = let t = arg ^. bpArgType in do
      val <- crucible_fresh_var bic opts ident t
      pure (val, Nothing, arg ^. bpArgName)
  where
    ident = maybe ("arg" <> show idx) Text.unpack $ arg ^. bpArgName

rebuildArg ::
  BuiltinContext ->
  Options ->
  (BPArg LLVM.Type, (TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text))  ->
  Int ->
  LLVMCrucibleSetupM (TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)
rebuildArg bic opts (arg, prearg) idx
  | LLVM.PtrTo pt <- arg ^. bpArgType
  , (_, Just ptr, nm) <- prearg
  = let t = case arg ^. bpArgBufSize of
              Nothing -> pt
              Just s -> LLVM.Array (fromIntegral s) pt
        ident = maybe ("arg" <> show idx) Text.unpack nm
    in do
      val' <- crucible_fresh_var bic opts ident t
      crucible_points_to True bic opts ptr (anySetupTerm val')
      pure (val', Just ptr, nm)
  | otherwise = pure prearg

skelArgIndex ::
  Skeleton ->
  String ->
  Maybe Int
skelArgIndex state nm = flip findIndex (state ^. bpFunArgs) $ \arg ->
  arg ^. bpArgName == Just (Text.pack nm)

stateArgIndex ::
  SkeletonState ->
  String ->
  Maybe Int
stateArgIndex state nm = flip findIndex (state ^. skelArgs) $ \(_, _, mnm) ->
  mnm == Just (Text.pack nm)
