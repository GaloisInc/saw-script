{- |
Module      : SAWScript.Crucible.LLVM.Skeleton
Description : Inferring and using "skeletons" of LLVM specifications
Maintainer  : sbreese
Stability   : provisional
-}

{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}

module SAWScript.Crucible.LLVM.Skeleton.Builtins where

import Control.Monad
import Control.Monad.IO.Class
import Control.Lens

import Data.Maybe
import Data.List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Parameterized.Some
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Text.LLVM as LLVM

import Verifier.SAW.TypedTerm

import SAWScript.Options
import SAWScript.Value
import SAWScript.Crucible.Common.MethodSpec
import SAWScript.Crucible.LLVM.Builtins
import SAWScript.Crucible.LLVM.MethodSpecIR

import SAWScript.Crucible.LLVM.Skeleton

--------------------------------------------------------------------------------
-- ** Manipulating skeletons

module_skeleton ::
  Some LLVMModule ->
  TopLevel ModuleSkeleton
module_skeleton m = do
  let ast = viewSome modAST m
  liftIO $ moduleSkeleton ast

function_skeleton ::
  ModuleSkeleton ->
  String ->
  TopLevel FunctionSkeleton
function_skeleton mskel nm =
  case mskel ^. modSkelFunctions . at (Text.pack nm) of
    Just fskel -> pure fskel
    Nothing -> fail $ mconcat ["No skeleton exists for function \"", nm, "\""]

-- | Manually add a new guess for the size of the argument at the given index
skeleton_resize_arg_index ::
  FunctionSkeleton ->
  Int ->
  Int ->
  TopLevel FunctionSkeleton
skeleton_resize_arg_index skel idx sz =
  pure (skel & funSkelArgs . ix idx . argSkelType . typeSkelSizeGuesses %~ (guess:))
  where
    guess :: SizeGuess
    guess = SizeGuess
      { _sizeGuessElems = sz
      , _sizeGuessSource = ""
      }

skelArgIndex ::
  FunctionSkeleton ->
  String ->
  Maybe Int
skelArgIndex skel nm = flip findIndex (skel ^. funSkelArgs) $ \arg ->
  arg ^. argSkelName == Just (Text.pack nm)

-- | Manually add a new guess for the size of the argument with the given name
skeleton_resize_arg ::
  FunctionSkeleton ->
  String ->
  Int ->
  TopLevel FunctionSkeleton
skeleton_resize_arg skel nm sz
  | Just idx <- skelArgIndex skel nm
  = skeleton_resize_arg_index skel idx sz
  | otherwise = fail $ mconcat
    [ "No argument named \""
    , nm
    , "\" (enabling debug symbols when compiling might help)"
    ]

--------------------------------------------------------------------------------
-- ** Writing SAWScript specifications using skeletons 

skeleton_globals_pre ::
  BuiltinContext ->
  Options ->
  ModuleSkeleton ->
  LLVMCrucibleSetupM ()
skeleton_globals_pre bic opts mskel =
  forM_ (mskel ^. modSkelGlobals) $ \gskel ->
    when (gskel ^. globSkelMutable) $ do
      let gname = Text.unpack $ gskel ^. globSkelName
      crucible_alloc_global bic opts gname
      when (gskel ^. globSkelInitialized)
        . crucible_points_to True bic opts (anySetupGlobal gname)
        $ anySetupGlobalInitializer gname

skeleton_globals_post ::
  BuiltinContext ->
  Options ->
  ModuleSkeleton ->
  LLVMCrucibleSetupM ()
skeleton_globals_post bic opts mskel =
  forM_ (mskel ^. modSkelGlobals) $ \gskel -> do
    when (gskel ^. globSkelMutable && gskel ^. globSkelInitialized) $ do
      let gname = Text.unpack $ gskel ^. globSkelName
      crucible_points_to True bic opts (anySetupGlobal gname)
        $ anySetupGlobalInitializer gname

buildArg ::
  BuiltinContext ->
  Options ->
  ArgSkeleton ->
  Int ->
  LLVMCrucibleSetupM (TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)
buildArg bic opts arg idx
  | arg ^. argSkelType . typeSkelIsPointer
  = let
      pt = arg ^. argSkelType . typeSkelLLVMType
      t = case arg ^. argSkelType . typeSkelSizeGuesses of
        [] -> pt
        (s:_) -> LLVM.Array (fromIntegral $ s ^. sizeGuessElems) pt
    in do
      ptr <- crucible_alloc bic opts t
      val <- crucible_fresh_var bic opts ident t
      crucible_points_to True bic opts ptr (anySetupTerm val)
      pure (val, Just ptr, arg ^. argSkelName)
  | otherwise
  = do
      val <- crucible_fresh_var bic opts ident
        $ arg ^. argSkelType . typeSkelLLVMType
      pure (val, Nothing, arg ^. argSkelName)
  where
    ident = maybe ("arg" <> show idx) Text.unpack $ arg ^. argSkelName

skeleton_prestate ::
  BuiltinContext ->
  Options ->
  FunctionSkeleton ->
  LLVMCrucibleSetupM SkeletonState
skeleton_prestate bic opts skel = do
  _skelArgs <- mapM (uncurry $ buildArg bic opts) $ zip (skel ^. funSkelArgs) [1,2..]
  pure $ SkeletonState{..}

skeleton_exec ::
  BuiltinContext ->
  Options ->
  SkeletonState ->
  LLVMCrucibleSetupM ()
skeleton_exec bic opts prestate =
  crucible_execute_func bic opts
  $ (prestate ^. skelArgs) <&> \(val, mptr, _) -> fromMaybe (anySetupTerm val) mptr

rebuildArg ::
  BuiltinContext ->
  Options ->
  (ArgSkeleton, (TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text))  ->
  Int ->
  LLVMCrucibleSetupM (TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)
rebuildArg bic opts (arg, prearg) idx
  | arg ^. argSkelType . typeSkelIsPointer
  , (_, Just ptr, nm) <- prearg
  = let
      pt = arg ^. argSkelType . typeSkelLLVMType
      t = case arg ^. argSkelType . typeSkelSizeGuesses of
        [] -> pt
        (s:_) -> LLVM.Array (fromIntegral $ s ^. sizeGuessElems) pt
      ident = maybe ("arg" <> show idx) Text.unpack nm
    in do
      val' <- crucible_fresh_var bic opts ident t
      crucible_points_to True bic opts ptr $ anySetupTerm val'
      pure (val', Just ptr, nm)
  | otherwise = pure prearg

skeleton_poststate ::
  BuiltinContext ->
  Options ->
  FunctionSkeleton ->
  SkeletonState ->
  LLVMCrucibleSetupM SkeletonState
skeleton_poststate bic opts skel prestate = do
  _skelArgs <- zipWithM (rebuildArg bic opts)
    (zip (skel ^. funSkelArgs) (prestate ^. skelArgs))
    [1,2..]
  case skel ^. funSkelRet . typeSkelLLVMType of
    LLVM.PrimType LLVM.Void -> pure ()
    t -> do
      ret <- crucible_fresh_var bic opts ("return value of " <> (Text.unpack $ skel ^. funSkelName)) t
      crucible_return bic opts $ anySetupTerm ret
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

stateArgIndex ::
  SkeletonState ->
  String ->
  Maybe Int
stateArgIndex state nm = flip findIndex (state ^. skelArgs) $ \(_, _, mnm) ->
  mnm == Just (Text.pack nm)

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
