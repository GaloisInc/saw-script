{- |
Module      : SAWCentral.Crucible.LLVM.Skeleton
Description : Inferring and using "skeletons" of LLVM specifications
Maintainer  : sbreese
Stability   : provisional
-}

{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ImplicitParams #-}

module SAWCentral.Crucible.LLVM.Skeleton.Builtins
  ( module_skeleton
  , function_skeleton
  , skeleton_resize_arg_index
  , skeleton_resize_arg
  , skeleton_guess_arg_sizes
  , skeleton_globals_pre
  , skeleton_prestate
  , skeleton_exec
  , skeleton_globals_post
  , skeleton_poststate
  , skeleton_arg_index
  , skeleton_arg
  , skeleton_arg_index_pointer
  , skeleton_arg_pointer
  ) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Lens

import Data.List (findIndex)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Parameterized.Some

import qualified Text.LLVM as LLVM

import Lang.Crucible.LLVM.ArraySizeProfile
import qualified Lang.Crucible.LLVM.MemType as C.LLVM
import qualified Lang.Crucible.LLVM.TypeContext as C.LLVM

import CryptolSAWCore.TypedTerm

import SAWCentral.Value
import SAWCentral.Crucible.Common.MethodSpec
import SAWCentral.Crucible.LLVM.Builtins
import SAWCentral.Crucible.LLVM.MethodSpecIR

import SAWCentral.Crucible.LLVM.Skeleton

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
  Text ->
  TopLevel FunctionSkeleton
function_skeleton mskel nm =
  case mskel ^. modSkelFunctions . at nm of
    Just fskel -> pure fskel
    Nothing -> throwTopLevel $ Text.unpack $ "No skeleton exists for function \"" <> nm <> "\""

-- | Manually add a new guess for the size of the argument at the given index
skeleton_resize_arg_index ::
  FunctionSkeleton ->
  Int ->
  Int ->
  Bool ->
  TopLevel FunctionSkeleton
skeleton_resize_arg_index skel idx sz initialized =
  pure (skel & funSkelArgs . ix idx . argSkelType . typeSkelSizeGuesses %~ (guess:))
  where
    guess :: SizeGuess
    guess = SizeGuess
      { _sizeGuessElems = sz
      , _sizeGuessInitialized = initialized
      , _sizeGuessSource = "user guess"
      }

skelArgIndex ::
  FunctionSkeleton ->
  Text ->
  Maybe Int
skelArgIndex skel nm = flip findIndex (skel ^. funSkelArgs) $ \arg ->
  arg ^. argSkelName == Just nm

-- | Manually add a new guess for the size of the argument with the given name
skeleton_resize_arg ::
  FunctionSkeleton ->
  Text ->
  Int ->
  Bool ->
  TopLevel FunctionSkeleton
skeleton_resize_arg skel nm sz initialized
  | Just idx <- skelArgIndex skel nm
  = skeleton_resize_arg_index skel idx sz initialized
  | otherwise = throwTopLevel $ Text.unpack $
      "No argument named \"" <> nm <>
      "\" (enabling debug symbols when compiling might help)"

llvmTypeSize :: C.LLVM.TypeContext -> LLVM.Type -> Int
llvmTypeSize tc t =
  let ?lc = tc in
    case C.LLVM.liftMemType t of
      Left _ -> 1
      Right m -> fromIntegral $ C.LLVM.memTypeSize (C.LLVM.llvmDataLayout ?lc) m

skeleton_guess_arg_sizes ::
  ModuleSkeleton ->
  Some LLVMModule ->
  [(Text, [FunctionProfile])] ->
  TopLevel ModuleSkeleton
skeleton_guess_arg_sizes mskel (Some m) profiles = do
  let (_, tc) = C.LLVM.typeContextFromModule $ modAST m
  fskels <- forM (mskel ^. modSkelFunctions) $ \skel -> do
    case lookup (skel ^. funSkelName) profiles of
      Just (prof:_) -> let
        updateArg (a, p)
          | a ^. argSkelType . typeSkelIsPointer
          , Just s <- p ^. argProfileSize
          = a & argSkelType . typeSkelSizeGuesses
            %~ (SizeGuess
                 (quot s $ llvmTypeSize tc $ a ^. argSkelType . typeSkelLLVMType)
                 (p ^. argProfileInitialized)
                 "checking sizes in the simulator":)
          | otherwise = a
        uargs args = updateArg <$> zip args (prof ^. funProfileArgs)
        in pure (skel & funSkelArgs %~ uargs)
      _ -> pure skel
  pure $ mskel & modSkelFunctions .~ fskels

--------------------------------------------------------------------------------
-- ** Writing SAWScript specifications using skeletons 

skeleton_globals_pre ::
  ModuleSkeleton ->
  LLVMCrucibleSetupM ()
skeleton_globals_pre mskel =
  forM_ (mskel ^. modSkelGlobals) $ \gskel ->
    when (gskel ^. globSkelMutable) $ do
      let gname = gskel ^. globSkelName
      llvm_alloc_global gname
      when (gskel ^. globSkelInitialized)
        . llvm_points_to True (anySetupGlobal gname)
        $ anySetupGlobalInitializer gname

skeleton_globals_post ::
  ModuleSkeleton ->
  LLVMCrucibleSetupM ()
skeleton_globals_post mskel =
  forM_ (mskel ^. modSkelGlobals) $ \gskel -> do
    when (gskel ^. globSkelMutable && gskel ^. globSkelInitialized) $ do
      let gname = gskel ^. globSkelName
      llvm_points_to True (anySetupGlobal gname)
        $ anySetupGlobalInitializer gname

buildArg ::
  ArgSkeleton ->
  Int ->
  LLVMCrucibleSetupM (Maybe TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)
buildArg arg idx
  | arg ^. argSkelType . typeSkelIsPointer
  = let
      pt = arg ^. argSkelType . typeSkelLLVMType
      (t, initialized) = case arg ^. argSkelType . typeSkelSizeGuesses of
        (s:_)
          | s ^. sizeGuessElems > 1
            -> (LLVM.Array (fromIntegral $ s ^. sizeGuessElems) pt, s ^. sizeGuessInitialized)
          | otherwise -> (pt, s ^. sizeGuessInitialized)
        _ -> (pt, False)
    in do
      ptr <- llvm_alloc t
      mval <- if initialized
        then do
        val <- llvm_fresh_var ident t
        llvm_points_to True ptr (anySetupTerm val)
        pure $ Just val
        else pure Nothing
      pure (mval, Just ptr, arg ^. argSkelName)
  | otherwise
  = do
      val <- llvm_fresh_var ident
        $ arg ^. argSkelType . typeSkelLLVMType
      pure (Just val, Nothing, arg ^. argSkelName)
  where
    ident = maybe ("arg" <> Text.pack (show idx)) id $ arg ^. argSkelName

skeleton_prestate ::
  FunctionSkeleton ->
  LLVMCrucibleSetupM SkeletonState
skeleton_prestate skel = do
  _skelArgs <- mapM (uncurry buildArg) $ zip (skel ^. funSkelArgs) [1,2..]
  pure $ SkeletonState{..}

skeleton_exec ::
  SkeletonState ->
  LLVMCrucibleSetupM ()
skeleton_exec prestate = do
  args <- forM (prestate ^. skelArgs) $ \(mval, mptr, _) ->
    case (mval, mptr) of
      (_, Just ptr) -> pure ptr
      (Just val, Nothing) -> pure $ anySetupTerm val
      (Nothing, Nothing) -> throwLLVMFun "skeleton_exec" "Invalid pointer-pointee combination on skeleton argument"
  llvm_execute_func args

rebuildArg ::
  (ArgSkeleton, (Maybe TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text))  ->
  Int ->
  LLVMCrucibleSetupM (Maybe TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)
rebuildArg (arg, prearg) idx
  | arg ^. argSkelType . typeSkelIsPointer
  , (_, Just ptr, nm) <- prearg
  = let
      pt = arg ^. argSkelType . typeSkelLLVMType
      t = case arg ^. argSkelType . typeSkelSizeGuesses of
        (s:_)
          | s ^. sizeGuessElems > 1
            -> LLVM.Array (fromIntegral $ s ^. sizeGuessElems) pt
          | otherwise -> pt
        _ -> pt
      ident = maybe ("arg" <> Text.pack (show idx)) id nm
    in do
      val' <- llvm_fresh_var ident t
      llvm_points_to True ptr $ anySetupTerm val'
      pure (Just val', Just ptr, nm)
  | otherwise = pure prearg

skeleton_poststate ::
  FunctionSkeleton ->
  SkeletonState ->
  LLVMCrucibleSetupM SkeletonState
skeleton_poststate skel prestate = do
  _skelArgs <- zipWithM rebuildArg
    (zip (skel ^. funSkelArgs) (prestate ^. skelArgs))
    [1,2..]
  case skel ^. funSkelRet . typeSkelLLVMType of
    LLVM.PrimType LLVM.Void -> pure ()
    t -> do
      ret <- llvm_fresh_var ("return value of " <> (skel ^. funSkelName)) t
      llvm_return $ anySetupTerm ret
  pure $ SkeletonState{..}

skeleton_arg_index ::
  SkeletonState ->
  Int ->
  LLVMCrucibleSetupM TypedTerm
skeleton_arg_index state idx
  | idx < length (state ^. skelArgs)
  , (Just t, _, _) <- (state ^. skelArgs) !! idx
  = pure t
  | otherwise = throwLLVMFun "skeleton_arg_index" $ mconcat
    [ "No initialized argument at index "
    , show idx
    ]

stateArgIndex ::
  SkeletonState ->
  Text ->
  Maybe Int
stateArgIndex state nm = flip findIndex (state ^. skelArgs) $ \(_, _, mnm) ->
  mnm == Just nm

skeleton_arg ::
  SkeletonState ->
  Text ->
  LLVMCrucibleSetupM TypedTerm
skeleton_arg state nm
  | Just idx <- stateArgIndex state nm
  = skeleton_arg_index state idx
  | otherwise = throwLLVMFun "skeleton_arg" $ Text.unpack $
      "No initialized argument named \"" <> nm <>
      "\" (enabling debug symbols when compiling might help)"

skeleton_arg_index_pointer ::
  SkeletonState ->
  Int ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
skeleton_arg_index_pointer state idx
  | idx < length (state ^. skelArgs)
  , (_, mp, _) <- (state ^. skelArgs) !! idx
  = case mp of
      Just p -> pure p
      Nothing -> throwLLVMFun "skeleton_arg_index_pointer" $ mconcat
        [ "Argument at index "
        , show idx
        , " is not a pointer or array"
        ]
  | otherwise = throwLLVMFun "skeleton_arg_index_pointer" $ mconcat
    [ "No argument at index "
    , show idx
    ]

skeleton_arg_pointer ::
  SkeletonState ->
  Text ->
  LLVMCrucibleSetupM (AllLLVM SetupValue)
skeleton_arg_pointer state nm
  | Just idx <- stateArgIndex state nm
  = skeleton_arg_index_pointer state idx
  | otherwise = do
      throwLLVMFun "skeleton_arg_pointer" $ Text.unpack $
        "No argument named \"" <> nm <>
        "\" (enabling debug symbols when compiling might help)"

