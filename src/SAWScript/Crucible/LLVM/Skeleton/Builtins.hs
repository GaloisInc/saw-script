{- |
Module      : SAWScript.Crucible.LLVM.Skeleton
Description : Inferring and using "skeletons" of LLVM specifications
Maintainer  : sbreese
Stability   : provisional
-}

{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}
{-# Language ImplicitParams #-}

module SAWScript.Crucible.LLVM.Skeleton.Builtins where

import Control.Monad
import Control.Monad.IO.Class
import Control.Lens

import Data.List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Parameterized.Some

import qualified Text.LLVM as LLVM

import Lang.Crucible.LLVM.ArraySizeProfile
import qualified Lang.Crucible.LLVM.MemType as C.LLVM
import qualified Lang.Crucible.LLVM.TypeContext as C.LLVM

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
  String ->
  Maybe Int
skelArgIndex skel nm = flip findIndex (skel ^. funSkelArgs) $ \arg ->
  arg ^. argSkelName == Just (Text.pack nm)

-- | Manually add a new guess for the size of the argument with the given name
skeleton_resize_arg ::
  FunctionSkeleton ->
  String ->
  Int ->
  Bool ->
  TopLevel FunctionSkeleton
skeleton_resize_arg skel nm sz initialized
  | Just idx <- skelArgIndex skel nm
  = skeleton_resize_arg_index skel idx sz initialized
  | otherwise = fail $ mconcat
    [ "No argument named \""
    , nm
    , "\" (enabling debug symbols when compiling might help)"
    ]

llvmTypeSize :: C.LLVM.TypeContext -> LLVM.Type -> Int
llvmTypeSize tc t =
  let ?lc = tc in
    case C.LLVM.liftMemType t of
      Left _ -> 1
      Right m -> fromIntegral $ C.LLVM.memTypeSize (C.LLVM.llvmDataLayout ?lc) m

skeleton_guess_arg_sizes ::
  FunctionSkeleton ->
  Some LLVMModule ->
  [(String, [FunctionProfile])] ->
  TopLevel FunctionSkeleton
skeleton_guess_arg_sizes skel (Some m) profiles =
  let (_, tc) = C.LLVM.typeContextFromModule $ modAST m
  in case lookup (Text.unpack $ skel ^. funSkelName) profiles of
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
    _ -> fail $ mconcat
      [ "No profile for \""
      , Text.unpack $ skel ^. funSkelName
      , "\" was generated."
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
  LLVMCrucibleSetupM (Maybe TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)
buildArg bic opts arg idx
  | arg ^. argSkelType . typeSkelIsPointer
  = let
      pt = arg ^. argSkelType . typeSkelLLVMType
      (t, initialized) = case arg ^. argSkelType . typeSkelSizeGuesses of
        (s:_)
          | s ^. sizeGuessElems > 1
            -> (LLVM.Array (fromIntegral $ s ^. sizeGuessElems) pt, s ^. sizeGuessInitialized)
          | otherwise -> (pt, False)
        _ -> (pt, False)
    in do
      ptr <- crucible_alloc bic opts t
      mval <- if initialized
        then do
        val <- crucible_fresh_var bic opts ident t
        crucible_points_to True bic opts ptr (anySetupTerm val)
        pure $ Just val
        else pure Nothing
      pure (mval, Just ptr, arg ^. argSkelName)
  | otherwise
  = do
      val <- crucible_fresh_var bic opts ident
        $ arg ^. argSkelType . typeSkelLLVMType
      pure (Just val, Nothing, arg ^. argSkelName)
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
skeleton_exec bic opts prestate = do
  args <- forM (prestate ^. skelArgs) $ \(mval, mptr, _) ->
    case (mval, mptr) of
      (_, Just ptr) -> pure ptr
      (Just val, Nothing) -> pure $ anySetupTerm val
      (Nothing, Nothing) -> fail ""
  crucible_execute_func bic opts args

rebuildArg ::
  BuiltinContext ->
  Options ->
  (ArgSkeleton, (Maybe TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text))  ->
  Int ->
  LLVMCrucibleSetupM (Maybe TypedTerm, Maybe (AllLLVM SetupValue), Maybe Text)
rebuildArg bic opts (arg, prearg) idx
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
      ident = maybe ("arg" <> show idx) Text.unpack nm
    in do
      val' <- crucible_fresh_var bic opts ident t
      crucible_points_to True bic opts ptr $ anySetupTerm val'
      pure (Just val', Just ptr, nm)
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
  , (Just t, _, _) <- (state ^. skelArgs) !! idx
  = pure t
  | otherwise = fail $ mconcat
    [ "No initialized argument at index "
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
    [ "No initialized argument named \""
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
