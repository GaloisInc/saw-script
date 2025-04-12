{-# OPTIONS -Wall -Werror #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAWCentral.Crucible.LLVM.Boilerplate
  ( llvm_boilerplate
  ) where

import System.IO

import Control.Monad.IO.Class
import Control.Lens

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text.IO
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.Graph as Graph

import qualified Text.LLVM as LLVM

import SAWCentral.Value

import SAWCentral.Crucible.LLVM.Skeleton

sortByDeps :: [FunctionSkeleton] -> [FunctionSkeleton]
sortByDeps skels = reverse $ (\(f, _, _) -> f) . fromVertex <$> Graph.topSort g
  where
    (g, fromVertex, _) = Graph.graphFromEdges $ adjacency <$> skels
    adjacency :: FunctionSkeleton -> (FunctionSkeleton, Text, [Text])
    adjacency s = (s, s ^. funSkelName, Set.toList $ s ^. funSkelCalls)

preludeBoilerplate :: Bool -> ModuleSkeleton -> Text
preludeBoilerplate True _mskel = "enable_experimental;\nMODULE_SKEL <- module_skeleton MODULE;\n\n"
preludeBoilerplate False _mskel = "\n";

globalsPreBoilerplate :: Bool -> ModuleSkeleton -> Text
globalsPreBoilerplate True _mskel = "skeleton_globals_pre MODULE_SKEL;\n"
globalsPreBoilerplate False _mskel = "\n"

globalsPostBoilerplate :: Bool -> ModuleSkeleton -> Text
globalsPostBoilerplate True _mskel = "skeleton_globals_post MODULE_SKEL;\n"
globalsPostBoilerplate False _mskel = "\n"

llvmTypeBoilerplate :: LLVM.Type -> Text
llvmTypeBoilerplate (LLVM.PrimType (LLVM.Integer n)) = mconcat
  [ "(llvm_int ", Text.pack $ show n, ")"
  ]
llvmTypeBoilerplate (LLVM.PrimType (LLVM.FloatType LLVM.Float)) = "llvm_float"
llvmTypeBoilerplate (LLVM.PrimType (LLVM.FloatType LLVM.Double)) = "llvm_double"
llvmTypeBoilerplate (LLVM.Alias (LLVM.Ident n)) = mconcat
  [ "(llvm_type \"%", Text.pack n, ")"
  ]
llvmTypeBoilerplate _ = "undefined"

typeBoilerplate :: TypeSkeleton -> Text
typeBoilerplate t
  | t ^. typeSkelIsPointer
  , (s:_) <- t ^. typeSkelSizeGuesses
  = mconcat
    [ "(llvm_array "
    , Text.pack . show $ s ^. sizeGuessElems
    , " "
    , llvmTypeBoilerplate $ t ^. typeSkelLLVMType
    , ")"
    ]
  | otherwise = llvmTypeBoilerplate $ t ^. typeSkelLLVMType

bodyBoilerplate :: Bool -> FunctionSkeleton -> Text -> Text
bodyBoilerplate True _fskel skelName = mconcat
  [ "  prestate <- skeleton_prestate ", skelName, ";\n"
  , "  skeleton_exec prestate;\n"
  , "  poststate <- skeleton_poststate ", skelName,  " prestate;\n"
  ]
bodyBoilerplate False fskel _ = mconcat
  [ mconcat $ uncurry argPrecondition <$> numberedArgs
  , "  llvm_execute_func ["
  , Text.intercalate ", " $ uncurry argTerm <$> numberedArgs
  , "];\n\n"
  , if | LLVM.PrimType LLVM.Void <- fskel ^. funSkelRet . typeSkelLLVMType -> ""
       | fskel ^. funSkelRet . typeSkelIsPointer -> "  llvm_return undefined;\n\n"
       | otherwise -> mconcat
         [ "  __return <- llvm_fresh_var \"(return ", fskel ^. funSkelName
         , ")\" ", typeBoilerplate $ fskel ^. funSkelRet, ";\n"
         , "  llvm_return (llvm_term __return);\n\n"
         ]
  , mconcat $ uncurry argPostcondition <$> numberedArgs
  ]
  where
    numberedArgs = zip [0..] $ fskel ^. funSkelArgs
    argName :: Int -> ArgSkeleton -> Text
    argName i a
      | Just n <- a ^. argSkelName = n
      | otherwise = "arg" <> Text.pack (show i)
    argPrecondition :: Int -> ArgSkeleton -> Text
    argPrecondition i a
      | a ^. argSkelType . typeSkelIsPointer
      , (s:_) <- a ^. argSkelType . typeSkelSizeGuesses
      , s ^. sizeGuessInitialized
      = mconcat
        [ "  ", argName i a, " <- llvm_fresh_var \"", argName i a, "\" ", typeBoilerplate (a ^. argSkelType), ";\n"
        , "  ", argName i a, "_ptr <- llvm_alloc ", typeBoilerplate (a ^. argSkelType), ";\n"
        , "  llvm_points_to ", argName i a, "_ptr (llvm_term ", argName i a, ");\n\n"
        ]
      | a ^. argSkelType . typeSkelIsPointer
      = mconcat
        [ "  ", argName i a, "_ptr <- llvm_alloc ", typeBoilerplate (a ^. argSkelType), ";\n\n"
        ]
      | otherwise
      = mconcat
        [ "  ", argName i a, " <- llvm_fresh_var \"", argName i a, "\" ", typeBoilerplate (a ^. argSkelType), ";\n\n"
        ]
    argPostcondition :: Int -> ArgSkeleton -> Text
    argPostcondition i a
      | a ^. argSkelType . typeSkelIsPointer
      = mconcat
        [ "  ", argName i a, "_post <- llvm_fresh_var \"", argName i a, "_post\" ", typeBoilerplate (a ^. argSkelType), ";\n"
        , "  llvm_points_to ", argName i a, "_ptr (llvm_term ", argName i a, "_post);\n\n"
        ]
      | otherwise = ""
    argTerm :: Int -> ArgSkeleton -> Text
    argTerm i a
      | a ^. argSkelType . typeSkelIsPointer
      = argName i a <> "_ptr"
      | otherwise
      = "(llvm_term " <> argName i a <> ")"

functionBoilerplate :: Bool -> ModuleSkeleton -> FunctionSkeleton -> Text
functionBoilerplate skelBuiltins mskel fskel = mconcat
  [ if skelBuiltins
    then mconcat [skelName, " <- function_skeleton MODULE_SKEL \"", name, "\";\n"]
    else ""
  , "let ", specName, " = do {\n"
  , "  ", globalsPreBoilerplate skelBuiltins mskel
  , bodyBoilerplate skelBuiltins fskel skelName
  , "  ", globalsPostBoilerplate skelBuiltins mskel
  , "};\n"
  , overrideName, " <- llvm_verify MODULE \"", name, "\" ["
  , Text.intercalate ", " $ (<>"_override") <$> (Set.toList $ fskel ^. funSkelCalls)
  , "] false ", specName, " z3;\n"
  ]
  where
    name = fskel ^. funSkelName
    specName = name <> "_spec"
    skelName = name <> "_skel"
    overrideName = name <> "_override"

llvm_boilerplate :: FilePath -> ModuleSkeleton -> Bool -> TopLevel ()
llvm_boilerplate path mskel skelBuiltins = do
  let fskels = sortByDeps . Map.elems $ mskel ^. modSkelFunctions
  liftIO . withFile path WriteMode $ \h -> Text.IO.hPutStrLn h $ mconcat
    [ preludeBoilerplate skelBuiltins mskel
    , Text.unlines $ functionBoilerplate skelBuiltins mskel <$> fskels
    ]
