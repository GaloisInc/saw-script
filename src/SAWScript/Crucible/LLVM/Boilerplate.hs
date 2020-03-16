{-# OPTIONS -Wall -Werror #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAWScript.Crucible.LLVM.Boilerplate
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

import Data.Parameterized.Some

import SAWScript.Value

import SAWScript.Crucible.LLVM.MethodSpecIR

import SAWScript.Crucible.LLVM.Skeleton

sortByDeps :: [FunctionSkeleton] -> [FunctionSkeleton]
sortByDeps skels = reverse $ (\(f, _, _) -> f) . fromVertex <$> Graph.topSort g
  where
    (g, fromVertex, _) = Graph.graphFromEdges $ adjacency <$> skels
    adjacency :: FunctionSkeleton -> (FunctionSkeleton, Text, [Text])
    adjacency s = (s, s ^. funSkelName, Set.toList $ s ^. funSkelCalls)

preBoilerplate :: ModuleSkeleton -> Text
preBoilerplate _mskel = "enable_experimental;\nMODULE_SKEL <- module_skeleton MODULE;\n"

functionBoilerplate :: FunctionSkeleton -> Text
functionBoilerplate fskel = mconcat
  [ skelName, " <- function_skeleton MODULE_SKEL \"", name, "\";\n"
  , "let ", specName, " = do {\n"
  , "  skeleton_globals_pre MODULE_SKEL;\n"
  , "  prestate <- skeleton_prestate ", skelName, ";\n"
  , "  skeleton_exec prestate;\n"
  , "  poststate <- skeleton_poststate ", skelName,  " prestate;\n"
  , "  skeleton_globals_post MODULE_SKEL;\n"
  , "};\n"
  , overrideName, " <- crucible_llvm_verify MODULE \"", name, "\" ["
  , Text.intercalate ", " $ (<>"_override") <$> (Set.toList $ fskel ^. funSkelCalls)
  , "] false ", specName, " z3;\n"
  ]
  where
    name = fskel ^. funSkelName
    specName = name <> "_spec"
    skelName = name <> "_skel"
    overrideName = name <> "_override"

llvm_boilerplate :: FilePath -> Some LLVMModule -> TopLevel ()
llvm_boilerplate path (Some (modAST -> m)) = do
  mskel <- liftIO $ moduleSkeleton m
  let fskels = sortByDeps . Map.elems $ mskel ^. modSkelFunctions
  liftIO . withFile path WriteMode $ \h -> Text.IO.hPutStrLn h $ mconcat
    [ preBoilerplate mskel
    , Text.unlines $ functionBoilerplate <$> fskels
    ]
  pure ()
