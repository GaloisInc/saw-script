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

import Control.Monad.IO.Class
import Control.Lens

import Data.Text (Text)
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

llvm_boilerplate :: FilePath -> Some LLVMModule -> TopLevel ()
llvm_boilerplate _path (Some (modAST -> m)) = do
  fskels <- liftIO $ view modSkelFunctions <$> moduleSkeleton m
  let _fnames = sortByDeps $ Map.elems fskels
  pure ()
