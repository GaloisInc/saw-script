{-# LANGUAGE PatternGuards #-}
{- |
Module      : Verifier.SAW.PrettySExp
Copyright   : Galois, Inc. 2015
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.PrettySExp
  ( PPConfig(..)
  , defaultPPConfig
  , ppSharedTermSExp
  , ppSharedTermSExpWith
  ) where

import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)
import           Text.PrettyPrint.Leijen hiding ((<$>))

import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm

data PPConfig = PPConfig {
          ppShowConstTypes  :: !Bool         -- whether we should display the types of constant literals
        , ppMinSharingDepth :: !(Maybe Int)  -- anything less than this depth will always be shown, 0 will give maximum sharing. Nothing: show the full tree.
        , ppLineLength      :: !Int          -- line length for the printed page
        , ppMaxDepth        :: !(Maybe Int)  -- maximum depth of tree to show (Nothing for no limit)
        }

defaultPPConfig :: PPConfig
defaultPPConfig = PPConfig {
          ppShowConstTypes  = False
        , ppMinSharingDepth = Just 0
        , ppLineLength      = 80
        , ppMaxDepth        = Nothing
        }

type Visited  = Set Int
type NodeInfo = Map Int (Int, Int)  -- (depth, #of occs)

ppSharedTermSExp :: SharedTerm s -> Doc
ppSharedTermSExp = ppSharedTermSExpWith defaultPPConfig

ppSharedTermSExpWith :: PPConfig -> SharedTerm s -> Doc
ppSharedTermSExpWith cfg tm = doc
  where (_, doc)       = ppN 0 Set.empty tm
        cutoffDepth    = ppMinSharingDepth cfg
        maxDepth       = ppMaxDepth cfg
        nodeInfos      = collectNodeInfo tm Map.empty

        ppN :: Int -> Visited -> SharedTerm s -> (Visited, Doc)
        ppN cdepth sofar tm'@(STApp i _) =
          case tm' of
            (decomposeApp -> (opText, args))
              | maybe False (cdepth >=) maxDepth  -> (sofar, text "...")
              | maybe True (depth <=) cutoffDepth -> (sofar,  doline empty)
              | i `Set.member` sofar              -> (sofar,  nid)
              | cnt > 1                           -> (sofar', doline nref)
              | True                              -> (sofar', doline empty)
              where
                si                = show i
                nid               = text $ 'n' : si
                nref              = braces $ text $ si
                Just (depth, cnt) = Map.lookup i nodeInfos
                doline r = call opText r argDs
                call o r [] = o <> r
                call o r as = parens $ fillSep (o <> r : as)
                (sofar', reverse -> argDs) =
                  foldl nextArg (i `Set.insert` sofar, []) args
                nextArg (s, ds) a =
                  let (s', d) = ppN (cdepth + 1) s a in (s', d : ds)
        ppN _ sofar tm'@(Unshared _) = (sofar, scPrettyTermDoc tm')

-- | Collect the occurrence count and depth of nodes
collectNodeInfo :: SharedTerm s -> NodeInfo -> NodeInfo
collectNodeInfo tm@(STApp i _) ni =
  case tm of
    (decomposeApp -> (_, args)) ->
      case Map.lookup i ni of
        Just _  -> Map.adjust bumpCnt i ni
        Nothing -> d `seq` Map.insert i (d, 1) ni'
      where
        bumpCnt (depth, count) =
          let count' = count+1 in count' `seq` (depth, count')
        ni' = foldr collectNodeInfo ni args
        d   = 1 + maximum (0 : map (depthOf ni') args)
collectNodeInfo (Unshared _) ni = ni

-- | Compute the depth of a given node; note that this is a mere look-up from
-- the map, no computation is actually done
depthOf :: NodeInfo -> SharedTerm s -> Int
depthOf ni (STApp i _)
  | Just (d, _) <- i `Map.lookup` ni = d
  | True                           =
    error $ "Cannot locate depth info for node: " ++ show i
depthOf _ _ = 0

-- | Return the name and arguments of of an application-like term.
decomposeApp :: SharedTerm s -> (Doc, [SharedTerm s])
decomposeApp (asApplyAll -> (f, [])) =
  case f of
    (asLambda -> Just (n, ty, body)) ->
      (backslash <> parens (text n <> text "::" <> scPrettyTermDoc ty) <+>
       text "->", [body])
    _ -> (scPrettyTermDoc f, [])
decomposeApp (asApplyAll -> (f, as)) = (scPrettyTermDoc f, as)
