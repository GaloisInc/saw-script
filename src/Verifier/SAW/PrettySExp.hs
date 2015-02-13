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

import           Data.Foldable (foldl', foldr)
import qualified Data.Map as Map
import           Data.Map (Map)
import           Data.Maybe
import qualified Data.Set as Set
import           Data.Set (Set)
import           Prelude hiding (foldr)
import           Text.PrettyPrint.Leijen

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

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
  where
    (_, doc)       = ppN [] 0 Set.empty tm
    cutoffDepth    = ppMinSharingDepth cfg
    maxDepth       = ppMaxDepth cfg
    nodeInfos      = collectNodeInfo tm Map.empty

    ppN :: [Doc] -> Int -> Visited -> SharedTerm s -> (Visited, Doc)
    ppN lcls cdepth sofar (STApp i tf)
      | maybe False (cdepth >=) maxDepth  = (sofar, text "...")
      | maybe True (depth <=) cutoffDepth = (sofar,  doline empty)
      | i `Set.member` sofar              = (sofar,  nid)
      | cnt > 1                           = (sofar', doline nref)
      | True                              = (sofar', doline empty)
        where
          si                = show i
          nid               = text $ 'n' : si
          nref              = braces $ text $ si
          --(depth, cnt)      = fromMaybe (0, 1) $ Map.lookup i nodeInfos
          Just (depth, cnt) = Map.lookup i nodeInfos
          doline r =
            case tf of
              Constant n _ _ -> text (show n)
              Lambda _ _ _ -> parens (call opText r argDs)
              _ -> call opText r argDs
          call o r [] = r <> o
          call o r as = nest 2 $ parens (r <> o <+> sep as)
          (sofar', reverse -> argDs) =
            foldl' nextArg (i `Set.insert` sofar, []) tf
          lcls' =
            case tf of
              Lambda n _ _ -> text n : lcls
              _ -> lcls
          nextArg (s, ds) a =
            let (s', d) = ppN lcls' (cdepth + 1) s a in (s', d : ds)
          opText =
            case tf of
              FTermF (GlobalDef n) -> text (show n)
              FTermF (TupleValue _) -> text "tuple"
              FTermF (RecordValue _) -> text "record"
              FTermF (TupleType _) -> text "Tuple"
              FTermF (RecordType _) -> text "Record"
              FTermF (TupleSelector _ idx) ->
                text "proj" <> (braces (int idx))
              FTermF (RecordSelector _ fld) ->
                text "proj" <> (braces (text fld))
              FTermF (CtorApp n _) -> text (show n)
              FTermF (DataTypeApp n _) -> text (show n)
              FTermF (Sort s) -> text (show s)
              FTermF (NatLit n) -> text (show n)
              FTermF (ArrayValue _ _) -> text "array"
              FTermF (FloatLit f) -> text (show f)
              FTermF (DoubleLit f) -> text (show f)
              FTermF (StringLit s) -> text (show s)
              FTermF (ExtCns ec) ->
                text "?" <> text (show (ecVarIndex ec)) <>
                colon <> text (ecName ec)
              App _ _ -> empty
              Lambda n _ _ -> backslash <> text n
              Pi n _ _ -> backslash <> text n
              Let _ _  -> text "let[TODO]"
              LocalVar n -> lcls !! n
              Constant n _ _ -> text (show n)
    ppN _ _ sofar tm'@(Unshared _) = (sofar, scPrettyTermDoc tm')

-- | Collect the occurrence count and depth of nodes
collectNodeInfo :: SharedTerm s -> NodeInfo -> NodeInfo
collectNodeInfo (STApp i tf) ni =
  case Map.lookup i ni of
    Just _  -> Map.adjust bumpCnt i ni
    Nothing -> d `seq` Map.insert i (d, 1) ni'
  where
    bumpCnt (depth, count) =
      let count' = count+1 in count' `seq` (depth, count')
    ni' = foldr collectNodeInfo ni tf
    d = 1 + foldl' (\cd st -> max cd (depthOf ni' st)) 0 tf
collectNodeInfo (Unshared _) ni = ni

-- | Compute the depth of a given node; note that this is a mere look-up from
-- the map, no computation is actually done
depthOf :: NodeInfo -> SharedTerm s -> Int
depthOf ni (STApp i _)
  | Just (d, _) <- i `Map.lookup` ni = d
  | True                           =
    error $ "Cannot locate depth info for node: " ++ show i
depthOf _ _ = 0

