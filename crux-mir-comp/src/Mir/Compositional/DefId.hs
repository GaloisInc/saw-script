{-# LANGUAGE OverloadedStrings #-}
module Mir.Compositional.DefId
  ( hasInstPrefix
  ) where

import Data.List.Extra (unsnoc)
import qualified Data.Text as Text
import Data.Text (Text)

import Mir.DefId

-- | Check if @edid@ has the same path as @pfxInit@, plus a final path
-- component that begins with the name @_inst@.
hasInstPrefix :: [Text] -> ExplodedDefId -> Bool
hasInstPrefix pfxInit edid =
  case unsnoc edid of
    Nothing -> False
    Just (edidInit, edidLast) ->
      pfxInit == edidInit &&
      "_inst" `Text.isPrefixOf` edidLast
