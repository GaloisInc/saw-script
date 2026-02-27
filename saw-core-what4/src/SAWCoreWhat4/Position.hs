{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans  #-}

{- |
Module      : SAWCoreWhat4.Position
Description : SAW glue for What4 source positions
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}

module SAWCoreWhat4.Position () where

import qualified Prettyprinter as PP
import Prettyprinter ((<+>))

import qualified What4.ProgramLoc as W4

import SAWSupport.Position

-- | SAW IsPosition instance for What4 Position.
--
--   What4 provides a `Pretty` instance for its `Position` type,
--   so we can just use that.
instance IsPosition W4.Position where
    prettyPosition pos = PP.pretty pos

-- | SAW IsPosition instance for What4 ProgramLoc.
--
--   What4 does _not_ provide a `Pretty` instance for `ProgramLoc`, so
--   we need to roll one. (Instead, it provides a derived `Show`
--   instance. Blegh.)
instance IsPosition W4.ProgramLoc where
    prettyPosition pl =
        let pos = W4.plSourceLoc pl
            func = W4.plFunction pl
        in
        let pos' = prettyPosition pos
            func' =
                -- W4.FunctionName is a wrapper around Text, but does
                -- provide a Pretty instance. It isn't clear if we'll
                -- ever get empty function names, but just in case
                -- let's not print nonsense if we do.
                if func == "" then
                    PP.emptyDoc
                else
                    " in" <+> PP.pretty func
        in
        pos' <> func'
