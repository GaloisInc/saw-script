{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWSupport.ConsoleSupport
Description : Backend support for console messages
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

This module contains infrastructure for use by _implementations_ of
the material in SAWSupport.Console.
-}

module SAWSupport.ConsoleSupport (
    Fatal(..),
    unimplementedMessage,
    errN, errP,
    warnN, warnP,
    noteN, noteP,
    errN', errP',
    warnN', warnP',
    noteN', noteP'
  )
  where

import Control.Exception (Exception)

import Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import Data.Text (Text)

import qualified SAWVersion.GitRev as GitRev

import SAWSupport.Position (IsPosition(..))
import qualified SAWSupport.Pretty as PPS


-- | Exception thrown by fatal errors.
--
-- The boolean argument is called @needTrace@; if it is true, a stack
-- trace was requested but has not been printed. This is temporary
-- scaffolding to work around things the `IO` instance of `SAWConsole`
-- can't do properly. See `SAWCentral.Value`.
--
-- The `Show` instance is required to be an `Exception`; however,
-- ideally, the `Show` text should never be seen. (It contains a real
-- message rather than being "" to avoid confusion in the event it
-- _does_ get printed at some point.)
--
-- This exception is thrown after an error message has already been
-- posted (or more than one) and no further printing is needed. To
-- accomplish this, it's caught at strategic points:
--    - in the REPL, it rolls back the operation that was in progress
--      and continues;
--    - when executing SAWScript straight from a file, it just exits;
--    - in the remote API it results in a failed action.
--
data Fatal = Fatal Bool
instance Show Fatal where show (Fatal _) = "Encountered an error."
instance Exception Fatal

-- | Type for the printer functions used below
type SayFunc m = Text -> m ()

-- | Fetch the version info from `GitRev`.
--   XXX: this is pasted from PanicSupport and should be shared.
{-# Noinline unimplementedRevision #-}
unimplementedRevision :: (Text, Text)
unimplementedRevision =
    if GitRev.foundGit then
        let hash = fromMaybe "(unknown revision)" GitRev.hash 
            branch = fromMaybe "(unknown branch)" GitRev.branch
        in
        (Text.pack hash, Text.pack branch)
    else
        ("(VCS-less build)", "(VCS-less build)")

-- | Generate the message to be used for "unimplemented", which is
--   intentionally like what `panic` produces.
unimplementedMessage :: Text -> Text -> [Text]
unimplementedMessage loc msg =
    let (revision, branch) = unimplementedRevision in
    [
        "You have encountered a limitation in SAW.",
        "If you need this functionality, please create an issue at",
        "https://github.com/GaloisInc/saw-script/issues",
        "",
        "%< ---------------------------------------------------",
        "Revision:  " <> revision,
        "Branch:    " <> branch,
        "Location:  " <> loc,
        "Message:   " <> msg,
        "%< ---------------------------------------------------"
    ]


-- | Backend for `errN` and `errDN` in `SAWConsole` in terms of a
--   function `say` for issuing a single message. Note: the
--   `SAWConsole` implementation is still responsible for bailing
--   out or recording that there was an error, respectively.
errN :: SayFunc m -> Text -> m ()
errN say msg =
    say $ "Error: " <> msg

-- | Backend for `errP`, `errDP`, `errX`, and `errDX` in `SAWConsole`
--   in terms of a function `say` for issuing a single message. Note:
--   the `SAWConsole` implementation is still responsible for bailing
--   out or recording that there was an error, as appropriate.
errP :: IsPosition pos => SayFunc m -> pos -> Text -> m ()
errP say pos msg = do
    let pos' = ppPosition pos
    say $ pos' <> ": Error: " <> msg

-- | Backend for `warnN` in `SAWConsole` in terms of a function `say`
--   for issuing a single message.
warnN :: SayFunc m -> Text -> m ()
warnN say msg =
    say $ "Warning: " <> msg

-- | Backend for `warnP` and `warnX` in `SAWConsole` in terms of a
--   function `say` for issuing a single message.
warnP :: IsPosition pos => SayFunc m -> pos -> Text -> m ()
warnP say pos msg = do
    let pos' = ppPosition pos
    say $ pos' <> ": Warning: " <> msg

-- | Backend for `noteN` in `SAWConsole` in terms of a function `say`
--   for issuing a single message.
noteN :: SayFunc m -> Text -> m ()
noteN say msg =
    -- XXX: it is probably good to insert "Notice:" as I'd planned...
    -- XXX: but not quite yet: it creates a huge test footprint.
    --say $ "Notice: " <> msg
    say msg

-- | Backend for `noteP` and `noteX` in `SAWConsole` in terms of a
--   function `say` for issuing a single message.
noteP :: IsPosition pos => SayFunc m -> pos -> Text -> m ()
noteP say pos msg = do
    let pos' = ppPosition pos
    say $ pos' <> ": Notice: " <> msg

-- | Backend for `errN'` and `errDN'` in `SAWConsole` in terms of a
--   function `say` for issuing a single message. Note: the
--   `SAWConsole` implementation is still responsible for bailing out
--   or recording that there was an error, respectively.
--
--   XXX: this will do to start with but ideally it should
--      - account for the width of the "Error: " prefix when rendering
--      - indent second and subsequent lines so long messages are visually
--        distinct
--
--   Alternatively it's possible that we should just have a SayFunc'
--   type that takes a Doc and leave all that to the implementation,
--   which might want to, for example, accumulate all errors as Doc
--   rather then Text.
--
errN' :: SayFunc m -> PPS.Opts -> PPS.Doc -> m ()
errN' say opts msg = errN say $ PPS.renderText opts msg

-- | Backend for `errP'`, `errDP'`, `errX'`, and `errDX'` in
--   `SAWConsole` in terms of a function `say` for issuing a single
--   message. Note: the `SAWConsole` implementation is still
--   responsible for bailing out or recording that there was an error,
--   as appropriate.
--
--   XXX: as in errN'
--
errP' :: IsPosition pos => SayFunc m -> PPS.Opts -> pos -> PPS.Doc -> m ()
errP' say opts pos msg = errP say pos $ PPS.renderText opts msg

-- | Backend for `warnN'` in `SAWConsole` in terms of a function `say`
--   for issuing a single message.
--
--   XXX: as in errN'
--
warnN' :: SayFunc m -> PPS.Opts -> PPS.Doc -> m ()
warnN' say opts msg = warnN say $ PPS.renderText opts msg

-- | Backend for `warnP'` and `warnX'` in `SAWConsole` in terms of a
--   function `say` for issuing a single message.
--
--   XXX: as in errN'
--
warnP' :: IsPosition pos => SayFunc m -> PPS.Opts -> pos -> PPS.Doc -> m ()
warnP' say opts pos msg = warnP say pos $ PPS.renderText opts msg

-- | Backend for `noteN` in `SAWConsole` in terms of a function `say`
--   for issuing a single message.
--
--   XXX: as in errN'
--
noteN' :: SayFunc m -> PPS.Opts -> PPS.Doc -> m ()
noteN' say opts msg = noteN say $ PPS.renderText opts msg

-- | Backend for `noteP` and `noteX` in `SAWConsole` in terms of a
--   function `say` for issuing a single message.
--
--   XXX: as in errN'
--
noteP' :: IsPosition pos => SayFunc m -> PPS.Opts -> pos -> PPS.Doc -> m ()
noteP' say opts pos msg = noteP say pos $ PPS.renderText opts msg
