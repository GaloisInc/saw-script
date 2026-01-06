{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWSupport.Console
Description : Console messages and error printing infrastructure
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

This module contains the infrastructure for printing messages to the
console from inside SAW.

Panic messages should use `panic`. Each component of SAW has its own
`Panic` module that defines the appropriate `panic` function for code
in that component.

All other messages, apart from directly user-facing UI logic, should
be printed through this interface. If it proves inadequate, it should
be strengthened. (Just printing to standard output or standard error
will not do the right thing with the remote API. That is ok for
temporary debug prints, but not for committed code.)

Note that the SAWScript interpreter is not user-facing UI code; only
the REPL code qualifies.

However, the terminal-based interactive logic in the AutoMatch code
will be treated as user-facing UI code; for now at least it will
continue to do its own thing and not go through this interface.

Note that the `SAWConsole` instance for `IO` is meant as temporary
scaffolding and expected to go away in the long run. `IO` by itself
doesn't provide adequate infrastructure to collect messages, only to
print them, and the latter isn't good enough for the remote API.

This module is intended to be imported unqualified.
-}

module SAWSupport.Console (
    SAWConsole(..),
  )
  where

import Control.Exception (throwIO)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.IO as TextIO

import SAWSupport.PanicSupport
import qualified SAWSupport.Pretty as PPS
import SAWSupport.Position
import qualified SAWSupport.ConsoleSupport as Supp
import SAWSupport.ConsoleSupport (Fatal(..))

------------------------------------------------------------
-- SAWConsole class

-- | Monad class for SAW message printing.
--
--   There are three basic kinds of diagnostic messages:
--      - @err@ prints an error;
--      - @warn@ prints a warning;
--      - @note@ prints a notice.
--
--   These are then further qualified as follows:
--      - @N@ prints without any position;
--      - @P@ prints with an explicit position;
--      - @X@ prints with the current execution position.
--      - The primed versions generate a prettyprinter doc rather than `Text`.
--
--   The @D@ variants of the error functions defer exit: they record
--   that a fatal error occurred but continue execution. This is
--   desirable behavior in a number of contexts (e.g. typechecking).
--
--   Use `checkFail` at suitable points to bail out if an error has
--   previously been recorded.
--
--   Use `unimplemented` (rather than either panic or @err@) to report
--   unimplemented features / missing code paths. We haven't been able
--   to decide if unimplemented features should be panics or errors,
--   and I think the reason is that they have properties of both:
--      - they are a problem in SAW, not something the user did, which
--        is like a panic;
--      - it typically does not make sense to continue executing with
--        a dummy value, which is like a panic;
--      - they do not represent a corrupted internal state and there's
--        no need to shut down, which is like an error.
--
--   The arguments of `unimplemented` are like `panic`. The first is
--   the "location", generally the function in which something's
--   missing, and the second is the message. The message is restricted
--   to a single line -- that should be all that is needed to name
--   what's missing, and there should be no need to print anything
--   else. The offending location in the SAW source is printed via
--   HasCallStack.
--
--   The @progress@ functions are for progress reporting. The idea is
--   that the actual printing will be throttled by the infrastructure,
--   so nothing happens until something's already taken a while. This
--   will not work as intended in the `IO` instance, so widespread
--   deployment needs to wait until we can get rid of it.
--
--   FUTURE: there is also eventually intended to be infrastructure in
--   here for printing execution traces, and for dumping internal
--   representations at key points.
--
--   Note that while we could provide workable default implementations
--   for most of these functions, this would require some additional
--   functions to use as building blocks, and we don't really want to
--   expose those functions.
--
class (Monad m) => SAWConsole m where
    errN :: Text -> m a
    errP :: IsPosition pos => pos -> Text -> m a
    errX :: Text -> m a

    errDN :: Text -> m ()
    errDP :: IsPosition pos => pos -> Text -> m ()
    errDX :: Text -> m ()

    warnN :: Text -> m ()
    warnP :: IsPosition pos => pos -> Text -> m ()
    warnX :: Text -> m ()

    noteN :: Text -> m ()
    noteP :: IsPosition pos => pos -> Text -> m ()
    noteX :: Text -> m ()

    errN' :: PPS.Doc -> m a
    errP' :: IsPosition pos => pos -> PPS.Doc -> m a
    errX' :: PPS.Doc -> m a

    errDN' :: PPS.Doc -> m ()
    errDP' :: IsPosition pos => pos -> PPS.Doc -> m ()
    errDX' :: PPS.Doc -> m ()

    warnN' :: PPS.Doc -> m ()
    warnP' :: IsPosition pos => pos -> PPS.Doc -> m ()
    warnX' :: PPS.Doc -> m ()

    noteN' :: PPS.Doc -> m ()
    noteP' :: IsPosition pos => pos -> PPS.Doc -> m ()
    noteX' :: PPS.Doc -> m ()

    checkFail :: m ()

    unimplemented :: HasCallStack => Text -> Text -> m a

    progressStart :: Text -> m ()
    progressStep :: Text -> m ()
    progressAmount :: Int -> Maybe Int -> m ()
    progressInterim :: Text -> m ()
    progressInterim' :: PPS.Doc -> m ()
    progressEnd :: m ()


------------------------------------------------------------
-- IO instanace

-- | Internal function for the `IO` instance.
say :: Text -> IO ()
say msg = TextIO.putStrLn msg

-- | Dummy position used by the `IO` instance.
newtype DummyPos = DummyPos ()
instance IsPosition DummyPos where
    ppPosition (DummyPos ()) = "Unknown position"
    prettyPosition (DummyPos ()) = "Unknown position"
dummyPos :: DummyPos
dummyPos = DummyPos ()

-- | `SAWConsole` instance for `IO`. This does not (and cannot) handle
--   deferred exit correctly, or the progress interface either, and is
--   expected to be removed in the long run.
--
--   Also note that there are, properly, prettyprinter options that
--   should get passed to `render`, which `IO` doesn't and can't
--   track. And it doesn't know what the current execution position
--   means.
instance SAWConsole IO where
    errN msg = Supp.errN say msg >> throwIO (Fatal False)
    errP pos msg = Supp.errP say pos msg >> throwIO (Fatal False)
    -- XXX: for now throw a Fatal with True and, provided we're
    -- actually inside TopLevel somewhere, the exception glop in
    -- Value.hs will see it and print a stack trace. (If we aren't
    -- actually inside TopLevel, it won't and there'll be no stack
    -- trace.) This is the best we can do if all we have is `IO`. All
    -- of this should be removed: we want all error calls to happen in
    -- a monad that has access to state, and then the stack trace will
    -- be available to print before throwing as intended.
    --
    errX msg = Supp.errN say msg >> throwIO (Fatal True)

    -- XXX: These can't be handled correctly in IO; they need state.
    errDN msg = Supp.errN say msg >> throwIO (Fatal False)
    errDP pos msg = Supp.errP say pos msg >> throwIO (Fatal False)
    -- XXX: same as above
    errDX msg = Supp.errN say msg >> throwIO (Fatal True)

    warnN msg = Supp.warnN say msg
    warnP pos msg = Supp.warnP say pos msg
    warnX msg = Supp.warnP say dummyPos msg

    noteN msg = Supp.noteN say msg
    noteP pos msg = Supp.noteP say pos msg
    noteX msg = Supp.noteP say dummyPos msg

    errN' msg = Supp.errN' say PPS.defaultOpts msg >> throwIO (Fatal False)
    errP' pos msg = Supp.errP' say PPS.defaultOpts pos msg >> throwIO (Fatal False)
    -- XXX: same as above
    errX' msg = Supp.errN' say PPS.defaultOpts msg >> throwIO (Fatal True)

    -- XXX: These can't be handled correctly in IO; they need state.
    errDN' msg = Supp.errN' say PPS.defaultOpts msg >> throwIO (Fatal False)
    errDP' pos msg = Supp.errP' say PPS.defaultOpts pos msg >> throwIO (Fatal False)
    -- XXX: same as above
    errDX' msg = Supp.errN' say PPS.defaultOpts msg >> throwIO (Fatal True)

    warnN' msg = Supp.warnN' say PPS.defaultOpts msg
    warnP' pos msg = Supp.warnP' say PPS.defaultOpts pos msg
    warnX' msg = Supp.warnP' say PPS.defaultOpts dummyPos msg

    noteN' msg = Supp.noteN' say PPS.defaultOpts msg
    noteP' pos msg = Supp.noteP' say PPS.defaultOpts pos msg
    noteX' msg = Supp.noteP' say PPS.defaultOpts dummyPos msg

    checkFail = pure ()

    unimplemented loc msg = do
        let msglines = Supp.unimplementedMessage loc msg
        mapM_ say msglines
        throwIO (Fatal False)

    -- XXX: this implementation is a very weak placeholder
    progressStart phase = say phase
    progressStep phase = say phase
    progressAmount n mm = do
        let n' = Text.pack $ show n
            m' = case mm of
                Nothing -> "unknown"
                Just m -> Text.pack $ show m
        TextIO.putStr $ "(" <> n' <> " of " <> m' <> ")\r"
    progressInterim msg = do
        TextIO.putStr "\n"
        say msg
    progressInterim' msg = do
        TextIO.putStr "\n"
        say $ PPS.renderText PPS.defaultOpts msg
    progressEnd =
        TextIO.putStr "\n"
