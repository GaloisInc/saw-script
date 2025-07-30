{- |
Module      : SAWCentral.Trace
Description : Stack traces for SAW-Script interpreter.
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional
-}
{-# LANGUAGE OverloadedStrings #-}

-- This module should be used as follows:
--    import SAWCentral.Trace (Trace)
--    import qualified SAWCentral.Trace as Trace

module SAWCentral.Trace (
    Trace(),
    empty,
    push,
    pop,
    ppTrace
 ) where

import Data.Text (Text)
import qualified Data.Text as Text

import SAWCentral.Panic (panic)
import SAWCentral.Position (Pos)

-- A stack trace is a list of call sites: positions with the name of
-- (and other information about) the function being called.
--
-- As it's being collected, the trace has that form. For printing, we
-- shift the positions by one so we report each call site as a
-- position in the function that called it. This produces stack traces
-- consistent with user expectations. See `prepareTrace` below.
--
-- The plumbing in the interpreter necessary to collect this
-- information is not entirely trivial, thanks to the need to handle
-- monadic actions, and particularly monadic actions passed as
-- callbacks to builtins, some of which may not actually involve any
-- direct evaluation in the interpreter, and is described elsewhere.
-- (See Value.hs.)
--
-- The interaction of Haskell lazy evaluation with the interpreter's
-- execution semantics is also complicated and difficult to reason
-- about, which does not help.
--
-- In order to avoid a cyclic dependency with Value.hs we handle only
-- Text in the stack trace itself; the printing happens when trace
-- frames are created. Lazy evaluation should make this not ruinously
-- expensive.

-- | Call information for a stack trace.
--
--   This bundles a function name and arguments and whatever else we
--   might want to record for examination (e.g. values of locals) in a
--   single type so the rest of the trace logic doesn't have to think
--   directly about what's in it.
--
--   Note that to avoid horrible cycles in the module dependency graph,
--   we can't have Values here, so we need to print arguments, values
--   of locals, etc. to text at the point we generate the frame. Lazy
--   evaluation should prevent that from being ruinously expensive.
--
--   (FUTURE: it might make sense for each frame to be a prettyprinter
--   document rather than Text.)
data TraceFunc = TraceFunc Text

-- | Entry in a stack trace.
--
-- In order to have a correct and coherent (and useful) stack trace,
-- we want the following information for each call that is currently
-- in progress:
--    - the call site as a source position
--    - the name and all other info (a TraceFunc) describing the
--      function/action/builtin/other object being called
--
-- This should take effect at the point when the call is actually
-- executed, that is, we begin executing in the function, and should
-- be cleared off again when that's done.
--
-- We don't need the source position of the called object, because the
-- next position in the stack should be in that function. (Tail call
-- optimization would break that expectation, but we don't do that.)
data TraceFrame = TraceFrame Pos TraceFunc

-- A stack trace is a list of frames, with the most recent frame at
-- the head of the list.
data Trace = Trace [TraceFrame]

-- | The starting trace.
empty :: Trace
empty = Trace []


-- | Push a fresh frame on a trace.
push :: Pos -> Text -> Trace -> Trace
push callpos func (Trace frames) =
  let func' = TraceFunc func
      frame = TraceFrame callpos func'
  in
  Trace (frame : frames)

-- | Pop a frame off a trace.
pop :: Trace -> Trace
pop (Trace frames) = case frames of
  [] -> panic "Trace.pop" ["Popping empty stack"]
  _ : frames' -> Trace frames'


-- | Print a TraceFunc. Simple for now, but we're going to want more
--   later.
ppTraceFunc :: TraceFunc -> Text
ppTraceFunc (TraceFunc name) = name

-- | Prepare a trace for printing.
--
--   The trace is a list of call sites, and that's not the way we want
--   to print it.
--
--   Suppose we had this code:
--
--      foo.saw:1: let f1 z = ...;
--      foo.saw:2: let f2 y = f1 (y + 1);
--      foo.saw:3: let f3 x = f2 (x + 1);
--      foo.saw.4: return (f3 0);
--
--   and we crash and produce a trace inside f1. (Assume none of this
--   is monadic because that just introduces additional complications
--   that aren't relevant here.)
--
--   The current position will be foo.saw:1, and the trace will contain:
--      foo.saw:2 called f1
--      foo.saw:3 called f2
--      foo.saw:4 called f3
--
--   but what we want to print is
--      foo.saw:1 in f1 (z = 2)
--      foo.saw:2 in f2 (y = 1)
--      foo.saw:3 in f3 (x = 0)
--      foo.saw:4 at top level
--
--   that is, we want to insert the current position and shift the
--   rest of the positions up by one. (Failure to do this coherently
--   was one of the root causes of #2108.)
--
-- Do this shift, and inject Nothing for "at top level".
prepareTrace :: Pos -> [TraceFrame] -> [(Pos, Maybe TraceFunc)]
prepareTrace curpos tfs = case tfs of
    [] -> [(curpos, Nothing)]
    (TraceFrame nextpos func) : tfs' ->
        (curpos, Just func) : prepareTrace nextpos tfs'

-- | Pretty-print a trace. This also takes the current position
--   to print at the bottom.
--
--   We don't reverse the frame, so the most recent call comes out at
--   the top, like gdb and most debuggers. Shift the current position
--   into the trace as described above before printing.
--
--   Takes the current position as well as the trace.  Note that the
--   "current position" should be read as "what's currently
--   executing", which in most cases will be PosInsideBuiltin. Don't
--   use the interpreter's last execution position; that will result
--   in a confusingly messed-up trace.
--
ppTrace :: Trace -> Pos -> Text
ppTrace (Trace frames) curpos =
  let frames' =
        let ppEntry (pos, mfunc) =
              let pos' = Text.pack (show pos)
                  mfunc' = case mfunc of
                    Nothing -> " (at top level)"
                    Just func -> " in " <> ppTraceFunc func
              in
              "   " <> pos' <> mfunc'
        in
        map ppEntry $ prepareTrace curpos frames
  in
  Text.unlines frames'
