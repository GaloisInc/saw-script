{-# LANGUAGE Safe #-}
-- |
-- Module      : SAWSupport.PanicSupport
-- License     : BSD3
-- Maintainer  : saw@galois.com
-- Stability   : provisional

-- Wrapper around the panic library.
--
-- Each library in SAW defines its own Panic module so that panics in
-- it come out with the "component name" set to the library involved.
--
-- This module contains the shared plumbing to make those modules as
-- small as reasonably possible.
--
-- Panic is for internal/programming errors, not user-facing errors.
-- Ideally users should never see panics, and if they do see a panic
-- they should file a bug report about it.
--
-- Note: any uses of the Haskell "error" function should be converted
-- to use panic instead, provided they are actually panic conditions.
-- Any others should be updated to use proper error handling channels.
--
-- Panic is immediately fatal and may be used in pure ("pure") code
-- when needed.
--
-- The exposed panic interface in SAW takes two arguments:
--    - the "location of the problem" (a single string)
--    - the "problem description" (a list of strings, one per line)
--
-- The infrastructure then adds the "component name" as well as the
-- Haskell module and line (via HasCallStack) and the git commit
-- information, and generates a print of the following form:
--
--    [18:30:30.500] You have encountered a bug in <component name>'s implementation.
--    *** Please create an issue at https://github.com/GaloisInc/saw-script/issues
--
--    %< --------------------------------------------------- 
--      Revision:  abcd1234abcd1234cdef5678cdef5678abcd1234
--      Branch:    master (uncommited files present)
--      Location:  <location of the problem>
--      Message:   <problem description>
--                 <problem description>
--                 <problem description>
--    CallStack (from HasCallStack):
--      panic, called at src/SAWScript/Panic.hs:20:9 in saw-script-1.3-inplace:SAWScript.Panic
--      panic, called at src/SAWCentral/Proof.hs:300:15 in saw-script-1.3-inplace:SAWCentral.Proof
--    %< ---------------------------------------------------
--
-- The arguments to each panic should be written so they make sense in
-- this context.
--
-- Also note that because the description lines are indented after
-- being unlines'd, they should not contain their own newlines.
--
-- It is reasonable to use the function name as the "location of the
-- problem"; however, it's often more helpful to use a short string
-- that describes what SAW was trying to do when things came unstuck.
--
-- Then, the rest of the message should indicate what happened and
-- also include the values of relevant variables. What gets printed
-- here may be all you ever get to try to figure out what broke.
--
-- It's important that the combination of the "location" string and
-- the beginning of the rest of the message should be unique.
--
-- Rationale:
--
-- In an ideal world no user would ever see a panic. However, the
-- reality of software is that sooner or later someone will see every
-- panic in the system. Furthermore, chances are that person will
-- probably be a downstream user, in the field. This will be someone
-- who has little or no familiarity with SAW's internals -- given the
-- nature of SAW they will probably not be a completely clueless end
-- user, but even so internal minutiae won't be helpful.
--
-- Therefore, that user (not the SAW developer) is the primary
-- audience for every panic message. Panic messages should tell the
-- user enough about what happened that they can try to rearrange
-- their stuff to avoid triggering it. They should also tell the user
-- enough that they have a reasonable chance at being able to cut down
-- whatever they're working on to something they can send upstream
-- with a bug report.
--
-- The SAW developer is the _secondary_ audience for every panic
-- message, but in general only via the bug reports that come from the
-- primary audience.
--
-- In most cases the function name where something blew up will not
-- mean much to the user seeing the panic. Hence the recommendation
-- for a short descriptive string instead.
--
-- The function name is also readily found via the module name, line
-- number, and message text. (The reason the message text needs to be
-- unique is that if it's not, it's easy to end up looking at the
-- wrong instance, despite line numbers, and then things become far
-- more confusing.) It's therefore not particularly important to
-- include it in the message if there's a better alternative.
--
-- Because panics in general get reported, not found directly by
-- developers, and are often hard to reproduce locally or on demand,
-- it's routinely necessary to diagnose and fix problems entirely or
-- almost entirely by analysis of the panic message and the code
-- around it. For this reason panics should include as much relevant
-- information as possible without flooding the recipient.

-- re-export HasCallStack for use by the per-library modules
module SAWSupport.PanicSupport (Panic.HasCallStack, doPanic) where

import Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Panic as Panic

import qualified SAWVersion.GitRev as GitRev

-- | Hook for the panic library's use. The upstream library uses types
--   as hooks to attach the panic metadata. We use a simpler scheme
--   where the metadata is implicit in which panic function you call
--   (at the cost of having a separate panic module in each library)
--   so we only need one of these.
--
--   The argument of the constructor is the component name to use
--   with the panic message.
newtype SAWPanic = SAWPanic Text

-- | Trigger a panic. This is called by each library's panic function;
--   the first argument should be the component name, and the second
--   and third should be the "location" and "description" to pass
--   through to the upstream panic function.
doPanic :: Panic.HasCallStack => Text -> Text -> [Text] -> a
doPanic component loc descs =
  Panic.panic (SAWPanic component) loc' descs'
  where
     loc' = Text.unpack loc
     descs' = map Text.unpack descs

instance Panic.PanicComponent SAWPanic where
  panicComponentName (SAWPanic component) = Text.unpack component
  panicComponentIssues _ = "https://github.com/GaloisInc/saw-script/issues"

  {-# Noinline panicComponentRevision #-}
  panicComponentRevision _ =
    if GitRev.foundGit then
        let hash = fromMaybe "(unknown revision)" GitRev.hash 
            branch = fromMaybe "(unknown branch)" GitRev.branch
        in
        (hash, branch)
    else
        ("(VCS-less build)", "(VCS-less build)")
