{-# LANGUAGE OverloadedStrings #-}
{- |
Module      : SAWSupport.PureFail
Description : Failure interface for legacy "pure" code
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

This module contains an exception and a throw function for it that can
be used in existing pure code to fail without it being a panic.

Replaces uses of `error`; `error` is specifically undesirable for
several reasons.

New code should not use this interface.

Needless to say, actual pure code doesn't throw exceptions. Throwing
exceptions from "pure" code is also fundamentally unsafe: it creates
logic bombs that sit in unevaluated expressions and can move around,
and in particular, can move out from under catches that were intended
to intercept them.

We are not supposed to be doing it at all in SAW, except for panic
(which is itself a compromise) ... however, there's some code that
needs major reworking to be able to fail properly, and for the moment
removing uses of `error` from it is a higher priority.

Usage: @pureFail location message@ where

* @location@ (a `Text`) should say where in the source the call is.
  The recommended format is the module name and function, and for
  huge functions perhaps also a sub-function or sub-part.

  In principle this information could perhaps be extracted with
  `HasCallStack` (e.g. panics do that) but I'm not especially
  interested in reducing the friction associated with using this code.

* @message@ (a `Text`) should be whatever you'd pass to a proper failure
  function.

Does not return.

The exception constructor is intentionally not exported.

This module is pure fail and should be removed.
-}

module SAWSupport.PureFail (MadeOfFail, ppMadeOfFail, pureFail) where

import Control.Exception (Exception, throw)
import qualified Data.Text as Text
import Data.Text (Text)


data MadeOfFail = MadeOfFail Text Text

ppMadeOfFail :: MadeOfFail -> Text
ppMadeOfFail (MadeOfFail location message) =
    "pureFail call at " <> location <> ":\n" <> message

instance Show MadeOfFail where
    show mof = Text.unpack $ ppMadeOfFail mof

instance Exception MadeOfFail

pureFail :: Text -> Text -> a
pureFail location message =
    throw $ MadeOfFail location message
