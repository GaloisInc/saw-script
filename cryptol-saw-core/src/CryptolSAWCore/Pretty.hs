{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : CryptolSAWCore.Pretty
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental

Wrapper around Cryptol's prettyprinter.

Cryptol and SAW have, regrettably, entirely incompatible
prettyprinters. They both use the @Prettyprinter@ package, but there
are at least two points of basic incompatibility: Cryptol wraps the
package in a monad to avoid needing to carry the printing options
around, which SAW doesn't; then even if it didn't do that, it also
uses a different set of annotations so the type of `Doc ann` wouldn't
match.

There's also an impedance mismatch because SAW's convention is (now)
to use `pretty` to produce docs and `pp` to produce strings, and
Cryptol's convention is for some reason the other way around.

This module wraps Cryptol's prettyprinter so that other code doesn't
have to worry about these complications.

It is possible that in the long run we should change SAW's
prettyprinter so it also carries its print options around monadically.
It is definitely a headache to pass that value around all over the
place; in Cryptol's model you only need the options at render time and
can interrogate them freely when actually printing.

For the time being we just render all Cryptol `Doc`s to text before
returning them to SAW's prettyprinter. In the FUTURE we should
probably possible to open Cryptol's monadic doc abstraction and pass
in the printing options to get a plain `Doc` back, and then by
converting annotations (currently Cryptol's are not representable in
SAW's, but that's easily fixed) we can return real `Doc`s out. This
is definitely better for having the output come out well.

This module is intended to be imported qualified, like this:
```
import qualified CryptolSAWCore.Pretty as CryPP
```

-}

module CryptolSAWCore.Pretty (
    pretty, pp,

    prettyWithNames,
    addTNames,

    -- These are used with ppWithNames; no need to wrap them
    Cry.NameMap, Cry.emptyNameMap,

    -- This is, for now anyway, needed in saw-server.
    Cry.defaultPPOpts
  ) where

import qualified Data.Text as Text
import Data.Text (Text)

import qualified Prettyprinter as PP

-- Don't call the upstream module @CryPP@ as that's what we call ourselves
-- everywhere else.
import qualified Cryptol.Utils.PP as Cry
import qualified Cryptol.TypeCheck.PP as Cry

-- Need this for `addTNames`
import qualified Cryptol.TypeCheck.Type as CryType (TParam, addTNames)


-- | Pretty-print a Cryptol value to a `Doc`.
--   As per the notes above, converts to `Text` first.
--
--   For now, print to a generic doc because we can; when/if we start
--   passing through Cryptol's docs and converting them to SAW docs
--   we'll need to change this. Postpone it for the moment because it
--   has a fairly large downstream footprint.
pretty :: (Cry.PP a) => a -> PP.Doc ann
pretty x = PP.pretty $ pp x

-- | Pretty-print a Cryptol value to `Text`.
pp :: (Cry.PP a) => a -> Text
pp x =
    -- Note: Cry.pp produces a Cryptol `Doc`, not text.
    let doc = Cry.pp x in
    -- For now, just use the default render via Cryptol's Show instance.
    -- XXX: there are actually printing options and we should pass in
    -- SAW's user settings where they apply (and where they don't, maybe
    -- we should grow a few more options, like for printing floats).
    Text.pack $ show doc

-- | Print using a `NameMap`
prettyWithNames :: Cry.PP (Cry.WithNames a) => Cry.NameMap -> a -> PP.Doc ann
prettyWithNames names x =
    PP.pretty $ Text.pack $ show $ Cry.ppWithNames names x

-- | Call Cryptol's `addTNames`. This is a function that provides
--   default names for type parameters that don't have any, and wouldn't
--   need to be here except it interacts directly with the prettyprinter
--   (hence the prettyprinter config) and is what you use to produce the
--   `NameMap` for calling `ppWithNames`.
--
--   FUTURE: maybe replace `Cry.defaultPPCfg` with a config built
--   from SAW's printing config.
--
addTNames :: [CryType.TParam] -> Cry.NameMap -> Cry.NameMap
addTNames tparams names =
    CryType.addTNames Cry.defaultPPCfg tparams names
