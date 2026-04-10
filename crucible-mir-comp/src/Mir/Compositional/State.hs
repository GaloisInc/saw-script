{-# Language ConstraintKinds #-}
{-# Language ImplicitParams #-}
{-# Language TypeFamilies #-}
module Mir.Compositional.State where

import Control.Monad(foldM)
import qualified Data.ByteString as BS
import Data.IORef
import Data.Set(Set)
import qualified Data.Set as Set
import Data.Text(Text)
import qualified Data.Text as Text

import qualified SAWCentral.Builtins as SAW
import qualified SAWCore.SharedTerm as SAW
import qualified CryptolSAWCore.CryptolEnv as SAW
import qualified CryptolSAWCore.Prelude as SAW
import qualified SAWCoreWhat4.ReturnTrip as SAW
import qualified What4.Expr as W4


type MirSym t fs = W4.ExprBuilder t MirState fs

data MirState t = MirState {
  mirSharedContext   :: SAW.SharedContext,
  -- ^ Shared context for building Cryptol terms

  mirCryEnv           :: IORef SAW.CryptolEnv,
  -- ^ Inforamtion about what terms are loaded

  mirKeepUninterp     :: IORef (Set Text),
  {- ^ Set of names we'd like to keep uninterpreted;
    we use `_cryEnv` to compute what they refer to.
    Note that in SAW, the MIRContext has a similar field,
    of type `Set VarIndex`. We can't do the same here, instead we keep the
    actual `Text` names.  The reason is because `crux-mir-comp` loads Cryptol
    code lazily, only when a function is first called.  As a result we can't
    resolve the names early, because the Cryptol code would not yet have been
    loaded.
  -}

  mirSAWCoreState :: SAW.SAWCoreState t
}

newMirState :: IO (MirState t)
newMirState =
  do
    sc <- SAW.mkSharedContext
    SAW.scLoadPreludeModule sc
    SAW.scLoadCryptolModule sc
    let ?fileReader = BS.readFile
    env <- newIORef =<< SAW.initCryptolEnv sc
    unintRef <- newIORef mempty
    sawcoreState <- SAW.newSAWCoreState sc
    pure MirState {
      mirSharedContext = sc,
      mirCryEnv = env,
      mirKeepUninterp = unintRef,
      mirSAWCoreState = sawcoreState
    }

-- | Resolve the given name and add it mark it as an uninterpreted function.
-- Throws an exception if the name does not refer to anything.  If it
-- refers to multiple things, they are all uninterpreted.
resolveUninterp :: MirState t -> IO (Set SAW.VarIndex)
resolveUninterp s =
  do
    env <- readIORef (mirCryEnv s)
    let resolve done nm =
          do
            vars <- SAW.resolveNameIO (mirSharedContext s) env nm
            case vars of
              [] -> fail ("uninterp: undefined name `" ++ Text.unpack nm ++ "`")
              _  -> pure (Set.union (Set.fromList vars) done)
    foldM resolve Set.empty =<< readIORef (mirKeepUninterp s)
  