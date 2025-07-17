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
import qualified SAWCoreWhat4.What4 as SAW
import qualified SAWCoreWhat4.ReturnTrip as SAW
import qualified What4.Expr as W4


data MirState sym = MirState {
  mirSharedContext   :: SAW.SharedContext,
  -- ^ Shared context for building Cryptol terms

  mirCryEnv           :: IORef SAW.CryptolEnv,
  -- ^ Inforamtion about what terms are loaded

  mirKeepUninterp     :: IORef (Set Text),
  -- ^ Set of names we'd like to keep uninterpreted;
  -- we use `_cryEnv` to compute what they refer to.

  mirUninterpFunCache :: IORef (SAW.SymFnCache sym),
  -- ^ A cache used by translation to What4, to keep track of
  -- which uninterpred functions we've already made.

  mirSAWCoreState :: SAW.SAWCoreState (SymScope sym)
}

type UsesMirState sym = (?mirState :: MirState sym)

type family SymScope sym
type instance SymScope (W4.ExprBuilder n st fs) = n


newMirState :: IO (MirState sym)
newMirState =
  do
    sc <- SAW.mkSharedContext
    SAW.scLoadPreludeModule sc
    SAW.scLoadCryptolModule sc
    let ?fileReader = BS.readFile
    env <- newIORef =<< SAW.initCryptolEnv sc
    cache <- newIORef mempty
    unintRef <- newIORef mempty
    sawcoreState <- SAW.newSAWCoreState sc
    pure MirState {
      mirSharedContext = sc,
      mirCryEnv = env,
      mirKeepUninterp = unintRef,
      mirUninterpFunCache = cache,
      mirSAWCoreState = sawcoreState
    }

-- | Resolve the given name and add it mark it as an uninterpreted function.
-- Throws an exception if the name does not refer to anything.  If it
-- refers to multiple things, they are all uninterpreted.
resolveUninterp :: MirState sym -> IO (Set SAW.VarIndex)
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
  