{- |
Module      : Verifier.SAW.MonadifyEnv
Copyright   : Galois, Inc. 2021
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternGuards #-}

module Verifier.SAW.MonadifyEnv where

import Data.List
import Control.Monad
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.ByteString as BS

import qualified Cryptol.TypeCheck.AST as T

import Verifier.SAW.SharedTerm
import Verifier.SAW.Cryptol as C
import Verifier.SAW.Cryptol.Monadify
import Verifier.SAW.CryptolEnv


-- | A monadification environment is a map for primitives and a memo table
data MonadifyEnv = MonadifyEnv {
  monEnvPrims :: MonadifyPrimMap,
  monEnvTable :: MonadifyMemoTable  
  }

-- | The empty monadification environment
emptyMonadifyEnv :: MonadifyEnv
emptyMonadifyEnv = MonadifyEnv { monEnvPrims = defaultMonPrims,
                                 monEnvTable = emptyMonadifyMemoTable }

-- | A Cryptol name, its translation to SAW core, and its type schema
type CryptolNameInfo = (T.Name, Term, T.Schema)

-- | The 'stAppIndex' of a 'Term', if it has one
stAppIndexMaybe :: Term -> Maybe TermIndex
stAppIndexMaybe (STApp { stAppIndex = i }) = Just i
stAppIndexMaybe (Unshared _) = Nothing

-- | The key for sorting a list of 'CryptolNameInfo's
cnameInfoKey :: CryptolNameInfo -> TermIndex
cnameInfoKey (_, t, _) = maybe maxBound id $ stAppIndexMaybe t

-- | Get a list of 'CryptolNameInfo' structures for all names, sorted
-- topologically, i.e., so that later names in the list can contain earlier ones
-- but not vice-versa. This topological sorting is done using the 'stAppIndex'
-- of the SAW core translations of the terms.
cryptolEnvNameInfos :: CryptolEnv -> [CryptolNameInfo]
cryptolEnvNameInfos cenv =
  sortOn cnameInfoKey $
  flip map (Map.assocs $ eExtraTypes cenv) $ \(cname,schema) ->
  case Map.lookup cname (eTermEnv cenv) of
    Just t -> (cname,t,schema)
    Nothing ->
      error ("cryptolEnvNameInfos: Cryptol name has type but no translation: "
             ++ show cname)

monadifyCNameInfo :: SharedContext -> C.Env -> MonadifyEnv ->
                     CryptolNameInfo -> IO MonadifyEnv
monadifyCNameInfo sc cryEnv menv (cname,trm,schema)
  | Just ix <- stAppIndexMaybe trm =
    do tp <- importSchema sc cryEnv schema
       nmi <- importName cname
       mtrm <-
         monadifyNamedTerm sc (monEnvPrims menv) (monEnvTable menv) nmi trm tp
       return $ menv { monEnvTable = IntMap.insert ix mtrm (monEnvTable menv) }
monadifyCNameInfo _ _ menv _ =
  -- We can't add a term with no memoization info to the memoization table
  return menv

-- | Apply monadification to all named terms in a 'CryptolEnv', adding the
-- results to the memoization table of a 'MonadifyEnv'
monadifyCryptolEnv :: SharedContext -> MonadifyEnv -> CryptolEnv ->
                      IO MonadifyEnv
monadifyCryptolEnv sc menv cenv =
  do cryEnv <- let ?fileReader = BS.readFile in mkCryEnv cenv
     foldM (monadifyCNameInfo sc cryEnv) menv (cryptolEnvNameInfos cenv)
