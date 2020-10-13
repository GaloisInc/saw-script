{-# LANGUAGE OverloadedStrings #-}

module SAWServer.VerifyCommon
  ( VerifyParams(..)
  , X86Alloc(..)
  , X86VerifyParams(..)
  , AssumeParams(..)
  ) where

import Prelude hiding (mod)
import Data.Aeson (FromJSON(..), withObject, (.:))

import CryptolServer.Data.Expression
import SAWServer
import SAWServer.Data.Contract
import SAWServer.ProofScript

data VerifyParams ty =
  VerifyParams
    { verifyModule       :: ServerName
    , verifyFunctionName :: String
    , verifyLemmas       :: [ServerName]
    , verifyCheckSat     :: Bool
    -- TODO: might want to be able to save contracts and refer to them by name?
    , verifyContract     :: Contract ty Expression -- ServerName
    -- TODO: might want to be able to save proof scripts and refer to them by name?
    , verifyScript       :: ProofScript
    , verifyLemmaName    :: ServerName
    }

-- | A global allocation from the x86 machine code perspective. The
-- first argument is the symbol name of the global, and the second
-- argument is how many bytes it should be allocated to point to.
data X86Alloc = X86Alloc String Integer

data X86VerifyParams ty =
  X86VerifyParams
    { x86VerifyModule       :: ServerName
    , x86VerifyObjectFile   :: String
    , x86VerifyFunctionName :: String
    , x86VerifyGlobals      :: [X86Alloc]
    , x86VerifyLemmas       :: [ServerName]
    , x86VerifyCheckSat     :: Bool
    , x86VerifyContract     :: Contract ty Expression -- ServerName
    , x86VerifyScript       :: ProofScript
    , x86VerifyLemmaName    :: ServerName
    }

instance (FromJSON ty) => FromJSON (VerifyParams ty) where
  parseJSON =
    withObject "SAW/verify params" $ \o ->
    VerifyParams <$> o .: "module"
                 <*> o .: "function"
                 <*> o .: "lemmas"
                 <*> o .: "check sat"
                 <*> o .: "contract"
                 <*> o .: "script"
                 <*> o .: "lemma name"

instance FromJSON X86Alloc where
  parseJSON =
    withObject "SAW/x86 allocation" $ \o ->
    X86Alloc <$> o .: "global name"
             <*> o .: "global size"

instance (FromJSON ty) => FromJSON (X86VerifyParams ty) where
  parseJSON =
    withObject "SAW/x86 verify params" $ \o ->
    X86VerifyParams <$> o .: "module"
                    <*> o .: "object file"
                    <*> o .: "function"
                    <*> o .: "globals"
                    <*> o .: "lemmas"
                    <*> o .: "check sat"
                    <*> o .: "contract"
                    <*> o .: "script"
                    <*> o .: "lemma name"

data AssumeParams ty =
  AssumeParams
    { assumeModule       :: ServerName
    , assumeFunctionName :: String
    -- TODO: might want to be able to save contracts and refer to them by name?
    , assumeContract     :: Contract ty Expression -- ServerName
    , assumeLemmaName    :: ServerName
    }

instance (FromJSON ty) => FromJSON (AssumeParams ty) where
  parseJSON =
    withObject "SAW/assume params" $ \o ->
    AssumeParams <$> o .: "module"
                 <*> o .: "function"
                 <*> o .: "contract"
                 <*> o .: "lemma name"
