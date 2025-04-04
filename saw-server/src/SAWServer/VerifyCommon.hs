{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module SAWServer.VerifyCommon
  ( VerifyParams(..)
  , X86Alloc(..)
  , X86VerifyParams(..)
  , AssumeParams(..)
  ) where

import qualified Argo.Doc as Doc
import Prelude hiding (mod)
import Data.Aeson (FromJSON(..), withObject, (.:))

import CryptolServer.Data.Expression ( Expression )
import SAWServer.SAWServer ( ServerName )
import SAWServer.Data.Contract ( Contract )
import SAWServer.OK ( OK )
import SAWServer.ProofScript ( ProofScript )

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


instance Doc.DescribedMethod (VerifyParams a) OK where
  parameterFieldDescription =
    [ ("module",
        Doc.Paragraph [Doc.Text "The module of the function being verified."])
    , ("function",
       Doc.Paragraph [Doc.Text "The function being verified."])
    , ("lemmas",
       Doc.Paragraph [Doc.Text "The specifications to use for other functions during this verification."])
    , ("check sat",
       Doc.Paragraph [Doc.Text "Whether or not to enable path satisfiability checking."])
    , ("contract",
       Doc.Paragraph [Doc.Text "The specification to verify for the function."])
    , ("script",
       Doc.Paragraph [Doc.Text "The script to use to prove the validity of the resulting verification conditions."])
    , ("lemma name",
       Doc.Paragraph [Doc.Text "The name to refer to this verification/contract by later."])
    ]
  resultFieldDescription = []

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

instance Doc.DescribedMethod (X86VerifyParams a) OK where
  parameterFieldDescription =
    [ ("module",
        Doc.Paragraph [Doc.Text "The LLVM  module of the caller."])
    , ("object file",
        Doc.Paragraph [Doc.Text "The ELF file containing the function to be verified."])
    , ("function",
       Doc.Paragraph [Doc.Text "The function to be verified's symbol name."])
    , ("globals",
       Doc.Paragraph [Doc.Text "The names and sizes (in bytes) of global variables to initialize."])
    , ("lemmas",
       Doc.Paragraph [Doc.Text "The specifications to use for other functions during this verification."])
    , ("check sat",
       Doc.Paragraph [Doc.Text "Whether or not to enable path satisfiability checking."])
    , ("contract",
       Doc.Paragraph [Doc.Text "The specification to verify for the function."])
    , ("script",
       Doc.Paragraph [Doc.Text "The script to use to prove the validity of the resulting verification conditions."])
    , ("lemma name",
       Doc.Paragraph [Doc.Text "The name to refer to this verification/contract by later."])
    ]
  resultFieldDescription = []

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

instance Doc.DescribedMethod (AssumeParams a) OK where
  parameterFieldDescription =
    [ ("module",
        Doc.Paragraph [Doc.Text "The LLVM  module containing the function."])
    , ("function",
       Doc.Paragraph [Doc.Text "The function we are assuming a contract for."])
    , ("contract",
       Doc.Paragraph [Doc.Text "The specification to assume for the function."])
    , ("lemma name",
       Doc.Paragraph [Doc.Text "The name to refer to this assumed contract by later."])
    ]
  resultFieldDescription = []
