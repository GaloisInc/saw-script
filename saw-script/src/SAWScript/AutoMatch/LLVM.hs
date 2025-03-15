{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP           #-}

module SAWScript.AutoMatch.LLVM where

import Control.Monad (when)
import Control.Monad.Free
import qualified Data.Text as Text

import qualified Data.AIG as AIG
import Text.LLVM
import SAWCore.SharedTerm

import SAWCentral.Crucible.LLVM.MethodSpecIR (LLVMModule, modAST, modFilePath)

--import Data.Maybe
import Data.Either
#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif

import SAWScript.AutoMatch.Interaction
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Util

-- | Parse an LLVM module into a list of declarations
--   Yields an Interaction so that we can talk to the user about what went wrong
getDeclsLLVM ::
  (AIG.IsAIG l g) =>
  AIG.Proxy l g ->
  SharedContext ->
  LLVMModule arch ->
  IO (Interaction (Maybe [Decl]))
getDeclsLLVM _proxy _sc lm =
    return $ do
      let (untranslateable, translations) =
            partitionEithers . for (modDefines (modAST lm)) $ \def ->
               maybe (Left (symStr (defName def))) Right $
                  symDefineToDecl def

      when (not . null $ untranslateable) $ do
         separator ThinSep
         liftF . flip Warning () $ "No translation for the following signatures in " ++ modFilePath lm ++ ":"
         bulleted $ map (\u -> Text.unpack ("'" <> u <> "'")) untranslateable

      return $ Just translations

   where
      symStr (Symbol s) = Text.pack s

      symDefineToDecl symDefine =
         let name = symStr $ defName symDefine
             tidName (Typed _ (Ident n)) = Text.pack n
             args = mapM (\tid -> Arg (tidName tid) <$> memTypeToStdType (typedType tid)) $ defArgs symDefine
             retType = memTypeToStdType (defRetType symDefine)
         in Decl name <$> retType <*> args

      memTypeToStdType t = case t of
         PrimType (Integer 8)  -> Just $ bitSeqType 8
         PrimType (Integer 16) -> Just $ bitSeqType 16
         PrimType (Integer 32) -> Just $ bitSeqType 32
         PrimType (Integer 64) -> Just $ bitSeqType 64
         _ -> Nothing
