-- Provides access to the preludeLanguage.Haskell.TH
{-# LANGUAGE TemplateHaskell #-}
module Verifier.SAW.Prelude
  ( Module
  , preludeModule
  ) where

import qualified Data.ByteString.Lazy as BL
import Data.ByteString.Unsafe (unsafePackAddressLen)
import Language.Haskell.TH
import System.IO.Unsafe (unsafePerformIO)

import Verifier.SAW.Grammar
import Verifier.SAW.TypedAST

{-# NOINLINE preludeModule #-}
-- | Returns a module containing the standard prelude for SAW. 
preludeModule :: Module
preludeModule = unsafePerformIO $ do
  b <- $(runIO $ do b <- BL.readFile "prelude/SAW.core"
                    case runParser "SAW.core" b parseSAW of
                      (_,[]) -> return (AppE (AppE packExpr lenExpr) primExpr)
                       where packExpr = VarE $ mkName "unsafePackAddressLen"
                             lenExpr  = LitE $ IntegerL $ toInteger $ BL.length b
                             primExpr = LitE $ StringPrimL $ BL.unpack b
                      (_,errors) -> fail $ "Failed to parse prelude:\n" ++ show errors)
  let (decls,[]) = runParser "SAW.core" (BL.fromChunks [b]) parseSAW
  return (unsafeMkModule decls)