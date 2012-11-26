-- Provides access to the preludeLanguage.Haskell.TH
{-# LANGUAGE TemplateHaskell #-}
module Verifier.SAW.Prelude where

import qualified Data.ByteString.Lazy as BL
import Data.ByteString.Lazy.UTF8 as UTF8
import Data.ByteString.Unsafe (unsafePackAddressLen)
import Language.Haskell.TH
import System.IO.Unsafe (unsafePerformIO)

import Verifier.SAW.Grammar
import Verifier.SAW.TypedAST

{-# NOINLINE prelude #-}
-- | Returns a module containing the standard prelude for SAW. 
prelude :: Module
prelude = unsafePerformIO $ do
  b <- $(runIO $ do b <- BL.readFile "prelude/SAW.core"
                    case runParser "SAW.core" b parseSAW of
                      (_,[]) -> return (AppE (AppE packExpr lenExpr) primExpr)
                       where packExpr = VarE $ mkName "unsafePackAddressLen"
                             lenExpr  = LitE $ IntegerL $ toInteger $ BL.length b
                             primExpr = LitE $ StringPrimL $ UTF8.toString b
                      (_,errors) -> fail $ "Failed to parse prelude:\n" ++ show errors)
  let (decls,[]) = runParser "SAW.core" (BL.fromChunks [b]) parseSAW
  return (unsafeMkModule decls)