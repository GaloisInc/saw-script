-- Provides access to the preludeLanguage.Haskell.TH
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Verifier.SAW.Prelude
  ( Module
  , preludeModule
  ) where

import qualified Data.ByteString.Lazy as BL
#if __GLASGOW_HASKELL__ >= 706
#else
import qualified Data.ByteString.Lazy.UTF8 as UTF8
#endif

import Data.ByteString.Unsafe (unsafePackAddressLen)
import Language.Haskell.TH
import System.IO.Unsafe (unsafePerformIO)

import Verifier.SAW.Grammar
import Verifier.SAW.TypedAST
import Verifier.SAW.Typechecker

{-# NOINLINE preludeModule #-}
-- | Returns a module containing the standard prelude for SAW. 
preludeModule :: Module
preludeModule = unsafePerformIO $ do
  b <- $(runIO $ do b <- BL.readFile "prelude/SAW.core"
                    case runParser "SAW.core" b parseSAW of
                      (_,[]) -> return (AppE (AppE packExpr lenExpr) primExpr)
                       where packExpr = VarE $ mkName "unsafePackAddressLen"
                             lenExpr  = LitE $ IntegerL $ toInteger $ BL.length b
#if __GLASGOW_HASKELL__ >= 706
                             primExpr = LitE $ StringPrimL $ BL.unpack b
#else
                             primExpr = LitE $ StringPrimL $ UTF8.toString b
#endif
                      (_,errors) -> fail $ "Failed to parse prelude:\n" ++ show errors)
  let (m,[]) = runParser "SAW.core" (BL.fromChunks [b]) parseSAW
  return (unsafeMkModule [] m)