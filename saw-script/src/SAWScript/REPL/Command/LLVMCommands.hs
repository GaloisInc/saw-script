{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

{- |
Module      : SAWScript.REPL.Command.LLVMCommands
Description :
License     : BSD3
Maintainer  : saw@galois.com
Stability   : provisional

REPL :-commands for working with LLVMModule information.
-}

module SAWScript.REPL.Command.LLVMCommands
  (
    llvmDisCmd, llvmDisCmdHelp
  )
where

import           Control.Monad.IO.Class (liftIO)
import           Data.List (find)
import           Data.Parameterized.Some
import           Data.String (fromString)
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Text.PrettyPrint.HughesPJ as PPPJ
import           Text.Read (readMaybe)

import qualified SAWSupport.ScopedMap as ScopedMap

import qualified SAWCentral.AST as SAW_AST
import qualified SAWCentral.Crucible.LLVM.MethodSpecIR as CMSLLVM
import           SAWCentral.Value (Environ(..) , TopLevelRW(..) , Value(..))

import           SAWScript.REPL.Monad

import           Text.LLVM.AST
import           Text.LLVM.PP ( ppLLVM, llvmVlatest, ppDefine, ppUnnamedMd
                              , ppModuleAtLine )


llvmDisCmdHelp :: Text
llvmDisCmdHelp =
  "show LLVM disassembly for LLVMModule plus: symbol, file:line, or !N metadata"

llvmDisCmd :: Text -> Text -> REPL ()
llvmDisCmd modref ref

  | Text.null modref || Text.null ref =
    liftIO $ putStrLn usage

  | Just ('!', linestr) <- Text.uncons ref
  , Just mdId <- readMaybe (drop 1 $ Text.unpack linestr) :: Maybe Int =
      getModule modref >>= \case
      Right llvmMod ->
        case find ((mdId ==) . umIndex) $ modUnnamedMd llvmMod of
          Just um -> disp $ ppLLVM llvmVlatest $ ppUnnamedMd um
          Nothing -> err $ "Could not find metadata with ID " <> show mdId
      Left e -> err e

  | (file, linestr) <- Text.span (/= ':') ref
  , not (Text.null file)
  , Just line <- readMaybe (drop 1 $ Text.unpack linestr) :: Maybe Integer =
      getModule modref >>= \case
      Right llvmMod -> disp
                       $ ppLLVM llvmVlatest
                       $ ppModuleAtLine (Text.unpack file) line llvmMod
      Left e -> err e

  | otherwise =
    getModule modref >>= \case
      Right llvmMod ->
        do let dname = fromString $ Text.unpack ref
           case find ((dname ==) . defName) $ modDefines llvmMod of
             Just d -> disp $ ppLLVM llvmVlatest $ ppDefine d
             Nothing -> err $ Text.unpack ref <> " is not a function in this module"
      Left e -> err e

  where
    usage = unlines
            [ "The :llvmdis command requires an LLVMModule\
              \ followed by a symbol, a file:line, or !N argument."
              , ""
              , "For example:"
              , "   sawscript> bc <- llvm_load_module \"intTests/testmulti/foo.bc\""
              , "   sawscript> :llvmdis bc foo"
              , "   ... shows the foo function in LLVM textual format"
              , "   sawscript> :llvmdis bc foo.c:2"
              , "   ... shows just line 2 of the foo.bc file in LLVM textual format"
              , "   sawscript> :llvmdis bc !10"
              , "   ... shows the metadata at index 10"
            ]
    err msg = liftIO $ putStrLn $ "Error: " <> msg <> "\n\n  " <> usage <> "\n"
    disp = liftIO . putStrLn . PPPJ.render


getModule :: SAW_AST.Name -> REPL (Either String Module)
getModule nm = do
      rw <- getTopLevelRW

      let environ = rwEnviron rw

      let varEnv = eVarEnv environ
      case ScopedMap.lookup nm varEnv of
        Just (_pos, _life, _schema, val, _help) ->
          do case val of
               VLLVMModule someCMSMod -> return $ Right
                                         $ viewSome CMSLLVM.modAST someCMSMod
               _ -> return $ Left "Error: first argument must be an LLVMModule"
        Nothing -> return $ Left $ "Could not find " <> show nm
