{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module SAWCoreIsabelle.Runner(
  cryptolTheoryHash
, processModules
, RunnerError(..)
, fatalErr
) where

import           Prelude hiding (log)
import           Control.Exception (catch, throw, IOException, Exception)
import           Control.Monad (forM_,forM)
import qualified Control.Monad.IO.Class as IO
import           Control.Monad.Writer (execWriterT, tell, WriterT (..))
import qualified Crypto.Hash.SHA1 as SHA1

import qualified Data.ByteString as BS
import           Data.ByteString.Builder (byteStringHex, toLazyByteString)
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Maybe (mapMaybe, fromMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.Text.IO as T

import           System.Directory (listDirectory)
import           System.FilePath ((</>), takeFileName)
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

import qualified Cryptol.ModuleSystem.Env as Cry
import qualified Cryptol.TypeCheck.AST as Cry
import qualified Cryptol.Utils.Ident as Cry
import           Cryptol.Utils.PP (pretty)

import           Language.Isabelle.Builtins (cryThy)
import qualified Language.Isabelle.Decl as Decl
import qualified Language.Isabelle.Name as Name
import qualified Language.Isabelle.Template as Template
import qualified Language.Isabelle.Theory as Theory
import qualified Language.Isabelle.Output as Output

import qualified SAWCoreIsabelle.Error as Error
import           SAWCoreIsabelle.Options (HasOptions, log, logErr)
import qualified SAWCoreIsabelle.Options as Options
import qualified SAWCoreIsabelle.Translate as Translate
import           SAWCoreIsabelle.IsaM (SAWEnv(..))
import qualified SAWCoreIsabelle.CryptolDeps as Deps
import qualified Data.Text as Text

data RunnerError = RunnerError String
  deriving (Eq, Ord)

instance Show RunnerError where
  show (RunnerError msg) = msg

instance Exception RunnerError

err :: (HasOptions, IO.MonadIO m) => String -> m ()
err msg = logErr (-1) $ "[error] " ++ msg

fatalErr :: (HasOptions, IO.MonadIO m) => String -> m a
fatalErr msg = IO.liftIO $ err msg >> throw (RunnerError msg)

unused_thys :: [String]
unused_thys = ["Unsupported.thy", "Unconstrain_Typedef.thy", "Word0.thy"]

bsToText :: BS.ByteString -> T.Text
bsToText bs = T.decodeUtf8 (BS.toStrict (toLazyByteString (byteStringHex bs)))


-- | Hash of all (used) Cryptol theories. Should correspond to
-- 'cryptol_theory_hash' in Cryptol.thy. Notably the individual file hashes
-- are converted into UTF-8 strings, combined, and then hashed together.
-- This is to simplify the Isabelle side of the hash computation, which
-- doesn't provide a convenient mechanism for natively combining hashes.
cryptolTheoryHash :: String
cryptolTheoryHash = 
  let 
    used_thys = filter (\(thy,_) -> not (List.elem thy unused_thys)) isaThys
    txt = bsToText $ BS.concat (map snd used_thys)
  in T.unpack $ bsToText $ SHA1.hash (T.encodeUtf8 txt)

isaThys :: [(String, BS.ByteString)]
isaThys = $(do
  let dir = "saw-core-isabelle" </> "isabelle" </> "theories"
  files <- runIO $ listDirectory dir
  bs <- runIO $ forM files $ \f -> do
    content <- BS.readFile (dir </> f)
    return (takeFileName f, SHA1.hash content)
  lift bs)

isBuiltinThy :: String -> Bool
isBuiltinThy str = List.any (\(nm,_) -> nm == str <> ".thy") isaThys

renameImports ::
  HasOptions => Theory.Theory -> IO Theory.Theory
renameImports thy = do
  decls <- Decl.traverseImports (Theory.thyDecls thy) $ \nm -> 
    case isBuiltinThy (Name.thyNm nm) of
      True -> case Options.isaImportPrefix of
        Options.NoPrefix -> return nm
        Options.CryptolImage ->
          return $ nm { Name.thyNm = "\"Cryptol." ++ Name.thyNm nm ++ "\"" }
        Options.CustomPrefix s ->
          return $ nm { Name.thyNm = "\"" ++ s ++ Name.thyNm nm ++ "\"" }
      False -> return nm
  return $ thy { Theory.thyDecls = decls }

extractRecordDecls :: Theory.Theory -> (Set.Set Decl.Decl, Theory.Theory)
extractRecordDecls thy =
  let (recDs, ds) = Decl.strip (\case Decl.RecordDecl{} -> True; _ -> False) (Theory.thyDecls thy)
  in (Set.fromList recDs, thy { Theory.thyDecls = ds })


recordDeclThy :: Decl.Decl -> Theory.Theory
recordDeclThy d@(Decl.RecordDecl flds) = 
  let thynm = Name.nmThy $ Decl.recordName flds
  in Theory.Theory thynm (Decl.singleton d) 
recordDeclThy _ = error "recordDeclThy: unexpected Decl kind"

allDepsOf :: Deps.CryptolDeps -> [Cry.ModName] -> Set.Set Cry.ModName
allDepsOf deps ms = 
  let acc_deps mnm = Set.union (fromMaybe Set.empty $ fmap snd $ Map.lookup mnm (Deps.moduleDeps deps))
  in foldr acc_deps Set.empty ms


asModule :: Set.Set Cry.ModName -> Cry.LoadedModule -> Maybe (Cry.Module, [Cry.ModName])
asModule selected lm
  | Cry.lmName lm /= Cry.preludeName
  , Set.member (Cry.lmName lm) selected
  = Just (Cry.lmModule lm, (Set.toList $ Cry.fiImportDeps (Cry.lmFileInfo lm)))
asModule _ _ = Nothing

data TranslateState = TranslateState
  { trErrs :: [Error.TranslationError]
  , trThys :: Theory.Theories
  }

resultState :: [Error.TranslationError] -> Theory.Theory -> TranslateState
resultState ers res = TranslateState ers (Theory.singleton res)

instance Monoid TranslateState where
  mempty = TranslateState mempty mempty

instance Semigroup TranslateState where
  TranslateState errs1 thys1 <> TranslateState errs2 thys2 =
    TranslateState (errs1 <> errs2) (thys1 <> thys2)

printErrs :: (HasOptions, IO.MonadIO m) => TranslateState -> m ()
printErrs st = forM_ (trErrs st) $ \terr -> err $ Error.showErr terr

writeResult :: HasOptions => [Error.TranslationError] -> Theory.Theory -> WriterT TranslateState IO ()
writeResult ers res = do
  let st = resultState ers res
  case ers of
    [] -> do
      log 0 $ "Successfully translated theory " ++ (show $ Theory.thyNm res)
      tell st
    _ -> case Options.keepGoing of
      True -> do
        err $ "Errors raised while translating theory " ++ (show $ Theory.thyNm res)
        tell st
      False -> do
        let errMsg = "Translating was unsuccessful for theory " ++ (show $ Theory.thyNm res)
        err errMsg
        printErrs st
        log (-1) $ "Set 'keep-going' flag to attempt an incomplete translation."
        IO.liftIO $ throw (RunnerError errMsg)



processModules ::
  Options.Options ->
  [Cry.LoadedModule] ->
  [Cry.DeclGroup] -> 
  [Cry.TySyn]  ->
  Maybe SAWEnv ->
  IO Bool
processModules opts loadedModules extraDecls extraTys _sawEnv = Options.withOptions opts $ do
  let
    outDir = Options.isaDestDir
    cryDeps = Deps.mkCryptolDeps loadedModules extraDecls extraTys
    allMods =  map Cry.lmName loadedModules
    
  trresult <- execWriterT $ do 
    imports <- case Options.targetSelect of
      Options.AllModules -> return allMods
      Options.NamedModules nms -> 
        return $ filter (\m -> elem (Text.unpack $ Cry.modNameToText m) nms) allMods
      Options.ModuleNames nms ->
        return $ filter (\m -> elem m nms) allMods
    let allDeps = allDepsOf cryDeps imports
    let modules = mapMaybe (asModule allDeps) loadedModules
    forM_ modules $ \(crymod,cryimports) -> do
      log 1 $ pretty crymod
      (errs,res) <- IO.liftIO $ Translate.translateModuleIO cryDeps cryimports crymod
      writeResult errs res
    log 1 $ "\n"
  case (trErrs trresult, Theory.null (trThys trresult))  of
    ([], False) -> log 0 $ "Translation successful. Generating theory files..."
    (_, True) -> log (-1) $ "Could not find any modules to translate"
    _ -> do
      err $ "Errors raised during translation:"
      printErrs trresult
      log (-1) $ "Resulting theories will be incomplete. Generating theory files..."
  log 1 $ "\n"
  templates <- Template.loadAll
  
  (recordThys,thys) <- Theory.forTheories (trThys trresult) (mempty,[]) $ \thy (recordThys,thys) -> do
    let (recDecls', thy') = extractRecordDecls thy
    let recordThys' = Set.map recordDeclThy recDecls'
    let thy'' = foldr (\rthy -> Theory.addDecl (Decl.Import (Theory.thyNm rthy))) thy' recordThys'
    return (Set.union recordThys recordThys', thy'':thys)
  
  let recordThys' = map (Theory.addDecl (Decl.Import cryThy)) (Set.toList recordThys)
  let allThys = recordThys' ++ thys

  forM_ allThys $ \thy -> do
    let theoryFile = Name.thyNm (Theory.thyNm thy) <> ".thy"
    log 0 $ "Generating " ++ theoryFile
    thy' <- renameImports thy
    let content = Output.withTemplates templates $ Output.out thy'
    let outputFile = outDir </> theoryFile
    result <- tryIO $ T.writeFile outputFile (T.pack content)
    case result of
      Left e -> fatalErr $ "Failed to write output file '" ++ outputFile ++ "': " ++ show e
      Right () -> do
        log (-1) $ "Successfully wrote '" ++ outputFile ++ "'"
  return $ (null $ trErrs trresult) && (not $ null allThys)

tryIO :: IO a -> IO (Either IOException a)
tryIO f = catch (Right <$> f) (\e -> return $ Left (e :: IOException))