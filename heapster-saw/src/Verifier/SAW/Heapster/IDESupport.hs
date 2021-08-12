{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.Heapster.IDESupport where

import Control.Monad.Reader
  ( MonadReader (ask, local),
    ReaderT (..),
  )
import Control.Monad.Writer
  ( MonadWriter (tell),
    Writer,
    execWriter,
  )
import Data.Aeson (ToJSON, Value, encodeFile)
import Data.Binding.Hobbits
  ( Liftable (..),
    Mb,
    NuMatching (..),
    RList,
    mbMatch,
    nuMP,
    nuMultiWithElim1,
    unsafeMbTypeRepr,
  )
import Data.Maybe (catMaybes, listToMaybe, mapMaybe)
import Data.Parameterized.Some (Some (..))
import qualified Data.Text as T
import qualified Data.Type.RList as RL
import GHC.Generics (Generic)
import Lang.Crucible.FunctionHandle
import Lang.Crucible.Types (CrucibleType)
import What4.FunctionName (FunctionName (functionName))
import What4.ProgramLoc
  ( Position (BinaryPos, InternalPos, OtherPos, SourcePos),
    ProgramLoc (..),
  )

import Verifier.SAW.Heapster.CruUtil
import Verifier.SAW.Heapster.Implication
import Verifier.SAW.Heapster.Permissions
import Verifier.SAW.Heapster.TypedCrucible
import Verifier.SAW.Heapster.JSONExport(ppToJson)


-- | The entry point for dumping a Heapster environment to a file for IDE
-- consumption.
printIDEInfo :: PermEnv -> [Some SomeTypedCFG] -> FilePath -> PPInfo -> IO ()
printIDEInfo _penv tcfgs file ppinfo =
  encodeFile file $ IDELog (runWithLoc ppinfo tcfgs)


type ExtractionM = ReaderT (PPInfo, ProgramLoc, String) (Writer [LogEntry])

emit :: LogEntry -> ExtractionM ()
emit entry = tell [entry]

-- | A single entry in the IDE info dump log.  At a bare minimum, this must
-- include a location and corresponding permission.  Once the basics are
-- working, we can enrich the information we log.
data LogEntry
  = LogEntry
      { leLocation :: String
      , leEntryId :: LogEntryID
      , leCallers :: [LogEntryID]
      , leFunctionName :: String
      , leExport :: Value
      , lePermissions :: String
      }
  | LogError
      { lerrLocation :: String
      , lerrError :: String
      , lerrFunctionName :: String
      }
  deriving (Generic, Show)
instance ToJSON LogEntry
instance NuMatching LogEntry where
  nuMatchingProof = unsafeMbTypeRepr
instance Liftable LogEntry where
  mbLift mb = case mbMatch mb of
    [nuMP| LogEntry u v w x y z |] -> 
      LogEntry (mbLift u) (mbLift v) (mbLift w) 
               (mbLift x) (mbLift y) (mbLift z)
    [nuMP| LogError x y z |] -> 
      LogError (mbLift x) (mbLift y) (mbLift z)


data LogEntryID = LogEntryID
  { leIdBlock :: Int
  , leIdHeapster :: Int
  }
  deriving (Generic, Show)
instance ToJSON LogEntryID
instance NuMatching LogEntryID where
  nuMatchingProof = unsafeMbTypeRepr 
instance Liftable LogEntryID where
  mbLift mb = case mbMatch mb of
    [nuMP| LogEntryID x y |] -> LogEntryID (mbLift x) (mbLift y)

-- | A complete IDE info dump log, which is just a sequence of entries.  Once
-- the basics are working, we can enrich the information we log.
newtype IDELog = IDELog {
  lmfEntries :: [LogEntry]
} deriving (Generic, Show)
instance ToJSON IDELog


class ExtractLogEntries a where
  extractLogEntries :: a -> ExtractionM ()

instance (PermCheckExtC ext)
    => ExtractLogEntries
         (TypedEntry TransPhase ext blocks tops ret args ghosts) where
  extractLogEntries te = do
    let loc = mbLift $ fmap getFirstProgramLocTS (typedEntryBody te)
    withLoc loc (mbExtractLogEntries (typedEntryBody te))
    let entryId = mkLogEntryID $ typedEntryID te
    let callers = callerIDs $ typedEntryCallers te
    mbValPermEntries entryId callers (typedEntryPermsIn te)

mkLogEntryID :: TypedEntryID blocks args -> LogEntryID
mkLogEntryID = uncurry LogEntryID . entryIDIndices

callerIDs :: [Some (TypedCallSite phase blocks tops args ghosts)] -> [LogEntryID]
callerIDs = map $ \(Some tcs) -> case typedCallSiteID tcs of 
    TypedCallSiteID tei _ _ _ -> mkLogEntryID tei

instance ExtractLogEntries (TypedStmtSeq ext blocks tops ret ps_in) where
  extractLogEntries (TypedImplStmt (AnnotPermImpl _str pimpl)) =
    -- fmap (setErrorMsg str) <$> extractLogEntries pimpl
    extractLogEntries pimpl
  extractLogEntries (TypedConsStmt loc _ _ rest) = do
    withLoc loc $ mbExtractLogEntries rest
  extractLogEntries (TypedTermStmt _ _) = pure ()

instance ExtractLogEntries
    (PermImpl (TypedStmtSeq ext blocks tops ret) ps_in) where
  extractLogEntries (PermImpl_Step pi1 mbpis) = do
    pi1Entries <- extractLogEntries pi1
    pisEntries <- extractLogEntries mbpis
    return $ pi1Entries <> pisEntries
  extractLogEntries (PermImpl_Done stmts) = extractLogEntries stmts

instance ExtractLogEntries (PermImpl1 ps_in ps_outs) where
  extractLogEntries (Impl1_Fail err) =
    do (_, loc, fname) <- ask
       emit (LogError (snd (ppLoc loc)) (ppError err) fname)
  extractLogEntries _ = pure ()

instance ExtractLogEntries
    (MbPermImpls (TypedStmtSeq ext blocks tops ret) ps_outs) where
  extractLogEntries (MbPermImpls_Cons _ mbpis pis) = do
    mbExtractLogEntries pis
    extractLogEntries mbpis
  extractLogEntries MbPermImpls_Nil = pure ()

instance (PermCheckExtC ext)
  => ExtractLogEntries (TypedCFG ext blocks ghosts inits ret) where
    extractLogEntries tcfg = extractLogEntries $ tpcfgBlockMap tcfg

instance (PermCheckExtC ext)
  => ExtractLogEntries (TypedBlockMap TransPhase ext blocks tops ret) where
  extractLogEntries tbm =
    sequence_ $ RL.mapToList extractLogEntries tbm

instance (PermCheckExtC ext)
  => ExtractLogEntries (TypedBlock TransPhase ext blocks tops ret args) where
    extractLogEntries tb =
      mapM_ (\(Some te) -> extractLogEntries te) $ _typedBlockEntries tb

mbExtractLogEntries
  :: ExtractLogEntries a => Mb (ctx :: RList CrucibleType) a -> ExtractionM ()
mbExtractLogEntries mb_a =
  ReaderT $ \(ppi, loc, fname) ->
  tell $ mbLift $ flip nuMultiWithElim1 mb_a $ \ns x ->
  execWriter $ runReaderT (extractLogEntries x) 
                          (ppInfoAddExprNames "x" ns ppi, loc, fname)

-- TODO: The next two functions are a hack, and we should probably rethink how
-- this is architected a bit.  They don't fit into the type signature of
-- `ExtractLogEntries` currently because we push down the extra information
-- about the entrypoint IDs which we need wherever `LogEntry`s are created.

mbValPermEntries 
  :: LogEntryID 
  -> [LogEntryID] 
  -> Mb ctx (ValuePerms ctx) 
  -> ExtractionM ()
mbValPermEntries entryId callers mb_vp =
  ReaderT $ \(ppi, loc, fname) ->
  tell $ mbLift $ flip nuMultiWithElim1 mb_vp $ \ns vp ->
  execWriter $ runReaderT (valPermEntries entryId callers vp) 
                          (ppInfoAddExprNames "x" ns ppi, loc, fname)

valPermEntries :: LogEntryID -> [LogEntryID] -> ValuePerms ctx -> ExtractionM ()
valPermEntries entryId callers vps = do
  (ppi, loc, fname) <- ask
  let loc' = snd (ppLoc loc)
  let strs = foldValuePerms (\xs vp -> 
               (ppToJson ppi vp, permPrettyString ppi vp) : xs) [] vps
  tell [LogEntry loc' entryId callers fname export str | (export, str) <- strs]

typedStmtOutCtx :: TypedStmt ext rets ps_in ps_next -> CruCtx rets
typedStmtOutCtx = error "FIXME: write typedStmtOutCtx"

withLoc :: ProgramLoc -> ExtractionM a -> ExtractionM a
withLoc loc = local (\(ppinfo, _, fname) -> (ppinfo, loc, fname))

setErrorMsg :: String -> LogEntry -> LogEntry
setErrorMsg msg le@LogError {} = le { lerrError = msg }
setErrorMsg msg le@LogEntry {} =
  LogError { lerrError = msg
           , lerrLocation = leLocation le
           , lerrFunctionName = leFunctionName le
           }


runWithLoc :: PPInfo -> [Some SomeTypedCFG] -> [LogEntry]
runWithLoc ppi =
  concatMap (runWithLocHelper ppi)
  where
    runWithLocHelper :: PPInfo -> Some SomeTypedCFG -> [LogEntry]
    runWithLocHelper ppi' sstcfg = case sstcfg of
      Some (SomeTypedCFG tcfg) -> do
        let env = (ppi', getFirstProgramLoc tcfg, getFunctionName tcfg)
        execWriter (runReaderT (extractLogEntries tcfg) env)

getFunctionName :: TypedCFG ext blocks ghosts inits ret -> String
getFunctionName tcfg = case tpcfgHandle tcfg of
  TypedFnHandle _ handle -> show $ handleName handle

getFirstProgramLoc
  :: PermCheckExtC ext
  => TypedCFG ext blocks ghosts inits ret -> ProgramLoc
getFirstProgramLoc tcfg =
  case listToMaybe $ catMaybes $
         RL.mapToList getFirstProgramLocBM $ tpcfgBlockMap tcfg of
    Just pl -> pl
    _ -> error "Unable to get initial program location"

getFirstProgramLocBM
  :: PermCheckExtC ext
  => TypedBlock TransPhase ext blocks tops ret ctx
  -> Maybe ProgramLoc
getFirstProgramLocBM block =
  listToMaybe $ mapMaybe helper (_typedBlockEntries block)
  where
    helper
      :: PermCheckExtC ext
      => Some (TypedEntry TransPhase ext blocks tops ret ctx)
      -> Maybe ProgramLoc
    helper ste = case ste of
      Some TypedEntry { typedEntryBody = stmts } ->
        Just $ mbLift $ fmap getFirstProgramLocTS stmts

-- | From the sequence, get the first program location we encounter, which
-- should correspond to the permissions for the entry point we want to log
getFirstProgramLocTS :: PermCheckExtC ext
  => TypedStmtSeq ext blocks tops ret ctx
  -> ProgramLoc
getFirstProgramLocTS (TypedImplStmt (AnnotPermImpl _ pis)) =
  getFirstProgramLocPI pis
getFirstProgramLocTS (TypedConsStmt loc _ _ _) = loc
getFirstProgramLocTS (TypedTermStmt loc _) = loc

getFirstProgramLocPI
  :: PermCheckExtC ext
  => PermImpl (TypedStmtSeq ext blocks tops ret) ctx
  -> ProgramLoc
getFirstProgramLocPI (PermImpl_Done stmts) = getFirstProgramLocTS stmts
getFirstProgramLocPI (PermImpl_Step _ mbps) = getFirstProgramLocMBPI mbps

getFirstProgramLocMBPI
  :: PermCheckExtC ext
  => MbPermImpls (TypedStmtSeq ext blocks tops ret) ctx
  -> ProgramLoc
getFirstProgramLocMBPI MbPermImpls_Nil =
  error "Error finding program location for IDE log"
getFirstProgramLocMBPI (MbPermImpls_Cons _ _ pis) =
  mbLift $ fmap getFirstProgramLocPI pis

-- | Print a `ProgramLoc` in a way that is useful for an IDE, i.e., machine
-- readable
ppLoc :: ProgramLoc -> (String, String)
ppLoc pl =
  let fnName = T.unpack $ functionName $ plFunction pl
      locStr = ppPos $ plSourceLoc pl

      ppPos (SourcePos file line column) =
        T.unpack file <> ":" <> show line <> ":" <> show column
      ppPos (BinaryPos _ _) = "<unknown binary pos>"
      ppPos (OtherPos _) = "<unknown other pos>"
      ppPos InternalPos = "<unknown internal pos>"
  in (fnName, locStr)
