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
{-# LANGUAGE PolyKinds #-}
module Heapster.IDESupport where

import Control.Monad.Reader
  ( MonadReader (ask, local),
    ReaderT (..),
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
    Name,
  )
import Data.Kind (Type)
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

import Heapster.CruUtil
import Heapster.Permissions
import Heapster.Implication
import Heapster.TypedCrucible
import Heapster.SAWTranslation (SomeTypedCFG (..))
import Heapster.JSONExport(ppToJson)
import Data.Type.RList (mapRAssign)
import Data.Functor.Constant
import Control.Monad.Writer
import Data.Binding.Hobbits.NameMap (NameMap)
import qualified Data.Binding.Hobbits.NameMap as NameMap
import Heapster.NamedMb

-- | The entry point for dumping a Heapster environment to a file for IDE
-- consumption.
printIDEInfo :: PermEnv -> [Some SomeTypedCFG] -> FilePath -> PPInfo -> IO ()
printIDEInfo _penv tcfgs file ppinfo =
  encodeFile file $ IDELog (runWithLoc ppinfo tcfgs)


type ExtractionM = ReaderT (PPInfo, ProgramLoc, String) (Writer [LogEntry])

emit :: LogEntry -> ExtractionM ()
emit entry = tell [entry]

gather :: ExtractionM () -> ExtractionM [LogEntry]
gather m = snd <$> listen m

-- | A single entry in the IDE info dump log.  At a bare minimum, this must
-- include a location and corresponding permission.  Once the basics are
-- working, we can enrich the information we log.
data LogEntry
  = LogEntry
      { leLocation :: String
      , leEntryId :: LogEntryID
      , leCallers :: [LogEntryID]
      , leFunctionName :: String
      , lePermissions :: [(String, String, Value)]
      }
  | LogError
      { lerrLocation :: String
      , lerrError :: String
      , lerrFunctionName :: String
      }
  | LogImpl
      { limplLocation :: String
      , limplExport :: Value
      , limplFunctionName :: String
      }

  deriving (Generic, Show)
instance ToJSON LogEntry
instance NuMatching LogEntry where
  nuMatchingProof = unsafeMbTypeRepr
instance Liftable LogEntry where
  mbLift mb = case mbMatch mb of
    [nuMP| LogEntry v w x y z |] -> 
      LogEntry (mbLift v) (mbLift w) (mbLift x) (mbLift y) (mbLift z)
    [nuMP| LogError x y z |] -> 
      LogError (mbLift x) (mbLift y) (mbLift z)
    [nuMP| LogImpl x y z |] -> 
      LogImpl (mbLift x) (mbLift y) (mbLift z)

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

instance (PermCheckExtC ext extExpr)
    => ExtractLogEntries
         (TypedEntry TransPhase ext blocks tops ret args ghosts) where
  extractLogEntries te = do
    let loc = mbLiftNamed $ fmap getFirstProgramLocTS (typedEntryBody te)
    withLoc loc (mb'ExtractLogEntries (typedEntryBody te))
    let entryId = mkLogEntryID $ typedEntryID te
    let callers = callerIDs $ typedEntryCallers te
    (ppi, _, fname) <- ask
    let loc' = snd (ppLoc loc)
    let debugNames = _mbNames (typedEntryBody te)
    let insertNames ::
          RL.RAssign Name (x :: RList CrucibleType) ->
          RL.RAssign StringF x ->
          NameMap (StringF :: CrucibleType -> Type)->
          NameMap (StringF :: CrucibleType -> Type)
        insertNames RL.MNil RL.MNil m = m
        insertNames (ns RL.:>: n) (xs RL.:>: StringF name) m =
          insertNames ns xs (NameMap.insert n (StringF name) m)
        inputs = mbLift
               $ flip nuMultiWithElim1 (typedEntryPermsIn te)
               $ \ns body ->
                 let ppi' = ppi { ppExprNames = insertNames ns debugNames (ppExprNames ppi) }
                     f :: 
                      (Pair StringF ValuePerm) x ->
                      Constant (String, String, Value) x
                     f (Pair (StringF name) vp) = Constant (name, permPrettyString ppi' vp, ppToJson ppi' vp)
                 in RL.toList (mapRAssign f (zipRAssign debugNames body))
    tell [LogEntry loc' entryId callers fname inputs]

mkLogEntryID :: TypedEntryID blocks args -> LogEntryID
mkLogEntryID = uncurry LogEntryID . entryIDIndices

callerIDs :: [Some (TypedCallSite phase blocks tops args ghosts)] -> [LogEntryID]
callerIDs = map $ \(Some tcs) -> case typedCallSiteID tcs of 
    TypedCallSiteID tei _ _ _ -> mkLogEntryID tei

data Pair f g x = Pair (f x) (g x)

zipRAssign :: RL.RAssign f x -> RL.RAssign g x -> RL.RAssign (Pair f g) x
zipRAssign RL.MNil RL.MNil = RL.MNil
zipRAssign (xs RL.:>: x) (ys RL.:>: y) = zipRAssign xs ys RL.:>: Pair x y

instance ExtractLogEntries (TypedStmtSeq ext blocks tops ret ps_in) where
  extractLogEntries (TypedImplStmt (AnnotPermImpl _str pimpl)) =
    -- fmap (setErrorMsg str) <$> extractLogEntries pimpl
    extractLogEntries pimpl
  extractLogEntries (TypedConsStmt loc _ _ rest) = do
    withLoc loc $ mb'ExtractLogEntries rest
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
    -- The error message is available further up the stack, so we just leave it
  extractLogEntries impl =
    do (ppi, loc, fname) <- ask
       emit (LogImpl (snd (ppLoc loc)) (ppToJson ppi impl) fname)

instance ExtractLogEntries
    (MbPermImpls (TypedStmtSeq ext blocks tops ret) ps_outs) where
  extractLogEntries (MbPermImpls_Cons ctx mbpis pis) = do
    mbExtractLogEntries ctx pis
    extractLogEntries mbpis
  extractLogEntries MbPermImpls_Nil = pure ()

instance (PermCheckExtC ext extExpr)
  => ExtractLogEntries (TypedCFG ext blocks ghosts inits gouts ret) where
    extractLogEntries tcfg = extractLogEntries $ tpcfgBlockMap tcfg

instance (PermCheckExtC ext extExpr)
  => ExtractLogEntries (TypedBlockMap TransPhase ext blocks tops ret) where
  extractLogEntries tbm =
    sequence_ $ RL.mapToList extractLogEntries tbm

instance (PermCheckExtC ext extExpr)
  => ExtractLogEntries (TypedBlock TransPhase ext blocks tops ret args) where
    extractLogEntries tb =
      mapM_ (\(Some te) -> extractLogEntries te) $ _typedBlockEntries tb

mbExtractLogEntries
  :: ExtractLogEntries a => CruCtx ctx -> Mb (ctx :: RList CrucibleType) a -> ExtractionM ()
mbExtractLogEntries ctx mb_a =
  ReaderT $ \(ppi, loc, fname) ->
  tell $ mbLift $ flip nuMultiWithElim1 mb_a $ \ns x ->
  let ppi' = ppInfoAddTypedExprNames ctx ns ppi in
  execWriter $ runReaderT (extractLogEntries x) (ppi', loc, fname)

mb'ExtractLogEntries
  :: ExtractLogEntries a => NamedMb (ctx :: RList CrucibleType) a -> ExtractionM ()
mb'ExtractLogEntries mb_a =
  ReaderT $ \(ppi, loc, fname) ->
  tell $ mbLift $ flip nuMultiWithElim1 (_mbBinding mb_a) $ \ns x ->
  let ppi' = ppInfoApplyAllocation ns (_mbNames mb_a) ppi in
  execWriter $ runReaderT (extractLogEntries x) (ppi', loc, fname)

typedStmtOutCtx :: TypedStmt ext rets ps_in ps_next -> CruCtx rets
typedStmtOutCtx = error "FIXME: write typedStmtOutCtx"

withLoc :: ProgramLoc -> ExtractionM a -> ExtractionM a
withLoc loc = local (\(ppinfo, _, fname) -> (ppinfo, loc, fname))

setErrorMsg :: String -> LogEntry -> LogEntry
setErrorMsg msg le@LogError {} = le { lerrError = msg }
setErrorMsg msg le@LogImpl {} =
  LogError { lerrError = msg
           , lerrLocation = limplLocation le
           , lerrFunctionName = limplFunctionName le}
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
      Some (SomeTypedCFG _ _ tcfg) -> do
        let env = (ppi', getFirstProgramLoc tcfg, getFunctionName tcfg)
        execWriter (runReaderT (extractLogEntries tcfg) env)

getFunctionName :: TypedCFG ext blocks ghosts inits gouts ret -> String
getFunctionName tcfg = case tpcfgHandle tcfg of
  TypedFnHandle _ _ handle -> show $ handleName handle

getFirstProgramLoc
  :: PermCheckExtC ext extExpr
  => TypedCFG ext blocks ghosts inits gouts ret -> ProgramLoc
getFirstProgramLoc tcfg =
  case listToMaybe $ catMaybes $
         RL.mapToList getFirstProgramLocBM $ tpcfgBlockMap tcfg of
    Just pl -> pl
    _ -> error "Unable to get initial program location"

getFirstProgramLocBM
  :: PermCheckExtC ext extExpr
  => TypedBlock TransPhase ext blocks tops ret ctx
  -> Maybe ProgramLoc
getFirstProgramLocBM block =
  listToMaybe $ mapMaybe helper (_typedBlockEntries block)
  where
    helper
      :: PermCheckExtC ext extExpr
      => Some (TypedEntry TransPhase ext blocks tops ret ctx)
      -> Maybe ProgramLoc
    helper ste = case ste of
      Some TypedEntry { typedEntryBody = stmts } ->
        Just $ mbLiftNamed $ fmap getFirstProgramLocTS stmts

-- | From the sequence, get the first program location we encounter, which
-- should correspond to the permissions for the entry point we want to log
getFirstProgramLocTS :: PermCheckExtC ext extExpr
  => TypedStmtSeq ext blocks tops ret ctx
  -> ProgramLoc
getFirstProgramLocTS (TypedImplStmt (AnnotPermImpl _ pis)) =
  getFirstProgramLocPI pis
getFirstProgramLocTS (TypedConsStmt loc _ _ _) = loc
getFirstProgramLocTS (TypedTermStmt loc _) = loc

getFirstProgramLocPI
  :: PermCheckExtC ext extExpr
  => PermImpl (TypedStmtSeq ext blocks tops ret) ctx
  -> ProgramLoc
getFirstProgramLocPI (PermImpl_Done stmts) = getFirstProgramLocTS stmts
getFirstProgramLocPI (PermImpl_Step _ mbps) = getFirstProgramLocMBPI mbps

getFirstProgramLocMBPI
  :: PermCheckExtC ext extExpr
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
