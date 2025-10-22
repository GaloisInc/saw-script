{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : SAWCore.ExternalFormat
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module SAWCore.ExternalFormat (
  scWriteExternal, scReadExternal, scReadExternalTyped
  ) where

import qualified Control.Monad.State.Strict as State
import Control.Monad.Trans.Class (MonadTrans(..))
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Vector as V
import Text.Read (readMaybe)
import Text.URI

import SAWCore.Name
import SAWCore.SharedTerm
  ( SharedContext
  , scFreshVarName
  , scRegisterName
  , scResolveNameByURI
  )
import qualified SAWCore.SharedTerm as Raw
import SAWCore.Term.Functor
import SAWCore.Term.Raw (TermIndex)
import SAWCore.Term.Certified

--------------------------------------------------------------------------------
-- External text format

type WriteM = State.State (Map TermIndex Int, Map VarIndex (Either Text NameInfo), [String], Int)

renderNames :: Map VarIndex (Either Text NameInfo) -> String
renderNames nms = show
  [ (idx, f nmi)
  | (idx,nmi) <- Map.toList nms
  ]
 where
   f (Left s) = Left s
   f (Right (ModuleIdentifier i))  = Right (Left (show i))
   f (Right (ImportedName uri as)) = Right (Right (render uri, as))

readNames :: String -> Maybe (Map VarIndex (Either Text NameInfo))
readNames xs = Map.fromList <$> (mapM readName =<< readMaybe xs)
 where
   readName :: (VarIndex, Either Text (Either Text (Text,[Text]))) -> Maybe (VarIndex, Either Text NameInfo)
   readName (idx, Left x) = pure (idx, Left x)
   readName (idx, Right (Left i)) = pure (idx, Right (ModuleIdentifier (parseIdent (Text.unpack i))))
   readName (idx, Right (Right (uri,as))) =
       do uri' <- mkURI uri
          pure (idx, Right (ImportedName uri' as))

-- | Render to external text format
scWriteExternal :: Raw.Term -> String
scWriteExternal t0 =
    let (x, (_, nms, lns, _)) = State.runState (go t0) (Map.empty, Map.empty, [], 1)
    in unlines $
        [ unwords ["SAWCoreTerm", show x]
        , renderNames nms
        ] ++ reverse lns
  where
    nextId :: WriteM Int
    nextId =
       do (m, nms, lns, x) <- State.get
          State.put (m, nms, lns, x+1)
          return x
    output :: String -> WriteM ()
    output l =
       do (m, nms, lns, x) <- State.get
          State.put (m, nms, l:lns, x)
    memoize :: TermIndex -> WriteM Int
    memoize i =
       do (m, nms, lns, x) <- State.get
          State.put (Map.insert i x m, nms, lns, x+1)
          return x
    stashName :: Name -> WriteM ()
    stashName ec =
       do (m, nms, lns, x) <- State.get
          State.put (m, Map.insert (nameIndex ec) (Right (nameInfo ec)) nms, lns, x)
    stashVarName :: VarName -> WriteM ()
    stashVarName vn =
       do (m, nms, lns, x) <- State.get
          State.put (m, Map.insert (vnIndex vn) (Left (vnName vn)) nms, lns, x)

    go :: Raw.Term -> WriteM Int
    go (Raw.Unshared tf) = do
      tf' <- traverse go tf
      body <- writeTermF tf'
      x <- nextId
      output (unwords [show x, body])
      return x

    go Raw.STApp{ Raw.stAppIndex = i, Raw.stAppTermF = tf } = do
      (memo, _, _, _) <- State.get
      case Map.lookup i memo of
        Just x -> return x
        Nothing -> do
          tf' <- traverse go tf
          body <- writeTermF tf'
          x <- memoize i
          output (unwords [show x, body])
          return x

    writeTermF :: TermF Int -> WriteM String
    writeTermF tf =
      case tf of
        App e1 e2      -> pure $ unwords ["App", show e1, show e2]
        Lambda s t e   ->
          do stashVarName s
             pure $ unwords ["Lam", show (vnIndex s), show t, show e]
        Pi s t e       ->
          do stashVarName s
             pure $ unwords ["Pi", show (vnIndex s), show t, show e]
        Constant nm    ->
            do stashName nm
               pure $ unwords ["Constant", show (nameIndex nm)]
        Variable nm tp ->
           do stashVarName nm
              pure $ unwords ["Variable", show (vnIndex nm), show tp]
        FTermF ftf     ->
          case ftf of
            UnitValue           -> pure $ unwords ["Unit"]
            UnitType            -> pure $ unwords ["UnitT"]
            PairValue x y       -> pure $ unwords ["Pair", show x, show y]
            PairType x y        -> pure $ unwords ["PairT", show x, show y]
            PairLeft e          -> pure $ unwords ["ProjL", show e]
            PairRight e         -> pure $ unwords ["ProjR", show e]

            Recursor (CompiledRecursor d s _ _ _) ->
              do stashName d
                 let show_s = if s == propSort then "Prop" else drop 5 (show s)
                 pure $ unwords ["Recursor", show (nameIndex d), show_s]

            RecordType elem_tps -> pure $ unwords ["RecordType", show elem_tps]
            RecordValue elems   -> pure $ unwords ["Record", show elems]
            RecordProj e prj    -> pure $ unwords ["RecordProj", show e, Text.unpack prj]
            Sort s h
              | s == propSort -> pure $ unwords ("Prop" : map show (sortFlagsToList h))
              | otherwise     -> pure $ unwords ("Sort" : drop 5 (show s) : map show (sortFlagsToList h))
                                                        -- /\ Ugly hack to drop "sort "
            NatLit n            -> pure $ unwords ["Nat", show n]
            ArrayValue e v      -> pure $ unwords ("Array" : show e :
                                            map show (V.toList v))
            StringLit s         -> pure $ unwords ["String", show s]


-- | During parsing, we maintain various maps used for renumbering.
-- We do not reuse any such numbers that appear in the external file,
-- but generate fresh ones that are valid in the current
-- 'SharedContext'.
data ReadState =
  ReadState
  { rsTerms :: Map Int Term
    -- ^ Map 'Int' term identifiers from external core file to SAWCore terms
  , rsNames :: Map VarIndex (Either Text NameInfo)
    -- ^ Map 'VarIndex'es from external core file to global names
  , rsVars :: Map VarIndex VarIndex
    -- ^ Map 'VarIndex'es from external core file to variables
  }

type ReadM = State.StateT ReadState IO

scReadExternal :: SharedContext -> String -> IO Raw.Term
scReadExternal sc input = rawTerm <$> scReadExternalTyped sc input

scReadExternalTyped :: SharedContext -> String -> IO Term
scReadExternalTyped sc input =
  case lines input of
    ( (words -> ["SAWCoreTerm", final]) : nmlist : rows ) ->
      case readNames nmlist of
        Nothing -> fail "scReadExternal: failed to parse name table"
        Just nms ->
          State.evalStateT (mapM_ (go . words) rows >> readIdx final) (ReadState Map.empty nms Map.empty)

    _ -> fail "scReadExternal: failed to parse input file"
  where
    go :: [String] -> ReadM ()
    go (tok : tokens) =
      do i <- readM tok
         t <- parse tokens
         State.modify $ \s -> s { rsTerms = Map.insert i t (rsTerms s) }
    go [] = pure () -- empty lines are ignored

    readM :: forall a. Read a => String -> ReadM a
    readM tok =
      case readMaybe tok of
        Nothing -> fail $ "scReadExternal: parse error: " ++ show tok
        Just x -> pure x

    getTerm :: Int -> ReadM Term
    getTerm i =
      do ts <- State.gets rsTerms
         case Map.lookup i ts of
           Nothing -> fail $ "scReadExternal: invalid term index: " ++ show i
           Just t -> pure t

    readIdx :: String -> ReadM Term
    readIdx tok = getTerm =<< readM tok

    readName' :: VarIndex -> ReadM Name
    readName' vi =
      do nms <- State.gets rsNames
         vs <- State.gets rsVars
         nmi <- case Map.lookup vi nms of
                  Just (Right nmi) -> pure nmi
                  _ -> lift $ fail $ "scReadExternal: Name missing name info: " ++ show vi
         case nmi of
           ModuleIdentifier ident ->
             lift (scResolveNameByURI sc (moduleIdentToURI ident)) >>= \case
               Just vi' -> pure (Name vi' nmi)
               Nothing  -> lift $ fail $ "scReadExternal: missing module identifier: " ++ show ident
           ImportedName uri _aliases ->
             lift (scResolveNameByURI sc uri) >>= \case
               Just vi' -> pure (Name vi' nmi)
               Nothing -> case Map.lookup vi vs of
                 Just vi' -> pure $ Name vi' nmi
                 Nothing ->
                   do nm <- lift $ scRegisterName sc nmi
                      State.modify $ \s -> s { rsVars = Map.insert vi (nameIndex nm) (rsVars s) }
                      pure nm

    readName :: String -> ReadM Name
    readName i =
      do vi <- readM i
         readName' vi

    readVarName' :: VarIndex -> ReadM VarName
    readVarName' vi =
      do nms <- State.gets rsNames
         vs <- State.gets rsVars
         case Map.lookup vi nms of
           Just (Left x) ->
             case Map.lookup vi vs of
               Just vi' -> pure (VarName vi' x)
               Nothing ->
                 do vn <- lift $ scFreshVarName sc x
                    State.modify $ \s -> s { rsVars = Map.insert vi (vnIndex vn) (rsVars s) }
                    pure vn
           _ -> lift $ fail $ "scReadExternal: VarName missing name: " ++ show vi

    readVarName :: String -> ReadM VarName
    readVarName i =
      do vi <- readM i
         readVarName' vi

    parse :: [String] -> ReadM Term
    parse tokens =
      case tokens of
        ["App", e1, e2]     -> do t1 <- readIdx e1
                                  t2 <- readIdx e2
                                  lift $ scApply sc t1 t2
        ["Lam", s, e1, e2]  -> do x <- readVarName s
                                  t1 <- readIdx e1
                                  t2 <- readIdx e2
                                  lift $ scLambda sc x t1 t2
        ["Pi", s, e1, e2]   -> do x <- readVarName s
                                  t1 <- readIdx e1
                                  t2 <- readIdx e2
                                  lift $ scPi sc x t1 t2
        ["Constant", i]     -> do nm <- readName i
                                  lift $ scConstant sc nm
        ["Unit"]            -> lift $ scUnitValue sc
        ["UnitT"]           -> lift $ scUnitType sc
        ["Pair", e1, e2]    -> do t1 <- readIdx e1
                                  t2 <- readIdx e2
                                  lift $ scPairValue sc t1 t2
        ["PairT", e1, e2]   -> do t1 <- readIdx e1
                                  t2 <- readIdx e2
                                  lift $ scPairType sc t1 t2
        ["ProjL", e1]       -> do t1 <- readIdx e1
                                  lift $ scPairLeft sc t1
        ["ProjR", e1]       -> do t1 <- readIdx e1
                                  lift $ scPairRight sc t1

        ["Recursor", i, s]  ->
          do nm <- readName i
             s' <- if s == "Prop" then pure propSort else mkSort <$> readM s
             lift $ scRecursor sc nm s'

        ["RecordType", elem_tps]
                            -> do ts <- traverse (traverse getTerm) =<< readM elem_tps
                                  lift $ scRecordType sc ts
        ["Record", elems]   -> do ts <- traverse (traverse getTerm) =<< readM elems
                                  lift $ scRecordValue sc ts
        ["RecordProj", e, prj]
                            -> do t <- readIdx e
                                  lift $ scRecordProj sc t (Text.pack prj)
        ("Prop" : h)        -> do flags <- sortFlagsFromList <$> mapM readM h
                                  lift $ scSort' sc propSort flags
        ("Sort" : s : h)    -> do s' <- mkSort <$> readM s
                                  flags <- sortFlagsFromList <$> mapM readM h
                                  lift $ scSort' sc s' flags
        ["Nat", n]          -> do n' <- readM n
                                  lift $ scNat sc n'
        ("Array" : e : es)  -> do t <- readIdx e
                                  ts <- traverse readIdx es
                                  lift $ scVector sc t ts
        ("String" : ts)     -> do str <- readM (unwords ts)
                                  lift $ scString sc str
        ["Variable", i, t]  -> do vn <- readVarName i
                                  tp <- readIdx t
                                  lift $ scVariable sc vn tp
        _ -> fail $ "Parse error: " ++ unwords tokens
