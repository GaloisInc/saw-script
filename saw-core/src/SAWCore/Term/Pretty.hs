{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternGuards #-}

{- |
Module      : SAWCore.Term.Pretty
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Term.Pretty
  ( ppTerm
  , ppTermInCtx
  , showTerm
  , scPrettyTerm
  , scPrettyTermInCtx
  , ppTermWithNames
  , showTermWithNames
  , scTermCount
  , shouldMemoizeTerm
  , ppName
  , ppTermContainerWithNames
  ) where

import Data.Char (intToDigit, isDigit)
import Data.Maybe (isJust)
import Control.Monad (forM)
import Control.Monad.Reader (MonadReader(..), Reader, asks, runReader)
import Control.Monad.State.Strict (MonadState(..), State, evalState, execState, get, modify)
import qualified Data.Foldable as Fold
import Data.Hashable (hash)
import qualified Data.Text as Text
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Numeric (showHex)
import Prettyprinter
import Text.URI

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import SAWSupport.Pretty (prettyNat, prettyTypeConstraint)
import qualified SAWSupport.Pretty as PPS (
    Style(..), Doc, MemoStyle(..), Opts(..), defaultOpts, render
 )

import SAWCore.Panic (panic)
import SAWCore.Name
import SAWCore.Term.Functor
import SAWCore.Recognizer


-- | Test if a depth is "allowed", meaning not greater than the max depth
depthAllowed :: PPS.Opts -> Int -> Bool
depthAllowed (PPS.Opts { ppMaxDepth = Just max_d }) d = d < max_d
depthAllowed _ _ = True

-- | Precedence levels, each of which corresponds to a parsing nonterminal
data Prec
  = PrecCommas -- ^ Nonterminal @sepBy(Term, \',\')@
  | PrecTerm   -- ^ Nonterminal @Term@
  | PrecLambda -- ^ Nonterminal @LTerm@
  | PrecProd   -- ^ Nonterminal @ProdTerm@
  | PrecApp    -- ^ Nonterminal @AppTerm@
  | PrecArg    -- ^ Nonterminal @AtomTerm@
  deriving (Eq, Ord)

-- | Test if the first precedence "contains" the second, meaning that terms at
-- the latter precedence level can be printed in the context of the former
-- without parentheses.
precContains :: Prec -> Prec -> Bool
precContains x y = x <= y

-- | Optionally print parentheses around a document, iff the incoming, outer
-- precedence (listed first) contains (as in 'precContains') the required
-- precedence (listed second) for printing the given document.
--
-- Stated differently: @ppParensPrec p1 p2 d@ means we are pretty-printing in a
-- term context that requires precedence @p1@, but @d@ was pretty-printed at
-- precedence level @p2@. If @p1@ does not contain @p2@ (e.g., if @p1@ is
-- 'PrecArg', meaning we are pretty-printing the argument of an application, and
-- @p2@ is 'PrecLambda', meaning the construct we are pretty-printing is a
-- lambda or pi abstraction) then add parentheses.
ppParensPrec :: Prec -> Prec -> PPS.Doc -> PPS.Doc
ppParensPrec p1 p2 d
  | precContains p1 p2 = d
  | otherwise = parens $ align d


----------------------------------------------------------------------
-- * Local Variable Namings
----------------------------------------------------------------------

-- | Local variable namings, which map each deBruijn index in scope to a unique
-- string to be used to print it. This mapping is given by position in a list.
-- Renamings for named variables are in an 'IntMap' indexed by 'VarIndex'.
-- The third argument caches the set of all used or reserved names;
-- fresh 'LocalName's are chosen while avoiding names in this set.
data VarNaming = VarNaming [LocalName] (IntMap LocalName) (Set LocalName)

-- | The empty local variable context
emptyVarNaming :: Set LocalName -> VarNaming
emptyVarNaming reserved = VarNaming [] IntMap.empty reserved

-- | Look up a string to use for a 'DeBruijnIndex', if the first
-- argument is 'True', or just print the variable number if the first
-- argument is 'False'.
lookupDeBruijn :: Bool -> VarNaming -> DeBruijnIndex -> LocalName
lookupDeBruijn True (VarNaming names _ _) i
  | i >= length names = Text.pack ('!' : show (i - length names))
lookupDeBruijn True (VarNaming names _ _) i = names!!i
lookupDeBruijn False _ i = Text.pack ('!' : show i)

-- | Look up a string to use for a 'VarName'.
lookupVarName :: VarNaming -> VarName -> LocalName
lookupVarName (VarNaming _ renames _) vn =
  case IntMap.lookup (vnIndex vn) renames of
    Just alias -> alias
    Nothing -> vnName vn

-- | Generate a fresh name from a base name that does not clash with any names
-- already in a given list, unless it is "_", in which case return it as is
freshName :: Set LocalName -> LocalName -> LocalName
freshName used name
  | name == "_" = name
  | Set.member name used = freshName used (nextName name)
  | otherwise = name

-- | Generate a variant of a name by incrementing the number at the
-- end, or appending the number 1 if there is none.
nextName :: LocalName -> LocalName
nextName = Text.pack . reverse . go . reverse . Text.unpack
  where
    go :: String -> String
    go (c : cs)
      | c == '9'  = '0' : go cs
      | isDigit c = succ c : cs
    go cs = '1' : cs

-- | Add a new variable with the given base name to the local variable list,
-- returning both the fresh name actually used and the new variable list. As a
-- special case, if the base name is "_", it is not modified.
consVarNaming :: VarNaming -> LocalName -> (LocalName, VarNaming)
consVarNaming (VarNaming names renames used) name =
  let nm = freshName used name
  in (nm, VarNaming (nm : names) renames (Set.insert nm used))

-- | Add a new variable with the given 'VarName' to the 'VarNaming',
-- returning both the chosen fresh name and the new 'VarNaming'.
-- As a special case, if the base name is "_", it is not modified.
insertVarNaming :: VarNaming -> VarName -> (LocalName, VarNaming)
insertVarNaming (VarNaming names renames used) (VarName i name) =
  let nm = freshName used name
  in (nm, VarNaming names (IntMap.insert i nm renames) (Set.insert nm used))

-- | Compute the set of all free 'VarName's in a term.
termVarNames :: Term -> Set VarName
termVarNames t0 = evalState (go t0) IntMap.empty
  where
    go :: Term -> State (IntMap (Set VarName)) (Set VarName)
    go tm =
      case tm of
        Unshared tf -> termf <$> traverse go tf
        STApp { stAppIndex = i, stAppTermF = tf, stAppFreeVars = _vs } ->
          do memo <- get
             case IntMap.lookup i memo of
               Just vars -> pure vars
               Nothing ->
                 do vars <- termf <$> traverse go tf
                    modify (IntMap.insert i vars)
                    pure vars
    termf :: TermF (Set VarName) -> Set VarName
    termf tf =
      case tf of
        FTermF ftf -> Fold.fold ftf
        App e1 e2 -> Set.union e1 e2
        Lambda _ e1 e2 -> Set.union e1 e2
        Pi _ e1 e2 -> Set.union e1 e2
        LocalVar _ -> Set.empty
        Constant _ -> Set.empty
        Variable ec -> Set.insert (ecName ec) (ecType ec)

--------------------------------------------------------------------------------
-- * Pretty-printing monad
--------------------------------------------------------------------------------

-- | Memoization variables contain several pieces of information about the term
-- they bind. What subset is displayed when they're printed is governed by the
-- 'ppMemoStyle' field of 'PPS.Opts', in tandem with 'ppMemoVar'.
data MemoVar =
  MemoVar
    {
      -- | A unique value - like a deBruijn index, but evinced only during
      -- printing when a term is to be memoized.
      memoFresh :: Int,
      -- | A likely-unique value - the hash of the term this 'MemoVar'
      -- represents.
      memoHash :: Int }

-- | The local state used by pretty-printing computations
data PPState =
  PPState
  {
    -- | The global pretty-printing options
    ppOpts :: PPS.Opts,
    -- | The current depth of printing
    ppDepth :: Int,
    -- | The current naming for the local variables
    ppNaming :: VarNaming,
    -- | The top-level naming environment
    ppNamingEnv :: DisplayNameEnv,
    -- | A source of freshness for memoization variables
    ppMemoFresh :: Int,
    -- | Memoization table for the global, closed terms, mapping term indices to
    -- "memoization variables" that are in scope
    ppGlobalMemoTable :: IntMap MemoVar,
    -- | Memoization table for terms at the current binding level, mapping term
    -- indices to "memoization variables" that are in scope
    ppLocalMemoTable :: IntMap MemoVar,

    -- | Terms to not inline because they're memoized (see 'withMemoVar')
    ppNoInlineIdx :: Set TermIndex
  }

emptyPPState :: PPS.Opts -> DisplayNameEnv -> PPState
emptyPPState opts ne =
  PPState { ppOpts = opts,
            ppDepth = 0,
            ppNaming = emptyVarNaming (Map.keysSet (displayIndexes ne)),
            ppNamingEnv = ne,
            ppMemoFresh = 1,
            ppGlobalMemoTable = IntMap.empty,
            ppLocalMemoTable = IntMap.empty,
            ppNoInlineIdx = mempty
   }

-- | The pretty-printing monad
--
-- XXX: let's find a better name than PPM
newtype PPM a = PPM (Reader PPState a)
              deriving (Functor, Applicative, Monad)

-- | Run a pretty-printing computation in a top-level, empty context
runPPM :: PPS.Opts -> DisplayNameEnv -> PPM a -> a
runPPM opts ne (PPM m) = runReader m $ emptyPPState opts ne

instance MonadReader PPState PPM where
  ask = PPM ask
  local f (PPM m) = PPM $ local f m

-- | Look up the given local variable by deBruijn index to get its name
varLookupM :: DeBruijnIndex -> PPM LocalName
varLookupM idx =
  lookupDeBruijn <$> (PPS.ppShowLocalNames <$> ppOpts <$> ask)
  <*> (ppNaming <$> ask) <*> return idx

-- | Test if a given term index is memoized, returning its memoization variable
-- if so and otherwise returning 'Nothing'
memoLookupM :: TermIndex -> PPM (Maybe MemoVar)
memoLookupM idx =
  do s <- ask
     return $ case (IntMap.lookup idx (ppGlobalMemoTable s),
                    IntMap.lookup idx (ppLocalMemoTable s)) of
       (res@(Just _), _) -> res
       (_, res@(Just _)) -> res
       _ -> Nothing

-- | Run a pretty-printing computation at the next greater depth, returning the
-- default value if the max depth has been exceeded
atNextDepthM :: a -> PPM a -> PPM a
atNextDepthM dflt m =
  do s <- ask
     let new_depth = ppDepth s + 1
     if depthAllowed (ppOpts s) new_depth
       then local (\_ -> s { ppDepth = new_depth }) m
       else return dflt

-- | Run a pretty-printing computation in the context of a new bound variable,
-- also erasing the local memoization table (which is no longer valid in an
-- extended variable context) during that computation. Return the result of the
-- computation and also the name that was actually used for the bound variable.
withBoundVarM :: LocalName -> PPM a -> PPM (LocalName, a)
withBoundVarM basename m =
  do st <- ask
     let (var, naming) = consVarNaming (ppNaming st) basename
     ret <- local (\_ -> st { ppNaming = naming,
                              ppLocalMemoTable = IntMap.empty }) m
     return (var, ret)

-- | Run a pretty-printing computation in a context with an additional
-- declared 'VarName'.
withVarName :: VarName -> PPM a -> PPM a
withVarName vn =
  local (\s -> s { ppNaming = snd (insertVarNaming (ppNaming s) vn) })

-- | Run a pretty-printing computation in a context with multiple
-- additional declared 'VarName's.
withVarNames :: [VarName] -> PPM a -> PPM a
withVarNames vs m = foldr withVarName m vs

-- | Attempt to memoize the given term (index) 'termIdx' and run a computation
-- in the context that the attempt produces. If memoization succeeds, the
-- context will contain a binding (global in scope if 'global_p' is set, local
-- if not) of a fresh memoization variable to the term, and the fresh variable
-- will be supplied to the computation. If memoization fails, the context will
-- not contain such a binding, and no fresh variable will be supplied.
withMemoVar :: Bool -> TermIndex -> Int -> (Maybe MemoVar -> PPM a) -> PPM a
withMemoVar global_p termIdx termHash f =
  do
    memoFresh <- asks ppMemoFresh
    let memoVar = MemoVar { memoFresh = memoFresh, memoHash = termHash }
    memoFreshSkips <- asks (PPS.ppNoInlineMemoFresh . ppOpts)
    termIdxSkips <- asks ppNoInlineIdx
    case memoFreshSkips of
      -- Even if we must skip this memoization variable, we still want to
      -- "pretend" we memoized by calling `freshen`, so that non-inlined
      -- memoization identifiers are kept constant between two
      -- otherwise-identical terms with differing inline strategies.
      (skip:skips)
        | skip == memoFresh ->
          local (freshen . addIdxSkip . setMemoFreshSkips skips) (f Nothing)
      _
        | termIdx `Set.member` termIdxSkips -> f Nothing
        | otherwise -> local (freshen . bind memoVar) (f (Just memoVar))
  where
    bind = if global_p then bindGlobal else bindLocal

    bindGlobal memoVar PPState{ .. } =
      PPState { ppGlobalMemoTable = IntMap.insert termIdx memoVar ppGlobalMemoTable, .. }

    bindLocal memoVar PPState{ .. } =
      PPState { ppLocalMemoTable = IntMap.insert termIdx memoVar ppLocalMemoTable, .. }

    setMemoFreshSkips memoSkips PPState{ ppOpts = PPS.Opts{ .. }, .. } =
      PPState { ppOpts = PPS.Opts { ppNoInlineMemoFresh = memoSkips, ..}, ..}

    addIdxSkip PPState{ .. } =
      PPState { ppNoInlineIdx = Set.insert termIdx ppNoInlineIdx, .. }

    freshen PPState{ .. } =
      PPState { ppMemoFresh = ppMemoFresh + 1, .. }

--------------------------------------------------------------------------------
-- * The Pretty-Printing of Specific Constructs
--------------------------------------------------------------------------------

-- | Pretty-print an identifier
ppIdent :: Ident -> PPS.Doc
ppIdent = viaShow

-- | Pretty-print a memoization variable, according to 'ppMemoStyle'
ppMemoVar :: MemoVar -> PPM PPS.Doc
ppMemoVar MemoVar{..} = asks (PPS.ppMemoStyle . ppOpts) >>= \case
  PPS.Incremental ->
    pure ("x@" <> pretty memoFresh)
  PPS.Hash prefixLen ->
    pure ("x@" <> pretty (take prefixLen hashStr))
  PPS.HashIncremental prefixLen ->
    pure ("x" <> pretty memoFresh <> "@" <> pretty (take prefixLen hashStr))
  where
    hashStr = showHex (abs memoHash) ""

-- | Pretty-print an application to 0 or more arguments at the given precedence
ppAppList :: Prec -> PPS.Doc -> [PPS.Doc] -> PPS.Doc
ppAppList _ f [] = f
ppAppList p f args = ppParensPrec p PrecApp $ group $ hang 2 $ vsep (f : args)

-- | Pretty-print "let x = t ... x' = t' in body"
ppLetBlock :: [(MemoVar, PPS.Doc)] -> PPS.Doc -> PPM PPS.Doc
ppLetBlock defs body =
  do
    lets <- align . vcat <$> mapM ppEqn defs
    pure $
      vcat
        [ "let" <+> lbrace <+> lets
        , indent 4 rbrace
        , " in" <+> body
        ]
  where
    ppEqn (var,d) =
      do
        mv <- ppMemoVar var
        pure $ mv <+> pretty '=' <+> d


-- | Pretty-print pairs as "(x, y)"
ppPair :: Prec -> PPS.Doc -> PPS.Doc -> PPS.Doc
ppPair prec x y = ppParensPrec prec PrecCommas (group (vcat [x <> pretty ',', y]))

-- | Pretty-print pair types as "x * y"
ppPairType :: Prec -> PPS.Doc -> PPS.Doc -> PPS.Doc
ppPairType prec x y = ppParensPrec prec PrecProd (x <+> pretty '*' <+> y)

-- | Pretty-print records (if the flag is 'False') or record types (if the flag
-- is 'True'), where the latter are preceded by the string @#@, either as:
--
-- * @(val1, val2, .., valn)@, if the record represents a tuple; OR
--
-- * @{ fld1 op val1, ..., fldn op valn }@ otherwise, where @op@ is @::@ for
--   types and @=@ for values.
ppRecord :: Bool -> [(FieldName, PPS.Doc)] -> PPS.Doc
ppRecord type_p alist =
  (if type_p then (pretty '#' <>) else id) $
  encloseSep lbrace rbrace comma $ map ppField alist
  where
    ppField (fld, rhs) = group (nest 2 (vsep [pretty fld <+> op_str, rhs]))
    op_str = if type_p then ":" else "="

-- | Pretty-print a projection / selector "x.f"
ppProj :: FieldName -> PPS.Doc -> PPS.Doc
ppProj sel doc = doc <> pretty '.' <> pretty sel

-- | Pretty-print an array value @[v1, ..., vn]@
ppArrayValue :: [PPS.Doc] -> PPS.Doc
ppArrayValue = list

-- | Pretty-print a lambda abstraction as @\(x :: tp) -> body@, where the
-- variable name to use for @x@ is bundled with @body@
ppLambda :: PPS.Doc -> (LocalName, PPS.Doc) -> PPS.Doc
ppLambda tp (name, body) =
  group $ hang 2 $
  vsep ["\\" <> parens (prettyTypeConstraint (pretty name) tp) <+> "->", body]

-- | Pretty-print a pi abstraction as @(x :: tp) -> body@, or as @tp -> body@ if
-- @x == "_"@
ppPi :: PPS.Doc -> (LocalName, PPS.Doc) -> PPS.Doc
ppPi tp (name, body) = vsep [lhs, "->" <+> body]
  where
    lhs = if name == "_" then tp else parens (prettyTypeConstraint (pretty name) tp)


--------------------------------------------------------------------------------
-- * Pretty-Printing Terms
--------------------------------------------------------------------------------

-- | Pretty-print a built-in atomic construct
ppFlatTermF :: Prec -> FlatTermF Term -> PPM PPS.Doc
ppFlatTermF prec tf =
  case tf of
    UnitValue     -> return "(-empty-)"
    UnitType      -> return "#(-empty-)"
    PairValue x y -> ppPair prec <$> ppTerm' PrecTerm x <*> ppTerm' PrecCommas y
    PairType x y  -> ppPairType prec <$> ppTerm' PrecApp x <*> ppTerm' PrecProd y
    PairLeft t    -> ppProj "1" <$> ppTerm' PrecArg t
    PairRight t   -> ppProj "2" <$> ppTerm' PrecArg t

    RecursorType ty -> ppTerm' prec ty

    Recursor (CompiledRecursor d params motive _motiveTy cs_fs ctorOrder _ty) ->
      do params_pp <- mapM (ppTerm' PrecArg) params
         motive_pp <- ppTerm' PrecArg motive
         fs_pp <- traverse (ppTerm' PrecTerm . fst) cs_fs
         nm <- ppBestName d
         f_pps <- forM ctorOrder $ \c ->
                    do cnm <- ppBestName c
                       case Map.lookup (nameIndex c) fs_pp of
                         Just f_pp -> pure $ vsep [cnm, "=>", f_pp]
                         Nothing -> panic "ppFlatTermF" ["missing constructor in recursor: " <> Text.pack (show cnm)]
         return $
           ppAppList prec (annotate PPS.RecursorStyle (nm <> "#rec"))
             (params_pp ++ [motive_pp, tupled f_pps])

    RecursorApp r ixs ->
      do rec_pp <- ppTerm' PrecApp r
         ixs_pp <- mapM (ppTerm' PrecArg) ixs
         return $ ppAppList prec rec_pp ixs_pp

    RecordType alist ->
      ppRecord True <$> mapM (\(fld,t) -> (fld,) <$> ppTerm' PrecTerm t) alist
    RecordValue alist ->
      ppRecord False <$> mapM (\(fld,t) -> (fld,) <$> ppTerm' PrecTerm t) alist
    RecordProj e fld -> ppProj fld <$> ppTerm' PrecArg e
    Sort s h -> return (viaShow h <> viaShow s)
    NatLit i -> prettyNat <$> (ppOpts <$> ask) <*> return (toInteger i)
    ArrayValue (asBoolType -> Just _) args
      | Just bits <- mapM asBool $ V.toList args ->
        if length bits `mod` 4 == 0 then
          return $ pretty ("0x" ++ ppBitsToHex bits)
        else
          return $ pretty ("0b" ++ map (\b -> if b then '1' else '0') bits)
    ArrayValue _ args   ->
      ppArrayValue <$> mapM (ppTerm' PrecTerm) (V.toList args)
    StringLit s -> return $ viaShow s

-- | Pretty-print a big endian list of bit values as a hexadecimal number
ppBitsToHex :: [Bool] -> String
ppBitsToHex (b8:b4:b2:b1:bits') =
  intToDigit (8 * toInt b8 + 4 * toInt b4 + 2 * toInt b2 + toInt b1) :
  ppBitsToHex bits'
  where toInt True = 1
        toInt False = 0
ppBitsToHex [] = ""
ppBitsToHex bits =
  panic "ppBitsToHex" [
      "length of bit list " <> bits' <> " is not a multiple of 4"
  ]
  where bits' = Text.pack (show bits)

-- | Pretty-print an 'ExtCns' according to the current 'VarNaming'.
ppExtCns :: ExtCns e -> PPM PPS.Doc
ppExtCns ec = ppVarName (ecName ec)

-- | Pretty-print a 'VarName' according to the current 'VarNaming'.
ppVarName :: VarName -> PPM PPS.Doc
ppVarName vn =
  do naming <- asks ppNaming
     pure $ pretty (lookupVarName naming vn)

-- | Pretty-print a 'Name', using the best unambiguous alias from the
-- naming environment.
ppBestName :: Name -> PPM PPS.Doc
ppBestName nm =
  do ne <- asks ppNamingEnv
     case bestDisplayName ne (nameIndex nm) of
       Just alias -> pure $ pretty alias
       Nothing -> pure $ ppName (nameInfo nm)

ppName :: NameInfo -> PPS.Doc
ppName (ModuleIdentifier i) = ppIdent i
ppName (ImportedName absName _) = pretty (render absName)

-- | Pretty-print a non-shared term
ppTermF :: Prec -> TermF Term -> PPM PPS.Doc
ppTermF prec (FTermF ftf) = ppFlatTermF prec ftf
ppTermF prec (App e1 e2) =
  ppAppList prec <$> ppTerm' PrecApp e1 <*> mapM (ppTerm' PrecArg) [e2]
ppTermF prec (Lambda x tp body) =
  ppParensPrec prec PrecLambda <$>
  (ppLambda <$> ppTerm' PrecApp tp <*> ppTermInBinder PrecLambda x body)
ppTermF prec (Pi x tp body) =
  ppParensPrec prec PrecLambda <$>
  (ppPi <$> ppTerm' PrecApp tp <*>
   ppTermInBinder PrecLambda x body)
ppTermF _ (LocalVar x) = annotate PPS.LocalVarStyle <$> pretty <$> varLookupM x
ppTermF _ (Constant nm) = annotate PPS.ConstantStyle <$> ppBestName nm
ppTermF _ (Variable ec) = annotate PPS.ExtCnsStyle <$> ppExtCns ec


-- | Internal function to recursively pretty-print a term
ppTerm' :: Prec -> Term -> PPM PPS.Doc
ppTerm' prec = atNextDepthM "..." . ppTerm'' where
  ppTerm'' (Unshared tf) = ppTermF prec tf
  ppTerm'' (STApp {stAppIndex = idx, stAppTermF = tf}) =
    do maybe_memo_var <- memoLookupM idx
       case maybe_memo_var of
         Just memo_var -> ppMemoVar memo_var
         Nothing -> ppTermF prec tf


--------------------------------------------------------------------------------
-- * Memoization Tables and Dealing with Binders in Terms
--------------------------------------------------------------------------------

-- | An occurrence map maps each shared term index to its term and how many
-- times that term occurred
type OccurrenceMap = IntMap (Term, Int)

-- | Returns map that associates each term index appearing in the term
-- to the number of occurrences in the shared term.
-- Partially-applied functions are excluded, because let-binding such
-- subterms makes terms harder to read.
-- The boolean flag indicates whether to descend under lambdas and
-- other binders.
scTermCount :: Bool -> Term -> OccurrenceMap
scTermCount doBinders t = execState (scTermCountAux doBinders [t]) IntMap.empty

scTermCountAux :: Bool -> [Term] -> State OccurrenceMap ()
scTermCountAux doBinders = go
  where go :: [Term] -> State OccurrenceMap ()
        go [] = return ()
        go (t:r) =
          case t of
            Unshared _ -> recurse
            STApp{ stAppIndex = i } -> do
              m <- get
              case IntMap.lookup i m of
                Just (_, n) -> do
                  put $ n `seq` IntMap.insert i (t, n+1) m
                  go r
                Nothing -> do
                  put (IntMap.insert i (t, 1) m)
                  recurse
          where
            recurse = go (r ++ argsAndSubterms t)

        argsAndSubterms :: Term -> [Term]
        argsAndSubterms (asApplyAll -> (f, args)) | not (null args) = f : args
        argsAndSubterms h =
          case unwrapTermF h of
            Lambda _ t1 _ | not doBinders  -> [t1]
            Pi _ t1 _     | not doBinders  -> [t1]
            Constant{}                     -> []
            FTermF (Recursor crec)         -> recursorParams crec ++
                                              [recursorMotive crec] ++
                                              map fst (Map.elems (recursorElims crec))
            tf                             -> Fold.toList tf


-- | Return true if the printing of the given term should be memoized; we do not
-- want to memoize the printing of terms that are "too small"
shouldMemoizeTerm :: Term -> Bool
shouldMemoizeTerm t =
  case unwrapTermF t of
    FTermF UnitValue -> False
    FTermF UnitType -> False
    FTermF Sort{} -> False
    FTermF NatLit{} -> False
    FTermF (ArrayValue _ v) | V.length v == 0 -> False
    FTermF StringLit{} -> False
    Constant{} -> False
    LocalVar{} -> False
    Variable{} -> False
    _ -> True

-- | Compute a memoization table for a term, and pretty-print the term using the
-- table to memoize the printing. Also print the table itself as a sequence of
-- let-bindings for the entries in the memoization table. If the flag is true,
-- compute a global table, otherwise compute a local table.
ppTermWithMemoTable :: Prec -> Bool -> Term -> PPM PPS.Doc
ppTermWithMemoTable prec global_p trm = do
     min_occs <- PPS.ppMinSharing <$> ppOpts <$> ask
     let occPairs = IntMap.assocs $ filterOccurenceMap min_occs global_p $ scTermCount global_p trm
     ppLets global_p occPairs [] (ppTerm' prec trm)

-- Filter an occurrence map, filtering out terms that only occur
-- once, that are "too small" to memoize, and, for the global table, terms
-- that are not closed
filterOccurenceMap :: Int -> Bool -> OccurrenceMap -> OccurrenceMap
filterOccurenceMap min_occs global_p =
    IntMap.filter
      (\(t,cnt) ->
        cnt >= min_occs && shouldMemoizeTerm t &&
        (if global_p then termIsClosed t else True))


-- For each (TermIndex, Term) pair in the occurrence map, pretty-print the
-- Term and then add it to the memoization table of subsequent printing. The
-- pretty-printing of these terms is reverse-accumulated in the second
-- list. Finally, print the given base document in the context of let-bindings
-- for the bound terms.
ppLets :: Bool -> [(TermIndex, (Term, Int))] -> [(MemoVar, PPS.Doc)] -> PPM PPS.Doc -> PPM PPS.Doc

-- Special case: don't print let-binding if there are no bound vars
ppLets _ [] [] baseDoc = baseDoc

-- When we have run out of (idx,term) pairs, pretty-print a let binding for
-- all the accumulated bindings around the term
ppLets _ [] bindings baseDoc = ppLetBlock (reverse bindings) =<< baseDoc

-- To add an (idx,term) pair, first check if idx is already bound, and, if
-- not, add a new MemoVar bind it to idx
ppLets global_p ((termIdx, (term,_)):idxs) bindings baseDoc =
  do isBound <- isJust <$> memoLookupM termIdx
     if isBound then ppLets global_p idxs bindings baseDoc else
       do termDoc <- ppTerm' PrecTerm term
          withMemoVar global_p termIdx (hash term) $ \memoVarM ->
            let bindings' = case memoVarM of
                  Just memoVar -> (memoVar, termDoc):bindings
                  Nothing -> bindings
            in  ppLets global_p idxs bindings' baseDoc

-- | Pretty-print a term inside a binder for a variable of the given name,
-- returning both the result of pretty-printing and the fresh name actually used
-- for the newly bound variable. If the variable occurs in the term, then do not
-- use an underscore for it, and use "_x" instead.
--
-- Also, pretty-print let-bindings around the term for all subterms that occur
-- more than once at the same binding level.
ppTermInBinder :: Prec -> LocalName -> Term -> PPM (LocalName, PPS.Doc)
ppTermInBinder prec basename trm =
  let nm = if basename == "_" && inBitSet 0 (looseVars trm) then "_x"
           else basename in
  withBoundVarM nm $ ppTermWithMemoTable prec False trm

-- | Pretty-print a term, also adding let-bindings for all subterms that occur
-- more than once at the same binding level
ppTerm :: PPS.Opts -> Term -> PPS.Doc
ppTerm opts = ppTermWithNames opts emptyDisplayNameEnv

-- | Like 'ppTerm', but also supply a context of bound names, where the most
-- recently-bound variable is listed first in the context
ppTermInCtx :: PPS.Opts -> [LocalName] -> Term -> PPS.Doc
ppTermInCtx opts ctx trm =
  runPPM opts emptyDisplayNameEnv $
  withVarNames (Set.toList (termVarNames trm)) $
  flip (Fold.foldl' (\m x -> snd <$> withBoundVarM x m)) ctx $
  ppTermWithMemoTable PrecTerm True trm

-- | Pretty-print a term and render it to a string, using the given options
scPrettyTerm :: PPS.Opts -> Term -> String
scPrettyTerm opts t =
  PPS.render opts $ ppTerm opts t

-- | Like 'scPrettyTerm', but also supply a context of bound names, where the
-- most recently-bound variable is listed first in the context
scPrettyTermInCtx :: PPS.Opts -> [LocalName] -> Term -> String
scPrettyTermInCtx opts ctx trm =
  PPS.render opts $
  runPPM opts emptyDisplayNameEnv $
  withVarNames (Set.toList (termVarNames trm)) $
  flip (Fold.foldl' (\m x -> snd <$> withBoundVarM x m)) ctx $
  ppTermWithMemoTable PrecTerm False trm


-- | Pretty-print a term and render it to a string
showTerm :: Term -> String
showTerm t = scPrettyTerm PPS.defaultOpts t


--------------------------------------------------------------------------------
-- * Pretty-printers with naming environments
--------------------------------------------------------------------------------

-- | Pretty-print a term, also adding let-bindings for all subterms that occur
-- more than once at the same binding level
ppTermWithNames :: PPS.Opts -> DisplayNameEnv -> Term -> PPS.Doc
ppTermWithNames opts ne trm =
  runPPM opts ne $
  withVarNames (Set.toList (termVarNames trm)) $
  ppTermWithMemoTable PrecTerm True trm

showTermWithNames :: PPS.Opts -> DisplayNameEnv -> Term -> String
showTermWithNames opts ne trm =
  PPS.render opts $ ppTermWithNames opts ne trm


ppTermContainerWithNames ::
  (Traversable m) =>
  (m PPS.Doc -> PPS.Doc) ->
  PPS.Opts -> DisplayNameEnv -> m Term -> PPS.Doc
ppTermContainerWithNames ppContainer opts ne trms =
  let min_occs = PPS.ppMinSharing opts
      global_p = True
      occPairs = IntMap.assocs $
                   filterOccurenceMap min_occs global_p $
                   flip execState mempty $
                   traverse (\t -> scTermCountAux global_p [t]) $
                   trms
   in runPPM opts ne $
      withVarNames (Set.toList (Fold.foldMap termVarNames trms)) $
      ppLets global_p occPairs []
        (ppContainer <$> traverse (ppTerm' PrecTerm) trms)
