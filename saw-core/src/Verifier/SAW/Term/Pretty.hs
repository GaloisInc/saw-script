{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : Verifier.SAW.Term.Pretty
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.Term.Pretty
  ( PPOpts(..)
  , defaultPPOpts
  , depthPPOpts
  , ppNat
  , ppTerm
  , showTerm
  , scPrettyTerm
  , scPrettyTermInCtx
  , ppTermDepth
  , PPModule(..), PPDecl(..)
  , ppPPModule
  ) where

import Data.Maybe (isJust)
import Control.Monad.Reader
import Control.Monad.State.Strict as State
#if !MIN_VERSION_base(4,8,0)
import Data.Foldable (Foldable)
#endif
import qualified Data.Foldable as Fold
import qualified Data.Vector as V
import Numeric (showIntAtBase)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as PPL ((<$>))

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

import Verifier.SAW.Term.Functor


--------------------------------------------------------------------------------
-- * Pretty-Printing Options and Precedences
--------------------------------------------------------------------------------

-- | Global options for pretty-printing
data PPOpts = PPOpts { ppBase :: Int
                     , ppColor :: Bool
                     , ppShowLocalNames :: Bool
                     , ppMaxDepth :: Maybe Int }

-- | Default options for pretty-printing
defaultPPOpts :: PPOpts
defaultPPOpts = PPOpts { ppBase = 10, ppColor = False,
                         ppShowLocalNames = True, ppMaxDepth = Nothing }

-- | Options for printing with a maximum depth
depthPPOpts :: Int -> PPOpts
depthPPOpts max_d = defaultPPOpts { ppMaxDepth = Just max_d }

-- | Test if a depth is "allowed", meaning not greater than the max depth
depthAllowed :: PPOpts -> Int -> Bool
depthAllowed (PPOpts { ppMaxDepth = Just max_d }) d = d < max_d
depthAllowed _ _ = True

-- | Precedence levels, each of which corresponds to a parsing nonterminal
data Prec
  = PrecNone   -- ^ Nonterminal 'Term'
  | PrecLambda -- ^ Nonterminal 'LTerm'
  | PrecProd   -- ^ Nonterminal 'ProductTerm'
  | PrecApp    -- ^ Nonterminal 'AppTerm'
  | PrecArg    -- ^ Nonterminal 'AtomTerm'

-- | Test if the first precedence "contains" the second, meaning that terms at
-- the latter precedence level can be printed in the context of the former
-- without parentheses.
--
-- NOTE: we write this explicitly here, instead of generating it from an 'Ord'
-- instance, so that readers of this code understand it and know what it is.
precContains :: Prec -> Prec -> Bool
precContains _ PrecArg = True
precContains PrecArg _ = False
precContains _ PrecApp = True
precContains PrecApp _ = False
precContains _ PrecProd = True
precContains PrecProd _ = False
precContains _ PrecLambda = True
precContains PrecLambda _ = False
precContains PrecNone PrecNone = True

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
ppParensPrec :: Prec -> Prec -> Doc -> Doc
ppParensPrec p1 p2 d
  | precContains p1 p2 = d
  | otherwise = parens $ align d


----------------------------------------------------------------------
-- * Local Variable Namings
----------------------------------------------------------------------

-- | Local variable namings, which map each deBruijn index in scope to a unique
-- string to be used to print it. This mapping is given by position in a list.
newtype VarNaming = VarNaming [String]

-- | The empty local variable context
emptyVarNaming :: VarNaming
emptyVarNaming = VarNaming []

-- | Look up a string to use for a variable, if the first argument is 'True', or
-- just print the variable number if the first argument is 'False'
lookupVarName :: Bool -> VarNaming -> DeBruijnIndex -> String
lookupVarName True (VarNaming names) i
  | i >= length names = '!' : show (i - length names)
lookupVarName True (VarNaming names) i = names!!i
lookupVarName False _ i = '!' : show i

-- | Generate a fresh name from a base name that does not clash with any names
-- already in a given list, unless it is "_", in which case return it as is
freshName :: [String] -> String -> String
freshName used name
  | name == "_" = name
  | elem name used = freshName used (name ++ "'")
  | otherwise = name

-- | Add a new variable with the given base name to the local variable list,
-- returning both the fresh name actually used and the new variable list. As a
-- special case, if the base name is "_", it is not modified.
consVarNaming :: VarNaming -> String -> (String, VarNaming)
consVarNaming (VarNaming names) name =
  let nm = freshName names name in (nm, VarNaming (nm : names))


--------------------------------------------------------------------------------
-- * Pretty-printing monad
--------------------------------------------------------------------------------

-- | Memoization variables, which are like deBruijn index variables but for
-- terms that we are memoizing during printing
type MemoVar = Int

-- | The local state used by pretty-printing computations
data PPState =
  PPState
  {
    -- | The global pretty-printing options
    ppOpts :: PPOpts,
    -- | The current depth of printing
    ppDepth :: Int,
    -- | The current naming for the local variables
    ppNaming :: VarNaming,
    -- | The next "memoization variable" to generate
    ppNextMemoVar :: MemoVar,
    -- | Memoization table for the global, closed terms, mapping term indices to
    -- "memoization variables" that are in scope
    ppGlobalMemoTable :: IntMap MemoVar,
    -- | Memoization table for terms at the current binding level, mapping term
    -- indices to "memoization variables" that are in scope
    ppLocalMemoTable :: IntMap MemoVar
  }

emptyPPState :: PPOpts -> PPState
emptyPPState opts =
  PPState { ppOpts = opts, ppDepth = 0, ppNaming = emptyVarNaming,
            ppNextMemoVar = 1, ppGlobalMemoTable = IntMap.empty,
            ppLocalMemoTable = IntMap.empty }

-- | The pretty-printing monad
newtype PPM a = PPM (Reader PPState a)
              deriving (Functor, Applicative, Monad)

-- | Run a pretty-printing computation in a top-level, empty context
runPPM :: PPOpts -> PPM a -> a
runPPM opts (PPM m) = runReader m $ emptyPPState opts

instance MonadReader PPState PPM where
  ask = PPM ask
  local f (PPM m) = PPM $ local f m

-- | Color a document, using the supplied function (1st argument), if the
-- 'ppColor' option is set
maybeColorM :: (Doc -> Doc) -> Doc -> PPM Doc
maybeColorM f d =
  (ppColor <$> ppOpts <$> ask) >>= \b ->
  return ((if b then f else id) d)

-- | Look up the given local variable by deBruijn index to get its name
varLookupM :: DeBruijnIndex -> PPM String
varLookupM idx =
  lookupVarName <$> (ppShowLocalNames <$> ppOpts <$> ask)
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
withBoundVarM :: String -> PPM a -> PPM (String, a)
withBoundVarM basename m =
  do st <- ask
     let (var, naming) = consVarNaming (ppNaming st) basename
     ret <- local (\_ -> st { ppNaming = naming,
                              ppLocalMemoTable = IntMap.empty }) m
     return (var, ret)

-- | Run a computation in the context of a fresh "memoization variable" that is
-- bound to the given term index, passing the new memoization variable to the
-- computation. If the flag is true, use the global table, otherwise use the
-- local table.
withMemoVar :: Bool -> TermIndex -> (MemoVar -> PPM a) -> PPM a
withMemoVar global_p idx f =
  do memo_var <- ppNextMemoVar <$> ask
     local (\s -> add_to_table global_p memo_var s) (f memo_var)
       where
         add_to_table True v st =
           st { ppNextMemoVar = v + 1,
                ppGlobalMemoTable = IntMap.insert idx v (ppGlobalMemoTable st) }
         add_to_table False v st =
           st { ppNextMemoVar = v + 1,
                ppLocalMemoTable = IntMap.insert idx v (ppLocalMemoTable st) }


--------------------------------------------------------------------------------
-- * The Pretty-Printing of Specific Constructs
--------------------------------------------------------------------------------

(<<$>>) :: Doc -> Doc -> Doc
x <<$>> y = (PPL.<$>) x y

-- | Pretty-print an identifier
ppIdent :: Ident -> Doc
ppIdent i = text (show i)

-- | Pretty-print an integer in the correct base
ppNat :: PPOpts -> Integer -> Doc
ppNat (PPOpts{..}) i
  | ppBase > 36 = integer i
  | otherwise = prefix <> text value
  where
    prefix = case ppBase of
      2  -> text "0b"
      8  -> text "0o"
      10 -> empty
      16 -> text "0x"
      _  -> text "0"  <> char '<' <> int ppBase <> char '>'

    value  = showIntAtBase (toInteger ppBase) (digits !!) i ""
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"

-- | Pretty-print a memoization variable
ppMemoVar :: MemoVar -> Doc
ppMemoVar mv = text "x@" <> integer (toInteger mv)

-- | Pretty-print a type constraint (also known as an ascription) @x : tp@
ppTypeConstraint :: Doc -> Doc -> Doc
ppTypeConstraint x tp =
  hang 2 $ group (x <<$>> text ":" <+> tp)

-- | Pretty-print an application to 0 or more arguments at the given precedence
ppAppList :: Prec -> Doc -> [Doc] -> Doc
ppAppList _ f [] = f
ppAppList p f args = ppParensPrec p PrecApp $ group $ hang 2 $ vsep (f : args)

-- | Pretty-print "let x1 = t1 ... xn = tn in body"
ppLetBlock :: [(MemoVar,Doc)] -> Doc -> Doc
ppLetBlock defs body =
  text "let" <+> lbrace <+> align (vcat (map ppEqn defs)) <$$>
  indent 4 rbrace <$$>
  text " in" <+> body
  where
    ppEqn (var,d) = ppMemoVar var <+> char '=' <+> d


-- | Pretty-print pairs as "(x, y)"
ppPair :: Prec -> Doc -> Doc -> Doc
ppPair prec x y = ppParensPrec prec PrecNone (group (x <> char ',' <$$> y))

-- | Pretty-print pair types as "x * y"
ppPairType :: Prec -> Doc -> Doc -> Doc
ppPairType prec x y = ppParensPrec prec PrecProd (x <+> char '*' <+> y)

-- | Pretty-print records (if the flag is 'False') or record types (if the flag
-- is 'True'), where the latter are preceded by the string @#@, either as:
--
-- * @(val1, val2, .., valn)@, if the record represents a tuple; OR
--
-- * @{ fld1 op val1, ..., fldn op valn }@ otherwise, where @op@ is @::@ for
--   types and @=@ for values.
ppRecord :: Bool -> [(String,Doc)] -> Doc
ppRecord type_p alist =
  (if type_p then (char '#' <>) else id) $
  encloseSep lbrace rbrace comma $ map ppField alist
  where
    ppField (fld, rhs) = group (nest 2 (text fld <+> text op_str <<$>> rhs))
    op_str = if type_p then ":" else "="

-- | Pretty-print a projection / selector "x.f"
ppProj :: String -> Doc -> Doc
ppProj sel doc = doc <> char '.' <> text sel

-- | Pretty-print an array value @[v1, ..., vn]@
ppArrayValue :: [Doc] -> Doc
ppArrayValue = list

-- | Pretty-print a lambda abstraction as @\(x :: tp) -> body@, where the
-- variable name to use for @x@ is bundled with @body@
ppLambda :: Doc -> (String, Doc) -> Doc
ppLambda tp (name, body) =
  group $ hang 2 $
  text "\\" <> parens (ppTypeConstraint (text name) tp)
  <+> text "->" PPL.<$> body

-- | Pretty-print a pi abstraction as @(x :: tp) -> body@, or as @tp -> body@ if
-- @x == "_"@
ppPi :: Doc -> (String, Doc) -> Doc
ppPi tp (name, body) = lhs <<$>> text "->" <+> body
  where
    lhs = if name == "_" then tp else parens (ppTypeConstraint (text name) tp)

-- | Pretty-print a definition @d :: tp = body@
ppDef :: Doc -> Doc -> Maybe Doc -> Doc
ppDef d tp Nothing = ppTypeConstraint d tp
ppDef d tp (Just body) = ppTypeConstraint d tp <+> equals <+> body

-- | Pretty-print a datatype declaration of the form
-- > data d (p1:tp1) .. (pN:tpN) : tp where {
-- >   c1 (x1_1:tp1_1)  .. (x1_N:tp1_N) : tp1
-- >   ...
-- > }
ppDataType :: Ident -> (Doc, ((Doc,Doc), [Doc])) -> Doc
ppDataType d (params, ((d_ctx,d_tp), ctors)) =
  group $ (group
           ((text "data" <+> ppIdent d <+> params <+> text ":" <+>
             (d_ctx <+> text "->" <+> d_tp))
            <<$>> (text "where" <+> lbrace)))
          <<$>>
          vcat (map (<> semi) ctors)
          <$$>
          rbrace


--------------------------------------------------------------------------------
-- * Pretty-Printing Terms
--------------------------------------------------------------------------------

-- | Pretty-print a built-in atomic construct
ppFlatTermF :: Prec -> FlatTermF Term -> PPM Doc
ppFlatTermF prec tf =
  case tf of
    GlobalDef i   -> return $ ppIdent i
    UnitValue     -> return $ text "(-empty-)"
    UnitType      -> return $ text "#(-empty-)"
    PairValue x y -> ppPair prec <$> ppTerm' PrecLambda x <*> ppTerm' PrecNone y
    PairType x y  -> ppPairType prec <$> ppTerm' PrecApp x <*> ppTerm' PrecProd y
    PairLeft t    -> ppProj "1" <$> ppTerm' PrecArg t
    PairRight t   -> ppProj "2" <$> ppTerm' PrecArg t

    CtorApp c params args ->
      ppAppList prec (ppIdent c) <$> mapM (ppTerm' PrecArg) (params ++ args)
    DataTypeApp dt params args ->
      ppAppList prec (ppIdent dt) <$> mapM (ppTerm' PrecArg) (params ++ args)
    RecursorApp d params p_ret cs_fs ixs arg ->
      do params_pp <- mapM (ppTerm' PrecArg) params
         p_ret_pp <- ppTerm' PrecArg p_ret
         fs_pp <- mapM (ppTerm' PrecNone . snd) cs_fs
         ixs_pp <- mapM (ppTerm' PrecArg) ixs
         arg_pp <- ppTerm' PrecArg arg
         return $
           ppAppList prec (ppIdent d <> text "#rec")
           (params_pp ++ [p_ret_pp] ++
            [tupled $
             zipWith (\(c,_) f_pp -> ppIdent c <<$>> text "=>" <<$>> f_pp)
             cs_fs fs_pp]
            ++ ixs_pp ++ [arg_pp])
    RecordType alist ->
      ppRecord True <$> mapM (\(fld,t) -> (fld,) <$> ppTerm' PrecNone t) alist
    RecordValue alist ->
      ppRecord False <$> mapM (\(fld,t) -> (fld,) <$> ppTerm' PrecNone t) alist
    RecordProj e fld -> ppProj fld <$> ppTerm' PrecArg e
    Sort s -> return $ text (show s)
    NatLit i -> ppNat <$> (ppOpts <$> ask) <*> return (toInteger i)
    ArrayValue _ args   ->
      ppArrayValue <$> mapM (ppTerm' PrecNone) (V.toList args)
    StringLit s -> return $ text (show s)
    ExtCns cns -> maybeColorM dullred $ text $ ecName cns


-- | Pretty-print a non-shared term
ppTermF :: Prec -> TermF Term -> PPM Doc
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
ppTermF _ (LocalVar x) = (text <$> varLookupM x) >>= maybeColorM dullgreen
ppTermF _ (Constant ec _) = maybeColorM dullblue $ text $ ecName ec


-- | Internal function to recursively pretty-print a term
ppTerm' :: Prec -> Term -> PPM Doc
ppTerm' prec = atNextDepthM (text "...") . ppTerm'' where
  ppTerm'' (Unshared tf) = ppTermF prec tf
  ppTerm'' (STApp {stAppIndex = idx, stAppTermF = tf}) =
    do maybe_memo_var <- memoLookupM idx
       case maybe_memo_var of
         Just memo_var -> return $ ppMemoVar memo_var
         Nothing -> ppTermF prec tf


--------------------------------------------------------------------------------
-- * Memoization Tables and Dealing with Binders in Terms
--------------------------------------------------------------------------------

-- | An occurrence map maps each shared term index to its term and how many
-- times that term occurred
type OccurrenceMap = IntMap (Term, Int)

-- | Returns map that associates each term index appearing in the term to the
-- number of occurrences in the shared term. Subterms that are on the left-hand
-- side of an application are excluded. (FIXME: why?) The boolean flag indicates
-- whether to descend under lambdas and other binders.
scTermCount :: Bool -> Term -> OccurrenceMap
scTermCount doBinders t0 = execState (go [t0]) IntMap.empty
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
        argsAndSubterms (unwrapTermF -> App f arg) = arg : argsAndSubterms f
        argsAndSubterms h =
          case unwrapTermF h of
            Lambda _ t1 _ | not doBinders -> [t1]
            Pi _ t1 _     | not doBinders -> [t1]
            Constant{}                    -> []
            tf                            -> Fold.toList tf

-- | Return true if the printing of the given term should be memoized; we do not
-- want to memoize the printing of terms that are "too small"
shouldMemoizeTerm :: Term -> Bool
shouldMemoizeTerm t =
  case unwrapTermF t of
    FTermF GlobalDef{} -> False
    FTermF UnitValue -> False
    FTermF UnitType -> False
    FTermF (CtorApp _ [] []) -> False
    FTermF (DataTypeApp _ [] []) -> False
    FTermF Sort{} -> False
    FTermF NatLit{} -> False
    FTermF (ArrayValue _ v) | V.length v == 0 -> False
    FTermF StringLit{} -> False
    FTermF ExtCns{} -> False
    LocalVar{} -> False
    _ -> True

-- | Compute a memoization table for a term, and pretty-print the term using the
-- table to memoize the printing. Also print the table itself as a sequence of
-- let-bindings for the entries in the memoization table. If the flag is true,
-- compute a global table, otherwise compute a local table.
ppTermWithMemoTable :: Prec -> Bool -> Term -> PPM Doc
ppTermWithMemoTable prec global_p trm = ppLets occ_map_elems [] where

  -- Generate an occurrence map for trm, filtering out terms that only occur
  -- once, that are "too small" to memoize, and, for the global table, terms
  -- that are not closed
  occ_map_elems =
    IntMap.assocs $
    IntMap.filter
    (\(t,cnt) ->
      cnt > 1 && shouldMemoizeTerm t &&
      (if global_p then looseVars t == emptyBitSet else True)) $
    scTermCount global_p trm

  -- For each (TermIndex, Term) pair in the occurrence map, pretty-print the
  -- Term and then add it to the memoization table of subsequent printing. The
  -- pretty-printing of these terms is reverse-accumulated in the second
  -- list. Finally, print trm with a let-binding for the bound terms.
  ppLets :: [(TermIndex, (Term, Int))] -> [(MemoVar,Doc)] -> PPM Doc

  -- Special case: don't print let-binding if there are no bound vars
  ppLets [] [] = ppTerm' prec trm
  -- When we have run out of (idx,term) pairs, pretty-print a let binding for
  -- all the accumulated bindings around the term
  ppLets [] bindings = ppLetBlock (reverse bindings) <$> ppTerm' prec trm
  -- To add an (idx,term) pair, first check if idx is already bound, and, if
  -- not, add a new MemoVar bind it to idx
  ppLets ((idx, (t_rhs,_)):idxs) bindings =
    do isBound <- isJust <$> memoLookupM idx
       if isBound then ppLets idxs bindings else
         do doc_rhs <- ppTerm' prec t_rhs
            withMemoVar global_p idx $ \memo_var ->
              ppLets idxs ((memo_var, doc_rhs):bindings)


-- | Pretty-print a term inside a binder for a variable of the given name,
-- returning both the result of pretty-printing and the fresh name actually used
-- for the newly bound variable. If the variable occurs in the term, then do not
-- use an underscore for it, and use "_x" instead.
--
-- Also, pretty-print let-bindings around the term for all subterms that occur
-- more than once at the same binding level.
ppTermInBinder :: Prec -> String -> Term -> PPM (String, Doc)
ppTermInBinder prec basename trm =
  let nm = if basename == "_" && inBitSet 0 (looseVars trm) then "_x"
           else basename in
  withBoundVarM nm $ ppTermWithMemoTable prec False trm

-- | Run a pretty-printing computation inside a context that binds zero or more
-- variables, returning the result of the computation and also the
-- pretty-printing of the context. Note: we do not use any local memoization
-- tables for the inner computation; the justification is that this function is
-- only used for printing datatypes, which we assume are not very big.
ppWithBoundCtx :: [(String, Term)] -> PPM a -> PPM (Doc, a)
ppWithBoundCtx [] m = (empty ,) <$> m
ppWithBoundCtx ((x,tp):ctx) m =
  (\tp_d (x', (ctx_d, ret)) ->
    (parens (ppTypeConstraint (text x') tp_d) <+> ctx_d, ret))
  <$> ppTerm' PrecNone tp <*> withBoundVarM x (ppWithBoundCtx ctx m)

-- | Pretty-print a term, also adding let-bindings for all subterms that occur
-- more than once at the same binding level
ppTerm :: PPOpts -> Term -> Doc
ppTerm opts trm = runPPM opts $ ppTermWithMemoTable PrecNone True trm

-- | Pretty-print a term, but only to a maximum depth
ppTermDepth :: Int -> Term -> Doc
ppTermDepth depth t = ppTerm (depthPPOpts depth) t

-- | Pretty-print a term and render it to a string, using the given options
scPrettyTerm :: PPOpts -> Term -> String
scPrettyTerm opts t =
  flip displayS "" $ renderPretty 0.8 80 $ ppTerm opts t

-- | Like 'scPrettyTerm', but also supply a context of bound names, where the
-- most recently-bound variable is listed first in the context
scPrettyTermInCtx :: PPOpts -> [String] -> Term -> String
scPrettyTermInCtx opts ctx trm =
  flip displayS "" $ renderPretty 0.8 80 $ runPPM opts $
  flip (Fold.foldl' (\m x -> snd <$> withBoundVarM x m)) ctx $
  ppTermWithMemoTable PrecNone False trm


-- | Pretty-print a term and render it to a string
showTerm :: Term -> String
showTerm t = scPrettyTerm defaultPPOpts t


--------------------------------------------------------------------------------
-- * Pretty-printers for Modules and Top-level Constructs
--------------------------------------------------------------------------------

-- | Datatype for representing modules in pretty-printer land. We do not want to
-- make the pretty-printer dependent on @Verifier.SAW.Module@, so we instead
-- have that module translate to this representation.
data PPModule = PPModule [ModuleName] [PPDecl]

data PPDecl
  = PPTypeDecl Ident [(String,Term)] [(String,Term)] Sort [(Ident,Term)]
  | PPDefDecl Ident Term (Maybe Term)

-- | Pretty-print a 'PPModule'
ppPPModule :: PPOpts -> PPModule -> Doc
ppPPModule opts (PPModule importNames decls) =
  vcat $ concat $ fmap (map (<> line)) $
  [ map ppImport importNames
  , map (runPPM opts . ppDecl) decls
  ]
  where
    ppImport nm = text $ "import " ++ show nm
    ppDecl (PPTypeDecl dtName dtParams dtIndices dtSort dtCtors) =
      ppDataType dtName <$> ppWithBoundCtx dtParams
      ((,) <$>
       ppWithBoundCtx dtIndices (return $ text $ show dtSort) <*>
       mapM (\(ctorName,ctorType) ->
              ppTypeConstraint (ppIdent ctorName) <$>
              ppTerm' PrecNone ctorType)
       dtCtors)
    ppDecl (PPDefDecl defIdent defType defBody) =
      ppDef (ppIdent defIdent) <$> ppTerm' PrecNone defType <*>
      case defBody of
        Just body -> Just <$> ppTerm' PrecNone body
        Nothing -> return Nothing
