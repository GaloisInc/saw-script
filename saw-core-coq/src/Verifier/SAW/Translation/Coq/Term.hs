{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternGuards #-}

{- |
Module      : Verifier.SAW.Translation.Coq
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Translation.Coq.Term where

import           Control.Lens                                  (makeLenses, over, set, to, view)
import qualified Control.Monad.Except                          as Except
import qualified Control.Monad.Fail                            as Fail
import           Control.Monad.Reader                          hiding (fail, fix)
import           Control.Monad.State                           hiding (fail, fix, state)
import           Data.Char                                     (isDigit)
import qualified Data.IntMap                                   as IntMap
import           Data.List                                     (intersperse, sortOn)
import           Data.Maybe                                    (fromMaybe)
import qualified Data.Map                                      as Map
import qualified Data.Set                                      as Set
import qualified Data.Text                                     as Text
import           Prelude                                       hiding (fail)
import           Prettyprinter

import           Data.Parameterized.Pair
import           Data.Parameterized.NatRepr
import qualified Data.BitVector.Sized                          as BV
import qualified Data.Vector                                   as Vector (toList)
import qualified Language.Coq.AST                              as Coq
import qualified Language.Coq.Pretty                           as Coq
import           Verifier.SAW.Recognizer
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Term.Pretty
import           Verifier.SAW.Term.Functor
import           Verifier.SAW.Translation.Coq.Monad
import           Verifier.SAW.Translation.Coq.SpecialTreatment

{-
import Debug.Trace
traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

newtype TranslationReader = TranslationReader
  { _currentModule  :: Maybe ModuleName
  }
  deriving (Show)

makeLenses ''TranslationReader

data TranslationState = TranslationState

  { _globalDeclarations :: [String]
  -- ^ Some Cryptol terms seem to capture the name and body of some functions
  -- they use (whether from the Cryptol prelude, or previously defined in the
  -- same file).  We want to translate those exactly once, so we need to keep
  -- track of which ones have already been translated.

  , _topLevelDeclarations :: [Coq.Decl]
  -- ^ Because some terms capture their dependencies, translating one term may
  -- result in multiple declarations: one for the term itself, but also zero or
  -- many for its dependencies.  We store all of those in this, so that a caller
  -- of the translation may retrieve all the declarations needed to translate
  -- the term.  The translation function itself will return only the declaration
  -- for the term being translated.

  , _localEnvironment  :: [Coq.Ident]
  -- ^ The list of Coq identifiers for de Bruijn-indexed local
  -- variables, innermost (index 0) first.

  , _unavailableIdents :: Set.Set Coq.Ident
  -- ^ The set of Coq identifiers that are either reserved or already
  -- in use. To avoid shadowing, fresh identifiers should be chosen to
  -- be disjoint from this set.

  , _sharedNames :: IntMap.IntMap Coq.Ident
  -- ^ Index of identifiers for repeated subterms that have been
  -- lifted out into a let expression.

  , _nextSharedName :: Coq.Ident
  -- ^ The next available name to be used for a let-bound shared
  -- sub-expression.

  }
  deriving (Show)

makeLenses ''TranslationState

type TermTranslationMonad m =
  TranslationMonad TranslationReader TranslationState m

-- | The set of reserved identifiers in Coq, obtained from section
-- "Gallina Specification Language" of the Coq reference manual.
-- <https://coq.inria.fr/refman/language/gallina-specification-language.html>
reservedIdents :: Set.Set Coq.Ident
reservedIdents =
  Set.fromList $
  concatMap words $
  [ "_ Axiom CoFixpoint Definition Fixpoint Hypothesis IF Parameter Prop"
  , "SProp Set Theorem Type Variable as at by cofix discriminated else"
  , "end exists exists2 fix for forall fun if in lazymatch let match"
  , "multimatch return then using where with"
  ]

-- | Extract the list of names from a list of Coq declarations.  Not all
-- declarations have names, e.g. comments and code snippets come without names.
namedDecls :: [Coq.Decl] -> [String]
namedDecls = concatMap filterNamed
  where
    filterNamed :: Coq.Decl -> [String]
    filterNamed (Coq.Axiom n _)                               = [n]
    filterNamed (Coq.Parameter n _)                           = [n]
    filterNamed (Coq.Variable n _)                            = [n]
    filterNamed (Coq.Comment _)                               = []
    filterNamed (Coq.Definition n _ _ _)                      = [n]
    filterNamed (Coq.InductiveDecl (Coq.Inductive n _ _ _ _)) = [n]
    filterNamed (Coq.Snippet _)                               = []
    filterNamed (Coq.Section _ ds)                            = namedDecls ds

-- | Retrieve the names of all local and global declarations from the
-- translation state.
getNamesOfAllDeclarations ::
  TermTranslationMonad m =>
  m [String]
getNamesOfAllDeclarations = view allDeclarations <$> get
  where
    allDeclarations =
      to (\ (TranslationState {..}) -> namedDecls _topLevelDeclarations ++ _globalDeclarations)

runTermTranslationMonad ::
  TranslationConfiguration ->
  TranslationReader ->
  [String] ->
  [Coq.Ident] ->
  (forall m. TermTranslationMonad m => m a) ->
  Either (TranslationError Term) (a, TranslationState)
runTermTranslationMonad configuration r globalDecls localEnv =
  runTranslationMonad configuration r
  (TranslationState { _globalDeclarations = globalDecls
                    , _topLevelDeclarations  = []
                    , _localEnvironment   = localEnv
                    , _unavailableIdents  = Set.union reservedIdents (Set.fromList localEnv)
                    , _sharedNames        = IntMap.empty
                    , _nextSharedName     = "var__0"
                    })

errorTermM :: TermTranslationMonad m => String -> m Coq.Term
errorTermM str = return $ Coq.App (Coq.Var "error") [Coq.StringLit str]

translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Coq.Term
translateIdentWithArgs i args = do
  currentModuleName <- asks (view currentModule . otherConfiguration)
  let identToCoq ident =
        if Just (identModule ident) == currentModuleName
          then escapeIdent (identName ident)
          else
            show (translateModuleName (identModule ident))
            ++ "." ++ escapeIdent (identName ident)
  specialTreatment <- findSpecialTreatment i
  applySpecialTreatment identToCoq (atUseSite specialTreatment)

  where

    applySpecialTreatment identToCoq UsePreserve =
      Coq.App (Coq.Var $ identToCoq i) <$> mapM translateTerm args
    applySpecialTreatment identToCoq (UseRename targetModule targetName expl) =
      Coq.App
        ((if expl then Coq.ExplVar else Coq.Var) $ identToCoq $
          mkIdent (fromMaybe (translateModuleName $ identModule i) targetModule)
          (Text.pack targetName))
          <$> mapM translateTerm args
    applySpecialTreatment _identToCoq (UseReplaceDropArgs n replacement)
      | length args >= n =
        Coq.App replacement <$> mapM translateTerm (drop n args)
    applySpecialTreatment _identToCoq (UseReplaceDropArgs n _) =
      errorTermM (unwords
        [ "Identifier"
        , show i
        , "not applied to required number of args, which is"
        , show n
        ]
      )

translateIdent :: TermTranslationMonad m => Ident -> m Coq.Term
translateIdent i = translateIdentWithArgs i []

translateIdentToIdent :: TermTranslationMonad m => Ident -> m (Maybe Ident)
translateIdentToIdent i =
  (atUseSite <$> findSpecialTreatment i) >>= \case
    UsePreserve -> return $ Just (mkIdent translatedModuleName (identBaseName i))
    UseRename   targetModule targetName _ ->
      return $ Just $ mkIdent (fromMaybe translatedModuleName targetModule) (Text.pack targetName)
    UseReplaceDropArgs _ _ -> return Nothing
  where
    translatedModuleName = translateModuleName (identModule i)

translateSort :: Sort -> Coq.Sort
translateSort s = if s == propSort then Coq.Prop else Coq.Type

flatTermFToExpr ::
  TermTranslationMonad m =>
  FlatTermF Term ->
  m Coq.Term
flatTermFToExpr tf = -- traceFTermF "flatTermFToExpr" tf $
  case tf of
    Primitive pn  -> translateIdent (primName pn)
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      ->
      -- We need to explicitly tell Coq that we want unit to be a Type, since
      -- all SAW core sorts are translated to Types
      pure (Coq.Ascription (Coq.Var "unit") (Coq.Sort Coq.Type))
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse translateTerm [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse translateTerm [x, y]
    PairLeft t    ->
      Coq.App <$> pure (Coq.Var "SAWCoreScaffolding.fst") <*> traverse translateTerm [t]
    PairRight t   ->
      Coq.App <$> pure (Coq.Var "SAWCoreScaffolding.snd") <*> traverse translateTerm [t]
    -- TODO: maybe have more customizable translation of data types
    DataTypeApp n is as -> translateIdentWithArgs (primName n) (is ++ as)
    CtorApp n is as -> translateIdentWithArgs (primName n) (is ++ as)

    RecursorType _d _params motive motiveTy ->
      -- type of the motive looks like
      --      (ix1 : _) -> ... -> (ixn : _) -> d ps ixs -> sort
      -- to get the type of the recursor, we compute
      --      (ix1 : _) -> ... -> (ixn : _) -> (x:d ps ixs) -> motive ixs x
      do let (bs, _srt) = asPiList motiveTy
         (varsT,bindersT) <- unzip <$>
           (forM bs $ \ (b, bType) -> do
             bTypeT <- translateTerm bType
             b' <- freshenAndBindName b
             return (Coq.Var b', Coq.PiBinder (Just b') bTypeT))

         motiveT <- translateTerm motive
         let bodyT = Coq.App motiveT varsT
         return $ Coq.Pi bindersT bodyT

    -- TODO: support this next!
    Recursor (CompiledRecursor d parameters motive _motiveTy eliminators elimOrder) ->
      do maybe_d_trans <- translateIdentToIdent (primName d)
         rect_var <- case maybe_d_trans of
           Just i -> return $ Coq.Var (show i ++ "_rect")
           Nothing ->
             errorTermM ("Recursor for " ++ show d ++
                         " cannot be translated because the datatype " ++
                         "is mapped to an arbitrary Coq term")

         let fnd c = case Map.lookup (primVarIndex c) eliminators of
                       Just (e,_ety) -> translateTerm e
                       Nothing -> errorTermM
                          ("Recursor eliminator missing eliminator for constructor " ++ show c)

         ps <- mapM translateTerm parameters
         m  <- translateTerm motive
         elimlist <- mapM fnd elimOrder

         pure (Coq.App rect_var (ps ++ [m] ++ elimlist))

    RecursorApp r indices termEliminated ->
      do r' <- translateTerm r
         let args = indices ++ [termEliminated]
         Coq.App r' <$> mapM translateTerm args

    Sort s _h -> pure (Coq.Sort (translateSort s))
    NatLit i -> pure (Coq.NatLit (toInteger i))
    ArrayValue (asBoolType -> Just ()) (traverse asBool -> Just bits)
      | Pair w bv <- BV.bitsBE (Vector.toList bits)
      , Left LeqProof <- decideLeq (knownNat @1) w -> do
          return (Coq.App (Coq.Var "intToBv")
                  [Coq.NatLit (intValue w), Coq.ZLit (BV.asSigned w bv)])
    ArrayValue _ vec -> do
      elems <- Vector.toList <$> mapM translateTerm vec
      return (Coq.App (Coq.Var "Vector.of_list") [Coq.List elems])
    StringLit s -> pure (Coq.Scope (Coq.StringLit (Text.unpack s)) "string")

    ExtCns ec ->
      do configuration <- asks translationConfiguration
         let renamed = translateConstant (notations configuration) ec
         alreadyTranslatedDecls <- getNamesOfAllDeclarations
         let definitionsToSkip = skipDefinitions configuration
         if elem renamed alreadyTranslatedDecls || elem renamed definitionsToSkip
           then Coq.Var <$> pure renamed
           else do
             tp <-
              -- Translate type in a top-level name scope
              withLocalTranslationState $
              do modify $ set localEnvironment []
                 modify $ set unavailableIdents reservedIdents
                 modify $ set sharedNames IntMap.empty
                 modify $ set nextSharedName "var__0"
                 translateTermLet (ecType ec)
             modify $ over topLevelDeclarations $ (Coq.Variable renamed tp :)
             Coq.Var <$> pure renamed

    -- The translation of a record type {fld1:tp1, ..., fldn:tpn} is
    -- RecordTypeCons fld1 tp1 (... (RecordTypeCons fldn tpn RecordTypeNil)...).
    -- Note that SAW core equates record types up to reordering, so we sort our
    -- record types by field name to canonicalize them.
    RecordType fs ->
      foldr (\(name, tp) rest_m ->
              do rest <- rest_m
                 tp_trans <- translateTerm tp
                 return (Coq.App (Coq.Var "RecordTypeCons")
                         [Coq.StringLit (Text.unpack name), tp_trans, rest]))
      (return (Coq.Var "RecordTypeNil"))
      (sortOn fst fs)

    -- The translation of a record value {fld1 = x1, ..., fldn = xn} is
    -- RecordCons fld1 x1 (... (RecordCons fldn xn RecordNil) ...). Note that
    -- SAW core equates record values up to reordering, so we sort our record
    -- values by field name to canonicalize them.
    RecordValue fs ->
      foldr (\(name, trm) rest_m ->
              do rest <- rest_m
                 trm_trans <- translateTerm trm
                 return (Coq.App (Coq.Var "RecordCons")
                         [Coq.StringLit (Text.unpack name), trm_trans, rest]))
      (return (Coq.Var "RecordNil"))
      (sortOn fst fs)

    RecordProj r f -> do
      r_trans <- translateTerm r
      return (Coq.App (Coq.Var "RecordProj") [r_trans, Coq.StringLit (Text.unpack f)])

-- | Recognizes an $App (App "Cryptol.seq" n) x$ and returns ($n$, $x$).
asSeq :: Recognizer Term (Term, Term)
asSeq t = do (f, args) <- asApplyAllRecognizer t
             fid <- asGlobalDef f
             case (fid, args) of
               ("Cryptol.seq", [n, x]) -> return (n,x)
               _ -> Fail.fail "not a seq"

asApplyAllRecognizer :: Recognizer Term (Term, [Term])
asApplyAllRecognizer t = do _ <- asApp t
                            return $ asApplyAll t

-- | Run a translation, but keep some changes to the translation state local to
-- that computation, restoring parts of the original translation state before
-- returning.
withLocalTranslationState :: TermTranslationMonad m => m a -> m a
withLocalTranslationState action = do
  before <- get
  result <- action
  after <- get
  put (TranslationState
    -- globalDeclarations is **not** restored, because we want to translate each
    -- global declaration exactly once!
    { _globalDeclarations = view globalDeclarations after
    -- topLevelDeclarations is **not** restored, because it accumulates the
    -- declarations witnessed in a given module so that we can extract it.
    , _topLevelDeclarations = view topLevelDeclarations after
    -- localEnvironment **is** restored, because the identifiers added to it
    -- during translation are local to the term that was being translated.
    , _localEnvironment = view localEnvironment before
    -- unavailableIdents **is** restored, because the extra identifiers
    -- unavailable in the term that was translated are local to it.
    , _unavailableIdents = view unavailableIdents before
    -- sharedNames **is** restored, because we are leaving the scope of the
    -- locally shared names.
    , _sharedNames = view sharedNames before
    -- nextSharedName **is** restored, because we are leaving the scope of the
    -- last names used.
    , _nextSharedName = view nextSharedName before
    })
  return result

mkDefinition :: Coq.Ident -> Coq.Term -> Coq.Decl
mkDefinition name (Coq.Lambda bs t) = Coq.Definition name bs Nothing t
mkDefinition name t = Coq.Definition name [] Nothing t

-- | Make sure a name is not used in the current environment, adding
-- or incrementing a numeric suffix until we find an unused name. When
-- we get one, add it to the current environment and return it.
freshenAndBindName :: TermTranslationMonad m => LocalName -> m Coq.Ident
freshenAndBindName n =
  do n' <- translateLocalIdent n
     modify $ over localEnvironment (n' :)
     pure n'

mkLet :: (Coq.Ident, Coq.Term) -> Coq.Term -> Coq.Term
mkLet (name, rhs) body = Coq.Let name [] Nothing rhs body

translateParams ::
  TermTranslationMonad m =>
  [(LocalName, Term)] -> m [Coq.Binder]
translateParams bs = concat <$> mapM translateParam bs

translateParam ::
  TermTranslationMonad m =>
  (LocalName, Term) -> m [Coq.Binder]
translateParam (n, ty) =
  translateBinder n ty >>= \case
    Left (n',ty') -> return [Coq.Binder n' (Just ty')]
    Right (n',ty',nh,nhty) ->
      return [Coq.Binder n' (Just ty'), Coq.ImplicitBinder nh (Just nhty)]

translatePi :: TermTranslationMonad m => [(LocalName, Term)] -> Term -> m Coq.Term
translatePi binders body = withLocalTranslationState $ do
  bindersT <- concat <$> mapM translatePiBinder binders
  bodyT <- translateTermLet body
  return $ Coq.Pi bindersT bodyT

translatePiBinder ::
  TermTranslationMonad m => (LocalName, Term) -> m [Coq.PiBinder]
translatePiBinder (n, ty) =
  translateBinder n ty >>= \case
    Left (n',ty')
      | n == "_"  -> return [Coq.PiBinder Nothing ty']
      | otherwise -> return [Coq.PiBinder (Just n') ty']
    Right (n',ty',nh,nhty) ->
      return [Coq.PiBinder (Just n') ty', Coq.PiImplicitBinder (Just nh) nhty]

translateBinder ::
  TermTranslationMonad m =>
  LocalName ->
  Term ->
  m (Either (Coq.Ident,Coq.Type) (Coq.Ident,Coq.Type,Coq.Ident,Coq.Type))
translateBinder n ty@(asPiList -> (args, asISort -> Just _s)) =
  do ty' <- translateTerm ty
     n' <- freshenAndBindName n
     hty' <- translateInhHyp args (Coq.Var n')
     hn' <- translateLocalIdent ("Inh_" <> n )
     return $ Right (n',ty',hn',hty')
translateBinder n ty =
  do ty' <- translateTerm ty
     n'  <- freshenAndBindName n
     return $ Left (n',ty')

translateInhHyp ::
  TermTranslationMonad m =>
  [(LocalName, Term)] -> Coq.Term -> m Coq.Term
translateInhHyp [] tm = return (Coq.App (Coq.Var "SAWCoreScaffolding.Inhabited") [tm])
translateInhHyp args tm = withLocalTranslationState $
  do args' <- mapM (uncurry translateBinder) args
     return $ Coq.Pi (concatMap mkPi args')
                (Coq.App (Coq.Var "SAWCoreScaffolding.Inhabited") [Coq.App tm (map mkArg args')])
 where
  mkPi (Left (nm,ty)) =
    [Coq.PiBinder (Just nm) ty]
  mkPi (Right (nm,ty,hnm,hty)) =
    [Coq.PiBinder (Just nm) ty, Coq.PiImplicitBinder (Just hnm) hty]

  mkArg (Left (nm,_)) = Coq.Var nm
  mkArg (Right (nm,_,_,_)) = Coq.Var nm

-- | Translate a local name from a saw-core binder into a fresh Coq identifier.
translateLocalIdent :: TermTranslationMonad m => LocalName -> m Coq.Ident
translateLocalIdent x = freshVariant (escapeIdent (Text.unpack x))

-- | Find an fresh, as-yet-unused variant of the given Coq identifier.
freshVariant :: TermTranslationMonad m => Coq.Ident -> m Coq.Ident
freshVariant x =
  do used <- view unavailableIdents <$> get
     let ident0 = x
     let findVariant i = if Set.member i used then findVariant (nextVariant i) else i
     let ident = findVariant ident0
     modify $ over unavailableIdents (Set.insert ident)
     return ident

nextVariant :: Coq.Ident -> Coq.Ident
nextVariant = reverse . go . reverse
  where
    go :: String -> String
    go (c : cs)
      | c == '9'  = '0' : go cs
      | isDigit c = succ c : cs
    go cs = '1' : cs

translateTermLet :: TermTranslationMonad m => Term -> m Coq.Term
translateTermLet t =
  withLocalTranslationState $
  do let counts = scTermCount False t
     let locals = fmap fst $ IntMap.filter keep counts
     names <- traverse (const nextName) locals
     modify $ set sharedNames names
     defs <- traverse translateTermUnshared locals
     body <- translateTerm t
     -- NOTE: Larger terms always have later IDs than their subterms,
     -- so ordering by VarIndex is a valid dependency order.
     let binds = IntMap.elems (IntMap.intersectionWith (,) names defs)
     pure (foldr mkLet body binds)
  where
    keep (t', n) = n > 1 && shouldMemoizeTerm t'
    nextName =
      do x <- view nextSharedName <$> get
         x' <- freshVariant x
         modify $ set nextSharedName (nextVariant x')
         pure x'

translateTerm :: TermTranslationMonad m => Term -> m Coq.Term
translateTerm t =
  case t of
    Unshared {} -> translateTermUnshared t
    STApp { stAppIndex = i } ->
      do shared <- view sharedNames <$> get
         case IntMap.lookup i shared of
           Nothing -> translateTermUnshared t
           Just x -> pure (Coq.Var x)

translateTermUnshared :: TermTranslationMonad m => Term -> m Coq.Term
translateTermUnshared t = withLocalTranslationState $ do
  -- traceTerm "translateTerm" t $
  -- NOTE: env is in innermost-first order
  env <- view localEnvironment <$> get
  -- let t' = trace ("translateTerm: " ++ "env = " ++ show env ++ ", t =" ++ showTerm t) t
  -- case t' of
  case unwrapTermF t of

    FTermF ftf -> flatTermFToExpr ftf

    Pi {} -> translatePi params e
      where
        (params, e) = asPiList t

    Lambda {} -> do
      paramTerms <- translateParams params
      e' <- translateTermLet e
      pure (Coq.Lambda paramTerms e')
        where
          -- params are in normal, outermost first, order
          (params, e) = asLambdaList t

    App {} ->
      -- asApplyAll: innermost argument first
      let (f, args) = asApplyAll t
      in
      case f of
      (asGlobalDef -> Just i) ->
        case i of
        "Prelude.natToInt" ->
          case args of
          [n] -> translateTerm n >>= \case
            Coq.NatLit n' -> pure $ Coq.ZLit n'
            _ -> translateIdentWithArgs "Prelude.natToInt" [n]
          _ -> badTerm
        "Prelude.intNeg" ->
          case args of
          [z] -> translateTerm z >>= \case
            Coq.ZLit z' -> pure $ Coq.ZLit (-z')
            _ -> translateIdentWithArgs "Prelude.intNeg" [z]
          _ -> badTerm
        "Prelude.ite" ->
          case args of
          -- `rest` can be non-empty in examples like:
          -- (if b then f else g) arg1 arg2
          _ty : c : tt : ft : rest -> do
            ite <- Coq.If <$> translateTerm c <*> translateTerm tt <*> translateTerm ft
            case rest of
              [] -> return ite
              _  -> Coq.App ite <$> mapM translateTerm rest
          _ -> badTerm

        -- Refuse to translate any recursive value defined using Prelude.fix
        "Prelude.fix" -> badTerm

        _ -> translateIdentWithArgs i args
      _ -> Coq.App <$> translateTerm f <*> traverse translateTerm args

    LocalVar n
      | n < length env -> Coq.Var <$> pure (env !! n)
      | otherwise -> Except.throwError $ LocalVarOutOfBounds t

    -- Constants with no body
    Constant n Nothing -> do
      configuration <- asks translationConfiguration
      let renamed = translateConstant (notations configuration) n
      alreadyTranslatedDecls <- getNamesOfAllDeclarations
      let definitionsToSkip = skipDefinitions configuration
      if elem renamed alreadyTranslatedDecls || elem renamed definitionsToSkip
        then Coq.Var <$> pure renamed
        else do
          tp <-
           -- Translate type in a top-level name scope
           withLocalTranslationState $
           do modify $ set localEnvironment []
              modify $ set unavailableIdents reservedIdents
              modify $ set sharedNames IntMap.empty
              modify $ set nextSharedName "var__0"
              translateTermLet (ecType n)
          modify $ over topLevelDeclarations $ (Coq.Variable renamed tp :)
          Coq.Var <$> pure renamed

    -- Constants with a body
    Constant n (Just body) -> do
      configuration <- asks translationConfiguration
      let renamed = translateConstant (notations configuration) n
      alreadyTranslatedDecls <- getNamesOfAllDeclarations
      let definitionsToSkip = skipDefinitions configuration
      if elem renamed alreadyTranslatedDecls || elem renamed definitionsToSkip
        then Coq.Var <$> pure renamed
        else do
        b <-
          -- Translate body in a top-level name scope
          withLocalTranslationState $
          do modify $ set localEnvironment []
             modify $ set unavailableIdents reservedIdents
             modify $ set sharedNames IntMap.empty
             modify $ set nextSharedName "var__0"
             translateTermLet body
        modify $ over topLevelDeclarations $ (mkDefinition renamed b :)
        Coq.Var <$> pure renamed

  where
    badTerm          = Except.throwError $ BadTerm t

-- | In order to turn fixpoint computations into iterative computations, we need
-- to be able to create "dummy" values at the type of the computation.
defaultTermForType ::
  TermTranslationMonad m =>
  Term -> m Coq.Term
defaultTermForType typ = do
  case typ of
    (asBoolType -> Just ()) -> translateIdent (mkIdent preludeName "False")

    (isGlobalDef "Prelude.Nat" -> Just ()) -> return $ Coq.NatLit 0

    (asIntegerType -> Just ()) -> return $ Coq.ZLit 0

    (asSeq -> Just (n, typ')) -> do
      seqConst <- translateIdent (mkIdent (mkModuleName ["Cryptol"]) "seqConst")
      nT       <- translateTerm n
      typ'T    <- translateTerm typ'
      defaultT <- defaultTermForType typ'
      return $ Coq.App seqConst [ nT, typ'T, defaultT ]

    (asPairType -> Just (x,y)) -> do
      x' <- defaultTermForType x
      y' <- defaultTermForType y
      return $ Coq.App (Coq.Var "pair") [x',y']

    (asPiList -> (bs,body))
      | not (null bs)
      , looseVars body == emptyBitSet ->
      do bs'   <- forM bs $ \ (_nm, ty) -> Coq.Binder "_" . Just <$> translateTerm ty
         body' <- defaultTermForType body
         return $ Coq.Lambda bs' body'

    _ -> Except.throwError $ CannotCreateDefaultValue typ

translateTermToDocWith ::
  TranslationConfiguration ->
  TranslationReader ->
  [String] ->
  [String] ->
  (Coq.Term -> Doc ann) ->
  Term ->
  Either (TranslationError Term) (Doc ann)
translateTermToDocWith configuration r globalDecls localEnv f t = do
  (term, state) <-
    runTermTranslationMonad configuration r globalDecls localEnv (translateTermLet t)
  let decls = view topLevelDeclarations state
  return $
    vcat $
    [ (vcat . intersperse hardline . map Coq.ppDecl . reverse) decls
    , if null decls then mempty else hardline
    , f term
    ]

translateDefDoc ::
  TranslationConfiguration ->
  TranslationReader ->
  [String] ->
  Coq.Ident -> Term ->
  Either (TranslationError Term) (Doc ann)
translateDefDoc configuration r globalDecls name =
  translateTermToDocWith configuration r globalDecls [name]
  (Coq.ppDecl . mkDefinition name)
