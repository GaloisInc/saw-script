{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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
import qualified Data.Set                                      as Set
import           Prelude                                       hiding (fail)
import           Text.PrettyPrint.ANSI.Leijen                  hiding ((<$>))

import qualified Data.Vector                                   as Vector (reverse)
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

data TranslationState = TranslationState

  { _globalDeclarations :: [String]
  -- ^ Some Cryptol terms seem to capture the name and body of some functions
  -- they use (whether from the Cryptol prelude, or previously defined in the
  -- same file).  We want to translate those exactly once, so we need to keep
  -- track of which ones have already been translated.

  , _localDeclarations :: [Coq.Decl]
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

  , _currentModule :: Maybe ModuleName
  }
  deriving (Show)

makeLenses ''TranslationState

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
    filterNamed (Coq.Comment _)                               = []
    filterNamed (Coq.Definition n _ _ _)                      = [n]
    filterNamed (Coq.InductiveDecl (Coq.Inductive n _ _ _ _)) = [n]
    filterNamed (Coq.Snippet _)                               = []

-- | Retrieve the names of all local and global declarations from the
-- translation state.
getNamesOfAllDeclarations ::
  TermTranslationMonad m =>
  m [String]
getNamesOfAllDeclarations = view allDeclarations <$> get
  where
    allDeclarations =
      to (\ (TranslationState {..}) -> namedDecls _localDeclarations ++ _globalDeclarations)

type TermTranslationMonad m = TranslationMonad TranslationState m

runTermTranslationMonad ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  [String] ->
  [Coq.Ident] ->
  (forall m. TermTranslationMonad m => m a) ->
  Either (TranslationError Term) (a, TranslationState)
runTermTranslationMonad configuration modname globalDecls localEnv =
  runTranslationMonad configuration
  (TranslationState { _globalDeclarations = globalDecls
                    , _localDeclarations  = []
                    , _localEnvironment   = localEnv
                    , _unavailableIdents  = Set.union reservedIdents (Set.fromList localEnv)
                    , _sharedNames        = IntMap.empty
                    , _nextSharedName     = "var__0"
                    , _currentModule      = modname
                    })

errorTermM :: TermTranslationMonad m => String -> m Coq.Term
errorTermM str = return $ Coq.App (Coq.Var "error") [Coq.StringLit str]

translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Coq.Term
translateIdentWithArgs i args =
  (view currentModule <$> get) >>= \cur_modname ->
  let identToCoq ident =
        if Just (identModule ident) == cur_modname then "@" ++ identName ident else
          "@" ++ show (translateModuleName (identModule ident))
          ++ "." ++ identName ident in

  (atUseSite <$> findSpecialTreatment i) >>= \case
    UsePreserve -> Coq.App (Coq.Var $ identToCoq i) <$> mapM translateTerm args
    UseRename targetModule targetName ->
      Coq.App (Coq.Var $ identToCoq $
               mkIdent (fromMaybe (translateModuleName $ identModule i) targetModule)
               targetName) <$>
      mapM translateTerm args
    UseReplaceDropArgs n replacement
      | length args >= n -> Coq.App replacement <$> mapM translateTerm (drop n args)
    UseReplaceDropArgs n _ ->
      errorTermM ("Identifier " ++ show i
                  ++ " not applied to required number of args,"
                  ++ " which is " ++ show n)

translateIdent :: TermTranslationMonad m => Ident -> m Coq.Term
translateIdent i = translateIdentWithArgs i []

translateIdentToIdent :: TermTranslationMonad m => Ident -> m (Maybe Ident)
translateIdentToIdent i =
  (atUseSite <$> findSpecialTreatment i) >>= \case
    UsePreserve -> return $ Just (mkIdent translatedModuleName (identName i))
    UseRename   targetModule targetName ->
      return $ Just $ mkIdent (fromMaybe translatedModuleName targetModule) targetName
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
    GlobalDef i   -> translateIdent i
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      -> pure (Coq.Var "unit")
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse translateTerm [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse translateTerm [x, y]
    PairLeft t    ->
      Coq.App <$> pure (Coq.Var "SAWCoreScaffolding.fst") <*> traverse translateTerm [t]
    PairRight t   ->
      Coq.App <$> pure (Coq.Var "SAWCoreScaffolding.snd") <*> traverse translateTerm [t]
    -- TODO: maybe have more customizable translation of data types
    DataTypeApp n is as -> translateIdentWithArgs n (is ++ as)
    CtorApp n is as -> translateIdentWithArgs n (is ++ as)
    -- TODO: support this next!
    RecursorApp d parameters motive eliminators indices termEliminated ->
      do maybe_d_trans <- translateIdentToIdent d
         rect_var <- case maybe_d_trans of
           Just i -> return $ Coq.Var (show i ++ "_rect")
           Nothing ->
             errorTermM ("Recursor for " ++ show d ++
                         " cannot be translated because the datatype " ++
                         "is mapped to an arbitrary Coq term")
         let args =
               parameters ++ [motive] ++ map snd eliminators
               ++ indices ++ [termEliminated]
         Coq.App rect_var <$> mapM translateTerm args
    Sort s -> pure (Coq.Sort (translateSort s))
    NatLit i -> pure (Coq.NatLit (toInteger i))
    ArrayValue _ vec -> do
      let addElement accum element = do
            elementTerm <- translateTerm element
            return (Coq.App (Coq.Var "Vector.cons")
                    [Coq.Var "_", elementTerm, Coq.Var "_", accum]
                   )
        in
        foldM addElement (Coq.App (Coq.Var "Vector.nil") [Coq.Var "_"]) (Vector.reverse vec)
    StringLit s -> pure (Coq.Scope (Coq.StringLit s) "string")
    ExtCns (EC _ _ _) -> errorTermM "External constants not supported"

    -- The translation of a record type {fld1:tp1, ..., fldn:tpn} is
    -- RecordTypeCons fld1 tp1 (... (RecordTypeCons fldn tpn RecordTypeNil)...).
    -- Note that SAW core equates record types up to reordering, so we sort our
    -- record types by field name to canonicalize them.
    RecordType fs ->
      foldr (\(name, tp) rest_m ->
              do rest <- rest_m
                 tp_trans <- translateTerm tp
                 return (Coq.App (Coq.Var "RecordTypeCons")
                         [Coq.StringLit name, tp_trans, rest]))
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
                         [Coq.StringLit name, trm_trans, rest]))
      (return (Coq.Var "RecordNil"))
      (sortOn fst fs)

    RecordProj r f -> do
      r_trans <- translateTerm r
      return (Coq.App (Coq.Var "RecordProj") [r_trans, Coq.StringLit f])

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

-- | Run a translation, but keep changes to the environment local to it,
-- restoring the current environment before returning.
withLocalLocalEnvironment :: TermTranslationMonad m => m a -> m a
withLocalLocalEnvironment action = do
  env <- view localEnvironment <$> get
  used <- view unavailableIdents <$> get
  result <- action
  modify $ set localEnvironment env
  modify $ set unavailableIdents used
  return result

mkDefinition :: Coq.Ident -> Coq.Term -> Coq.Decl
mkDefinition name (Coq.Lambda bs t) = Coq.Definition name bs Nothing t
mkDefinition name t = Coq.Definition name [] Nothing t

mkLet :: (Coq.Ident, Coq.Term) -> Coq.Term -> Coq.Term
mkLet (name, rhs) body = Coq.Let name [] Nothing rhs body

translateParams ::
  TermTranslationMonad m =>
  [(String, Term)] -> m [Coq.Binder]
translateParams [] = return []
translateParams ((n, ty):ps) = do
  ty' <- translateTerm ty
  n' <- translateLocalIdent n
  modify $ over localEnvironment (n' :)
  ps' <- translateParams ps
  return (Coq.Binder n' (Just ty') : ps')

translatePi :: TermTranslationMonad m => [(String, Term)] -> Term -> m Coq.Term
translatePi binders body = withLocalLocalEnvironment $ do
  bindersT <- forM binders $ \ (b, bType) -> do
    bTypeT <- translateTerm bType
    modify $ over localEnvironment (b :)
    let n = if b == "_" then Nothing else Just b
    return (Coq.PiBinder n bTypeT)
  bodyT <- translateTermLet body
  return $ Coq.Pi bindersT bodyT

-- | Translate a local name from a saw-core binder into a fresh Coq identifier.
translateLocalIdent :: TermTranslationMonad m => String -> m Coq.Ident
translateLocalIdent x =
  do used <- view unavailableIdents <$> get
     let ident0 = x -- TODO: use some string encoding to ensure lexically valid Coq identifiers
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
  withLocalLocalEnvironment $
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
         x' <- translateLocalIdent x
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
translateTermUnshared t = withLocalLocalEnvironment $ do
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
      Coq.Lambda <$> pure paramTerms
                 -- env is in innermost first (reverse) binder order
                 <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asLambdaList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params

    App {} ->
      -- asApplyAll: innermost argument first
      let (f, args) = asApplyAll t
      in
      case f of
      (asGlobalDef -> Just i) ->
        case i of
        "Prelude.ite" ->
          case args of
          -- `rest` can be non-empty in examples like:
          -- (if b then f else g) arg1 arg2
          _ty : c : tt : ft : rest -> do
            ite <- Coq.If <$> go env c <*> go env tt <*> go env ft
            case rest of
              [] -> return ite
              _  -> Coq.App ite <$> mapM (go env) rest
          _ -> badTerm
        -- NOTE: the following works for something like CBC, because computing
        -- the n-th block only requires n steps of recursion
        -- FIXME: (pun not intended) better conditions for when this is safe to do
        "Prelude.fix" ->
          case args of
          []  -> errorTermM "call to Prelude.fix with no argument"
          [_] -> errorTermM "call to Prelude.fix with 1 argument"
          resultType : lambda : rest ->
            case resultType of
            -- TODO: check that 'n' is finite
            (asSeq -> Just (n, _)) ->
              case lambda of

              (asLambda -> Just (x, seqType, body)) | seqType == resultType ->
                  do
                    len <- go env n
                    expr <- go (x:env) body
                    seqTypeT <- go env seqType
                    defaultValueT <- defaultTermForType resultType
                    let iter =
                          Coq.App (Coq.Var "iter")
                          [ len
                          , Coq.Lambda [Coq.Binder x (Just seqTypeT)] expr
                          , defaultValueT
                          ]
                    case rest of
                      [] -> return iter
                      _  -> Coq.App iter <$> mapM (go env) rest
              _ -> badTerm
            -- NOTE: there is currently one instance of `fix` that will trigger
            -- `errorTermM`.  It is used in `Cryptol.cry` when translating
            -- `iterate`, which generates an infinite stream of nested
            -- applications of a given function.

            (asPiList -> (pis, afterPis)) ->
              -- NOTE: this will output some code, but it is likely that Coq
              -- will reject it for not being structurally recursive.
              case lambda of
              (asLambdaList -> ((recFn, _) : binders, body)) -> do
                let (_binderPis, otherPis) = splitAt (length binders) pis
                (bindersT, typeT, bodyT) <- withLocalLocalEnvironment $ do
                  -- this is very ugly...
                  modify $ over localEnvironment (recFn :)
                  bindersT <- mapM
                    (\ (b, bType) -> do
                      env' <- view localEnvironment <$> get
                      bTypeT <- go env' bType
                      modify $ over localEnvironment (b :)
                      return $ Coq.Binder b (Just bTypeT)
                    )
                    binders
                  typeT <- translatePi otherPis afterPis
                  env' <- view localEnvironment <$> get
                  bodyT <- go env' body
                  return (bindersT, typeT, bodyT)
                let fix = Coq.Fix recFn bindersT typeT bodyT
                case rest of
                  [] -> return fix
                  _  -> errorTermM "THAT" -- Coq.App fix <$> mapM (go env) rest
              _ -> errorTermM "call to Prelude.fix without lambda"

        _ ->
          translateIdentWithArgs i args
      _ -> Coq.App <$> go env f <*> traverse (go env) args

    LocalVar n
      | n < length env -> Coq.Var <$> pure (env !! n)
      | otherwise -> Except.throwError $ LocalVarOutOfBounds t

  -- Constants come with a body
    Constant n body -> do
      configuration <- ask
      let renamed = translateConstant (notations configuration) n
      alreadyTranslatedDecls <- getNamesOfAllDeclarations
      let definitionsToSkip = skipDefinitions configuration
      if elem renamed alreadyTranslatedDecls || elem renamed definitionsToSkip
        then Coq.Var <$> pure renamed
        else do
        b <- go env body
        modify $ over localDeclarations $ (mkDefinition renamed b :)
        Coq.Var <$> pure renamed

  where
    badTerm          = Except.throwError $ BadTerm t
    go env term      = do
      modify $ set localEnvironment env
      translateTerm term

-- | In order to turn fixpoint computations into iterative computations, we need
-- to be able to create "dummy" values at the type of the computation.  For now,
-- we will support arbitrary nesting of vectors of boolean values.
defaultTermForType ::
  TermTranslationMonad m =>
  Term -> m Coq.Term
defaultTermForType typ = do
  case typ of

    (asSeq -> Just (n, typ')) -> do
      seqConst <- translateIdent (mkIdent (mkModuleName ["Cryptol"]) "seqConst")
      nT       <- translateTerm n
      typ'T    <- translateTerm typ'
      defaultT <- defaultTermForType typ'
      return $ Coq.App seqConst [ nT, typ'T, defaultT ]

    (asBoolType -> Just ()) -> translateIdent (mkIdent preludeName "False")

    _ ->
      return $ Coq.App (Coq.Var "error")
      [Coq.StringLit ("Could not generate default value of type " ++ showTerm typ)]

    -- _ -> Except.throwError $ CannotCreateDefaultValue typ

translateTermToDocWith ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  [String] ->
  [String] ->
  (Coq.Term -> Doc) ->
  Term ->
  Either (TranslationError Term) Doc
translateTermToDocWith configuration mn globalDecls localEnv f t = do
  (term, state) <-
    runTermTranslationMonad configuration mn globalDecls localEnv (translateTermLet t)
  let decls = view localDeclarations state
  return
    $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls)
    <$$> (if null decls then empty else hardline)
    <$$> f term

translateDefDoc ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  [String] ->
  Coq.Ident -> Term ->
  Either (TranslationError Term) Doc
translateDefDoc configuration mn globalDecls name =
  translateTermToDocWith configuration mn globalDecls [name]
  (\ term -> Coq.ppDecl (mkDefinition name term))
