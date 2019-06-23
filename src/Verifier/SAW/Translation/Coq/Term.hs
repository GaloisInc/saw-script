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

import           Control.Lens                                  (makeLenses, over, set, view)
import qualified Control.Monad.Except                          as Except
import qualified Control.Monad.Fail                            as Fail
import           Control.Monad.Reader                          hiding (fail)
import           Control.Monad.State                           hiding (fail, state)
import           Data.List                                     (intersperse)
import           Data.Maybe                                    (fromMaybe)
import           Prelude                                       hiding (fail)
import           Text.PrettyPrint.ANSI.Leijen                  hiding ((<$>))

import qualified Data.Vector                                   as Vector (reverse, toList)
import qualified Language.Coq.AST                              as Coq
import qualified Language.Coq.Pretty                           as Coq
import           Verifier.SAW.Recognizer
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Term.Functor
import           Verifier.SAW.Translation.Coq.Monad
import           Verifier.SAW.Translation.Coq.SpecialTreatment

data TranslationState = TranslationState
  { _declarations     :: [Coq.Decl]
  , _localEnvironment :: [String]
  }
  deriving (Show)
makeLenses ''TranslationState

type TermTranslationMonad m = TranslationMonad TranslationState m

runTermTranslationMonad ::
  TranslationConfiguration ->
  (forall m. TermTranslationMonad m => m a) ->
  Either (TranslationError Term) (a, TranslationState)
runTermTranslationMonad configuration =
  runTranslationMonad configuration (TranslationState [] [])

findIdentTranslation :: Ident -> Ident
findIdentTranslation i =
  case atUseSite (findSpecialTreatment i) of
    UsePreserve                         -> mkIdent translatedModuleName (identName i)
    UseRename   targetModule targetName -> mkIdent (fromMaybe translatedModuleName targetModule) targetName
    UseReplace  _                       -> error $ "This identifier should have been replaced already: " ++ show i
  where
    translatedModuleName = translateModuleName (identModule i)

translateIdent :: Ident -> Coq.Ident
translateIdent = show . findIdentTranslation

translateIdentUnqualified :: Ident -> Coq.Ident
translateIdentUnqualified = identName .  findIdentTranslation

translateSort :: Sort -> Coq.Sort
translateSort s = if s == propSort then Coq.Prop else Coq.Type

flatTermFToExpr ::
  TermTranslationMonad m =>
  (Term -> m Coq.Term) ->
  FlatTermF Term ->
  m Coq.Term
flatTermFToExpr go tf = -- traceFTermF "flatTermFToExpr" tf $
  case tf of
    GlobalDef i   -> pure (Coq.Var ("@" ++ translateIdent i))
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      -> pure (Coq.Var "unit")
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse go [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse go [x, y]
    PairLeft t    -> Coq.App (Coq.Var "fst") <$> traverse go [t]
    PairRight t   -> Coq.App (Coq.Var "snd") <$> traverse go [t]
    -- TODO: maybe have more customizable translation of data types
    DataTypeApp n is as -> do
      Coq.App (Coq.Var ("@" ++ translateIdentUnqualified n)) <$> traverse go (is ++ as)
    -- TODO: maybe have more customizable translation of data constructors
    CtorApp n is as -> do
      Coq.App (Coq.Var ("@" ++ translateIdentUnqualified n)) <$> traverse go (is ++ as)
    -- TODO: support this next!
    RecursorApp typeEliminated parameters motive eliminators indices termEliminated ->
      Coq.App (Coq.Var $ "@" ++ translateIdentUnqualified typeEliminated ++ "_rect") <$>
      (traverse go $
       parameters ++ [motive] ++ map snd eliminators ++ indices ++ [termEliminated]
      )
    Sort s -> pure (Coq.Sort (translateSort s))
    NatLit i -> pure (Coq.NatLit i)
    ArrayValue _ vec -> do
      config <- ask
      if translateVectorsAsCoqVectors config
        then
        let addElement accum element = do
              elementTerm <- go element
              return (Coq.App (Coq.Var "Vector.cons")
                      [Coq.Var "_", elementTerm, Coq.Var "_", accum]
                     )
        in
        foldM addElement (Coq.App (Coq.Var "Vector.nil") [Coq.Var "_"]) (Vector.reverse vec)
        else
        (Coq.List . Vector.toList) <$> traverse go vec  -- TODO: special case bit vectors?
    StringLit s -> pure (Coq.Scope (Coq.StringLit s) "string")
    ExtCns (EC _ _ _) -> notSupported

    -- NOTE: The following requires the coq-extensible-records library, because
    -- Coq records are nominal rather than structural
    -- In this library, record types are represented as:
    -- (record (Fields FSNil))                         is the type of the empty record
    -- (record (Fields (FSCons ("x" %e nat) FSNil)))   has one field "x" of type "nat"
    RecordType fs ->
      let makeField name typ = do
            typTerm <- go typ
            return (Coq.App (Coq.Var "@pair")
              [ Coq.Var "field"
              , Coq.Var "_"
              , Coq.Scope (Coq.StringLit name) "string"
              , typTerm
              ])
      in
      let addField accum (name, typ) = do
            fieldTerm <- makeField name typ
            return (Coq.App (Coq.Var "FScons") [fieldTerm, accum])
      in
      do
        fields <- foldM addField (Coq.Var "FSnil") fs
        return $ Coq.App (Coq.Var "record") [ Coq.App (Coq.Var "Fields") [fields] ]

    RecordValue fs ->
      let makeField name val = do
            valTerm <- go val
            return (Coq.App (Coq.Var "@record_singleton")
              [ Coq.Var "_"
              , Coq.Scope (Coq.StringLit name) "string"
              , valTerm
              ])
      in
      let addField accum (name, typ) = do
            fieldTerm <- makeField name typ
            return (Coq.App (Coq.Var "@Rjoin") [Coq.Var "_", Coq.Var "_", fieldTerm, accum])
      in
      foldM addField (Coq.Var "record_empty") fs
    RecordProj r f -> do
      rTerm <- go r
      return (Coq.App (Coq.Var "@Rget")
              [ Coq.Var "_"
              , rTerm
              , Coq.Scope (Coq.StringLit f) "string"
              , Coq.Var "_"
              , Coq.Ltac "simpl; exact eq_refl"
              ])
  where
    notSupported = Except.throwError $ NotSupported errorTerm
    --badTerm = throwError $ BadTerm errorTerm
    errorTerm = Unshared $ FTermF tf
    --asString (asFTermF -> Just (StringLit s)) = pure s
    --asString _ = badTerm

-- | Recognizes an $App (App "Cryptol.seq" n) x$ and returns ($n$, $x$).
asSeq :: Fail.MonadFail f => Recognizer f Term (Term, Term)
asSeq t = do (f, args) <- asApplyAllRecognizer t
             fid <- asGlobalDef f
             case (fid, args) of
               ("Cryptol.seq", [n, x]) -> return (n,x)
               _ -> Fail.fail "not a seq"

asApplyAllRecognizer :: Fail.MonadFail f => Recognizer f Term (Term, [Term])
asApplyAllRecognizer t = do _ <- asApp t
                            return $ asApplyAll t

-- | Run a translation, but keep changes to the environment local to it,
-- restoring the current environment before returning.
withLocalLocalEnvironment :: TermTranslationMonad m => m a -> m a
withLocalLocalEnvironment action = do
  env <- view localEnvironment <$> get
  result <- action
  modify $ set localEnvironment env
  return result

mkDefinition :: Coq.Ident -> Coq.Term -> Coq.Decl
mkDefinition name (Coq.Lambda bs t) = Coq.Definition name bs Nothing t
mkDefinition name t = Coq.Definition name [] Nothing t

translateParams ::
  TermTranslationMonad m =>
  [(String, Term)] -> m [Coq.Binder]
translateParams [] = return []
translateParams ((n, ty):ps) = do
  ty' <- translateTerm ty
  modify $ over localEnvironment (n :)
  ps' <- translateParams ps
  return (Coq.Binder n (Just ty') : ps')

translatePiParams :: TermTranslationMonad m => [(String, Term)] -> m [Coq.PiBinder]
translatePiParams [] = return []
translatePiParams ((n, ty):ps) = do
  ty' <- translateTerm ty
  modify $ over localEnvironment (n :)
  ps' <- translatePiParams ps
  let n' = if n == "_" then Nothing else Just n
  return (Coq.PiBinder n' ty' : ps')

-- env is innermost first order
translateTerm :: TermTranslationMonad m => Term -> m Coq.Term
translateTerm t = withLocalLocalEnvironment $ do -- traceTerm "translateTerm" t $
  env <- view localEnvironment <$> get
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr (go env) tf
    (asPi -> Just _) -> do
      paramTerms <- translatePiParams params
      Coq.Pi <$> pure paramTerms
                 -- env is in innermost first (reverse) binder order
                 <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asPiList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params
    (asLambda -> Just _) -> do
      paramTerms <- translateParams params
      Coq.Lambda <$> pure paramTerms
                 -- env is in innermost first (reverse) binder order
                 <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asLambdaList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params
    (asApp -> Just _) ->
      -- asApplyAll: innermost argument first
      let (f, args) = asApplyAll t
      in case f of
           (asGlobalDef -> Just i) ->
             case i of
                "Prelude.ite" -> case args of
                  [_ty, c, tt, ft] ->
                    Coq.If <$> go env c <*> go env tt <*> go env ft
                  _ -> badTerm
                "Prelude.fix" -> case args of
                  [resultType, lambda] ->
                    case resultType of
                      -- TODO: check that 'n' is finite
                      (asSeq -> Just (n, _)) ->
                        case lambda of
                          (asLambda -> Just (x, ty, body)) | ty == resultType -> do
                              len <- go env n
                              -- let len = EC.App (EC.ModVar "size") [EC.ModVar x]
                              expr <- go (x:env) body
                              typ <- go env ty
                              return $ Coq.App (Coq.Var "iter") [len, Coq.Lambda [Coq.Binder x (Just typ)] expr, Coq.List []]
                          _ -> badTerm
                      _ -> notSupported
                  _ -> badTerm
                _ ->
                  case atUseSite (findSpecialTreatment i) of
                  UseReplace replacement -> return replacement
                  _ -> Coq.App <$> go env f
                               <*> traverse (go env) args
           _ -> Coq.App <$> go env f
                        <*> traverse (go env) args
    (asLocalVar -> Just n)
      | n < length env -> Coq.Var <$> pure (env !! n)
      | otherwise -> Except.throwError $ LocalVarOutOfBounds t
    (unwrapTermF -> Constant n body _) -> do
      configuration <- ask
      decls <- view declarations <$> get
      if | not (traverseConsts configuration) || any (matchDecl n) decls -> Coq.Var <$> pure n
         | otherwise -> do
             b <- go env body
             modify $ over declarations $ (mkDefinition n b :)
             Coq.Var <$> pure n
    _ -> {- trace "translateTerm fallthrough" -} notSupported
  where
    notSupported = Except.throwError $ NotSupported t
    badTerm = Except.throwError $ BadTerm t
    matchDecl n (Coq.Axiom n' _) = n == n'
    matchDecl _ (Coq.Comment _) = False
    matchDecl n (Coq.Definition n' _ _ _) = n == n'
    matchDecl n (Coq.InductiveDecl (Coq.Inductive n' _ _ _ _)) = n == n'
    matchDecl _ (Coq.Snippet _) = False
    go env term = do
      modify $ set localEnvironment env
      translateTerm term

translateTermToDocWith ::
  TranslationConfiguration -> (Coq.Term -> Doc) -> Term -> Either (TranslationError Term) Doc
translateTermToDocWith configuration _f t = do
  (_term, state) <- runTermTranslationMonad configuration (translateTerm t)
  let decls = view declarations state
  return
    $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls)
    -- <$$> (if null decls then empty else hardline)
    -- <$$> f term

translateDefDoc ::
  TranslationConfiguration -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
translateDefDoc configuration name =
  translateTermToDocWith configuration (\ term -> Coq.ppDecl (mkDefinition name term))
