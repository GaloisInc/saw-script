{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
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

module Verifier.SAW.Translation.Coq where

import Control.Lens (makeLenses, over, set, view)
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Fail as Fail
import Control.Monad.Reader hiding (fail)
import Control.Monad.State hiding (fail, state)
import Data.List (intersperse)
import qualified Data.Map as Map
import Prelude hiding (fail)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Language.Coq.AST as Coq
import qualified Language.Coq.Pretty as Coq
import Verifier.SAW.Module
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor
--import Verifier.SAW.Term.Pretty
-- import qualified Verifier.SAW.UntypedAST as Un
import qualified Data.Vector as Vector (reverse, toList)

--import Debug.Trace

data TranslationError a
  = NotSupported a
  | NotExpr a
  | NotType a
  | LocalVarOutOfBounds a
  | BadTerm a

showError :: (a -> String) -> TranslationError a -> String
showError printer err = case err of
  NotSupported a -> "Not supported: " ++ printer a
  NotExpr a      -> "Expecting an expression term: " ++ printer a
  NotType a      -> "Expecting a type term: " ++ printer a
  LocalVarOutOfBounds a -> "Local variable reference is out of bounds: " ++ printer a
  BadTerm a -> "Malformed term: " ++ printer a

instance {-# OVERLAPPING #-} Show (TranslationError Term) where
  show = showError showTerm

instance {-# OVERLAPPABLE #-} Show a => Show (TranslationError a) where
  show = showError show

data TranslationConfiguration = TranslationConfiguration
  { transleVectorsAsCoqVectors :: Bool -- ^ when `False`, transle vectors as Coq lists
  , traverseConsts            :: Bool
  }

data TranslationState = TranslationState
  { _declarations :: [Coq.Decl]
  , _environment  :: [String]
  }
  deriving (Show)
makeLenses ''TranslationState

type MonadCoqTrans m =
  ( Except.MonadError (TranslationError Term)  m
  , MonadReader       TranslationConfiguration m
  , MonadState        TranslationState         m
  )

showFTermF :: FlatTermF Term -> String
showFTermF = show . Unshared . FTermF

cryptolPreludeMap :: Map.Map String String
cryptolPreludeMap = Map.fromList
  [ ("repeat", "cryptolRepeat")
  , ("take", "cryptolTake")
  , ("drop", "cryptolDrop")
  , ("/\\", "cryptolAnd")
  ]

identMap :: Map.Map Ident Coq.Ident
identMap = Map.fromList
  [ ("Prelude.Bool", "bool")
  , ("Prelude.False", "false")
  , ("Prelude.True", "true")
  , ("Prelude.Nat", "nat")
  , ("Prelude.Vec", "sawVec")
  , ("Prelude.append", "vecAppend")
  , ("Cryptol.ecCat", "seqCat")
  , ("Cryptol.ecNumber", "ecNumber")
  , ("Prelude.take", "vecTake")
  , ("Prelude.drop", "vecDrop")
  , ("Prelude.zip", "vecZip")
  , ("Cryptol.seq", "seq")
  , ("Cryptol.seqZip", "seqZip")
  , ("Prelude.zipWith", "sawZipWith")
  , ("Prelude.uncurry", "sawUncurry")
  , ("Prelude.map", "vecMap")
  , ("Prelude.coerce", "sawCoerce")
  , ("Prelude.unsafeCoerce", "sawUnsafeCoerce")
  , ("Prelude.unsafeAssert", "sawUnsafeAssert")
  , ("Cryptol.seqMap", "seqMap")
  , ("Prelude.bvXor", "sawBVXor")
  , ("Cryptol.ecDemote", "ecDemote")
  , ("Cryptol.ecJoin", "ecJoin")
  , ("Cryptol.ecSplit", "ecSplit")
  , ("Cryptol.ecSplitAt", "ecSplitAt")
  , ("Cryptol.Num", "Num")
  , ("Cryptol.TCNum", "TCNum")
  , ("Cryptol.tcAdd", "tcAdd")
  , ("Cryptol.tcSub", "tcSub")
  , ("Cryptol.tcMul", "tcMul")
  , ("Cryptol.tcMin", "tcMin")
  , ("Cryptol.ecEq", "ecEq")
  , ("Cryptol.ecGt", "ecGt")
  , ("Cryptol.seqEq1", "seqEq1")
  , ("Prelude.eq", "sawEq")
  , ("Cryptol.ecAnd", "ecAnd")
  , ("Cryptol.ecOr", "ecOr")
  , ("Cryptol.ecXor", "ecXor")
  , ("Cryptol.PLogicBit", "PLogicBit")
  , ("Cryptol.PLogicSeq", "PLogicSeq")
  , ("Cryptol.PLogicSeqBool", "PLogicSeqBool")
  , ("Cryptol.PLogicWord", "PLogicSeqBool")
  , ("Cryptol.PCmpBit", "PCmpBit")
  , ("Cryptol.PCmpSeq", "PCmpSeq")
  , ("Cryptol.PCmpSeqBool", "PCmpSeqBool")
  , ("Cryptol.PCmpWord", "PCmpSeqBool")
  , ("Cryptol.PZeroBit", "PZeroBit")
  , ("Cryptol.PZeroSeq", "PZeroSeq")
  , ("Cryptol.PZeroSeqBool", "PZeroSeqBool")
  , ("Cryptol.PZeroWord", "PZeroSeqBool")
  , ("Cryptol.PLiteralSeqBool", "PLiteralSeqBool")
  ]

transleIdent :: Ident -> Coq.Ident
transleIdent i = Map.findWithDefault (show i) i identMap

{-
traceFTermF :: String -> FlatTermF Term -> a -> a
traceFTermF ctx tf = traceTerm ctx (Unshared $ FTermF tf)

traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

transleBinder ::
  MonadCoqTrans m =>
  (Ident, Term) -> m (Coq.Ident, Coq.Term)
transleBinder (ident, term) = (,) <$> pure (transleIdent ident) <*> transleTerm term

transleCtor ::
  MonadCoqTrans m =>
  Ctor -> m Coq.Constructor
transleCtor (Ctor {..}) = do
  let constructorName = transleIdent ctorName
  constructorType <- transleTerm ctorType
  return $ Coq.Constructor
    { constructorName
    , constructorType
    }

transleDataType :: MonadCoqTrans m => DataType -> m Coq.Decl
transleDataType (DataType {..}) = do
  let inductiveName = identName dtName -- eventually, might want the modules too
  let mkParamIndex (s, t) = do
        t' <- transleTerm t
        return (s, t')
  inductiveParameters   <- mapM mkParamIndex dtParams
  inductiveIndices      <- mapM mkParamIndex dtIndices
  inductiveSort         <- transleSort dtSort
  inductiveConstructors <- mapM transleCtor dtCtors
  return $ Coq.InductiveDecl $ Coq.Inductive
    { inductiveName
    , inductiveParameters
    , inductiveIndices
    , inductiveSort
    , inductiveConstructors
    }

transleModuleDecl :: MonadCoqTrans m => ModuleDecl -> m Coq.Decl
transleModuleDecl = \case
  TypeDecl dataType -> transleDataType dataType
  DefDecl definition -> transleDef definition

transleDef :: MonadCoqTrans m => Def -> m Coq.Decl
transleDef (Def {..}) =
  case defQualifier of
  NoQualifier -> case defBody of
    Nothing   -> error "Terms should have a body (unless axiom/primitive)"
    Just body -> Coq.Definition
                 <$> pure (transleIdent defIdent)
                 <*> pure []
                 <*> (Just <$> transleTerm defType)
                 <*> transleTerm body
  AxiomQualifier -> Coq.Axiom
                    <$> pure (transleIdent defIdent)
                    <*> transleTerm defType
  PrimQualifier -> Coq.Axiom
                   <$> pure (transleIdent defIdent)
                   <*> transleTerm defType

transleSort :: MonadCoqTrans m => Sort -> m Coq.Sort
transleSort s = pure (if s == propSort then Coq.Prop else Coq.Type)

flatTermFToExpr ::
  MonadCoqTrans m =>
  (Term -> m Coq.Term) ->
  FlatTermF Term ->
  m Coq.Term
flatTermFToExpr go tf = -- traceFTermF "flatTermFToExpr" tf $
  case tf of
    GlobalDef i   -> pure (Coq.Var (transleIdent i))
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      -> pure (Coq.Var "unit")
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse go [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse go [x, y]
    PairLeft t    -> Coq.App (Coq.Var "fst") <$> traverse go [t]
    PairRight t   -> Coq.App (Coq.Var "snd") <$> traverse go [t]
    -- TODO: maybe have more customizable translation of data types
    DataTypeApp n is as -> do
      Coq.App (Coq.Var (transleIdent n)) <$> traverse go (is ++ as)
    -- TODO: maybe have more customizable translation of data constructors
    CtorApp n is as -> do
      Coq.App (Coq.Var (transleIdent n)) <$> traverse go (is ++ as)
    -- TODO: support this next!
    RecursorApp _ _ _ _ _ _ -> notSupported
    Sort s -> Coq.Sort <$> transleSort s
    NatLit i -> pure (Coq.NatLit i)
    ArrayValue _ vec -> do
      config <- ask
      if transleVectorsAsCoqVectors config
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
      foldM addField (Coq.Var "FSnil") fs
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

mkDefinition :: Coq.Ident -> Coq.Term -> Coq.Decl
mkDefinition name (Coq.Lambda bs t) = Coq.Definition name bs Nothing t
mkDefinition name t = Coq.Definition name [] Nothing t

-- mkConstructor :: Un.CtorDecl -> Coq.Constructor
-- mkConstructor (Un.Ctor n ctx t) = _

transleParams ::
  MonadCoqTrans m =>
  [(String, Term)] -> m [Coq.Binder]
transleParams [] = return []
transleParams ((n, ty):ps) = do
  ty' <- transleTerm ty
  modify $ over environment (n :)
  ps' <- transleParams ps
  return (Coq.Binder n (Just ty') : ps')

translePiParams :: MonadCoqTrans m => [(String, Term)] -> m [Coq.PiBinder]
translePiParams [] = return []
translePiParams ((n, ty):ps) = do
  ty' <- transleTerm ty
  modify $ over environment (n :)
  ps' <- translePiParams ps
  let n' = if n == "_" then Nothing else Just n
  return (Coq.PiBinder n' ty' : ps')

-- TODO: I quickly fixed this to use a state monad, but the old code passed
-- `env` explicitly.  To make refactor faster, I left the code as-is, only
-- modifying what `go` meant.  This can be changed later.

-- env is innermost first order
transleTerm :: MonadCoqTrans m => Term -> m Coq.Term
transleTerm t = do -- traceTerm "transleTerm" t $
  env <- view environment <$> get
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr (go env) tf
    (asPi -> Just _) -> do
      paramTerms <- translePiParams params
      Coq.Pi <$> pure paramTerms
                 -- env is in innermost first (reverse) binder order
                 <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asPiList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params
    (asLambda -> Just _) -> do
      paramTerms <- transleParams params
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
      if | n `Map.member` cryptolPreludeMap ->
             Coq.Var <$> pure (cryptolPreludeMap Map.! n)
         | not (traverseConsts configuration) || any (matchDecl n) decls -> Coq.Var <$> pure n
         | otherwise -> do
             b <- go env body
             modify $ over declarations $ (mkDefinition n b :)
             Coq.Var <$> pure n
    _ -> {- trace "transleTerm fallthrough" -} notSupported
  where
    notSupported = Except.throwError $ NotSupported t
    badTerm = Except.throwError $ BadTerm t
    matchDecl n (Coq.Axiom n' _) = n == n'
    matchDecl n (Coq.Definition n' _ _ _) = n == n'
    matchDecl n (Coq.InductiveDecl (Coq.Inductive n' _ _ _ _)) = n == n'
    go env term = do
      modify $ set environment env
      transleTerm term

runMonadCoqTrans ::
  TranslationConfiguration ->
  (forall m. MonadCoqTrans m => m a) ->
  Either (TranslationError Term) (a, TranslationState)
runMonadCoqTrans configuration m =
  runStateT (runReaderT m configuration) (TranslationState [] [])

transleTermToDocWith :: TranslationConfiguration -> (Coq.Term -> Doc) -> Term -> Either (TranslationError Term) Doc
transleTermToDocWith configuration f t = do
  (term, state) <- runMonadCoqTrans configuration (transleTerm t)
  let decls = view declarations state
  return $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls) <$$>
           (if null decls then empty else hardline) <$$>
           f term

transleDefDoc :: TranslationConfiguration -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
transleDefDoc configuration name = transleTermToDocWith configuration (\ term -> Coq.ppDecl (mkDefinition name term))

transleDeclImports :: TranslationConfiguration -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
transleDeclImports configuration name t = do
  doc <- transleDefDoc configuration name t
  let imports = vcat [ "From Coq          Require Import Lists.List."
                     , "From Coq          Require Import String."
                     , "From Coq          Require Import Vectors.Vector."
                     , "From Records      Require Import Records."
                     , "From CryptolToCoq Require Import Cryptol."
                     , "From CryptolToCoq Require Import SAW."
                     , "Import ListNotations."
                     ]
  return (imports <$$> hardline <> doc)
