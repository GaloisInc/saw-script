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

import Control.Lens (_1, makeLenses, over, set, view)
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
-- import Verifier.SAW.Term.CtxTerm
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
  { translateVectorsAsCoqVectors :: Bool -- ^ when `False`, translate vectors as Coq lists
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

data SpecialTreatment
  = MapsTo Ident
  | Rename String
  | Skip

mkCoqIdent :: String -> String -> Ident
mkCoqIdent coqModule coqIdent = mkIdent (mkModuleName [coqModule]) coqIdent

preludeSpecialTreatmentMap :: Map.Map String SpecialTreatment
preludeSpecialTreatmentMap = Map.fromList $ []

  -- Unsafe SAW features
  ++
  [ ("coerce",            Skip)
  , ("coerce__def",       Skip)
  , ("coerce__eq",        Skip)
  , ("error",             MapsTo $ mkCoqIdent "CryptolToCoq.SAW" "error")
  , ("fix",               Skip)
  , ("rcoerce",           Skip)
  , ("unsafeAssert",      Skip)
  , ("unsafeCoerce",      Skip)
  , ("unsafeCoerce_same", Skip)
  ]

  -- Unit
  ++
  [ ("Unit",              MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "tt")
  , ("UnitType",          MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "unit")
  , ("UnitType__rec",     MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "unit_rect")
  ]

  -- Records
  ++
  [ ("EmptyType",         Skip)
  , ("EmptyType__rec",    Skip)
  , ("RecordType",        Skip)
  , ("RecordType__rec",   Skip)
  ]

  -- Decidable equality, does not make sense in Coq unless turned into a type
  -- class
  ++
  [ ("eq",                MapsTo $ mkCoqIdent "CryptolToCoq.SAW" "eq")
  , ("eq_refl",           MapsTo $ mkCoqIdent "CryptolToCow.SAW" "eq_refl")
  , ("eq_Bool",           MapsTo $ mkCoqIdent "CryptolToCow.SAW" "eq_Bool")
  -- not sure whether those are used
  , ("ite_eq_cong_1",     Skip)
  , ("ite_eq_cong_2",     Skip)
  ]

  -- Boolean
  ++
  [ ("and",               MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "andb")
  , ("and__eq",           MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "andb__eq")
  , ("Bool",              MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "Bool")
  , ("boolEq",            MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "boolEq")
  , ("boolEq__eq",        MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "eqb__eq")
  , ("False",             MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "false")
  , ("ite",               MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "ite")
  , ("iteDep",            MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "iteDep")
  , ("iteDep_True",       MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "iteDep_True")
  , ("iteDep_False",      MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "iteDep_False")
  , ("ite_bit",           Skip) -- FIXME: change this
  , ("ite_eq_iteDep",     MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "ite_eq_iteDep")
  , ("not",               MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "negb")
  , ("not__eq",           MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "negb__eq")
  , ("or",                MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "orb")
  , ("or__eq",            MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "orb__eq")
  , ("True",              MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "true")
  , ("xor",               MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "xorb")
  , ("xor__eq",           MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "xorb__eq")
  ]

  -- Pairs
  ++
  [ ("PairType",          MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "prod")
  , ("PairValue",         MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "pair")
  , ("Pair__rec",         MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "prod_rect")
  , ("fst",               MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "fst")
  , ("snd",               MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "snd")
  ]

  -- Equality
  ++
  [ ("Eq",                MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "identity")
  , ("Eq__rec",           MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "identity_rect")
  , ("Refl",              MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "identity_refl")
  ]

  -- Strings
  ++
  [ ("String",            MapsTo $ mkCoqIdent "Coq.Strings.String" "string")
  ]

  -- Utility functions
  ++
  [ ("id",                MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "id")
  , ("uncurry",           Rename "sawUncurry")
  ]

  -- Natural numbers
  ++
  [ ("divModNat",         MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "divModNat")
  , ("eq_Nat",            Skip)
  , ("Nat",               MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "nat")
  , ("widthNat",          MapsTo $ mkCoqIdent "CryptolToCoq.SAW"   "widthNat")
  , ("Zero",              MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "O")
  , ("Succ",              MapsTo $ mkCoqIdent "Coq.Init.Datatypes" "S")
  ]

  -- Vectors
  ++
  [ ("at",                Rename "sawAt") -- `at` is a reserved keyword in Coq
  , ("atWithDefault",     MapsTo $ mkCoqIdent "CryptolToCoq.VectorExtras" "vectorAtWithDefault")
  , ("coerceVec",         Skip)
  , ("EmptyVec",          MapsTo $ mkCoqIdent "Coq.Vectors.Vector"        "nil")
  , ("eq_Vec",            Skip)
  , ("gen",               MapsTo $ mkCoqIdent "CryptolToCoq.VectorExtras" "vectorGen")
  , ("take0",             Skip)
  -- cannot map directly to Vector.t because arguments are in a different order
  , ("Vec",               MapsTo $ mkCoqIdent "CryptolToCoq.SAW"          "sawVec")
  ]

specialTreatmentMap :: Map.Map ModuleName (Map.Map String SpecialTreatment)
specialTreatmentMap = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  [ ("Prelude", preludeSpecialTreatmentMap)
  ]

cryptolPreludeMap :: Map.Map String String
cryptolPreludeMap = Map.fromList
  [ ("repeat", "cryptolRepeat")
  , ("take", "cryptolTake")
  , ("drop", "cryptolDrop")
  , ("/\\", "cryptolAnd")
  ]

-- identMap :: Map.Map Ident Coq.Ident
-- identMap = Map.fromList
--   [ ("Prelude.Bool", "bool")
--   , ("Prelude.False", "false")
--   , ("Prelude.True", "true")
--   , ("Prelude.Nat", "nat")
--   , ("Prelude.Vec", "sawVec")
--   , ("Prelude.append", "vecAppend")
--   , ("Cryptol.ecCat", "seqCat")
--   , ("Cryptol.ecNumber", "ecNumber")
--   , ("Prelude.take", "vecTake")
--   , ("Prelude.drop", "vecDrop")
--   , ("Prelude.zip", "vecZip")
--   , ("Cryptol.seq", "seq")
--   , ("Cryptol.seqZip", "seqZip")
--   , ("Prelude.zipWith", "sawZipWith")
--   , ("Prelude.uncurry", "sawUncurry")
--   , ("Prelude.map", "vecMap")
--   , ("Prelude.coerce", "sawCoerce")
--   , ("Prelude.unsafeCoerce", "sawUnsafeCoerce")
--   , ("Prelude.unsafeAssert", "sawUnsafeAssert")
--   , ("Cryptol.seqMap", "seqMap")
--   , ("Prelude.bvXor", "sawBVXor")
--   , ("Cryptol.ecDemote", "ecDemote")
--   , ("Cryptol.ecJoin", "ecJoin")
--   , ("Cryptol.ecSplit", "ecSplit")
--   , ("Cryptol.ecSplitAt", "ecSplitAt")
--   , ("Cryptol.Num", "Num")
--   , ("Cryptol.TCNum", "TCNum")
--   , ("Cryptol.tcAdd", "tcAdd")
--   , ("Cryptol.tcSub", "tcSub")
--   , ("Cryptol.tcMul", "tcMul")
--   , ("Cryptol.tcMin", "tcMin")
--   , ("Cryptol.ecEq", "ecEq")
--   , ("Cryptol.ecGt", "ecGt")
--   , ("Cryptol.seqEq1", "seqEq1")
--   , ("Prelude.eq", "sawEq")
--   , ("Cryptol.ecAnd", "ecAnd")
--   , ("Cryptol.ecOr", "ecOr")
--   , ("Cryptol.ecXor", "ecXor")
--   , ("Cryptol.PLogicBit", "PLogicBit")
--   , ("Cryptol.PLogicSeq", "PLogicSeq")
--   , ("Cryptol.PLogicSeqBool", "PLogicSeqBool")
--   , ("Cryptol.PLogicWord", "PLogicSeqBool")
--   , ("Cryptol.PCmpBit", "PCmpBit")
--   , ("Cryptol.PCmpSeq", "PCmpSeq")
--   , ("Cryptol.PCmpSeqBool", "PCmpSeqBool")
--   , ("Cryptol.PCmpWord", "PCmpSeqBool")
--   , ("Cryptol.PZeroBit", "PZeroBit")
--   , ("Cryptol.PZeroSeq", "PZeroSeq")
--   , ("Cryptol.PZeroSeqBool", "PZeroSeqBool")
--   , ("Cryptol.PZeroWord", "PZeroSeqBool")
--   , ("Cryptol.PLiteralSeqBool", "PLiteralSeqBool")
--   ]

findSpecialTreatment :: Ident -> Maybe SpecialTreatment
findSpecialTreatment ident =
  let moduleMap = Map.findWithDefault Map.empty (identModule ident) specialTreatmentMap in
  Map.findWithDefault Nothing (identName ident) (Just <$> moduleMap)

findIdentTranslation :: Ident -> Ident
findIdentTranslation i =
  case findSpecialTreatment i of
  Nothing -> i
  Just st ->
    case st of
    MapsTo ident   -> ident
    Rename newName -> mkIdent (identModule i) newName
    Skip           -> i -- do we want a marker to indicate this will likely fail?

translateIdent :: Ident -> Coq.Ident
translateIdent = show . findIdentTranslation

translateIdentUnqualified :: Ident -> Coq.Ident
translateIdentUnqualified = identName .  findIdentTranslation

{-
traceFTermF :: String -> FlatTermF Term -> a -> a
traceFTermF ctx tf = traceTerm ctx (Unshared $ FTermF tf)

traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

translateBinder ::
  MonadCoqTrans m =>
  (Ident, Term) -> m (Coq.Ident, Coq.Term)
translateBinder (ident, term) = (,) <$> pure (translateIdent ident) <*> translateTerm term

dropPi :: Coq.Term -> Coq.Term
dropPi (Coq.Pi (_ : t) r) = Coq.Pi t r
dropPi (Coq.Pi _       r) = dropPi r
dropPi t                  = t

-- dropModuleName :: String -> String
-- dropModuleName s =
--   case elemIndices '.' s of
--   [] -> s
--   indices ->
--     let lastIndex = last indices in
--     drop (lastIndex + 1) s

-- unqualifyTypeWithinConstructor :: Coq.Term -> Coq.Term
-- unqualifyTypeWithinConstructor = go
--   where
--     go (Coq.Pi bs t)  = Coq.Pi bs (go t)
--     go (Coq.App t as) = Coq.App (go t) as
--     go (Coq.Var v)    = Coq.Var (dropModuleName v)
--     go t              = error $ "Unexpected term in constructor: " ++ show t

translateCtor ::
  MonadCoqTrans m =>
  [Coq.Binder] -> -- list of parameters to drop from `ctorType`
  Ctor -> m Coq.Constructor
translateCtor inductiveParameters (Ctor {..}) = do
  let constructorName = translateIdentUnqualified ctorName
  constructorType <-
    -- Unfortunately, `ctorType` qualifies the inductive type's name in the
    -- return type.
    -- dropModuleNameWithinCtor <$>
    -- Unfortunately, `ctorType` comes with the inductive parameters universally
    -- quantified.
    (\ t -> iterate dropPi t !! length inductiveParameters) <$>
    translateTerm ctorType
  return $ Coq.Constructor
    { constructorName
    , constructorType
    }

translateDataType :: MonadCoqTrans m => DataType -> m Coq.Decl
translateDataType (DataType {..}) =
  case findSpecialTreatment dtName of
  Just st ->
    case st of
    MapsTo ident -> pure $ mapped  dtName ident
    Rename _     -> translate
    Skip         -> pure $ skipped dtName
  Nothing -> translate
  where
    translate = do
      let inductiveName = identName dtName -- TODO: do we want qualified?
      let mkParam (s, t) = do
            t' <- translateTerm t
            modify $ over environment (s :)
            return $ Coq.Binder s (Just t')
      let mkIndex (s, t) = do
            t' <- translateTerm t
            modify $ over environment (s :)
            let s' = case s of
                  "_" -> Nothing
                  _   -> Just s
            return $ Coq.PiBinder s' t'
      inductiveParameters   <- mapM mkParam dtParams
      inductiveIndices      <- mapM mkIndex dtIndices
      inductiveSort         <- translateSort dtSort
      inductiveConstructors <- mapM (translateCtor inductiveParameters) dtCtors
      return $ Coq.InductiveDecl $ Coq.Inductive
        { inductiveName
        , inductiveParameters
        , inductiveIndices
        , inductiveSort
        , inductiveConstructors
        }

translateModuleDecl :: MonadCoqTrans m => ModuleDecl -> m Coq.Decl
translateModuleDecl = \case
  TypeDecl dataType -> translateDataType dataType
  DefDecl definition -> translateDef definition

mapped :: Ident -> Ident -> Coq.Decl
mapped sawIdent newIdent =
  Coq.Comment $ show sawIdent ++ " is mapped to " ++ show newIdent

skipped :: Ident -> Coq.Decl
skipped sawIdent =
  Coq.Comment $ show sawIdent ++ " was skipped"

translateDef :: MonadCoqTrans m => Def -> m Coq.Decl
translateDef (Def {..}) =
  case findSpecialTreatment defIdent of
  Just st ->
    case st of
    MapsTo ident -> pure $ mapped  defIdent ident
    Rename _     -> translate
    Skip         -> pure $ skipped defIdent
  Nothing -> translate
  where
    translate =
      case defQualifier of
      NoQualifier ->
        case defBody of
        Nothing   -> error "Terms should have a body (unless axiom/primitive)"
        Just body -> Coq.Definition
                     <$> pure (translateIdentUnqualified defIdent)
                     <*> pure []
                     <*> (Just <$> translateTerm defType)
                     <*> translateTerm body
      AxiomQualifier -> Coq.Axiom
                        <$> pure (translateIdentUnqualified defIdent)
                        <*> translateTerm defType
      PrimQualifier -> Coq.Axiom
                       <$> pure (translateIdentUnqualified defIdent)
                       <*> translateTerm defType

translateSort :: MonadCoqTrans m => Sort -> m Coq.Sort
translateSort s = pure (if s == propSort then Coq.Prop else Coq.Type)

flatTermFToExpr ::
  MonadCoqTrans m =>
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
    Sort s -> Coq.Sort <$> translateSort s
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

translateParams ::
  MonadCoqTrans m =>
  [(String, Term)] -> m [Coq.Binder]
translateParams [] = return []
translateParams ((n, ty):ps) = do
  ty' <- translateTerm ty
  modify $ over environment (n :)
  ps' <- translateParams ps
  return (Coq.Binder n (Just ty') : ps')

translatePiParams :: MonadCoqTrans m => [(String, Term)] -> m [Coq.PiBinder]
translatePiParams [] = return []
translatePiParams ((n, ty):ps) = do
  ty' <- translateTerm ty
  modify $ over environment (n :)
  ps' <- translatePiParams ps
  let n' = if n == "_" then Nothing else Just n
  return (Coq.PiBinder n' ty' : ps')

-- | Run a translation, but keep changes to the environment local to it,
-- restoring the current environment before returning.
withLocalEnvironment :: MonadCoqTrans m => m a -> m a
withLocalEnvironment action = do
  env <- view environment <$> get
  result <- action
  modify $ set environment env
  return result

-- | This is a convenient helper for when you want to add some bindings before
-- translating a term.
translateTermLocallyBinding :: MonadCoqTrans m => [String] -> Term -> m Coq.Term
translateTermLocallyBinding bindings term =
  withLocalEnvironment $ do
  modify $ over environment (bindings ++)
  translateTerm term

-- env is innermost first order
translateTerm :: MonadCoqTrans m => Term -> m Coq.Term
translateTerm t = withLocalEnvironment $ do -- traceTerm "translateTerm" t $
  env <- view environment <$> get
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
    _ -> {- trace "translateTerm fallthrough" -} notSupported
  where
    notSupported = Except.throwError $ NotSupported t
    badTerm = Except.throwError $ BadTerm t
    matchDecl n (Coq.Axiom n' _) = n == n'
    matchDecl _ (Coq.Comment _) = False
    matchDecl n (Coq.Definition n' _ _ _) = n == n'
    matchDecl n (Coq.InductiveDecl (Coq.Inductive n' _ _ _ _)) = n == n'
    go env term = do
      modify $ set environment env
      translateTerm term

runMonadCoqTrans ::
  TranslationConfiguration ->
  (forall m. MonadCoqTrans m => m a) ->
  Either (TranslationError Term) (a, TranslationState)
runMonadCoqTrans configuration m =
  runStateT (runReaderT m configuration) (TranslationState [] [])

translateTermToDocWith :: TranslationConfiguration -> (Coq.Term -> Doc) -> Term -> Either (TranslationError Term) Doc
translateTermToDocWith configuration f t = do
  (term, state) <- runMonadCoqTrans configuration (translateTerm t)
  let decls = view declarations state
  return $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls) <$$>
           (if null decls then empty else hardline) <$$>
           f term

translateDefDoc :: TranslationConfiguration -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
translateDefDoc configuration name = translateTermToDocWith configuration (\ term -> Coq.ppDecl (mkDefinition name term))

translateDeclImports :: TranslationConfiguration -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
translateDeclImports configuration name t = do
  doc <- translateDefDoc configuration name t
  let imports = vcat [ "From Coq          Require Import Lists.List."
                     , "From Coq          Require Import String."
                     , "From Coq          Require Import Vectors.Vector."
                     , "From Records      Require Import Records."
                     , "From CryptolToCoq Require Import Cryptol."
                     , "From CryptolToCoq Require Import SAW."
                     , "Import ListNotations."
                     ]
  return (imports <$$> hardline <> doc)
