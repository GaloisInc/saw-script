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

module Verifier.SAW.Translation.Coq where

import Control.Lens (_1, _2, makeLenses, over, set, view)
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Fail as Fail
import Control.Monad.Reader hiding (fail)
import Control.Monad.State hiding (fail, state)
import Data.List (intersperse)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.String.Interpolate as I
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
  , traverseConsts               :: Bool
  }

data ModuleTranslationState = ModuleTranslationState
  { _alreadyTranslated :: [Ident]
  , _globalEnvironment :: [String]
  }
  deriving (Show)
makeLenses ''ModuleTranslationState

data TermTranslationState = TermTranslationState
  { _declarations      :: [Coq.Decl]
  , _localEnvironment  :: [String]
  }
  deriving (Show)
makeLenses ''TermTranslationState

type TranslationMonad s m =
  ( Except.MonadError (TranslationError Term)  m
  , MonadReader       TranslationConfiguration m
  , MonadState        s                        m
  )

type ModuleTranslationMonad m = TranslationMonad ModuleTranslationState m
type TermTranslationMonad   m = TranslationMonad TermTranslationState   m

showFTermF :: FlatTermF Term -> String
showFTermF = show . Unshared . FTermF

data SpecialTreatment = SpecialTreatment
  { moduleRenaming        :: Map.Map ModuleName String
  , identSpecialTreatment :: Map.Map ModuleName (Map.Map String IdentSpecialTreatment)
  }

data DefSiteTreatment
  = DefPreserve
  | DefRename   (Maybe ModuleName) String -- optional module rename, then identifier itself
  | DefReplace  String
  | DefSkip

data UseSiteTreatment
  = UsePreserve
  | UseRename   (Maybe ModuleName) String
  | UseReplace  Coq.Term

data IdentSpecialTreatment = IdentSpecialTreatment
  { atDefSite :: DefSiteTreatment
  , atUseSite :: UseSiteTreatment
  }

-- Use `mapsTo` for identifiers whose definition has a matching definition
-- already on the Coq side.  As such, their definition can be skipped, and use
-- sites can be replaced by the appropriate call.
mapsTo :: ModuleName -> String -> IdentSpecialTreatment
mapsTo targetModule targetName = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseRename (Just targetModule) targetName
  }

-- Use `realize` for axioms that can be realized, or for primitives that must be
-- realized.  While some primitives can be written directly in a standalone Coq
-- module, some primitives depend on code from the extracted module, and are
-- depended upon by following code in the same module.  Such primitives can
-- therefore *neither* be defined a priori, *nor* a posteriori, and must be
-- realized where they were originally declared.
realize :: String -> IdentSpecialTreatment
realize code = IdentSpecialTreatment
  { atDefSite = DefReplace code
  , atUseSite = UsePreserve
  }

-- Use `rename` for identifiers whose definition can be translated, but has to
-- be renamed.  This is useful for certain definitions whose name on the
-- SAWCore/Cryptol side clashes with names on the Coq side.  For instance, `at`
-- is a reserved Coq keyword, but is used as a function name in SAWCore Prelude.
rename :: String -> IdentSpecialTreatment
rename ident = IdentSpecialTreatment
  { atDefSite = DefRename Nothing ident
  , atUseSite = UseRename Nothing ident
  }

-- TODO: document me
replace :: Coq.Term -> IdentSpecialTreatment
replace term = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UseReplace term
  }

-- Use `skip` for identifiers that are already defined in the appropriate module
-- on the Coq side.
skip :: IdentSpecialTreatment
skip = IdentSpecialTreatment
  { atDefSite = DefSkip
  , atUseSite = UsePreserve
  }

-- data IdentSpecialTreatment
--   = MapsTo  Ident    -- means "don't translate its definition, instead use provided"
--   | Realize String   -- inserts the string in the file to realize a primitive in place
--                      -- this is necessary when there is a primitive that depends
--                      -- on some definitions, but that subsequent definitions
--                      -- depend upon: thus is can not be defined in a separate file
--                      -- without code duplication and needs to be realized in-place
--   | Rename  String   -- means "translate its definition, but rename it"
--   | Replace Coq.Term -- skip definition site, replace with term at use sites
--   | Skip             -- means "don't translate its definition, no replacement"

mkCoqIdent :: String -> String -> Ident
mkCoqIdent coqModule coqIdent = mkIdent (mkModuleName [coqModule]) coqIdent

sawDefinitionsModule :: ModuleName
sawDefinitionsModule = mkModuleName ["SAW"]

cryptolPreludeModule :: ModuleName
cryptolPreludeModule = mkModuleName ["CryptolPrelude"]

cryptolToCoqModule :: ModuleName
cryptolToCoqModule = mkModuleName ["CryptolToCoq"]

-- NOTE: while I initially did the mapping from SAW core names to the
-- corresponding Coq construct here, it makes the job of translating SAW core
-- axioms into Coq theorems much more annoying, because one needs to manually
-- rename every constant mentioned in the statement to its Coq counterpart.
-- Instead, I am now trying to keep the names the same as much as possible
-- during this translation (it is sometimes impossible, for instance, `at` is a
-- reserved keyword in Coq), so that primitives' and axioms' types can be
-- copy-pasted as is on the Coq side.
sawCorePreludeSpecialTreatmentMap :: Map.Map String IdentSpecialTreatment
sawCorePreludeSpecialTreatmentMap = Map.fromList $ []

  -- Unsafe SAW features
  ++
  [ ("error",             mapsTo sawDefinitionsModule "error")
  , ("fix",               skip)
  , ("unsafeAssert",      rename "sawUnsafeAssert")
  , ("unsafeCoerce",      skip)
  , ("unsafeCoerce_same", skip)
  ]

  -- coercions
  ++
  [ ("coerce",            mapsTo sawDefinitionsModule "coerce")
  , ("coerce__def",       skip)
  , ("coerce__eq",        skip)
  , ("rcoerce",           skip)
  ]

  -- Unit
  ++
  [ ("Unit",              mapsTo sawDefinitionsModule "Unit")
  , ("UnitType",          mapsTo sawDefinitionsModule "UnitType")
  , ("UnitType__rec",     mapsTo sawDefinitionsModule "UnitType__rec")
  ]

  -- Records
  ++
  [ ("EmptyType",         skip)
  , ("EmptyType__rec",    skip)
  , ("RecordType",        skip)
  , ("RecordType__rec",   skip)
  ]

  -- Decidable equality, does not make sense in Coq unless turned into a type
  -- class
  -- Apparently, this is not used much for Cryptol, so we can skip it.
  ++
  [ ("eq",                skip) -- MapsTo $ mkCoqIdent sawDefinitionsModule "eq")
  , ("eq_bitvector",      skip)
  , ("eq_Bool",           skip) -- MapsTo $ mkCoqIdent "CryptolToCoq.SAW" "eq_Bool")
  , ("eq_Nat",            skip)
  , ("eq_refl",           skip) -- MapsTo $ mkCoqIdent "CryptolToCoq.SAW" "eq_refl")
  , ("eq_VecBool",        skip)
  , ("eq_VecVec",         skip)
  , ("ite_eq_cong_1",     skip)
  , ("ite_eq_cong_2",     skip)
  ]

  -- Boolean
  ++
  [ ("and",               mapsTo sawDefinitionsModule "and")
  , ("and__eq",           mapsTo sawDefinitionsModule "and__eq")
  , ("Bool",              mapsTo sawDefinitionsModule "Bool")
  , ("boolEq",            mapsTo sawDefinitionsModule "boolEq")
  , ("boolEq__eq",        mapsTo sawDefinitionsModule "boolEq__eq")
  , ("False",             mapsTo sawDefinitionsModule "False")
  , ("ite",               mapsTo sawDefinitionsModule "ite")
  , ("iteDep",            mapsTo sawDefinitionsModule "iteDep")
  , ("iteDep_True",       mapsTo sawDefinitionsModule "iteDep_True")
  , ("iteDep_False",      mapsTo sawDefinitionsModule "iteDep_False")
  , ("ite_bit",           skip) -- FIXME: change this
  , ("ite_eq_iteDep",     mapsTo sawDefinitionsModule "ite_eq_iteDep")
  , ("not",               mapsTo sawDefinitionsModule "not")
  , ("not__eq",           mapsTo sawDefinitionsModule "not__eq")
  , ("or",                mapsTo sawDefinitionsModule "or")
  , ("or__eq",            mapsTo sawDefinitionsModule "or__eq")
  , ("True",              mapsTo sawDefinitionsModule "True")
  , ("xor",               mapsTo sawDefinitionsModule "xor")
  , ("xor__eq",           mapsTo sawDefinitionsModule "xor__eq")
  ]

  -- Pairs
  ++
  [ ("PairType",          mapsTo sawDefinitionsModule "PairType")
  , ("PairValue",         mapsTo sawDefinitionsModule "PairValue")
  , ("Pair__rec",         mapsTo sawDefinitionsModule "Pair__rec")
  , ("fst",               mapsTo sawDefinitionsModule "fst")
  , ("snd",               mapsTo sawDefinitionsModule "snd")
  ]

  -- Equality
  ++
  [ ("Eq",                mapsTo sawDefinitionsModule "Eq")
  , ("Eq__rec",           mapsTo sawDefinitionsModule "Eq__rec")
  , ("Refl",              mapsTo sawDefinitionsModule "Refl")
  ]

  -- Strings
  ++
  [ ("String",            mapsTo sawDefinitionsModule "String")
  ]

  -- Utility functions
  ++
  [ ("id",                mapsTo sawDefinitionsModule "id")
  ]

  -- Natural numbers
  ++
  [ ("divModNat",         mapsTo sawDefinitionsModule "divModNat")
  , ("Nat",               mapsTo sawDefinitionsModule "Nat")
  , ("widthNat",          mapsTo sawDefinitionsModule "widthNat")
  , ("Zero",              mapsTo cryptolToCoqModule   "Zero")
  , ("Succ",              mapsTo cryptolToCoqModule   "Succ")
  ]

  -- Vectors
  ++
  [ ("at",                rename "sawAt") -- `at` is a reserved keyword in Coq
  , ("at_single",         skip) -- is boring, could be proved on the Coq side
  , ("atWithDefault",     mapsTo sawDefinitionsModule "atWithDefault")
  , ("coerceVec",         mapsTo sawDefinitionsModule "coerceVec")
  , ("EmptyVec",          mapsTo sawDefinitionsModule "EmptyVec")
  , ("eq_Vec",            skip)
  , ("foldr",             mapsTo sawDefinitionsModule "foldr")
  , ("gen",               mapsTo sawDefinitionsModule "gen")
  , ("take0",             skip)
  -- cannot map directly to Vector.t because arguments are in a different order
  , ("zip",               realize zipSnippet)
  , ("Vec",               mapsTo sawDefinitionsModule "Vec")
  ]

zipSnippet :: String
zipSnippet = [I.i|
Fixpoint zip (a b : sort 0) (m n : Nat) (xs : Vec m a) (ys : Vec n b) : Vec (minNat m n) (a * b) :=
  match
    xs in Vector.t _ m'
    return Vector.t _ (minNat m' n)
  with
  | Vector.nil _ => Vector.nil _
  | Vector.cons _ x pm xs =>
    match
      ys in Vector.t _ n'
      return Vector.t _ (minNat (S pm) n')
    with
    | Vector.nil _ => Vector.nil _
    | Vector.cons _ y pm' ys => Vector.cons _ (x, y) _ (zip _ _ _ _ xs ys)
    end
  end
.
|]

cryptolPreludeSpecialTreatmentMap :: Map.Map String IdentSpecialTreatment
cryptolPreludeSpecialTreatmentMap = Map.fromList $ []

  ++
  [ ("Num_rec",               mapsTo cryptolPreludeModule "Num_rect") -- automatically defined
  , ("unsafeAssert_same_Num", skip) -- unsafe and unused
  ]

specialTreatmentMap :: Map.Map ModuleName (Map.Map String IdentSpecialTreatment)
specialTreatmentMap = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  [ ("Cryptol", cryptolPreludeSpecialTreatmentMap)
  , ("Prelude", sawCorePreludeSpecialTreatmentMap)
  ]

moduleRenamingMap :: Map.Map ModuleName ModuleName
moduleRenamingMap = Map.fromList $
  over _1 (mkModuleName . (: [])) <$>
  over _2 (mkModuleName . (: [])) <$>
  [ ("Cryptol", "CryptolPrelude")
  , ("Prelude", "SAWCorePrelude")
  ]

translateModuleName :: ModuleName -> ModuleName
translateModuleName mn =
  Map.findWithDefault mn mn moduleRenamingMap

findSpecialTreatment :: Ident -> IdentSpecialTreatment
findSpecialTreatment ident =
  let moduleMap = Map.findWithDefault Map.empty (identModule ident) specialTreatmentMap in
  let defaultTreatment =
        IdentSpecialTreatment
        { atDefSite = DefPreserve
        , atUseSite = UsePreserve
        }
  in
  Map.findWithDefault defaultTreatment (identName ident) moduleMap

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

{-
traceFTermF :: String -> FlatTermF Term -> a -> a
traceFTermF ctx tf = traceTerm ctx (Unshared $ FTermF tf)

traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

-- translateBinder ::
--   TermTranslationMonad m =>
--   (Ident, Term) -> m (Coq.Ident, Coq.Term)
-- translateBinder (ident, term) =
--   (,)
--   <$> pure (translateIdent ident)
--   <*> translateTerm term

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
  ModuleTranslationMonad m =>
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
    (liftTermTranslationMonad (translateTerm ctorType))
  return $ Coq.Constructor
    { constructorName
    , constructorType
    }

translateDataType :: ModuleTranslationMonad m => DataType -> m Coq.Decl
translateDataType (DataType {..}) =
  case atDefSite (findSpecialTreatment dtName) of
  DefPreserve              -> translateNamed $ identName dtName
  DefRename   _ targetName -> translateNamed $ targetName
  DefReplace  str          -> return $ Coq.Snippet str
  DefSkip                  -> return $ skipped dtName
  where
    translateNamed :: ModuleTranslationMonad m => Coq.Ident -> m Coq.Decl
    translateNamed name = do
      let inductiveName = name
      let
        mkParam :: ModuleTranslationMonad m => (String, Term) -> m Coq.Binder
        mkParam (s, t) = do
          t' <- liftTermTranslationMonad (translateTerm t)
          modify $ over globalEnvironment (s :)
          return $ Coq.Binder s (Just t')
      let mkIndex (s, t) = do
            t' <- liftTermTranslationMonad (translateTerm t)
            modify $ over globalEnvironment (s :)
            let s' = case s of
                  "_" -> Nothing
                  _   -> Just s
            return $ Coq.PiBinder s' t'
      inductiveParameters   <- mapM mkParam dtParams
      inductiveIndices      <- mapM mkIndex dtIndices
      let inductiveSort = translateSort dtSort
      inductiveConstructors <- mapM (translateCtor inductiveParameters) dtCtors
      return $ Coq.InductiveDecl $ Coq.Inductive
        { inductiveName
        , inductiveParameters
        , inductiveIndices
        , inductiveSort
        , inductiveConstructors
        }

translateModuleDecl :: ModuleTranslationMonad m => ModuleDecl -> m Coq.Decl
translateModuleDecl = \case
  TypeDecl dataType -> translateDataType dataType
  DefDecl definition -> translateDef definition

mapped :: Ident -> Ident -> Coq.Decl
mapped sawIdent newIdent =
  Coq.Comment $ show sawIdent ++ " is mapped to " ++ show newIdent

skipped :: Ident -> Coq.Decl
skipped sawIdent =
  Coq.Comment $ show sawIdent ++ " was skipped"

translateDef :: ModuleTranslationMonad m => Def -> m Coq.Decl
translateDef (Def {..}) = do
  identsToSkip <- view alreadyTranslated <$> get
  if elem defIdent identsToSkip
    then return $ skipped defIdent
    else do
    modify (over alreadyTranslated (defIdent :))
    translateAccordingly (atDefSite (findSpecialTreatment defIdent))

  where

    translateAccordingly :: ModuleTranslationMonad m => DefSiteTreatment -> m Coq.Decl
    translateAccordingly  DefPreserve             = translateNamed $ identName defIdent
    translateAccordingly (DefRename _ targetName) = translateNamed $ targetName
    translateAccordingly (DefReplace  str)        = return $ Coq.Snippet str
    translateAccordingly  DefSkip                 = return $ skipped defIdent

    translateNamed :: ModuleTranslationMonad m => Coq.Ident -> m Coq.Decl
    translateNamed name = liftTermTranslationMonad (go defQualifier defBody)

      where

        go :: TermTranslationMonad m => DefQualifier -> Maybe Term -> m Coq.Decl
        go NoQualifier    Nothing     = error "Terms should have a body (unless axiom/primitive)"
        go NoQualifier    (Just body) = Coq.Definition
                                        <$> pure name
                                        <*> pure []
                                        <*> (Just <$> translateTerm defType)
                                        <*> translateTerm body
        go AxiomQualifier _           = Coq.Axiom
                                        <$> pure name
                                        <*> translateTerm defType
        go PrimQualifier  _           = Coq.Axiom
                                        <$> pure name
                                        <*> translateTerm defType

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

-- | Run a translation, but keep changes to the environment local to it,
-- restoring the current environment before returning.
-- withLocalEnvironment :: TermTranslationMonad m => m a -> m a
-- withLocalEnvironment action = do
--   env <- view environment <$> get
--   result <- action
--   modify $ set environment env
--   return result

-- | This is a convenient helper for when you want to add some bindings before
-- translating a term.
-- translateTermLocallyBinding :: ModuleTranslationMonad m => [String] -> Term -> m Coq.Term
-- translateTermLocallyBinding bindings term =
--   withLocalEnvironment $ do
--   modify $ over environment (bindings ++)
--   translateTerm term

liftTermTranslationMonad ::
  (forall n. TermTranslationMonad   n => n a) ->
  (forall m. ModuleTranslationMonad m => m a)
liftTermTranslationMonad n = do
  configuration <- ask
  let r = runTermTranslationMonad configuration n
  case r of
    Left  e      -> Except.throwError e
    Right (a, _) -> do
      return a

-- env is innermost first order
translateTerm :: TermTranslationMonad m => Term -> m Coq.Term
translateTerm t = do -- traceTerm "translateTerm" t $
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

runTranslationMonad ::
  TranslationConfiguration ->
  s ->
  (forall m. TranslationMonad s m => m a) ->
  Either (TranslationError Term) (a, s)
runTranslationMonad configuration state m = runStateT (runReaderT m configuration) state

runTermTranslationMonad ::
  TranslationConfiguration ->
  (forall m. TermTranslationMonad m => m a) ->
  Either (TranslationError Term) (a, TermTranslationState)
runTermTranslationMonad configuration =
  runTranslationMonad configuration (TermTranslationState [] [])

runModuleTranslationMonad ::
  TranslationConfiguration ->
  (forall m. ModuleTranslationMonad m => m a) ->
  Either (TranslationError Term) (a, ModuleTranslationState)
runModuleTranslationMonad configuration =
  runTranslationMonad configuration (ModuleTranslationState [] [])

-- Eventually, different modules will want different preambles, for now,
-- hardcoded.
preamblePlus :: Doc -> Doc
preamblePlus extraImports = vcat $
  [ "From Coq          Require Import Lists.List."
  , "Import            ListNotations."
  , "From Coq          Require Import String."
  , "From Coq          Require Import Vectors.Vector."
  , "From CryptolToCoq Require Import SAW."
  , "From Records      Require Import Records."
  , ""
  , extraImports
  , ""
  ]

preamble :: Doc
preamble = preamblePlus $ vcat []

translateTermToDocWith ::
  TranslationConfiguration -> (Coq.Term -> Doc) -> Term -> Either (TranslationError Term) Doc
translateTermToDocWith configuration _f t = do
  (_term, state) <- runTermTranslationMonad configuration (translateTerm t)
  let decls = view declarations state
  return
    $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls)
    -- <$$> (if null decls then empty else hardline)
    -- <$$> f term

translateDefDoc :: TranslationConfiguration -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
translateDefDoc configuration name =
  translateTermToDocWith configuration (\ term -> Coq.ppDecl (mkDefinition name term))

translateTermAsDeclImports :: TranslationConfiguration -> Coq.Ident -> Term -> Either (TranslationError Term) Doc
translateTermAsDeclImports configuration name t = do
  doc <- translateDefDoc configuration name t
  return (preamble <$$> hardline <> doc)

translateDecl :: TranslationConfiguration -> ModuleDecl -> Doc
translateDecl configuration decl =
  case decl of
  TypeDecl td -> do
    case runModuleTranslationMonad configuration (translateDataType td) of
      Left e -> error $ show e
      Right (tdecl, _) -> Coq.ppDecl tdecl
  DefDecl dd -> do
    case runModuleTranslationMonad configuration (translateDef dd) of
      Left e -> error $ show e
      Right (tdecl, _) -> Coq.ppDecl tdecl

translateModule :: TranslationConfiguration -> Module -> Doc
translateModule configuration m =
  let name = show $ translateModuleName (moduleName m)
  in
  vcat $ []
  ++ [ text $ "Module " ++ name ++ "."
     , ""
     ]
  ++ [ translateDecl configuration decl | decl <- moduleDecls m ]
  ++ [ text $ "End " ++ name ++ "."
     ]
