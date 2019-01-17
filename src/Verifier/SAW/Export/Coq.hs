{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Export.Coq
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Export.Coq where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (intersperse)
import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Language.Coq.AST as Coq
import qualified Language.Coq.Pretty as Coq
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.Term.Functor
--import Verifier.SAW.Term.Pretty
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

data ExportConfiguration = ExportConfiguration
  { exportVectorsAsCoqVectors :: Bool -- ^ when `False`, export vectors as Coq lists
  , traverseConsts            :: Bool
  }

type MonadCoqTrans m =
  ( MonadError  (TranslationError Term) m
  , MonadReader ExportConfiguration     m
  , MonadState  [Coq.Decl]              m
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

translateIdent :: Ident -> Coq.Ident
translateIdent i = Map.findWithDefault (show i) i identMap

{-
traceFTermF :: String -> FlatTermF Term -> a -> a
traceFTermF ctx tf = traceTerm ctx (Unshared $ FTermF tf)

traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

flatTermFToExpr ::
  MonadCoqTrans m =>
  (Term -> m Coq.Term) ->
  FlatTermF Term ->
  m Coq.Term
flatTermFToExpr go tf = -- traceFTermF "flatTermFToExpr" tf $
  case tf of
    GlobalDef i   -> pure (Coq.Var (translateIdent i))
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      -> pure (Coq.Var "unit")
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse go [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse go [x, y]
    PairLeft t    -> Coq.App (Coq.Var "fst") <$> traverse go [t]
    PairRight t   -> Coq.App (Coq.Var "snd") <$> traverse go [t]
    -- TODO: maybe have more customizable translation of data types
    DataTypeApp n is as -> do
      Coq.App (Coq.Var (translateIdent n)) <$> traverse go (is ++ as)
    -- TODO: maybe have more customizable translation of data constructors
    CtorApp n is as -> do
      Coq.App (Coq.Var (translateIdent n)) <$> traverse go (is ++ as)
    -- TODO: support this next!
    RecursorApp _ _ _ _ _ _ -> notSupported
    Sort s -> pure (Coq.Sort (if s == propSort then Coq.Prop else Coq.Type))
    NatLit i -> pure (Coq.NatLit i)
    ArrayValue _ vec -> do
      config <- ask
      if exportVectorsAsCoqVectors config
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
    notSupported = throwError $ NotSupported errorTerm
    --badTerm = throwError $ BadTerm errorTerm
    errorTerm = Unshared $ FTermF tf
    --asString (asFTermF -> Just (StringLit s)) = pure s
    --asString _ = badTerm

-- | Recognizes an $App (App "Cryptol.seq" n) x$ and returns ($n$, $x$).
asSeq :: Monad f => Recognizer f Term (Term, Term)
asSeq t = do (f, args) <- asApplyAllRecognizer t
             fid <- asGlobalDef f
             case (fid, args) of
               ("Cryptol.seq", [n, x]) -> return (n,x)
               _ -> fail "not a seq"

asApplyAllRecognizer :: Monad f => Recognizer f Term (Term, [Term])
asApplyAllRecognizer t = do _ <- asApp t
                            return $ asApplyAll t

mkDecl :: Coq.Ident -> Coq.Term -> Coq.Decl
mkDecl name (Coq.Lambda bs t) = Coq.Definition name bs Nothing t
mkDecl name t = Coq.Definition name [] Nothing t

translateParams ::
  MonadCoqTrans m =>
  [String] -> [(String, Term)] -> m [Coq.Binder]
translateParams _ [] = return []
translateParams env ((n, ty):ps) = do
  ty' <- translateTerm env ty
  ps' <- translateParams (n : env) ps
  return (Coq.Binder n (Just ty') : ps')

translatePiParams :: MonadCoqTrans m => [String] -> [(String, Term)] -> m [Coq.PiBinder]
translatePiParams _ [] = return []
translatePiParams env ((n, ty):ps) = do
  ty' <- translateTerm env ty
  ps' <- translatePiParams (n : env) ps
  let n' = if n == "_" then Nothing else Just n
  return (Coq.PiBinder n' ty' : ps')

-- env is innermost first order
translateTerm :: MonadCoqTrans m => [String] -> Term -> m Coq.Term
translateTerm env t = -- traceTerm "translateTerm" t $
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr (go env) tf
    (asPi -> Just _) -> do
      paramTerms <- translatePiParams env params
      Coq.Pi <$> pure paramTerms
                 -- env is in innermost first (reverse) binder order
                 <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asPiList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params
    (asLambda -> Just _) -> do
      paramTerms <- translateParams env params
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
      | otherwise -> throwError $ LocalVarOutOfBounds t
    (unwrapTermF -> Constant n body _) -> do
      configuration <- ask
      decls <- get
      if | n `Map.member` cryptolPreludeMap ->
             Coq.Var <$> pure (cryptolPreludeMap Map.! n)
         | not (traverseConsts configuration) || any (matchDecl n) decls -> Coq.Var <$> pure n
         | otherwise -> do
             b <- go env body
             modify (mkDecl n b :)
             Coq.Var <$> pure n
    _ -> {- trace "translateTerm fallthrough" -} notSupported
  where
    notSupported = throwError $ NotSupported t
    badTerm = throwError $ BadTerm t
    matchDecl n (Coq.Definition n' _ _ _) = n == n'
    go = translateTerm

translateDocWith :: (Coq.Term -> Doc) -> ExportConfiguration -> Term -> Either (TranslationError Term) Doc
translateDocWith f configuration t = do
  (term, decls) <- runStateT (runReaderT (translateTerm [] t) configuration) []
  return $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls) <$$>
           (if null decls then empty else hardline) <$$>
           f term

translateTermDoc :: ExportConfiguration -> Term -> Either (TranslationError Term) Doc
translateTermDoc = translateDocWith Coq.ppTerm

translateDefDoc :: Coq.Ident -> ExportConfiguration -> Term -> Either (TranslationError Term) Doc
translateDefDoc name = translateDocWith (\ term -> Coq.ppDecl (mkDecl name term))

translateDefDocImports :: Coq.Ident -> ExportConfiguration -> Term -> Either (TranslationError Term) Doc
translateDefDocImports name configuration t = do
  doc <- translateDefDoc name configuration t
  let imports = vcat [ "From Coq          Require Import Lists.List."
                     , "From Coq          Require Import String."
                     , "From Coq          Require Import Vectors.Vector."
                     , "From Records      Require Import Records."
                     , "From CryptolToCoq Require Import Cryptol."
                     , "From CryptolToCoq Require Import SAW."
                     , "Import ListNotations."
                     ]
  return (imports <$$> hardline <> doc)
