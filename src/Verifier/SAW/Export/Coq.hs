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
--import qualified Data.Vector as Vector (toList)

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
  
newtype CoqTrans a =
  CoqTrans {
    runCoqTrans :: StateT
                  [Coq.Decl]
                  (Either (TranslationError Term))
                  a
  }
  deriving (Applicative, Functor, Monad, MonadState [Coq.Decl])

instance MonadError (TranslationError Term) CoqTrans where
    throwError e = CoqTrans $ lift $ throwError e
    catchError (CoqTrans a) h = CoqTrans $ catchError a $ runCoqTrans . h

zipFilter :: [Bool] -> [a] -> [a]
zipFilter bs = map snd . filter fst . zip bs

showFTermF :: FlatTermF Term -> String
showFTermF = show . Unshared . FTermF

-- arg order: outermost binding first
globalArgsMap :: Map.Map Ident [Bool]
globalArgsMap = Map.fromList
  [ ("Prelude.append", [False, False, False, True, True])
  , ("Prelude.take", [False, True, False, True])
  , ("Prelude.drop", [False, False, True, True])
  , ("Prelude.Vec", [False, True])
  , ("Prelude.uncurry", [False, False, False, True])
  , ("Prelude.map", [False, False, True, False, True])
  , ("Prelude.bvXor", [False, True, True])
  , ("Prelude.zipWith", [False, False, False, True, False, True, True])
  , ("Prelude.eq", [False, True, True])
  , ("Cryptol.ecEq", [False, False, True, True])
  , ("Cryptol.ecDemote", [True, True])
  -- Assuming only finite Cryptol sequences
  , ("Cryptol.ecCat", [False, False, False, True, True])
  , ("Cryptol.seq", [True, False])
  , ("Cryptol.seqZip", [False, False, False, False, True, True])
  , ("Cryptol.seqMap", [False, False, False, True, True])
  , ("Cryptol.ecJoin", [False, False, False, True])
  , ("Cryptol.ecSplit", [False, True, False, True])
  , ("Cryptol.ecSplitAt", [True, True, False, True])
  , ("Cryptol.ecXor", [False, True, True, True])
  , ("Cryptol.ecZero", [True, False])
  , ("Cryptol.PLogicSeq", [False, False, True])
  , ("Cryptol.PLogicSeqBool", [False])
  , ("Cryptol.PLogicWord", [False])
  ]

cryptolPreludeMap :: Map.Map String String
cryptolPreludeMap = Map.fromList
  [ ("repeat", "cryptolRepeat")
  , ("take", "cryptolTake")
  , ("drop", "cryptolDrop")
  , ("/\\", "(/\\)")
  ]

identMap :: Map.Map Ident Coq.Ident
identMap = Map.fromList
  [ ("Prelude.Bool", "bool")
  , ("Prelude.False", "false")
  , ("Prelude.True", "true")
  , ("Prelude.Nat", "int")
  , ("Prelude.Vec", "list")
  , ("Prelude.append", "(++)")
  , ("Cryptol.ecCat", "(++)")
  , ("Prelude.take", "take")
  , ("Prelude.drop", "drop")
  , ("Prelude.zip", "zip")
  , ("Cryptol.seq", "cryptolSeq")
  , ("Cryptol.seqZip", "zip")
  , ("Prelude.zipWith", "zipWith")
  , ("Prelude.uncurry", "sawcoreUncurry")
  , ("Prelude.map", "map")
  , ("Cryptol.seqMap", "map")
  , ("Prelude.bvXor", "sawcoreBVXor")
  , ("Cryptol.ecDemote", "cryptolECDemote")
  , ("Cryptol.ecJoin", "cryptolECJoin")
  , ("Cryptol.ecSplit", "cryptolECSplit")
  , ("Cryptol.ecSplitAt", "cryptolECSplitAt")
  , ("Cryptol.Num", "int")
  , ("Cryptol.TCNum", "id")
  , ("Cryptol.tcAdd", "(+)")
  , ("Cryptol.tcSub", "(-)")
  , ("Cryptol.tcMul", "( * )")
  , ("Cryptol.ecEq", "(=)")
  , ("Prelude.eq", "(=)")
  , ("Cryptol.ecXor", "cryptolECXor")
  , ("Cryptol.PLogicSeq", "cryptolPLogicSeq")
  , ("Cryptol.PLogicSeqBool", "cryptolPLogicSeq")
  , ("Cryptol.PLogicWord", "cryptolPLogicWord")
  ]

filterArgs :: Ident -> [a] -> [a]
filterArgs i = maybe id zipFilter (Map.lookup i globalArgsMap)

translateIdent :: Ident -> Coq.Ident
translateIdent i = Map.findWithDefault (show i) i identMap

{-
traceFTermF :: String -> FlatTermF Term -> a -> a
traceFTermF ctx tf = traceTerm ctx (Unshared $ FTermF tf)
  
traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

flatTermFToExpr ::
  (Term -> CoqTrans Coq.Term) ->
  FlatTermF Term ->
  CoqTrans Coq.Term
flatTermFToExpr go tf = --traceFTermF "flatTermFToExpr" tf $
  case tf of
    GlobalDef i   -> pure (Coq.Var (translateIdent i))
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      -> pure (Coq.Var "unit")
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse go [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse go [x, y]
    PairLeft t    -> Coq.App (Coq.Var "fst") <$> traverse go [t]
    PairRight t   -> Coq.App (Coq.Var "snd") <$> traverse go [t]
    {-
    EmptyValue    -> undefined
    -}
    EmptyType     -> pure (Coq.Var "Empty_set")
    DataTypeApp n is as -> do
      Coq.App (Coq.Var (translateIdent n)) <$> traverse go (is ++ as)
    CtorApp n is as -> do
      Coq.App (Coq.Var (translateIdent n)) <$> traverse go (is ++ as)
    --RecursorApp _ _ _ _ _ _ -> undefined
    Sort s -> pure (Coq.Sort (if s == propSort then Coq.Prop else Coq.Type))
    {-
    NatLit i -> undefined
    ArrayValue _ vec -> undefined
    StringLit _    -> undefined
    ExtCns (EC _ _ _) -> undefined
    -}
    _ -> notSupported
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

-- env is innermost first order
translateTerm :: Bool -> [String] -> Term -> CoqTrans Coq.Term
translateTerm traverseConsts env t = --traceTerm "translateTerm" t $
  case t of
    (asFTermF -> Just tf)  -> flatTermFToExpr (go env) tf
    (asLambda -> Just _) -> do
      paramTerms <- mapM translateParam params
      Coq.Fun <$> pure paramTerms
              -- env is in innermost first (reverse) binder order
              <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asLambdaList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params
          translateParam (n, ty) = do
            -- TODO: what if argument types are dependent?
            ty' <- translateTerm traverseConsts env ty
            return (Coq.Binder n (Just ty'))
    (asApp -> Just _) ->
      -- asApplyAll: innermost argument first
      let (f, args) = asApplyAll t
      in case f of
           (asGlobalDef -> Just i) ->
             case i of
                "Cryptol.unsafeCoerce" ->
                -- assuming unsafeCoerce is safe in SAW-Core generated
                -- by the Cryptol compiler, so we just strip it
                -- away. For now throwing away the type, but we'll see
                -- if we need the resulting type (second parameter) in
                -- practice.
                  go env (last args)
                "Prelude.unsafeCoerce" ->
                  go env (last args)
                "Prelude.ite" -> case args of
                  [_ty, c, tt, ft] ->
                    Coq.If <$> go env c <*> go env tt <*> go env ft
                  _ -> badTerm
                {-
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
                              typ <- translateType env ty
                              return $ EC.App (EC.ModVar "iter") [len, EC.Binding EC.Lambda [(x, Just typ)] expr, EC.List []]
                          _ -> badTerm   
                      _ -> notSupported
                  _ -> badTerm
                -}
                _ -> Coq.App <$> go env f
                             <*> traverse (go env) (filterArgs i args)
                  
           _ -> Coq.App <$> go env f
                        <*> traverse (go env) args
    (asLocalVar -> Just n)
      | n < length env -> Coq.Var <$> pure (env !! n)
      | otherwise -> throwError $ LocalVarOutOfBounds t
    (unwrapTermF -> Constant n body _) -> do
      decls <- get
      if | n `Map.member` cryptolPreludeMap ->
             Coq.Var <$> pure (cryptolPreludeMap Map.! n)
         | not traverseConsts || any (matchDecl n) decls -> Coq.Var <$> pure n
         | otherwise -> do
             b <- go env body
             case b of
               Coq.Fun bs b' -> 
                 modify (Coq.Definition n bs Nothing b' :)
               _ -> modify (Coq.Definition n [] Nothing b :)
             Coq.Var <$> pure n
    _ -> {- trace "translateTerm fallthrough" -} notSupported
  where
    notSupported = throwError $ NotSupported t
    badTerm = throwError $ BadTerm t
    --matchDecl n (EC.OpDecl n' _ _) = n == n'
    matchDecl _ _ = False
    go = translateTerm traverseConsts

translateTermDoc :: Bool -> Term -> Either (TranslationError Term) Doc
translateTermDoc traverseConsts t = do
  (term, decls) <- runStateT (runCoqTrans $ translateTerm traverseConsts [] t) []
  return $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls) <$$>
           hardline <$$>
           Coq.ppTerm term
