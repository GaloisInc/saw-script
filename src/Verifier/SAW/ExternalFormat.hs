{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}

{- |
Module      : Verifier.SAW.ExternalFormat
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module Verifier.SAW.ExternalFormat (
  scWriteExternal, scReadExternal
  ) where

import Verifier.SAW.SharedTerm
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable
#endif
import Verifier.SAW.TypedAST
import Control.Monad.State.Strict as State
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- External text format

-- | Render to external text format
scWriteExternal :: Term -> String
scWriteExternal t0 =
    let (x, (_, output, _)) = State.runState (go t0) (Map.empty, [], 1)
    in unlines (unwords ["SAWCoreTerm", show x] : reverse output)
  where
    go :: Term -> State.State (Map TermIndex Int, [String], Int) Int
    go (Unshared tf) = do
      tf' <- traverse go tf
      (m, output, x) <- State.get
      let s = unwords [show x, writeTermF tf']
      State.put (m, s : output, x + 1)
      return x
    go STApp{ stAppIndex = i, stAppTermF = tf } = do
      (memo, _, _) <- State.get
      case Map.lookup i memo of
        Just x -> return x
        Nothing -> do
          tf' <- traverse go tf
          (m, output, x) <- State.get
          let s = unwords [show x, writeTermF tf']
          State.put (Map.insert i x m, s : output, x + 1)
          return x
    writeTermF :: TermF Int -> String
    writeTermF tf =
      case tf of
        App e1 e2      -> unwords ["App", show e1, show e2]
        Lambda s t e   -> unwords ["Lam", s, show t, show e]
        Pi s t e       -> unwords ["Pi", s, show t, show e]
        LocalVar i     -> unwords ["Var", show i]
        Constant x e t -> unwords ["Constant", x, show e, show t]
        FTermF ftf     ->
          case ftf of
            GlobalDef ident    -> unwords ["Global", show ident]
            UnitValue          -> unwords ["Unit"]
            UnitType           -> unwords ["UnitT"]
            PairValue x y      -> unwords ["Pair", show x, show y]
            PairType x y       -> unwords ["PairT", show x, show y]
            PairLeft e         -> unwords ["ProjL", show e]
            PairRight e        -> unwords ["ProjR", show e]
            EmptyValue         -> unwords ["Empty"]
            EmptyType          -> unwords ["EmptyT"]
            FieldValue f x y   -> unwords ["Record", show f, show x, show y]
            FieldType f x y    -> unwords ["RecordT", show f, show x, show y]
            RecordSelector e i -> unwords ["RecordSel", show e, show i]
            CtorApp i es       -> unwords ("Ctor" : show i : map show es)
            DataTypeApp i es   -> unwords ("Data" : show i : map show es)
            Sort s             -> unwords ["Sort", drop 5 (show s)] -- Ugly hack to drop "sort "
            NatLit n           -> unwords ["Nat", show n]
            ArrayValue e v     -> unwords ("Array" : show e : map show (V.toList v))
            StringLit s        -> unwords ["String", show s]
            ExtCns ext         -> unwords ("ExtCns" : writeExtCns ext)
    writeExtCns ec = [show (ecVarIndex ec), ecName ec, show (ecType ec)]

scReadExternal :: SharedContext -> String -> IO Term
scReadExternal sc input =
  case map words (lines input) of
    (["SAWCoreTerm", read -> final] : rows) ->
        do m <- foldM go Map.empty rows
           return $ (Map.!) m final
    _ -> fail "scReadExternal: failed to parse input file"
  where
    go :: Map Int Term -> [String] -> IO (Map Int Term)
    go m (n : tokens) =
        do
          t <- scTermF sc (fmap ((Map.!) m) (parse tokens))
          return (Map.insert (read n) t m)
    go m [] = return m -- empty lines are ignored
    parse :: [String] -> TermF Int
    parse tokens =
      case tokens of
        ["App", e1, e2]     -> App (read e1) (read e2)
        ["Lam", x, t, e]    -> Lambda x (read t) (read e)
        ["Pi", s, t, e]     -> Pi s (read t) (read e)
        ["Var", i]          -> LocalVar (read i)
        ["Constant",x,e,t]  -> Constant x (read e) (read t)
        ["Global", x]       -> FTermF (GlobalDef (parseIdent x))
        ["Unit"]            -> FTermF UnitValue
        ["UnitT"]           -> FTermF UnitType
        ["Pair", x, y]      -> FTermF (PairValue (read x) (read y))
        ["PairT", x, y]     -> FTermF (PairType (read x) (read y))
        ["ProjL", x]        -> FTermF (PairLeft (read x))
        ["ProjR", x]        -> FTermF (PairRight (read x))
        ["Empty"]           -> FTermF EmptyValue
        ["EmptyT"]          -> FTermF EmptyType
        ["Record",f,x,y]    -> FTermF (FieldValue (read f) (read x) (read y))
        ["RecordT",f,x,y]   -> FTermF (FieldType (read f) (read x) (read y))
        ["RecordSel", e, i] -> FTermF (RecordSelector (read e) (read i))
        ("Ctor" : i : es)   -> FTermF (CtorApp (parseIdent i) (map read es))
        ("Data" : i : es)   -> FTermF (DataTypeApp (parseIdent i) (map read es))
        ["Sort", s]         -> FTermF (Sort (mkSort (read s)))
        ["Nat", n]          -> FTermF (NatLit (read n))
        ("Array" : e : es)  -> FTermF (ArrayValue (read e) (V.fromList (map read es)))
        ("String" : ts)     -> FTermF (StringLit (read (unwords ts)))
        ["ExtCns", i, n, t] -> FTermF (ExtCns (EC (read i) n (read t)))
        _ -> error $ "Parse error: " ++ unwords tokens
