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

import Control.Monad.State.Strict as State
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable
#endif
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (elemIndex)
import qualified Data.Vector as V
import Text.Read (readMaybe)

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

--------------------------------------------------------------------------------
-- External text format

-- | A string to use to separate parameters from normal arguments of datatypes
-- and constructors
argsep :: String
argsep = "|"

-- | Separate a list of arguments into parameters and normal arguments by
-- finding the occurrence of 'argSep' in the list
separateArgs :: [String] -> Maybe ([String], [String])
separateArgs args =
  case elemIndex argsep args of
    Just i -> Just (take i args, drop (i+1) args)
    Nothing -> Nothing

-- | Split the last element from the rest of a list, for non-empty lists
splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast xs = Just (take (length xs - 1) xs, last xs)

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
        Constant ec e  -> unwords ["Constant", show (ecVarIndex ec), ecName ec, show (ecType ec), show e]
        FTermF ftf     ->
          case ftf of
            GlobalDef ident     -> unwords ["Global", show ident]
            UnitValue           -> unwords ["Unit"]
            UnitType            -> unwords ["UnitT"]
            PairValue x y       -> unwords ["Pair", show x, show y]
            PairType x y        -> unwords ["PairT", show x, show y]
            PairLeft e          -> unwords ["ProjL", show e]
            PairRight e         -> unwords ["ProjR", show e]
            CtorApp i ps es     ->
              unwords ("Ctor" : show i : map show ps ++ argsep : map show es)
            DataTypeApp i ps es ->
              unwords ("Data" : show i : map show ps ++ argsep : map show es)
            RecursorApp i ps p_ret cs_fs ixs e ->
              unwords (["Recursor" , show i] ++ map show ps ++
                       [argsep, show p_ret, show cs_fs] ++
                       map show ixs ++ [show e])
            RecordType elem_tps -> unwords ["RecordType", show elem_tps]
            RecordValue elems   -> unwords ["Record", show elems]
            RecordProj e prj    -> unwords ["RecordProj", show e, prj]
            Sort s              ->
              if s == propSort then unwords ["Prop"] else
                unwords ["Sort", drop 5 (show s)] -- Ugly hack to drop "sort "
            NatLit n            -> unwords ["Nat", show n]
            ArrayValue e v      -> unwords ("Array" : show e :
                                            map show (V.toList v))
            StringLit s         -> unwords ["String", show s]
            ExtCns ext          -> unwords ("ExtCns" : writeExtCns ext)
    writeExtCns ec = [show (ecVarIndex ec), ecName ec, show (ecType ec)]

-- | During parsing, we maintain two maps used for renumbering: The
-- first is for the 'Int' values that appear in the external core
-- file, and the second is for the 'VarIndex' values that appear
-- inside 'Constant' and 'ExtCns' constructors. We do not reuse any
-- such numbers that appear in the external file, but generate fresh
-- ones that are valid in the current 'SharedContext'.
type ReadM = State.StateT (Map Int Term, Map VarIndex VarIndex) IO

scReadExternal :: SharedContext -> String -> IO Term
scReadExternal sc input =
  case map words (lines input) of
    (["SAWCoreTerm", final] : rows) ->
      State.evalStateT (mapM_ go rows >> readIdx final) (Map.empty, Map.empty)
    _ -> fail "scReadExternal: failed to parse input file"
  where
    go :: [String] -> ReadM ()
    go (tok : tokens) =
      do i <- readM tok
         tf <- parse tokens
         t <- lift $ scTermF sc tf
         (ts, vs) <- State.get
         put (Map.insert i t ts, vs)
    go [] = pure () -- empty lines are ignored

    readM :: forall a. Read a => String -> ReadM a
    readM tok =
      case readMaybe tok of
        Nothing -> fail $ "scReadExternal: parse error: " ++ show tok
        Just x -> pure x

    getTerm :: Int -> ReadM Term
    getTerm i =
      do ts <- fst <$> State.get
         case Map.lookup i ts of
           Nothing -> fail $ "scReadExternal: invalid term index: " ++ show i
           Just t -> pure t

    readIdx :: String -> ReadM Term
    readIdx tok = getTerm =<< readM tok

    readEC :: String -> String -> String -> ReadM (ExtCns Term)
    readEC i x t =
      do vi <- readM i
         t' <- readIdx t
         (ts, vs) <- State.get
         case Map.lookup vi vs of
           Just vi' -> pure $ EC vi' x t'
           Nothing ->
             do vi' <- lift $ scFreshGlobalVar sc
                State.put (ts, Map.insert vi vi' vs)
                pure $ EC vi' x t'

    parse :: [String] -> ReadM (TermF Term)
    parse tokens =
      case tokens of
        ["App", e1, e2]     -> App <$> readIdx e1 <*> readIdx e2
        ["Lam", x, t, e]    -> Lambda x <$> readIdx t <*> readIdx e
        ["Pi", s, t, e]     -> Pi s <$> readIdx t <*> readIdx e
        ["Var", i]          -> pure $ LocalVar (read i)
        ["Constant",i,x,t,e]-> Constant <$> readEC i x t <*> readIdx e
        ["Global", x]       -> pure $ FTermF (GlobalDef (parseIdent x))
        ["Unit"]            -> pure $ FTermF UnitValue
        ["UnitT"]           -> pure $ FTermF UnitType
        ["Pair", x, y]      -> FTermF <$> (PairValue <$> readIdx x <*> readIdx y)
        ["PairT", x, y]     -> FTermF <$> (PairType <$> readIdx x <*> readIdx y)
        ["ProjL", x]        -> FTermF <$> (PairLeft <$> readIdx x)
        ["ProjR", x]        -> FTermF <$> (PairRight <$> readIdx x)
        ("Ctor" : i : (separateArgs -> Just (ps, es))) ->
          FTermF <$> (CtorApp (parseIdent i) <$> traverse readIdx ps <*> traverse readIdx es)
        ("Data" : i : (separateArgs -> Just (ps, es))) ->
          FTermF <$> (DataTypeApp (parseIdent i) <$> traverse readIdx ps <*> traverse readIdx es)
        ("Recursor" : i :
         (separateArgs ->
          Just (ps, p_ret : cs_fs : (splitLast -> Just (ixs, arg))))) ->
          FTermF <$>
          (RecursorApp (parseIdent i) <$>
           traverse readIdx ps <*>
           readIdx p_ret <*>
           (traverse (traverse getTerm) =<< readM cs_fs) <*>
           traverse readIdx ixs <*>
           readIdx arg)
        ["RecordType", elem_tps] ->
          FTermF <$> (RecordType <$> (traverse (traverse getTerm) =<< readM elem_tps))
        ["Record", elems] ->
          FTermF <$> (RecordValue <$> (traverse (traverse getTerm) =<< readM elems))
        ["RecordProj", e, prj] -> FTermF <$> (RecordProj <$> readIdx e <*> pure prj)
        ["Prop"]            -> pure $ FTermF (Sort propSort)
        ["Sort", s]         -> FTermF <$> (Sort <$> (mkSort <$> readM s))
        ["Nat", n]          -> FTermF <$> (NatLit <$> readM n)
        ("Array" : e : es)  -> FTermF <$> (ArrayValue <$> readIdx e <*> (V.fromList <$> traverse readIdx es))
        ("String" : ts)     -> FTermF <$> (StringLit <$> (readM (unwords ts)))
        ["ExtCns", i, n, t] -> FTermF <$> (ExtCns <$> readEC i n t)
        _ -> fail $ "Parse error: " ++ unwords tokens
