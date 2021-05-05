{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}
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
import qualified Data.Text as Text
import Data.Text (Text)
import Data.List (elemIndex)
import qualified Data.Vector as V
import Text.Read (readMaybe)
import Text.URI

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

type WriteM = State.State (Map TermIndex Int, Map VarIndex NameInfo, [String], Int)

renderNames :: Map VarIndex NameInfo -> String
renderNames nms = show
  [ (idx, f nmi)
  | (idx,nmi) <- Map.toList nms
  ]
 where
   f (ModuleIdentifier i)  = Left (show i)
   f (ImportedName uri as) = Right (render uri, as)

readNames :: String -> Maybe (Map VarIndex NameInfo)
readNames xs = Map.fromList <$> (mapM readName =<< readMaybe xs)
 where
   readName :: (VarIndex, Either Text (Text,[Text])) -> Maybe (VarIndex, NameInfo)
   readName (idx, Left i) = pure (idx, ModuleIdentifier (parseIdent (Text.unpack i)))
   readName (idx, Right (uri,as)) =
       do uri' <- mkURI uri
          pure (idx, ImportedName uri' as)

-- | Render to external text format
scWriteExternal :: Term -> String
scWriteExternal t0 =
    let (x, (_, nms, lns, _)) = State.runState (go t0) (Map.empty, Map.empty, [], 1)
    in unlines $
        [ unwords ["SAWCoreTerm", show x]
        , renderNames nms
        ] ++ reverse lns
  where
    nextId :: WriteM Int
    nextId =
       do (m, nms, lns, x) <- State.get
          State.put (m, nms, lns, x+1)
          return x
    output :: String -> WriteM ()
    output l =
       do (m, nms, lns, x) <- State.get
          State.put (m, nms, l:lns, x)
    memoize :: TermIndex -> WriteM Int
    memoize i =
       do (m, nms, lns, x) <- State.get
          State.put (Map.insert i x m, nms, lns, x+1)
          return x
    stashName :: ExtCns Int -> WriteM ()
    stashName ec =
       do (m, nms, lns, x) <- State.get
          State.put (m, Map.insert (ecVarIndex ec) (ecName ec) nms, lns, x)

    go :: Term -> WriteM Int
    go (Unshared tf) = do
      tf' <- traverse go tf
      body <- writeTermF tf'
      x <- nextId
      output (unwords [show x, body])
      return x

    go STApp{ stAppIndex = i, stAppTermF = tf } = do
      (memo, _, _, _) <- State.get
      case Map.lookup i memo of
        Just x -> return x
        Nothing -> do
          tf' <- traverse go tf
          body <- writeTermF tf'
          x <- memoize i
          output (unwords [show x, body])
          return x

    writeTermF :: TermF Int -> WriteM String
    writeTermF tf =
      case tf of
        App e1 e2      -> pure $ unwords ["App", show e1, show e2]
        Lambda s t e   -> pure $ unwords ["Lam", Text.unpack s, show t, show e]
        Pi s t e       -> pure $ unwords ["Pi", Text.unpack s, show t, show e]
        LocalVar i     -> pure $ unwords ["Var", show i]
        Constant ec e  ->
            do stashName ec
               pure $ unwords ["Constant", show (ecVarIndex ec), show (ecType ec), show e]
        FTermF ftf     ->
          case ftf of
            Primitive ec ->
               do stashName ec
                  pure $ unwords ["Primitive", show (ecVarIndex ec), show (ecType ec)]
            UnitValue           -> pure $ unwords ["Unit"]
            UnitType            -> pure $ unwords ["UnitT"]
            PairValue x y       -> pure $ unwords ["Pair", show x, show y]
            PairType x y        -> pure $ unwords ["PairT", show x, show y]
            PairLeft e          -> pure $ unwords ["ProjL", show e]
            PairRight e         -> pure $ unwords ["ProjR", show e]
            CtorApp i ps es     -> pure $
              unwords ("Ctor" : show i : map show ps ++ argsep : map show es)
            DataTypeApp i ps es -> pure $
              unwords ("Data" : show i : map show ps ++ argsep : map show es)

            RecursorType d ps motive motive_ty -> pure $
              unwords (["RecursorType", show d] ++
                       map show ps ++
                       [argsep, show motive, show motive_ty])
            Recursor (CompiledRecursor i ps motive motive_ty cs_fs ctorOrder) -> pure $
              unwords (["Recursor" , show i] ++ map show ps ++
                       [ argsep, show motive, show motive_ty
                       , show (Map.toList cs_fs)
                       , show ctorOrder
                       ])
            RecursorApp rec ixs e -> pure $
              unwords (["RecursorApp", show rec] ++
                       map show ixs ++ [show e])

            RecordType elem_tps -> pure $ unwords ["RecordType", show elem_tps]
            RecordValue elems   -> pure $ unwords ["Record", show elems]
            RecordProj e prj    -> pure $ unwords ["RecordProj", show e, Text.unpack prj]
            Sort s              -> pure $
              if s == propSort then unwords ["Prop"] else
                unwords ["Sort", drop 5 (show s)] -- Ugly hack to drop "sort "
            NatLit n            -> pure $ unwords ["Nat", show n]
            ArrayValue e v      -> pure $ unwords ("Array" : show e :
                                            map show (V.toList v))
            StringLit s         -> pure $ unwords ["String", show s]
            ExtCns ec ->
               do stashName ec
                  pure $ unwords ["ExtCns",show (ecVarIndex ec), show (ecType ec)]


-- | During parsing, we maintain two maps used for renumbering: The
-- first is for the 'Int' values that appear in the external core
-- file, and the second is for the 'VarIndex' values that appear
-- inside 'Constant' and 'ExtCns' constructors. We do not reuse any
-- such numbers that appear in the external file, but generate fresh
-- ones that are valid in the current 'SharedContext'.
type ReadM = State.StateT (Map Int Term, Map VarIndex NameInfo, Map VarIndex VarIndex) IO

scReadExternal :: SharedContext -> String -> IO Term
scReadExternal sc input =
  case lines input of
    ( (words -> ["SAWCoreTerm", final]) : nmlist : rows ) ->
      case readNames nmlist of
        Nothing -> fail "scReadExternal: failed to parse name table"
        Just nms ->
          State.evalStateT (mapM_ (go . words) rows >> readIdx final) (Map.empty, nms, Map.empty)

    _ -> fail "scReadExternal: failed to parse input file"
  where
    go :: [String] -> ReadM ()
    go (tok : tokens) =
      do i <- readM tok
         tf <- parse tokens
         t <- lift $ scTermF sc tf
         (ts, nms, vs) <- State.get
         put (Map.insert i t ts, nms, vs)
    go [] = pure () -- empty lines are ignored

    readM :: forall a. Read a => String -> ReadM a
    readM tok =
      case readMaybe tok of
        Nothing -> fail $ "scReadExternal: parse error: " ++ show tok
        Just x -> pure x

    getTerm :: Int -> ReadM Term
    getTerm i =
      do (ts,_,_) <- State.get
         case Map.lookup i ts of
           Nothing -> fail $ "scReadExternal: invalid term index: " ++ show i
           Just t -> pure t

    readIdx :: String -> ReadM Term
    readIdx tok = getTerm =<< readM tok

    readElimsMap :: String -> ReadM (Map Ident (Term,Term))
    readElimsMap str =
      do (ls :: [(Ident,(Int,Int))]) <- readM str
         elims  <- forM ls (\(c,(e,ty)) ->
                    do e'  <- getTerm e
                       ty' <- getTerm ty
                       pure (c, (e',ty')))
         pure (Map.fromList elims)

    readEC :: String -> String -> ReadM (ExtCns Term)
    readEC i t =
      do vi <- readM i
         t' <- readIdx t
         (ts, nms, vs) <- State.get
         nmi <- case Map.lookup vi nms of
                  Just nmi -> pure nmi
                  Nothing -> lift $ fail $ "scReadExternal: ExtCns missing name info: " ++ show vi
         case Map.lookup vi vs of
           Just vi' -> pure $ EC vi' nmi t'
           Nothing ->
             do vi' <- lift $ scFreshGlobalVar sc
                State.put (ts, nms, Map.insert vi vi' vs)
                pure $ EC vi' nmi t'

    parse :: [String] -> ReadM (TermF Term)
    parse tokens =
      case tokens of
        ["App", e1, e2]     -> App <$> readIdx e1 <*> readIdx e2
        ["Lam", x, t, e]    -> Lambda (Text.pack x) <$> readIdx t <*> readIdx e
        ["Pi", s, t, e]     -> Pi (Text.pack s) <$> readIdx t <*> readIdx e
        ["Var", i]          -> pure $ LocalVar (read i)
        ["Constant",i,t,e]  -> Constant <$> readEC i t <*> readIdx e
        ["Primitive", i, t] -> FTermF <$> (Primitive <$> readEC i t)
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

        ("RecursorType" : i :
         (separateArgs ->
          Just (ps, [motive,motive_ty]))) ->
            do tp <- RecursorType (parseIdent i) <$>
                       traverse readIdx ps <*>
                       readIdx motive <*>
                       readIdx motive_ty
               pure (FTermF tp)
        ("Recursor" : i :
         (separateArgs ->
          Just (ps, [motive, motiveTy, elims, ctorOrder]))) ->
            do rec <- CompiledRecursor (parseIdent i) <$>
                        traverse readIdx ps <*>
                        readIdx motive <*>
                        readIdx motiveTy <*>
                        readElimsMap elims <*>
                        readM ctorOrder
               pure (FTermF (Recursor rec))
        ("RecursorApp" : rec : (splitLast -> Just (ixs, arg))) ->
            do app <- RecursorApp <$>
                        readIdx rec <*>
                        traverse readIdx ixs <*>
                        readIdx arg
               pure (FTermF app)

        ["RecordType", elem_tps] ->
          FTermF <$> (RecordType <$> (traverse (traverse getTerm) =<< readM elem_tps))
        ["Record", elems] ->
          FTermF <$> (RecordValue <$> (traverse (traverse getTerm) =<< readM elems))
        ["RecordProj", e, prj] -> FTermF <$> (RecordProj <$> readIdx e <*> pure (Text.pack prj))
        ["Prop"]            -> pure $ FTermF (Sort propSort)
        ["Sort", s]         -> FTermF <$> (Sort <$> (mkSort <$> readM s))
        ["Nat", n]          -> FTermF <$> (NatLit <$> readM n)
        ("Array" : e : es)  -> FTermF <$> (ArrayValue <$> readIdx e <*> (V.fromList <$> traverse readIdx es))
        ("String" : ts)     -> FTermF <$> (StringLit <$> (readM (unwords ts)))
        ["ExtCns", i, t] -> FTermF <$> (ExtCns <$> readEC i t)
        _ -> fail $ "Parse error: " ++ unwords tokens
