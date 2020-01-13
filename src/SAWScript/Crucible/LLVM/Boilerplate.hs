{-# OPTIONS -Wall -Werror #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}

module SAWScript.Crucible.LLVM.Boilerplate
  ( llvm_boilerplate_info
  , llvm_boilerplate
  ) where

import System.IO

import Control.Exception (Exception)
import Control.Monad.Catch
import Control.Monad.IO.Class

import Data.Bifunctor
import Data.Maybe
import Data.Tuple
import Data.List
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text.IO
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Graph as Graph

import Data.Parameterized.Some

import qualified Text.LLVM as LLVM

import SAWScript.Value
import SAWScript.Crucible.LLVM.MethodSpecIR

import qualified Lang.Crucible.LLVM.TypeContext as Crucible
import qualified Lang.Crucible.LLVM.MemType as Crucible

import Lang.Crucible.LLVM.ArraySizeProfile

newtype BPException
  = BPException Text
  deriving Show
instance Exception BPException

data BPType
  = BPVoid
  | BPInt Int
  | BPFloat
  | BPDouble
  | BPAlias Text
  | BPPointer BPType
  | BPArray Text BPType
  | BPStruct [BPType]
  deriving (Show, Eq, Ord)

-- Tuple of argument type, possibly buffer size in bytes,
-- possibly argument name from debug symbols
type BPArg ty = (ty, Maybe Int, Maybe Text)

data BPFun ty = BPFun
  { bpFunName :: Text
  , bpFunSetup :: Text
  , bpFunRet :: ty
  , bpFunArgs :: [BPArg ty]
  , bpFunLenArgs :: [(Int, Int)]
  , bpFunDeps :: [Text]
  } deriving (Show, Functor, Foldable, Traversable)

-- Ignore differences in setup name
instance Eq ty => Eq (BPFun ty) where
  f1 == f2 = bpFunName f1 == bpFunName f2 &&
             bpFunRet f1 == bpFunRet f2 &&
             bpFunArgs f1 == bpFunArgs f2 &&
             bpFunLenArgs f1 == bpFunLenArgs f2 &&
             bpFunDeps f1 == bpFunDeps f2

debugInfoArgName :: LLVM.Module -> LLVM.Define -> Int -> Maybe Text
debugInfoArgName m d i = defScope >>= lookup i . scopeArgs
  where
    defScope :: Maybe Int
    defScope = case Map.lookup "dbg" $ LLVM.defMetadata d of
      Just (LLVM.ValMdRef s) -> Just s
      _ -> Nothing
    scopeArgs :: Int -> [(Int, Text)]
    scopeArgs s = go $ LLVM.modUnnamedMd m
      where go :: [LLVM.UnnamedMd] -> [(Int, Text)]
            go [] = []
            go (LLVM.UnnamedMd
                 { LLVM.umValues =
                   LLVM.ValMdDebugInfo
                     (LLVM.DebugInfoLocalVariable
                       LLVM.DILocalVariable
                       { LLVM.dilvScope = Just (LLVM.ValMdRef s')
                       , LLVM.dilvArg = a
                       , LLVM.dilvName = Just n
                       })}:xs) =
              if s == s' then (fromIntegral a, Text.pack n):go xs else go xs
            go (_:xs) = go xs

stmtInputsOutputs :: LLVM.Stmt -> (Set LLVM.Ident, Set LLVM.Ident)
stmtInputsOutputs (LLVM.Result r i _) = second (Set.insert r) $ instrInputsOutputs i
stmtInputsOutputs (LLVM.Effect i _) = instrInputsOutputs i

instrInputsOutputs :: LLVM.Instr -> (Set LLVM.Ident, Set LLVM.Ident)
instrInputsOutputs (LLVM.Ret v) = (valueIdents $ LLVM.typedValue v, mempty)
instrInputsOutputs (LLVM.Arith _ v v') = (valueIdents (LLVM.typedValue v) <> valueIdents v', mempty)
instrInputsOutputs (LLVM.Bit _ v v') = (valueIdents (LLVM.typedValue v) <> valueIdents v', mempty)
instrInputsOutputs (LLVM.Conv _ v _) = (valueIdents $ LLVM.typedValue v, mempty)
instrInputsOutputs (LLVM.Call _ _ _ vs) = (mconcat $ valueIdents . LLVM.typedValue <$> vs, mempty)
instrInputsOutputs (LLVM.Alloca _ (Just v) _) = (valueIdents $ LLVM.typedValue v, mempty)
instrInputsOutputs (LLVM.Load v _ _) = (valueIdents $ LLVM.typedValue v, mempty)
instrInputsOutputs (LLVM.Store v l _ _) =
  (valueIdents $ LLVM.typedValue v, valueIdents $ LLVM.typedValue l)
instrInputsOutputs (LLVM.ICmp _ v v') = (valueIdents (LLVM.typedValue v) <> valueIdents v', mempty)
instrInputsOutputs (LLVM.FCmp _ v v') = (valueIdents (LLVM.typedValue v) <> valueIdents v', mempty)
instrInputsOutputs (LLVM.Phi _ vs) = (mconcat $ valueIdents . fst <$> vs, mempty)
instrInputsOutputs (LLVM.GEP _ v vs) =
  (valueIdents (LLVM.typedValue v) <> mconcat (valueIdents . LLVM.typedValue <$> vs), mempty)
instrInputsOutputs (LLVM.ExtractValue v _) = (valueIdents $ LLVM.typedValue v, mempty)
instrInputsOutputs (LLVM.InsertValue v v' _) =
  ( valueIdents (LLVM.typedValue v) <> valueIdents (LLVM.typedValue v')
  , valueIdents $ LLVM.typedValue v
  )
instrInputsOutputs (LLVM.ExtractElt v v') =
  (valueIdents (LLVM.typedValue v) <> valueIdents v', mempty)
instrInputsOutputs (LLVM.InsertElt v v' v'') =
  (valueIdents (LLVM.typedValue v) <> valueIdents (LLVM.typedValue v') <> valueIdents v''
  , valueIdents $ LLVM.typedValue v
  )
instrInputsOutputs _ = (mempty, mempty)

valueIdents :: LLVM.Value -> Set LLVM.Ident
valueIdents (LLVM.ValIdent i) = Set.singleton i
valueIdents (LLVM.ValArray _ vs) = mconcat $ valueIdents <$> vs
valueIdents (LLVM.ValStruct vs) = mconcat $ valueIdents . LLVM.typedValue <$> vs
valueIdents (LLVM.ValPackedStruct vs) = mconcat $ valueIdents . LLVM.typedValue <$> vs
valueIdents _ = mempty

analyzeUsage :: [Set LLVM.Ident] -> [LLVM.Stmt] -> [Set LLVM.Ident]
analyzeUsage gs [] = gs
analyzeUsage gs (stmt:stmts) = analyzeUsage (update <$> gs) stmts
  where (i, o) = stmtInputsOutputs stmt
        update g = if any (`elem` i) g
                   then o <> g
                   else g

extractAllocas :: [LLVM.Stmt] -> [LLVM.Ident]
extractAllocas [] = []
extractAllocas (LLVM.Result i LLVM.Alloca{} _:stmts) = i:extractAllocas stmts
extractAllocas (_:stmts) = extractAllocas stmts

extractICmps :: [LLVM.Stmt] -> [Set LLVM.Ident]
extractICmps [] = []
extractICmps (LLVM.Result _
               (LLVM.ICmp _
                (LLVM.Typed _ (LLVM.ValIdent i))
                (LLVM.ValIdent i'))
               _:stmts) = Set.fromList [i, i']:extractICmps stmts
extractICmps (_:stmts) = extractICmps stmts

extractGEPs :: [LLVM.Stmt] -> [(LLVM.Ident, Set LLVM.Ident)]
extractGEPs [] = []
extractGEPs (LLVM.Result _
              (LLVM.GEP _
                (LLVM.Typed _ (LLVM.ValIdent s))
                vs)
              _:stmts) =
  (s, mconcat $ valueIdents . LLVM.typedValue <$> vs):extractGEPs stmts
extractGEPs (_:stmts) = extractGEPs stmts

llvmRefTypeSize :: Crucible.TypeContext -> LLVM.Type -> Maybe Int
llvmRefTypeSize tc (LLVM.PtrTo t) =
  let ?lc = tc in
    case Crucible.liftMemType t of
      Left _ -> Nothing
      Right m -> Just . fromIntegral $ Crucible.memTypeSize (Crucible.llvmDataLayout ?lc) m
llvmRefTypeSize _ _ = Nothing

convertDefine :: LLVM.Module -> Crucible.TypeContext -> [Profile] -> LLVM.Define -> [BPFun LLVM.Type]
convertDefine m tc profs d =
  (\(suffix, pargs) -> BPFun
    { bpFunName = defName d
    , bpFunSetup = defName d <> suffix <> "_setup"
    , bpFunRet = LLVM.defRetType d
    , bpFunArgs =
        (\(t, mp, i) -> ( LLVM.typedType t
                        , do p <- quot <$> mp <*> llvmRefTypeSize tc (LLVM.typedType t)
                             if p <= 1 ||
                                (i - 1) `elem` (fst <$> lenPairs) ||
                                (i - 1) `elem` (snd <$> lenPairs)
                               then Nothing else Just p
                        , debugInfoArgName m d i
                        )
        ) <$> zip3 (LLVM.defArgs d) pargs [1, 2..]
    , bpFunLenArgs = lenPairs
    , bpFunDeps = Set.toList (Set.intersection
                               (Set.fromList $ defName <$> LLVM.modDefines m)
                               $ extractCalls stmts)
    }) <$> profileArgs
  where
    defName :: LLVM.Define -> Text
    defName d' = case LLVM.defName d' of LLVM.Symbol s -> Text.pack s
    profileArgs :: [(Text, [Maybe Int])]
    profileArgs = case lookup (defName d) profs of
      Nothing -> [("", repeat Nothing)]
      Just as -> first (("_profile" <>) . Text.pack . show) <$> zip [0 :: Int, 1..] as
    stmts :: [LLVM.Stmt]
    stmts = mconcat . fmap LLVM.bbStmts $ LLVM.defBody d
    icmps :: [Set LLVM.Ident]
    icmps = extractICmps stmts
    geps :: [(LLVM.Ident, Set LLVM.Ident)]
    geps = extractGEPs stmts
    allocas :: [Set LLVM.Ident]
    allocas = analyzeUsage (Set.singleton <$> extractAllocas stmts) stmts
    guessIsLen :: Set LLVM.Ident -> Set LLVM.Ident -> Bool
    guessIsLen len buf = not . null $ filter
      (\x -> any (`elem` x) comparedWith && any (`elem` x) indexedBy) allocas
      where
        comparedWith :: Set LLVM.Ident
        comparedWith = Set.difference (mconcat $ filter (any $ flip elem len) icmps) len
        indexedBy :: Set LLVM.Ident
        indexedBy = mconcat $ snd <$> filter (flip elem buf . fst) geps
    isPointer :: LLVM.Type -> Bool
    isPointer (LLVM.PtrTo _) = True
    isPointer _ = False
    isInt :: LLVM.Type -> Bool
    isInt (LLVM.PrimType (LLVM.Integer _)) = True
    isInt _ = False
    args :: [(Int, Set LLVM.Ident)]
    args = zip [0, 1..] $ analyzeUsage (Set.singleton . LLVM.Ident . show <$> [0 :: Int, 1..]) stmts
    labeledArgs :: [(LLVM.Type, Int)]
    labeledArgs = zip (LLVM.typedType <$> LLVM.defArgs d) [0, 1..]
    lenPairs :: [(Int, Int)]
    lenPairs = [(l, b)
               | l <- snd <$> filter (isInt . fst) labeledArgs
               , b <- snd <$> filter (isPointer . fst) labeledArgs
               , case (lookup l args, lookup b args) of
                   (Just len, Just buf) -> guessIsLen len buf
                   _ -> False
               ]

extractCalls :: [LLVM.Stmt] -> Set Text
extractCalls [] = Set.empty
extractCalls (LLVM.Result _ (LLVM.Call _ _ (LLVM.ValSymbol (LLVM.Symbol s)) _) _:stmts) =
  Set.insert (Text.pack s) $ extractCalls stmts
extractCalls (LLVM.Effect (LLVM.Call _ _ (LLVM.ValSymbol (LLVM.Symbol s)) _) _:stmts) =
  Set.insert (Text.pack s) $ extractCalls stmts
extractCalls (_:stmts) = extractCalls stmts

sortByDeps :: [LLVM.Define] -> [LLVM.Define]
sortByDeps defs = reverse $ (\(f, _, _) -> f) . fromVertex <$> Graph.topSort g
  where (g, fromVertex, _) = Graph.graphFromEdges (adjacency <$> defs)
        adjacency :: LLVM.Define -> (LLVM.Define, Text, [Text])
        adjacency d = (d, symToText $ LLVM.defName d, calls d)
        symToText (LLVM.Symbol s) = Text.pack s
        calls :: LLVM.Define -> [Text]
        calls = Set.toList . extractCalls . mconcat . fmap LLVM.bbStmts . LLVM.defBody

extractDefines :: LLVM.Module -> [Profile] -> [BPFun LLVM.Type]
extractDefines m profs = nub . mconcat $ convertDefine m tc profs <$> sortByDeps (LLVM.modDefines m)
  where (_, tc) = Crucible.typeContextFromModule m

extractGlobals :: LLVM.Module -> [(LLVM.Type, Text, Bool)]
extractGlobals = fmap parseGlobal . LLVM.modGlobals
  where parseGlobal :: LLVM.Global -> (LLVM.Type, Text, Bool)
        parseGlobal LLVM.Global
          { LLVM.globalSym = LLVM.Symbol s
          , LLVM.globalType = t
          , LLVM.globalValue = m
          } = (t, Text.pack s, isJust m)

typeToBPType :: MonadThrow m => LLVM.Type -> m BPType
typeToBPType (LLVM.PrimType t) = primTypeToBPType t
  where
    primTypeToBPType :: MonadThrow m => LLVM.PrimType -> m BPType
    primTypeToBPType LLVM.Void = pure BPVoid
    primTypeToBPType (LLVM.Integer i) = pure . BPInt $ fromIntegral i
    primTypeToBPType (LLVM.FloatType LLVM.Float) = pure BPFloat
    primTypeToBPType (LLVM.FloatType LLVM.Double) = pure BPDouble
    primTypeToBPType t' = throwM . BPException $ "Unsupported primitive type " <> Text.pack (show t')
typeToBPType (LLVM.Alias (LLVM.Ident n)) = pure . BPAlias $ Text.pack n
typeToBPType (LLVM.PtrTo t) = BPPointer <$> typeToBPType t
typeToBPType (LLVM.Array i t) = BPArray (Text.pack $ show i) <$> typeToBPType t
typeToBPType (LLVM.Struct ts) = BPStruct <$> mapM typeToBPType ts
typeToBPType t = throwM . BPException $ "Unsupported type " <> Text.pack (show t)

bpTypeToCryptolType :: MonadThrow m => BPType -> m Text
bpTypeToCryptolType (BPInt i) = pure $ mconcat ["[", Text.pack $ show i, "]"]
bpTypeToCryptolType _ = throwM $ BPException "Attempted to generate non-integer Cryptol type"

bpTypeToSAWScriptType :: MonadThrow m => BPType -> m Text
bpTypeToSAWScriptType BPVoid = throwM $ BPException "Attempted to generate void"
bpTypeToSAWScriptType (BPInt i) = pure $ mconcat ["(llvm_int ", Text.pack $ show i, ")"]
bpTypeToSAWScriptType BPFloat = pure "llvm_float"
bpTypeToSAWScriptType BPDouble = pure "llvm_double"
bpTypeToSAWScriptType (BPAlias n) = pure $ mconcat ["(llvm_type \"%", n, "\")"]
bpTypeToSAWScriptType (BPPointer _) = throwM $ BPException "Attempted to generate pointer type"
bpTypeToSAWScriptType (BPArray i t) = do
  t' <- bpTypeToSAWScriptType t
  pure $ mconcat ["(llvm_array ", i, " ", t', ")"]
bpTypeToSAWScriptType (BPStruct _) = throwM $ BPException "Attempted to generate struct type"

bpTypeToSAWScriptArgBinds :: MonadThrow m => Text -> Text -> Maybe Int -> BPType -> m Text
bpTypeToSAWScriptArgBinds n n' (Just size) (BPPointer t) =
  bpTypeToSAWScriptArgBinds n n' Nothing . BPPointer $ BPArray (Text.pack $ show size) t
bpTypeToSAWScriptArgBinds n n' Nothing (BPPointer t) = do
  t' <- bpTypeToSAWScriptType t
  pure $ mconcat
    [ "  ", deref_n, " <- crucible_fresh_var \"", n', "\" ", t', ";\n  "
    , n, " <- crucible_alloc ", t', ";\n  "
    , "crucible_points_to ", n, " (crucible_term ", deref_n, ");\n"
    ]
  where deref_n = n <> "_star"
bpTypeToSAWScriptArgBinds n n' _ t = do
  t' <- bpTypeToSAWScriptType t
  pure $ mconcat
    [ "  ", n, " <- crucible_fresh_var \"", n', "\" ", t', ";\n"
    ]

bpTypeToSAWScriptGlobalBinds :: MonadThrow m => Text -> Text -> Bool -> BPType -> m Text
bpTypeToSAWScriptGlobalBinds _ n' True _ =
  pure $ mconcat
    [ "  crucible_points_to (crucible_global \"", n'
    , "\") (crucible_global_initializer \"", n', "\");\n"
    ]
bpTypeToSAWScriptGlobalBinds n n' _ (BPPointer t) = do
  t' <- bpTypeToSAWScriptType t
  pure $ mconcat
    [ "  ", deref_n, " <- crucible_fresh_var \"", n', "\" ", t', ";\n  "
    , n, " <- crucible_alloc ", t', ";\n  "
    , "crucible_points_to ", n, " (crucible_term ", deref_n, ");\n  "
    , "crucible_points_to (crucible_global \"", n', "\") ", n, ";\n"
    ]
  where deref_n = n <> "_star"
bpTypeToSAWScriptGlobalBinds n n' _ t = do
  t' <- bpTypeToSAWScriptType t
  pure $ mconcat
    [ "  ", n, " <- crucible_fresh_var \"", n', "\" ", t', ";\n  "
    , "crucible_points_to (crucible_global \"", n', "\") (crucible_term ", n, ");\n"
    ]

bpTypeToSAWScriptRetBinds :: MonadThrow m => BPType -> m Text
bpTypeToSAWScriptRetBinds BPVoid = pure "";
bpTypeToSAWScriptRetBinds t = do
  t' <- bpTypeToSAWScriptType t
  pure $ mconcat
    [ "  ret <- crucible_fresh_var \"return\" ", t'
    , ";\n  crucible_return (crucible_term ret);\n"
    ]

bpFunToSpec :: forall m. MonadThrow m => BPFun BPType -> m Text
bpFunToSpec (BPFun name setup ret as ls deps) = do
  binds <- mconcat <$> mapM argBinds args
  retbinds <- bpTypeToSAWScriptRetBinds ret
  pure $ mconcat
    [ "let ", setup
    , " = do {\n  GLOBALS;\n" , binds
    , "  crucible_execute_func ["
    , Text.intercalate ", " $ argParam <$> args
    , "];\n", retbinds, "};\n"
    , name, "_method_spec <- crucible_llvm_verify MODULE \""
    , name, "\" ["
    , Text.intercalate ", " $ (<>"_method_spec") <$> deps
    , "] false ", setup, " z3;\n\n"
    ]
  where args :: [(BPArg BPType, Int)]
        args = zip as [0, 1..]
        argName :: Int -> Text
        argName i = "arg" <> Text.pack (show i)
        argIdent :: (BPArg BPType, Int) -> Text
        argIdent ((_, _, Just i), _) = i
        argIdent ((_, _, Nothing), i) = argName i
        argParam :: (BPArg BPType, Int) -> Text
        argParam ((BPPointer{}, _, _), i) = argName i
        argParam (_, i) = mconcat ["crucible_term ", argName i]
        argBinds :: (BPArg BPType, Int) -> m Text
        argBinds a@((t, arr, _), i) =
          case (lookup i ls, lookup i $ swap <$> ls) of
            (Just _, _) -> do
              t' <- bpTypeToCryptolType t
              pure $ mconcat
                [ "  let ", argName i
                , " = {{ `ARRAY_LEN : ", t'
                , "}}; // ", argIdent a
                , "\n"
                ]
            (Nothing, Just _) ->
              case t of
                BPPointer t' ->
                  bpTypeToSAWScriptArgBinds (argName i) (argIdent a) Nothing
                  . BPPointer $ BPArray "ARRAY_LEN" t'
                _ -> throwM $ BPException "Guessed non-pointer type is array"
            (Nothing, Nothing) ->
              bpTypeToSAWScriptArgBinds (argName i) (argIdent a) arr t

llvm_boilerplate_info :: Some LLVMModule -> [Profile] -> TopLevel ()
llvm_boilerplate_info m profs = liftIO $
  (try . mapM (mapM typeToBPType) $ extractDefines (viewSome modAST m) profs) >>=
    \case Left (BPException e) -> liftIO . Text.IO.hPutStrLn stderr $ "[error] " <> e
          Right funs -> liftIO . Text.IO.putStrLn . Text.pack $ show funs

llvm_boilerplate :: FilePath -> Some LLVMModule -> [Profile] -> TopLevel ()
llvm_boilerplate path m profs = liftIO $
  (try . mapM (mapM typeToBPType) $ extractDefines (viewSome modAST m) profs) >>=
  \case Left (BPException e) -> liftIO . Text.IO.hPutStrLn stderr $ "[error] " <> e
        Right funs -> liftIO . withFile path WriteMode $ \h -> do
          binds <- mconcat <$> mapM globalBinds globals
          Text.IO.hPutStrLn h $ mconcat
            [ "let GLOBALS = do {\n"
            , binds
            , "};\n"
            ]
          mapM bpFunToSpec funs >>= Text.IO.hPutStrLn h . mconcat
  where
    globals :: [((LLVM.Type, Text, Bool), Text)]
    globals = zip (extractGlobals $ viewSome modAST m) $ globalName <$> [0, 1..]
      where globalName :: Int -> Text
            globalName i = "global" <> Text.pack (show i)
    globalBinds :: MonadThrow m => ((LLVM.Type, Text, Bool), Text) -> m Text
    globalBinds ((t, g, initialValue), i) =
      typeToBPType t >>= bpTypeToSAWScriptGlobalBinds i g initialValue
