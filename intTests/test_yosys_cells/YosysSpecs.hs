{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Control.Applicative (many, (<|>))
import Control.Arrow (second)
import Control.Monad (when, zipWithM_)
import Data.Attoparsec.ByteString.Char8 (Parser, (<?>))
import qualified Data.Attoparsec.ByteString.Char8 as A
import Data.ByteString.Char8 (ByteString, pack, unpack)
import qualified Data.ByteString.Char8 as B
import Data.Function (on)
import Data.Functor (($>))
import Data.List (foldl', groupBy, sortOn)
import Numeric (showBin)
import Numeric.Natural (Natural)
import System.Console.GetOpt (getOpt, usageInfo, OptDescr (..), ArgOrder (..), ArgDescr (..))
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)
import System.FilePath ((-<.>), (<.>))
import System.IO (hPutStr, stderr)

-- Yosys log, "eval -table" parsing.

type Id = ByteString

type Width = Natural

type Path = ByteString

type Bit = Maybe Bool -- Nothing for 'x', 'z'

data Value = Value
    { width :: Width
    , val :: [Bit]
    } deriving (Show)

data Header = Header
    { inputNames :: [Id]
    , outputNames :: [Id]
    } deriving (Show)

data Row = Row
    { inputs :: [Value]
    , outputs :: [Value]
    } deriving (Show)

data Table = Table
    { modName :: Id
    , allSigs :: Header
    , header :: Header
    , rows :: [Row]
    } deriving (Show)

data YosysLog = YosysLog Path [Table] deriving (Show)

isBit :: Char -> Bool
isBit = (`B.elem` "01xz")

isEol :: Char -> Bool
isEol = (`B.elem` "\r\n")

isHSpace :: Char -> Bool
isHSpace = (`B.elem` " \t")

isName :: Char -> Bool
isName c = A.isAlpha_ascii c || A.isDigit c || c `B.elem` "_$\\"

isFilePath :: Char -> Bool
isFilePath c = A.isAlpha_ascii c || A.isDigit c || c `B.elem` "\\/.$"

-- | Skip horizontal space.
hspace :: Parser ()
hspace = A.takeWhile isHSpace $> ()

natural :: Parser Natural
natural = (read . unpack <$> A.takeWhile1 A.isDigit) <* hspace

bit :: Parser Bit
bit = toN <$> A.satisfy isBit
  where
    toN = \case
        '0' -> Just False
        '1' -> Just True
        _ -> Nothing

eol :: Parser ()
eol = A.endOfLine *> hspace

tick :: Parser ()
tick = A.satisfy (== '\'') *> hspace

comma :: Parser ()
comma = A.satisfy (== ',') *> hspace

skipSemis :: Parser ()
skipSemis = A.takeWhile (== ';') $> ()

tok :: ByteString -> Parser ()
tok s = A.string s *> hspace

anyWord :: Parser ByteString
anyWord = A.takeWhile1 (not . A.isSpace) <* hspace

name :: Parser Id
name = A.takeWhile1 isName <* hspace

filePath :: Parser Path
filePath = A.takeWhile1 isFilePath <* hspace

value :: Parser Value
value = Value <$> natural <*> (tick *> A.many1 bit) <* hspace

manyThen :: Parser a -> Parser b -> Parser b
manyThen pa pb = pb <|> (pa *> manyThen pa pb)

anyLine :: Parser ByteString
anyLine = A.takeWhile (not . isEol) <* eol

hrule :: Parser ()
hrule = A.takeWhile (`B.elem` " -|") *> eol

skipBlanks :: Parser ()
skipBlanks = many eol $> ()

readJsonLine :: Parser Path
readJsonLine =
    tok "yosys>"
        *> tok "read_json"
        *> filePath
        <* skipSemis
        <* eol
            <?> "looking for: yosys> read_json ..."

evalLine :: Parser (Id, Header)
evalLine =
    ( do
        tok "yosys>" *> tok "eval" *> tok "-table"
        h <- Header <$> (name `A.sepBy` comma) <*> (tok "-show" *> (name `A.sepBy` comma) <|> pure [])
        x <- name <* skipSemis <* eol
        pure (x, h)
    )
        <?> "looking for: yosys> eval -table ..."

tableHeader :: Parser Header
tableHeader =
    ( (Header <$> A.manyTill name (tok "|") <*> A.manyTill name eol <* hrule)
        <|> (Header <$> A.manyTill name eol <*> pure [] <* hrule)
        <|> pure (Header [] [])
    )
        <?> "eval -table header"

row :: Parser Row
row =
    ( (Row <$> A.manyTill value (tok "|") <*> A.manyTill value eol)
        <|> (Row <$> ((:) <$> value <*> A.manyTill value eol) <*> pure [])
    )
        <?> "eval -table row"

execEvalPass :: Parser ()
execEvalPass =
    anyWord
        *> tok "Executing"
        *> tok "EVAL"
        *> manyThen anyWord eol
            <?> "... Executing EVAL ..."

table :: Parser Table
table = manyThen anyLine $ do
    (x, h) <- evalLine
    Table x h <$> (skipBlanks *> execEvalPass *> skipBlanks *> tableHeader) <*> many row

yosysLog :: Parser YosysLog
yosysLog = manyThen anyLine $ YosysLog <$> readJsonLine <*> many table

-- Cryptol function language

newtype SAW = SAW [Stmt]

data Stmt
    = EnableExperimental
    | YosysImport Id Path
    | Let Cryptol
    | ProvePrint Id Expr
    | ProveThenPrint Id Expr

newtype Cryptol = Cryptol [Def]

data Def
    = Def Id (Maybe Ty) [Id] Expr
    | Verb ByteString

data Ty
    = TySeq Natural (Maybe Ty)
    | TyTuple [Ty]
    | TyFun Ty Ty
    | TyRecord [(Id, Ty)]
    | TyIdent Id
    | TyApp Ty Ty

data Expr
    = IfElse Expr Expr [Branch] Expr
    | Lit Width Natural
    | Vec [Expr]
    | Tuple [Expr]
    | Ident Id
    | Record [(Id, Expr)]
    | Where Expr [Def]
    | App Expr Expr
    | Infix Id Expr Expr
    | Field Expr Id
    | One
    | Zero

data Branch = Branch Expr Expr

class Pretty a where
    pretty' :: Natural -> a -> ByteString

instance Pretty SAW where
    pretty' lvl (SAW ss) = B.intercalate "\n" $ pretty' lvl <$> ss

instance Pretty Stmt where
    pretty' lvl = \case
        EnableExperimental -> "enable_experimental;"
        YosysImport x p -> x <> " <- yosys_import " <> "\"" <> p <> "\";"
        Let cry -> "let {{\n" <> pretty' (lvl + 2) cry <> "\n}};"
        ProvePrint x e -> "prove_print " <> x <> " {{ " <> pretty e <> " }};"
        ProveThenPrint x e ->
            "do {p <- prove "
                <> x
                <> " {{ "
                <> pretty e
                <> " }}; "
                <> "caseProofResult p (\\_ -> return ()) (\\cex -> print (str_concat \"Failure: ("
                <> pretty e
                <> ") \" (show cex)));};"

instance Pretty Cryptol where
    pretty' lvl (Cryptol ds) = B.concat $ pp <$> ds
      where
        pp = \case
            d@Def{} -> pretty' lvl d <> "\n"
            d -> pretty' lvl d

instance Pretty Def where
    pretty' lvl (Def x t' as e)
        | Just t <- t' =
            indent lvl
                <> x
                <> " : "
                <> pretty t
                <> pretty' lvl (Def x Nothing as e)
        | otherwise = indent lvl <> lhs <> " = " <> rhs
      where
        lhs = x <> B.concat ((" " <>) <$> as)
        rhs = pretty' (lvl + len lhs + 3) e
    pretty' _ (Verb x) = x

instance Pretty Ty where
    pretty' _ = \case
        TySeq n (Just t@TyApp{}) -> "[" <> pack (show n) <> "]" <> parens (pretty t)
        TySeq n (Just t) -> "[" <> pack (show n) <> "]" <> pretty t
        TySeq n Nothing -> "[" <> pack (show n) <> "]"
        TyTuple ts -> "(" <> commas (pretty <$> ts) <> ")"
        TyFun ta tb -> pretty ta <> " -> " <> pretty tb
        TyRecord fs -> "{" <> commas (map (\(x, t) -> x <> ": " <> pretty t) fs) <> "}"
        TyIdent x -> x
        TyApp ta tb -> pretty ta <> " " <> pretty tb

instance Pretty Expr where
    pretty' lvl = \case
        IfElse e1 e2 bs els ->
            "if "
                <> pretty e1
                <> " then "
                <> pretty e2
                <> B.concat (pretty' (lvl + 1) <$> bs)
                <> indent lvl
                <> "else "
                <> pretty els
        Lit 0 _ -> "zero"
        Lit w n -> "0b" <> pad w (pack $ showBin n "")
        Tuple [e] -> pretty e
        Tuple es -> "(" <> commas (pretty <$> es) <> ")"
        Vec es -> "[" <> commas (pretty <$> es) <> "]"
        Ident x -> x
        Record fs -> "{" <> commas (map (\(x, e) -> x <> " = " <> pretty e) fs) <> "}"
        Where e ds -> pretty e <> indent lvl <> "where" <> B.concat (pretty' (lvl + 2) <$> ds)
        App e1 e2 -> pretty e1 <> " " <> pretty e2
        Infix op a b -> pretty a <> " " <> op <> " " <> pretty b
        Field e f -> pretty e <> "." <> f
        One -> "1"
        Zero -> "0"

instance Pretty Branch where
    pretty' lvl (Branch b e) = indent lvl <> "| " <> pretty b <> " then " <> pretty e

pretty :: (Pretty a) => a -> ByteString
pretty = pretty' 0

parens :: ByteString -> ByteString
parens x = "(" <> x <> ")"

commas :: [ByteString] -> ByteString
commas = B.intercalate ", "

indent :: Natural -> ByteString
indent lvl = "\n" <> B.replicate (fromIntegral lvl) ' '

pad :: Width -> ByteString -> ByteString
pad w s
    | len s < w = B.replicate (fromIntegral w - fromIntegral (len s)) '0' <> s
    | otherwise = s

len :: ByteString -> Natural
len = fromIntegral . B.length

fnEq :: Expr -> Expr -> Expr
fnEq = Infix "==="

refinedBy :: Expr -> Expr -> Expr
refinedBy = Infix "===>"

eq :: Expr -> Expr -> Expr
eq = Infix "=="

nones :: Expr
nones = App (Ident "repeat") (Ident "None")

tyOption :: Ty -> Ty
tyOption = TyApp (TyIdent "Option")

tyBit :: Ty
tyBit = TyIdent "Bit"

preamble :: [Def]
preamble = pure $ Verb $ B.unlines
    -- TODO: really should handle other output types as well.
    [ "  (===>) : {a, y} (fin y) => (a -> {Y: [y](Option Bit)}) -> (a -> {Y: [y]}) -> a -> Bit"
    , "  (===>) spec impl a = and [i == fromOption i s | i <- (impl a).Y | s <- (spec a).Y]"
    , "                       where"
    , "                         fromOption : {b} b -> Option b -> b"
    , "                         fromOption def opt = case opt of"
    , "                                                Some x -> x"
    , "                                                None   -> def"
    ]

-- Table -> SAW/Cryptol translation

toSpecId :: Id -> Id
toSpecId = ("spec_" <>)

{- | Parse Yosys "eval -table" log output and translate it into a Cryptol spec
  for comparing against SAW's own RTLIL semantics. The first argument
  determines if the first proof failure should be fatal or not in the
  generated SAW script.
-}
toSAW :: Bool -> YosysLog -> SAW
toSAW nonFatal (YosysLog fp tabs) =
    SAW $
        [ EnableExperimental
        , YosysImport "m" fp
        , Let $ toCryptol tabs
        ]
            <> (prove <$> tabs)
  where
    prove :: Table -> Stmt
    prove = (if nonFatal then ProveThenPrint else ProvePrint) "w4" . thm

    thm :: Table -> Expr
    thm (Table x (Header _ outs) _ _)
        | null outs = Ident (toSpecId x) `fnEq` Field (Ident "m") x
        | otherwise = Ident (toSpecId x) `refinedBy` Field (Ident "m") x

toCryptol :: [Table] -> Cryptol
toCryptol ts = Cryptol $ preamble <> (toDef <$> ts)

toDef :: Table -> Def
toDef (Table m ev h rs)
    | null outs = Def (toSpecId m) (Just $ TyFun inTy outTy) ["in"] $ Record outFields
    | otherwise = Def (toSpecId m) (Just $ TyFun inTy outTy) ["in"] $ Where (Record outFields) [out, spec]
  where
    spec = Def "spec" Nothing ["a"] $ toExpr ev h rs
    out = Def "out" Nothing [] $ App (Ident "spec") inTup
    inTup = Tuple $ Field (Ident "in") . fst <$> ins

    inTy = TyRecord $ second (flip TySeq Nothing . width) <$> ins
    outTy = TyRecord $ second (flip TySeq (Just $ tyOption tyBit) . width) <$> outs

    outFields
        | [(n, _)] <- outs = [(n, Ident "out")]
        | otherwise = zipWith (\(n, _) -> (n,) . Field (Ident "out") . pack . show) outs [0 :: Int ..]

    ins :: [(Id, Value)]
    ins = ingest (inputNames ev) $ zip (inputNames h) $ fst $ someRow rs

    outs :: [(Id, Value)]
    outs = ingest (outputNames ev) $ zip (outputNames h) $ snd $ someRow rs

{- | Take signal names from the "eval -table" line, but widths from
  the table body, substituting 0 when a signal is missing from the table.
-}
ingest :: [Id] -> [(Id, Value)] -> [(Id, Value)]
ingest ((clean -> e) : evIds) tabIds'@((clean -> i, v) : tabIds)
    | e == i = (i, v) : ingest evIds tabIds
    | otherwise = (e, Value 0 []) : ingest evIds tabIds'
ingest (e : evIds) [] = (e, Value 0 []) : ingest evIds []
ingest [] _ = []

clean :: ByteString -> ByteString
clean = B.filter (/= '\\')

toExpr :: Header -> Header -> [Row] -> Expr
toExpr ev h rs = case toBranch ev h <$> rs of
    [Branch _ e] -> e
    Branch e1 e2 : bs -> IfElse e1 e2 bs $ mkNone e2
    _ -> Vec [] -- TODO: actually needs to be either [] or ()
  where
    mkNone = \case
        Tuple vs -> Tuple $ mkNone <$> vs
        _ -> nones

toBranch :: Header -> Header -> Row -> Branch
toBranch ev h (Row inVals outVals) = Branch (eq (Ident "a") (toTuple $ toBitVec . snd <$> ins)) $ toTuple (toLit . snd <$> outs)
  where
    ins :: [(Id, Value)]
    ins = ingest (inputNames ev) $ zip (inputNames h) inVals

    outs :: [(Id, Value)]
    outs = ingest (outputNames ev) $ zip (outputNames h) outVals

someRow :: [Row] -> ([Value], [Value])
someRow = \case
    [] -> ([], [])
    (Row ins outs) : _ -> (ins, outs)

toTuple :: [Expr] -> Expr
toTuple = \case
    [e] -> e
    es -> Tuple es

toBitVec :: Value -> Expr
toBitVec (Value w v) = Lit w $ foldl' toNat 0 v
  where
    toNat :: Natural -> Bit -> Natural
    toNat n = \case
        Just True -> 2 * n + 1
        _ -> 2 * n -- Replace 'x' or 'z' with 0.

toLit :: Value -> Expr
toLit (Value w v)
    | fromIntegral w <= length v = Vec $ toOpt <$> v
    | v == [Nothing] = Vec $ toOpt <$> replicate (fromIntegral w - length v) Nothing <> v
    | otherwise = Vec $ toOpt <$> replicate (fromIntegral w - length v) (Just False) <> v

toOpt :: Bit -> Expr
toOpt = maybe (Ident "None") $ App (Ident "Some") . \b -> if b then One else Zero

data Flag
    = FlagHelp
    | FlagNonFatal
    | FlagSplit String
    deriving Eq

options :: [OptDescr Flag]
options =
    [ Option ['h'] ["help"]        (NoArg FlagHelp)       "Print this help message."
    , Option []    ["non-fatal"]   (NoArg FlagNonFatal)   "In the generated SAW test script, don't exit on the first test failure."
    , Option ['n'] ["split-tests"] (ReqArg FlagSplit "n") "Create <n> SAW test script files, splitting tests between them."
    ]

exitUsage :: [String] -> IO a
exitUsage errs = do
    mapM_ (hPutStr stderr . ("Error: " <>)) $ filter (/= "") errs
    me <- getProgName
    hPutStr stderr (usageInfo ("\nUsage: " <> me <> " [OPTION...]") options)
    exitFailure

getN :: [Flag] -> Natural
getN = flip foldr 1 $ \case
    FlagSplit (read -> n) | (n :: Natural) > 1 -> const n
    _                                          -> id

chunk :: Natural -> [Table] -> [[Table]]
chunk n = map (snd <$>) . groupBy ((==) `on` fst) . sortOn fst . zip (cycle [1..n])

writeSAW :: Bool -> Path -> Natural -> [Table] -> IO ()
writeSAW nonFatal fp n = B.writeFile out . pretty . toSAW nonFatal . YosysLog fp
    where
      out :: FilePath
      out = B.unpack fp -<.> (show n <.> "saw")

main :: IO ()
main = do
    (flags, extra, errs) <- getOpt Permute options <$> getArgs

    when (not $ null errs) $ exitUsage errs
    when (not $ null extra) $ exitUsage $ ("Unknown argument: " <>) <$> extra

    let nonFatal = FlagNonFatal `elem` flags
        n        = getN flags

    A.parseOnly yosysLog <$> B.getContents >>= \case
        Left err                 -> putStrLn ("Error: " <> err) >> exitFailure
        Right (YosysLog fp tbls) -> zipWithM_ (writeSAW nonFatal fp) [1..n] $ chunk n tbls
