#!/usr/bin/env cabal
{- cabal:
build-depends:
  base,
  aeson ^>=2.2,
  aeson-pretty ^>=0.8,
  bytestring ^>=0.12,
  containers ^>=0.6,
  mtl ^>=2.3,
  text ^>=2.1
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Control.Monad.State (State, evalState, gets, modify)
import Data.Aeson (ToJSON (..), Value (..), object, (.=))
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.Aeson.Key (fromString)
import Data.ByteString.Lazy.Char8 (ByteString)
import qualified Data.ByteString.Lazy.Char8 as B
import Data.List (stripPrefix)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Numeric (showBin)
import Numeric.Natural (Natural)
import System.Environment (getArgs, getProgName)
import System.Exit (exitFailure)

{- | The set of cells to instantiate for testing. The arguments define the
  various parameters for each cell type.
-}
tests :: [Cell]
tests = binaryOps False 0 0 0
     <> binaryOps False 0 0 2
     <> binaryOps False 2 2 2
     <> binaryOps True 2 0 1
     <> binaryOps True 0 2 1
     <> binaryOps True 2 2 1
     <> binaryOps True 2 2 3

     <> binaryOps' (1, False) (0, True)  1
     <> binaryOps' (2, False) (2, False) 1
     <> binaryOps' (2, False) (2, False) 3
     <> binaryOps' (2, False) (2, True)  3
     <> binaryOps' (1, True)  (0, False) 1
     <> binaryOps' (2, True)  (2, False) 3
     <> binaryOps' (2, True)  (2, True)  3

     <> unaryOps (0, False) 3
     <> unaryOps (1, False) 3
     <> unaryOps (2, False) 2
     <> unaryOps (3, False) 1
     <> unaryOps (0, True) 3
     <> unaryOps (1, True) 3
     <> unaryOps (2, True) 2
     <> unaryOps (3, True) 1

     <> shiftOps (0, False) 1 1
     <> shiftOps (1, False) 0 1
     <> shiftOps (1, False) 1 1
     <> shiftOps (1, False) 2 3
     <> shiftOps (2, False) 1 2
     <> shiftOps (2, False) 2 2
     -- <> shiftOps (0, True) 1 1 -- yosys segfault
     <> shiftOps (1, True) 0 1
     <> shiftOps (1, True) 1 1
     <> shiftOps (1, True) 2 3
     <> shiftOps (2, True) 1 2

     <> [ shiftx 1 (0, False) 1
        , shiftx 0 (1, False) 1
        , shiftx 1 (1, False) 1
        , shiftx 2 (1, False) 3
        , shiftx 1 (2, False) 2
        , shiftx 2 (2, False) 2
        , shiftx 0 (1, True) 1
        , shiftx 1 (0, True) 1
        , shiftx 1 (1, True) 1
        , shiftx 2 (1, True) 3
        , shiftx 1 (2, True) 2
        ]

     <> muxen 0 2
     <> muxen 2 0
     <> muxen 1 2
     <> muxen 2 1

     <> debugCells

-- | Params:
binaryOps ::
    -- \| {A,B}_SIGNED
    Bool ->
    -- \| A_WIDTH
    Width ->
    -- \| B_WIDTH
    Width ->
    -- \| Y_WIDTH
    Width ->
    [Cell]
binaryOps s a b y =
    binary (a, s) (b, s) y
        <$> [ "add"
            , "and"
            , "eq"
            , "eqx"
            , "mul"
            , "ne"
            , "nex"
            , "or"
            , "sub"
            , "xnor"
            , "xor"
            , "div" -- 'x' bits
            , "mod" -- 'x' bits
            , "ge"
            , "gt"
            , "le"
            , "lt"
            ]

-- | Params:
binaryOps' ::
    -- \| (A_WIDTH, A_SIGNED)
    (Width, Bool) ->
    -- \| (B_WIDTH, B_SIGNED)
    (Width, Bool) ->
    -- \| Y_WIDTH
    Width ->
    [Cell]
binaryOps' a b y =
    binary a b y
        <$> [ "logic_and"
            , "logic_or"
            , "shift" -- these shifts reverse when B is negative
            ]

-- | Like shift, but shift-in 'x' bits. Also, A_SIGNED must be false. Params:
shiftx ::
    -- \| A_WIDTH
    Width ->
    -- \| (B_WIDTH, B_SIGNED)
    (Width, Bool) ->
    -- \| Y_WIDTH
    Width ->
    Cell
shiftx aw b yw = binary (aw, False) b yw "shiftx"

-- | Same params as binaryOps', but B_SIGNED must be 0. Params:
shiftOps ::
    -- \| (A_WIDTH, A_SIGNED)
    (Width, Bool) ->
    -- \| B_WIDTH
    Width ->
    -- \| Y_WIDTH
    Width ->
    [Cell]
shiftOps a b y =
    shift a b y
        <$> [ "shl"
            , "shr"
            , "sshl"
            , "sshr"
            ]

-- | Params:
unaryOps ::
    -- \| (A_WIDTH, A_SIGNED)
    (Width, Bool) ->
    -- \| Y_WIDTH
    Width ->
    [Cell]
unaryOps a yw =
    unary a yw
        <$> [ "logic_not"
            , "neg"
            , "not"
            , "pos"
            , "reduce_and"
            , "reduce_bool"
            , "reduce_or"
            , "reduce_xnor"
            , "reduce_xor"
            ]

-- | Params:
muxen ::
    -- \| WIDTH
    Width ->
    -- \| S_WIDTH
    Width ->
    [Cell]
muxen w sw = [pmux w sw, bmux w sw, mux w]

-- check, print, scopeinfo
debugCells :: [Cell]
debugCells = [dbCheck 1 1, dbPrint 1 1, dbScopeinfo]

type Fresh = State (Map ByteString Natural)

fresh :: Id -> Fresh Id
fresh x = do
    n <- gets $ Map.findWithDefault 0 x
    modify $ Map.insert x $ n + 1
    pure $ x <> if n > 0 then B.pack (show n) else ""

type Width = Natural

type Id = ByteString

tyToMod :: Id -> Fresh Id
tyToMod = fresh

tyToCell :: Id -> Id
tyToCell = (<> "Cell")

tyToTy :: Id -> Id
tyToTy = ("$" <>)

newtype Device = Device [Module] deriving (Semigroup)

data Module = Module {modName :: Id, modPorts :: Ports, modCells :: Cells}

newtype Ports = Ports [Signal] deriving (Semigroup)

newtype Cells = Cells [Cell] deriving (Semigroup)

data Cell = Cell {cellType :: Id, cellParams :: Params, cellSigs :: [Signal]}

data Signal = Signal {sigName :: Id, sigDir :: Direction, sigWidth :: Width, sigWidthParam :: Maybe Id}

newtype Params = Params [Param] deriving (Semigroup)

data Param = Param {paramName :: Id, paramValue :: ParamValue}

data ParamValue = StrParam ByteString | NatParam Natural

data Direction = Input | Output

class Named a where
    getName :: a -> Id

instance Named Module where
    getName = modName

instance Named Cell where
    getName = tyToCell . cellType

instance Named Signal where
    getName = sigName

instance Named Param where
    getName = paramName

instance (Named a) => Named (a, b) where
    getName = getName . fst

named :: (Named a, ToJSON a) => [a] -> Value
named = named' id

named' :: (Named a, ToJSON b) => (a -> b) -> [a] -> Value
named' proj = object . map (\n -> (fromString . B.unpack . getName) n .= proj n)

instance ToJSON Device where
    toJSON (Device ms) = object ["modules" .= named ms]

instance ToJSON Module where
    toJSON (Module _ ps cs) =
        object
            [ "ports" .= ps
            , "cells" .= cs
            ]

instance ToJSON Ports where
    toJSON (Ports ps) = flip named' (getBits ps) $ \(s, bs) ->
        object
            [ "direction" .= sigDir s
            , "bits" .= bs
            ]

instance ToJSON Cells where
    toJSON (Cells cs) = named cs

instance ToJSON Cell where
    toJSON (Cell t ps ss) =
        object
            [ "type" .= B.unpack (tyToTy t)
            , "parameters" .= (ps <> getWidthParams ss)
            , "port_directions" .= named' sigDir ss
            , "connections" .= named' snd (getBits ss)
            ]

instance ToJSON Params where
    toJSON (Params ps) = object $ map (\p -> (fromString . B.unpack . paramName) p .= showValue p) ps

showValue :: Param -> String
showValue = \case
    Param _ (NatParam v) -> showBin v ""
    Param _ (StrParam s) -> B.unpack s

instance ToJSON Direction where
    toJSON = \case
        Input -> String "input"
        Output -> String "output"

getBits :: [Signal] -> [(Signal, [Natural])]
getBits = foldr bits [] . reverse
  where
    bits :: Signal -> [(Signal, [Natural])] -> [(Signal, [Natural])]
    bits s ss = (s, [lastBit ss + 1 .. lastBit ss + sigWidth s]) : ss

    lastBit :: [(Signal, [Natural])] -> Natural
    lastBit = \case
        (s, b : _) : _ -> sigWidth s + b - 1
        _ : ss -> lastBit ss
        [] -> 0

getWidthParams :: [Signal] -> Params
getWidthParams = Params . concatMap getP
  where
    getP :: Signal -> [Param]
    getP = \case
        Signal _ _ w (Just p) -> [Param p (NatParam w)]
        _ -> []

-- | Wrap a Cell in a Module that just passes through the cell's interface.
wrapCell :: Cell -> Fresh Module
wrapCell c = Module <$> tyToMod (cellType c) <*> pure (Ports $ cellSigs c) <*> pure (Cells [c])

params :: [(Id, Natural)] -> Params
params = Params . map (\(n, v) -> Param n $ NatParam v)

params' :: [(Id, ByteString)] -> Params
params' = Params . map (\(n, v) -> Param n $ StrParam v)

sig :: Direction -> Id -> Width -> Signal
sig d x w = Signal x d w (Just $ x <> "_WIDTH")

sig' :: Direction -> Id -> Width -> Signal
sig' d x w = Signal x d w Nothing

sIn :: Id -> Width -> Signal
sIn = sig Input

sOut :: Id -> Width -> Signal
sOut = sig Output

binary :: (Width, Bool) -> (Width, Bool) -> Width -> Id -> Cell
binary (a, aSigned) (b, bSigned) y t =
    Cell
        t
        (params [("A_SIGNED", if aSigned then 1 else 0), ("B_SIGNED", if bSigned then 1 else 0)])
        [sIn "A" a, sIn "B" b, sOut "Y" y]

shift :: (Width, Bool) -> Width -> Width -> Id -> Cell
shift a b = binary a (b, False)

unary :: (Width, Bool) -> Width -> Id -> Cell
unary (a, aSigned) y t =
    Cell
        t
        (params [("A_SIGNED", if aSigned then 1 else 0)])
        [sIn "A" a, sOut "Y" y]

-- | Instantiate a $bmux cell. Params:
bmux ::
    -- \| WIDTH
    Width ->
    -- \| S_WIDTH
    Width ->
    Cell
bmux w sw =
    Cell
        "bmux"
        (params [("WIDTH", w), ("S_WIDTH", sw)])
        [sig' Input "A" $ w * (2 ^ sw), sig' Input "S" sw, sig' Output "Y" w]

-- | Instantiate a $pmux cell. Params:
pmux ::
    -- \| WIDTH
    Width ->
    -- \| S_WIDTH
    Width ->
    Cell
pmux w sw =
    Cell
        "pmux"
        (params [("WIDTH", w), ("S_WIDTH", sw)])
        [sig' Input "A" w, sig' Input "B" $ w * sw, sig' Input "S" sw, sig' Output "Y" w]

-- | Instantiate a $mux cell. Params:
mux ::
    -- \| WIDTH
    Width ->
    Cell
mux w =
    Cell
        "mux"
        (params [("WIDTH", w)])
        [sig' Input "A" w, sig' Input "B" w, sig' Input "S" 1, sig' Output "Y" w]

-- | FLAVOR must be: assert, assume, live, fair, or cover. Params:
dbCheck ::
    -- \| TRG_WIDTH
    Width ->
    -- \| ARGS_WIDTH
    Width ->
    Cell
dbCheck tw aw =
    Cell
        "check"
        ( params [("PRIORITY", 0), ("TRG_ENABLE", 0), ("TRG_POLARITY", 0)]
            <> params' [("FLAVOR", "assert"), ("FORMAT", " ")]
        )
        [sig' Input "A" 1, sig' Input "EN" 1, sIn "TRG" tw, sIn "ARGS" aw]

-- | Params:
dbPrint ::
    -- \| TRG_WIDTH
    Width ->
    -- \| ARGS_WIDTH
    Width ->
    Cell
dbPrint tw aw =
    Cell
        "print"
        ( params [("PRIORITY", 0), ("TRG_ENABLE", 1), ("TRG_POLARITY", 0)]
            <> params' [("FORMAT", " ")]
        )
        [sig' Input "EN" 1, sIn "TRG" tw, sIn "ARGS" aw]

-- | TYPE must be: module, struct, or blackbox.
dbScopeinfo :: Cell
dbScopeinfo = Cell "scopeinfo" (params' [("TYPE", "module")]) []

ysContent :: FilePath -> Device -> B.ByteString
ysContent json (Device ms) =
    "read_json "
        <> B.pack json
        <> ";\n"
        <> B.concat (modToEval <$> ms)

modToEval :: Module -> B.ByteString
modToEval (Module m (Ports sigs) _)
    | ins == "" = ""
    | otherwise = "eval -table " <> ins <> showOuts <> m <> ";\n"
  where
    ins = B.intercalate "," $ concatMap filterInput sigs
    outs = B.intercalate "," $ concatMap filterOutput sigs
    showOuts
        | outs == "" = " "
        | otherwise = " -show " <> outs <> " "
    filterInput = \case
        Signal n Input _ _ -> [n]
        _ -> []
    filterOutput = \case
        Signal n Output _ _ -> [n]
        _ -> []

device :: Device
device = Device $ evalState (mapM wrapCell tests) mempty

main :: IO ()
main = do
    args <- getArgs
    me <- fromMaybe <$> getProgName <*> (stripPrefix "cabal-script-" <$> getProgName)
    case args of
        [jsonPath, ysPath] -> do
            B.writeFile jsonPath $ encodePretty device
            B.writeFile ysPath $ ysContent jsonPath device
        _ -> do
            putStrLn "Error: expecting exactly 2 arguments."
            putStrLn $ "Usage: ./" <> me <> " <yosys-json> <yosys-script>"
            putStrLn "  where both <yosys-json> and <yosys-script> are paths to files that will be overwritten."
            putStrLn "    <yosys-json>: Yosys RTLIL JSON file containing instantiated modules for testing."
            putStrLn "    <yosys-script>: Yosys script file for loading and evaluating the modules generated in <yosys-json>."
            exitFailure
