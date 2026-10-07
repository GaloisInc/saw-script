{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}
-- | Generate a Cryptol script that proves, checks, or disproves various
-- Cryptol properties about floating-point operations.
--
-- Note that all of these properties are parameterized over arbitrary exponents
-- and precisions, and many of the properties are also parameterized over
-- arbitrary rounding modes, so this will generate code which instantiates each
-- property at a particular float size and at all supported rounding modes.
module Main (main) where

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.FilePath (dropExtension)

data ResultType
  = ProveProperty
    -- ^ Something which should hold for all inputs, and an SMT solver is able
    -- to prove it.
  | CheckProperty
    -- ^ Something which should hold for all inputs, but most SMT solvers
    -- cannot prove it (at least, not without taking an extraordinarily long
    -- time). We resort to spot-checking these properties on specific inputs.
  | Counterexample
    -- ^ Something which does not hold for at least one input.

data Result = Result
  { resultName :: !Text
  , resultType :: !ResultType
  , resultHasRoundingMode :: !Bool
  , resultUsesFpCast :: !Bool
  , resultUsesBvConversion :: !Bool
  }

propertiesFile :: FilePath
propertiesFile = "FloatPropertiesGeneric.cry"

sawFile :: FilePath
sawFile = "test.saw"

scriptFile :: FilePath
scriptFile = "GenFloatProperties.hs"

scrapeResults :: IO [Result]
scrapeResults = do
  ls0 <- T.lines <$> T.readFile propertiesFile
  let ls1 = zip ls0 (drop 1 (cycle ls0))
  let ls2 =
        filter
          (\(l, _) ->
            any (`T.isPrefixOf` l) ["prop_", "check_", "counterexample_"] &&
            (" :" `T.isInfixOf` l))
          ls1
  pure $
    map
      (\(l1, l2) ->
        let name = head (T.splitOn " " l1) in
        Result
          { resultName =
              name
          , resultType =
              if "prop_" `T.isPrefixOf` l1 then ProveProperty
              else if "check_" `T.isPrefixOf` l1 then CheckProperty
              else if "counterexample_" `T.isPrefixOf` l1 then Counterexample
              else error $ "Unsupported result name: " ++ T.unpack name
          , resultHasRoundingMode =
              any ("RoundingMode" `T.isInfixOf`) [l1, l2]
          , resultUsesFpCast = "fpCast" `T.isInfixOf` l1
          , resultUsesBvConversion =
              any (`T.isInfixOf` l1)
                  ["fpFromBV", "fpFromSBV", "fpToBV", "fpToSBV"]
          })
      ls2

resultCommandLines :: Result -> [Text]
resultCommandLines r = header : commands
  where
    header :: Text
    header = "print \"" <> action <> " " <> resultName r <> "...\";"

    action :: Text
    action =
      case resultType r of
        ProveProperty -> "Proving"
        CheckProperty -> "Checking"
        Counterexample -> "Disproving"

    commands :: [Text]
    commands
      -- Special cases for results involving `fpCast` or bitvector conversions,
      -- which take extra type parameters.
      | resultUsesFpCast r =
          [ fpCastCommand floatSize1 floatSize2 rm
          | floatSize1 <- allFloatSizes
          , floatSize2 <- allFloatSizes
          , rm <- roundingModes
          ]

      | resultUsesBvConversion r =
          [ bvConversionCommand bvSize rm
          | bvSize <- bvConversionSizes
          , rm <- roundingModes
          ]

      | otherwise =
          if resultHasRoundingMode r
            then [basicCommand (" " <> rm) | rm <- roundingModes]
            else [basicCommand ""]

    -- We arbitrarily instantiate each property at Float32 (`{8, 24}), but
    -- these properties should hold for any Float size.
    basicCommand :: Text -> Text
    basicCommand rm =
        command <> " {{ " <> resultName r <>
        "`{" <> ppFloatSize defaultFloatSize <> "}" <> rm <> " }};"

    fpCastCommand :: (Int, Int) -> (Int, Int) -> Text -> Text
    fpCastCommand floatSize1 floatSize2 rm =
      command <> " {{ " <> resultName r <>
      "`{" <> ppFloatSize floatSize1 <> ", " <> ppFloatSize floatSize2 <>
      "} " <> rm <> " }};"

    bvConversionCommand :: Int -> Text -> Text
    bvConversionCommand bvSize rm =
      command <> " {{ " <> resultName r <>
      "`{" <> T.pack (show bvSize) <> ", " <>
      ppFloatSize defaultFloatSize <> "} " <> rm <> " }};"

    command :: Text
    command =
      case resultType r of
        ProveProperty -> "prove_print " <> prover
        CheckProperty -> "prove_print " <> quickcheck
        Counterexample -> "sat_print " <> prover

    -- We arbitrarily instantiate each property at Float32 (`{8, 24}), but
    -- these properties should hold for any Float size.
    defaultFloatSize :: (Int, Int)
    defaultFloatSize = (8, 24)

    -- For results involving `fpCast`, we include both Float32 and Float64
    -- (`{11, 53}) for increased coverage.
    allFloatSizes :: [(Int, Int)]
    allFloatSizes = [(8, 24), (11, 53)]

    ppFloatSize :: (Int, Int) -> Text
    ppFloatSize (e, p) = T.pack (show e) <> ", " <> T.pack (show p)

    roundingModes :: [Text]
    roundingModes = ["rne", "rna", "rtp", "rtn", "rtz"]

    -- A variety of bitvector sizes to use for properties involving bitvector
    -- conversions.
    bvConversionSizes :: [Int]
    bvConversionSizes = [16, 32, 64]

    prover, quickcheck :: Text
    prover = "(w4_unint_bitwuzla [])" -- A reasonably fast solver for floating-point-related properties
    quickcheck = "(quickcheck 100)"

main :: IO ()
main = do
  results <- scrapeResults
  T.putStrLn $ T.unlines $
    [ "// THIS IS AUTO-GENERATED"
    , "//"
    , "// Rather than modifying this file, please modify the script which"
    , "// generated it (" <> T.pack scriptFile <> ") and regenerate it using:"
    , "//"
    , "//   runghc " <> T.pack scriptFile <> " > " <> T.pack sawFile
    , ""
    , "import Float;"
    , "import " <> T.pack (dropExtension propertiesFile) <> ";"
    ] ++
    concatMap resultCommandLines results
