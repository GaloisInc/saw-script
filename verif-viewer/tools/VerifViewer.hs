{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}

module Main where

import Control.Monad
import Data.Aeson
import qualified Data.Aeson.Parser as AP
import Data.Aeson.Types (Parser)
import qualified Data.Aeson.Types as AE
import Data.Maybe (isJust)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (toList)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import qualified Data.Set as Set
import System.IO
import System.Exit (exitFailure)
import System.Environment (getArgs)
import Data.Time.Clock

import GHC.IO.Encoding (setLocaleEncoding, utf8)

import qualified Data.Attoparsec.ByteString as AT
import qualified Data.ByteString as BS
import qualified Data.GraphViz as GV
import qualified Data.GraphViz.Attributes as GV
import qualified Data.GraphViz.Attributes.Complete as GV
import qualified Data.GraphViz.Printing as GV
import qualified Data.GraphViz.Attributes.HTML as HTML

main :: IO ()
main = do
     setLocaleEncoding utf8
     [f,o] <- getArgs
     bs <- BS.readFile f
     case AT.parseOnly AP.json' bs of
       Left msg -> putStrLn msg >> exitFailure
       Right v ->
         case AE.parse parseNodes v of
           AE.Error msg  -> putStrLn msg >> exitFailure
           AE.Success ns -> handleNodes o ns

handleNodes :: FilePath -> [SummaryNode] -> IO ()
handleNodes o ns = TL.writeFile o (GV.renderDot (GV.toDot dot))
  where
    dot = GV.graphElemsToDot params nodes uniqEdges

    params :: GV.GraphvizParams Integer SummaryNode () Integer SummaryNode
    params = GV.defaultParams
             { GV.fmtNode = fmt
             , GV.globalAttributes =
                 [ GV.GraphAttrs [ GV.RankDir GV.FromLeft , GV.RankSep [2.0], GV.Splines GV.Ortho ] ]
             }

    nodeMap :: Map Integer SummaryNode
    nodeMap = Map.fromList [ (summaryNodeId n, n) | n <- ns ]

    nodes :: [(Integer,SummaryNode)]
    nodes = do n <- ns
               pure (summaryNodeId n, n)

    uniqEdges :: [(Integer,Integer,())]
    uniqEdges = Set.toList (Set.fromList edges)

    edges :: [(Integer,Integer,())]
    edges = do n <- ns
               let i = summaryNodeId n
               n' <- summaryNodeDeps n
               pure (i,n',())

    fmt :: (Integer, SummaryNode) -> GV.Attributes
    fmt (_, TheoremSummary _ s) = fmtThm s
    fmt (_, MethodSummary _ s)  = fmtMethod nodeMap s


fmtThm :: TheoremNode -> GV.Attributes
fmtThm thm = [ GV.shape GV.Trapezium
             , GV.Tooltip (TL.fromStrict (thmTooltip thm))
             , GV.textLabel (TL.fromStrict lab)
             , GV.style GV.filled
             , GV.FillColor [GV.toWC (thmColor thm)]
             ]

  where
   lab = thmStatusText thm <> "\n" <> T.pack (show (thmElapsedTime thm))


fmtMethod :: Map Integer SummaryNode -> MethodNode -> GV.Attributes
fmtMethod nodeMap mn = [ GV.Label (GV.HtmlLabel top), GV.Shape GV.PlainText ]
  where
   top =
     if null subs then
       HTML.Table (HTML.HTable Nothing [HTML.CellBorder 0] [ HTML.Cells [main] ])
     else
       HTML.Table (HTML.HTable Nothing [HTML.CellBorder 0] [ HTML.Cells [main], HTML.Cells [subsTab]])

   main = HTML.LabelCell
           [ HTML.Title (TL.fromStrict maintt)
           , HTML.HRef "#"
           , HTML.BGColor fillcol
           ]
           (HTML.Text [ HTML.Str (TL.fromStrict maintext) ])

   subsTab :: HTML.Cell
   subsTab = HTML.LabelCell [] (HTML.Table (HTML.HTable Nothing [HTML.Border 0, HTML.CellBorder 1] [HTML.Cells subs]))

   vcs = methodVCs mn

   subs :: [HTML.Cell]
   subs = map mkSub vcs

   mkSub :: VCNode -> HTML.Cell
   mkSub vc = HTML.LabelCell attrs (HTML.Text [ HTML.Str (TL.fromStrict (T.pack (show (vcElapsedTime vc)))) ])
     where
     attrs =
       [ HTML.BGColor (vcColor vc)
       , HTML.Title (TL.fromStrict (vcTooltip vc))
       , HTML.HRef "#"
       ]

   fillcol = statusColor $
     foldr (<>) (methodToStatus mn) (map vcToStatus vcs)

   maintext =
      T.intercalate "\n"
        [ methodName mn
        , T.pack (show (methodElapsedtime mn))
        ]
   maintt = methodLoc mn


data Status = Proved | Tested | Assumed

statusColor :: Status -> GV.Color
statusColor Proved  = GV.X11Color GV.Green
statusColor Tested  = GV.X11Color GV.Yellow
statusColor Assumed = GV.X11Color GV.Red

instance Semigroup Status where
  Assumed <> _     = Assumed
  _  <> Assumed    = Assumed
  Tested <> Proved = Tested
  Proved <> Tested = Tested
  Tested <> Tested = Tested
  Proved <> Proved = Proved

thmToStatus :: TheoremNode -> Status
thmToStatus thm = case thmStatus thm of
                    TheoremVerified{} -> Proved
                    TheoremTested{}   -> Tested
                    TheoremAdmitted{} -> Assumed

vcToStatus :: VCNode -> Status
vcToStatus vc = case vcStatus vc of
                    TheoremVerified{} -> Proved
                    TheoremTested{}   -> Tested
                    TheoremAdmitted{} -> Assumed

methodToStatus :: MethodNode -> Status
methodToStatus mn = case methodStatus mn of
                      MethodAssumed -> Assumed
                      MethodVerified -> Proved

thmColor :: TheoremNode -> GV.Color
thmColor = statusColor . thmToStatus

vcColor :: VCNode -> GV.Color
vcColor = statusColor . vcToStatus

thmStatusText :: TheoremNode -> Text
thmStatusText thm = T.intercalate "\n" $
   case thmStatus thm of
     TheoremVerified sls -> [T.unwords ("verified:" : sls)]
     TheoremTested nm    -> [T.unwords ["tested:", T.pack (show nm)]]
     TheoremAdmitted msg -> ["Admitted!", msg]

vcTooltip :: VCNode -> Text
vcTooltip vc = T.intercalate "\n" $
          [ vcReason vc
          , vcLoc vc
          ]

thmTooltip :: TheoremNode -> Text
thmTooltip thm = T.intercalate "\n" $
         ([ thmReason thm
          , thmLoc thm
          ] ++
          case thmPLoc thm of
            Nothing -> []
            Just (fn,l) -> [ fn <> " " <> l ])


parseNodes :: Value -> Parser [SummaryNode]
parseNodes = withArray "summary nodes" (mapM parseNode . toList)

parseNode :: Value -> Parser SummaryNode
parseNode = withObject "summary node" $ \o ->
  do i  <- o .: "id"
     tp <- o .: "type"
     case tp :: Text of
       "method"   -> MethodSummary i <$> parseMethodNode o
       "property" -> TheoremSummary i  <$> parseTheoremNode o
       _ -> fail ("unexpected 'type' value " ++ show tp)

parseMethodNode :: Object -> Parser MethodNode
parseMethodNode o =
  MethodNode <$>
    o .: "method" <*>
    o .: "loc" <*>
    parseMethodStatus o <*>
    parseDeps o <*>
    parseVCs o <*>
    o .: "elapsedtime"

parseMethodStatus :: Object -> Parser MethodStatus
parseMethodStatus o =
  do st <- o .: "status"
     case st :: Text of
       "assumed"  -> pure MethodAssumed
       "verified" -> pure MethodVerified
       _ -> fail ("Unexpected moethod status " ++ show st)

parseVCs :: Object -> Parser [VCNode]
parseVCs o =
  (o .: "vcs") >>= parseJSONList >>= mapM parseVCNode

parseDeps :: Object -> Parser [Integer]
parseDeps o = (o .: "dependencies") >>= parseJSONList

parseVCNode :: Object -> Parser VCNode
parseVCNode o =
  VCNode <$>
    o .: "loc" <*>
    parseTheoremStatus o <*>
    o .: "reason" <*>
    o .: "elapsedtime" <*>
    parseDeps o <*>
    o .: "tags"

parseTheoremNode :: Object -> Parser TheoremNode
parseTheoremNode o =
  TheoremNode <$>
    o .: "loc" <*>
    o .: "reason" <*>
    o .: "elapsedtime" <*>
    parseTheoremStatus o <*>
    (o .:? "ploc" >>= traverse parsePLoc) <*>
    parseDeps o

parsePLoc :: Value -> Parser (Text, Text)
parsePLoc = withObject "ploc" $ \o ->
  do fn <- o .: "function"
     l  <- o .: "loc"
     pure (fn,l)

parseTheoremStatus :: Object -> Parser TheoremStatus
parseTheoremStatus o =
  do st <- o .: "status"
     case st :: Text of
       "verified" -> TheoremVerified <$> (o .: "provers" >>= parseJSONList)
       "tested"   -> TheoremTested   <$> (o .: "numtests")
       "assumed"  -> TheoremAdmitted <$> (o .: "admitmsg")
       _ -> fail ("Unexpected theorem status " ++ show st)

data SummaryNode
  = TheoremSummary Integer TheoremNode
  | MethodSummary  Integer MethodNode
 deriving (Show)

summaryNodeId :: SummaryNode -> Integer
summaryNodeId (TheoremSummary i _) = i
summaryNodeId (MethodSummary i _)  = i

summaryNodeDeps :: SummaryNode -> [Integer]
summaryNodeDeps (TheoremSummary _ s) = thmDeps s
summaryNodeDeps (MethodSummary _ s)  =
  methodDeps s ++ (vcDeps =<< methodVCs s)


data TheoremNode =
  TheoremNode
  { thmLoc :: Text
  , thmReason :: Text
  , thmElapsedTime :: NominalDiffTime
  , thmStatus :: TheoremStatus
  , thmPLoc :: Maybe (Text, Text)
  , thmDeps :: [Integer]
 }
 deriving (Show)

data VCNode =
  VCNode
  { vcLoc :: Text
  , vcStatus :: TheoremStatus
  , vcReason :: Text
  , vcElapsedTime :: NominalDiffTime
  , vcDeps :: [Integer]
  , vcTags :: [String]
  }
 deriving (Show)

data TheoremStatus
  = TheoremVerified [Text]
  | TheoremTested Integer
  | TheoremAdmitted Text
 deriving (Show)

data MethodNode =
  MethodNode
  { methodName :: Text
  , methodLoc :: Text
  , methodStatus :: MethodStatus
  , methodDeps :: [Integer]
  , methodVCs :: [VCNode]
  , methodElapsedtime :: NominalDiffTime
  }
 deriving (Show)

data MethodStatus
  = MethodAssumed
  | MethodVerified
 deriving (Show)
