{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}

module Main where

import Control.Monad
import Data.Aeson
import Data.Aeson.Types (Parser)
import qualified Data.Aeson.Types as AE
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Foldable (toList)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import System.IO
import System.Exit (exitFailure)
import System.Environment (getArgs)
import Data.Time.Clock

import qualified Data.Attoparsec.ByteString as AT
import qualified Data.ByteString as BS
import qualified Data.GraphViz as GV
import qualified Data.GraphViz.Attributes as GV
import qualified Data.GraphViz.Attributes.Complete as GV
import qualified Data.GraphViz.Printing as GV

main :: IO ()
main =
  do [f,o] <- getArgs
     bs <- BS.readFile f
     case AT.parseOnly json' bs of
       Left msg -> putStrLn msg >> exitFailure
       Right v -> 
         case AE.parse parseNodes v of
           AE.Error msg  -> putStrLn msg >> exitFailure
           AE.Success ns -> handleNodes o ns

handleNodes :: FilePath -> [SummaryNode] -> IO ()
handleNodes o ns = TL.writeFile o (GV.renderDot (GV.toDot dot))
  where
    dot = GV.graphElemsToDot params nodes edges 

    params :: GV.GraphvizParams Integer SummaryNode () Integer SummaryNode
    params = GV.defaultParams
             { GV.fmtNode = fmt
             , GV.clusterBy = cls
             , GV.clusterID = clsID
             , GV.globalAttributes =
                 [ GV.GraphAttrs [ GV.RankDir GV.FromLeft , GV.RankSep [2.0] ]
                 ]                 
             }

    revMethodDep :: Map Integer Integer
    revMethodDep = Map.fromList $
                     do MethodSummary i s <- ns
                        t <- methodDeps s
                        pure (t, i)

    clsID :: Integer -> GV.GraphID
    clsID = GV.Num . GV.Int . fromInteger

    cls :: (Integer, SummaryNode) -> GV.NodeCluster Integer (Integer, SummaryNode)
    cls (i, s@TheoremSummary{})
      | Just mth <- Map.lookup i revMethodDep = GV.C mth (GV.N (i,s))
      | otherwise = GV.N (i,s)
    cls (i, s@MethodSummary{}) = GV.C i (GV.N (i,s))

    nodes :: [(Integer,SummaryNode)]
    nodes = map (\n -> (summaryNodeId n, n)) ns

    edges :: [(Integer,Integer,())]
    edges = do n <- ns
               n' <- summaryNodeDeps n
               pure (summaryNodeId n,n',())

    fmt :: (Integer, SummaryNode) -> GV.Attributes
    fmt (_, TheoremSummary _ s) = fmtThm s
    fmt (_, MethodSummary _ s)  = fmtMethod s



fmtThm :: TheoremNode -> GV.Attributes
fmtThm thm = [ GV.shape GV.Trapezium
             , GV.Tooltip (TL.fromStrict tt)
             , GV.textLabel (TL.fromStrict lab)
             , GV.style GV.filled
             , fillcol
             ]
  where
   fillcol =
     case thmStatus thm of
       TheoremVerified{} -> GV.fillColor GV.Green
       TheoremTested{}   -> GV.fillColor GV.Yellow
       TheoremAdmitted{} -> GV.fillColor GV.Red

   lab = T.unlines (status ++ [T.pack (show (thmElapsedTime thm))])

   status = case thmStatus thm of
              TheoremVerified sls -> [T.unwords ("verified:" : sls)]
              TheoremTested nm    -> [T.unwords ["tested:", T.pack (show nm)]]
              TheoremAdmitted msg -> ["Admitted!", msg]

   tt = T.unlines
         ([ thmReason thm
          , thmLoc thm
          ] ++
          case thmPLoc thm of
            Nothing -> []
            Just (fn,l) -> [ fn <> " " <> l ])

fmtMethod :: MethodNode -> GV.Attributes
fmtMethod mn = [ GV.textLabel (TL.fromStrict lab)
               , GV.Tooltip (TL.fromStrict tt)
               , GV.style GV.filled
               , fillcol
               ]
  where
   fillcol =
     case methodStatus mn of
       MethodVerified -> GV.fillColor GV.Green
       MethodAssumed  -> GV.fillColor GV.Red

   lab = T.unlines
          [ methodName mn
          , T.pack (show (methodElapsedtime mn))
          ]
   tt = T.unlines
          [ methodLoc mn
          ] 


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
    o .: "elapsedtime"
  
parseMethodStatus :: Object -> Parser MethodStatus
parseMethodStatus o =
  do st <- o .: "status"
     case st :: Text of
       "assumed"  -> pure MethodAssumed
       "verified" -> pure MethodVerified
       _ -> fail ("Unexpected moethod status " ++ show st)

parseDeps :: Object -> Parser [Integer]
parseDeps o = (o .: "dependencies") >>= parseJSONList

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
summaryNodeDeps (MethodSummary _ s)  = methodDeps s


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
  , methodElapsedtime :: NominalDiffTime
  }
 deriving (Show)

data MethodStatus
  = MethodAssumed
  | MethodVerified
 deriving (Show)
