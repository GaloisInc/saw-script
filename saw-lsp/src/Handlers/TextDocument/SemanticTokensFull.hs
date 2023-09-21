{-# LANGUAGE DisambiguateRecordFields #-}
-- {-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Handlers.TextDocument.SemanticTokensFull (handleTextDocumentSemanticTokensFull, mkResponse) where

import Control.Concurrent.STM
import Control.Lens ((^.))
import Control.Monad.Catch (Exception, MonadThrow, throwM)
import Control.Monad.IO.Class
import Control.Monad.Reader (asks)
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Exts (IsList (..))
import Language.LSP.Server
import Language.LSP.Types
import Language.LSP.Types.Capabilities (ClientCapabilities)
import Language.LSP.Types.Lens qualified as LSP
import Language.LSP.VFS (virtualFileText)
import SAWScript.Lexer (lexSAW)
import SAWScript.Position as SAW (Pos (..))
import SAWScript.Token as SAW (Token (..))
import Server.Monad (ServerM, debug, liftEither, liftMaybe)

handleTextDocumentSemanticTokensFull :: Handlers ServerM
handleTextDocumentSemanticTokensFull = requestHandler STextDocumentSemanticTokensFull doSemanticTokens

doSemanticTokens ::
  RequestMessage 'TextDocumentSemanticTokensFull ->
  (Either ResponseError (Maybe SemanticTokens) -> ServerM ()) ->
  ServerM ()
doSemanticTokens request responder =
  do
    debug "doSemanticTokens" "doing semantic tokens"
    -- doc <- getVirtualFile normalizedUri
    -- wChannel <- asks ssWorkerChannel
    -- liftIO $ atomically $ writeTChan wChannel (Worker.SemanticTokens uri)

    -- let sampler = [0,0,1,0,0] : map (\x -> [0, 1, 1, x, 0]) [1..21]
    -- responder $ Right $ Just $ SemanticTokens Nothing $ List $ concat sampler
    response <- mkResponse uri
    responder (Just <$> response)
  where
    uri = request ^. LSP.params . LSP.textDocument . LSP.uri
    normalizedUri = toNormalizedUri uri

-- let tokens =
--       concat
--         [ [0, 0, 3, 15, 0],
--           [0, 4, 1, 8, 0],
--           [0, 6, 1, 0, 0],
--           [0, 8, 1, 19, 0]
--         ]
-- let sts =
--       SemanticTokens
--         Nothing
--         (List tokens)

-- responder (Right (Just sts))

-- let sts = SemanticTokens Nothing [0, 0, 3, 1, 0]
-- { tokenTypes: ['property', 'type', 'class'],
--   tokenModifiers: ['private', 'static'] }
--
-- { line: 2, startChar:  5, length: 3, tokenType: "property", tokenModifiers: ["private", "static"] }
--
-- [2, 5, 3, 0, 3]
--           |  ^-- bitpacking of indices in `tokenModifier` list in
--           |      initialization request
--           ^-- index in `tokenTypes` list in initialization request

-- responder (Right (Just sts))

-- liftEither :: Either ResponseError a -> LspM Config a

mkResponse ::
  Uri ->
  ServerM (Either ResponseError SemanticTokens)
mkResponse uri =
  do
    vfM <- getVirtualFile normalizedUri
    vf <- liftMaybe getVFError vfM
    let fileContents = virtualFileText vf

    caps <- getClientCapabilities
    tts <- liftEither (tokTypes caps)
    tms <- liftEither (tokMods caps)

    pure (mkTokens tts tms fileContents)
  where
    normalizedUri = toNormalizedUri uri
    getVFError = ResponseError InternalError "TextDocumentSemanticTokensFull: vfs error" Nothing

    tokTypes :: ClientCapabilities -> Either ResponseError (List SemanticTokenTypes)
    tokTypes caps =
      case caps ^. LSP.textDocument >>= (^. LSP.semanticTokens) >>= \sts -> pure (sts ^. LSP.tokenTypes) of
        Nothing -> Left (ResponseError InternalError "client lacks appropriate token capabilities" Nothing)
        Just tts -> Right tts

    tokMods :: ClientCapabilities -> Either ResponseError (List SemanticTokenModifiers)
    tokMods caps =
      case caps ^. LSP.textDocument >>= (^. LSP.semanticTokens) >>= \sts -> pure (sts ^. LSP.tokenModifiers) of
        Nothing -> Left (ResponseError InternalError "client lacks appropriate token capabilities" Nothing)
        Just tms -> Right tms

-- data SemanticTokensParams = SemanticTokensParams
--   { _workDoneToken :: (Maybe ProgressToken)
--   , _partialResultToken :: (Maybe ProgressToken)
--   , _textDocument :: TextDocumentIdentifier }

mkTokens ::
  List SemanticTokenTypes ->
  List SemanticTokenModifiers ->
  Text ->
  Either ResponseError SemanticTokens
mkTokens tts tms txt =
  let ints = encodePositions (lexSAW "TODO" (Text.unpack txt))
   in Right (Language.LSP.Types.SemanticTokens Nothing (List (map fromIntegral ints)))

encodePositions :: [Token Pos] -> [Int]
encodePositions tokens =
  case tokens of
    [] -> mempty
    ts@(tok : _) ->
      let (_, reversedLocs) = foldl encode (tok {tokPos = SAW.Range "" 1 1 1 1}, mempty) ts
       in reverse reversedLocs
  where
    encode :: (Token Pos, [Int]) -> Token Pos -> (Token Pos, [Int])
    encode (prev, locAcc) this =
      case styleM prev this of
        Nothing -> (prev, locAcc)
        Just (lineDelta, startCharDelta, len, tokType, tokMods) ->
          (this, tokMods : tokType : len : startCharDelta : lineDelta : locAcc)

styleM :: Token Pos -> Token Pos -> Maybe (Int, Int, Int, Int, Int)
styleM prev this =
  do
    (lineDelta, startCharDelta) <- distance this prev
    len <- lenM
    tokType <- tokTypeM
    pure (lineDelta, startCharDelta, len, tokType, tokMods)
  where
    lenM =
      case tokPos this of
        SAW.Range _ lb cb le ce
          | lb /= le -> Nothing -- TODO
          | lb == le ->
              case this of
                TLit {} -> Just (fromIntegral (ce - cb + 2))
                TCode {} -> Just (fromIntegral (ce - cb + 4))
                _ -> Just (fromIntegral (ce - cb))
        _ -> Nothing

    -- ttNamespace = 0
    ttType = 1
    -- ttClass = 2
    -- ttEnum = 3
    -- ttInterface = 4
    -- ttStruct = 5
    -- ttTypeParameter = 6
    -- ttParameter = 7
    ttVariable = 8
    -- ttProperty = 9
    -- ttEnumMember = 10
    -- ttEvent = 11
    -- ttFunction = 12
    -- ttMethod = 13
    -- ttMacro = 14
    ttKeyword = 15
    -- ttModifier = 16
    ttComment = 17
    ttString = 18
    ttNumber = 19
    ttRegexp = 20
    ttOperator = 21

    tokTypeM =
      case this of
        TVar {} -> Just ttVariable
        TQVar {} -> Just ttVariable
        TLit {} -> Just ttString
        TCode {} -> Just ttComment
        TCType {} -> Just ttType
        TUnknown {} -> Nothing
        TPunct {} -> Just ttRegexp
        TReserved {} -> Just ttKeyword
        TOp {} -> Just ttOperator
        TNum {} -> Just ttNumber
        TCmntS {} -> Just ttComment
        TCmntE {} -> Just ttComment
        TEOF {} -> Nothing

    tokMods = 0

distance :: Token Pos -> Token Pos -> Maybe (Int, Int) -- (lines away, characters away)
distance token root =
  case (tokPos token, tokPos root) of
    (SAW.Range _ tlb tcb tle tce, SAW.Range _ rlb rcb rle rce)
      | tlb /= rle -> Just (tlb - rlb, tcb - 1)
      | otherwise -> Just (tlb - rlb, tcb - rcb)
    _ -> Nothing

instance IsList (List a) where
  type Item (List a) = a
  fromList = List
  toList (List xs) = xs
