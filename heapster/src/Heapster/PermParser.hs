{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Heapster.PermParser (
  parseFunPermString,
  parseParsedCtxString,
  parseCtxString,
  parseTypeString,
  parsePermsString,
  parseFunPermStringMaybeRust,

  parseAtomicPermsInCtxString,
  parsePermInCtxString,
  parseExprInCtxString,
  parseRustTypeString,
  ) where

import Data.List
import GHC.TypeLits
import qualified Control.Monad.Fail as Fail
import Data.Binding.Hobbits

import Data.Parameterized.Some
import Data.Parameterized.TraversableF

import Lang.Crucible.Types

import Heapster.CruUtil
import Heapster.Permissions
import Heapster.RustTypes

import Heapster.Lexer (lexer)
import Heapster.Located (Pos(..), Located(..))
import Heapster.Token (Token, describeToken)
import Heapster.Parser (ParseError(..), parseFunPerm, parseCtx, parseType, parseExpr, parseValuePerms)
import Heapster.TypeChecker (Tc, TypeError(..), startTc, tcFunPerm, tcCtx, tcType, tcExpr, inParsedCtxM, tcAtomicPerms, tcSortedMbValuePerms, tcValPerm)
import Heapster.ParsedCtx (ParsedCtx, parsedCtxCtx)

----------------------------------------------------------------------
-- * Top-level Entrypoints for Parsing Things
----------------------------------------------------------------------

-- | One of the generated parsers from "Heapster.Parser"
-- which is intended to be used with 'Heapster.Lexer.lexer'
type Parser p = [Located Token] -> Either ParseError p

-- | Harness for running the lexer, parser, and type-checker.
-- Human-readable errors are raised through 'fail'.
runParser ::
  Fail.MonadFail m =>
  String                {- ^ object name                -} ->
  PermEnv               {- ^ permission environment     -} ->
  Parser p              {- ^ parser                     -} ->
  (p -> Tc a)           {- ^ checker                    -} ->
  String                {- ^ input                      -} ->
  m a
runParser obj env parser checker str =
  case parser (lexer str) of
    Left UnexpectedEnd ->
      fail $ unlines
        [ "Error parsing " ++ obj
        , "Unexpected end of input"
        , pointEnd str
        ]
    Left (UnexpectedToken p t) ->
      fail $ unlines
        [ "Error parsing " ++ obj ++ " at " ++ renderPos p
        , "Unexpected " ++ describeToken t
        , point p str
        ]
    Right ast ->
      case startTc (checker ast) env of
        Left (TypeError p e) ->
          fail $ unlines
            [ "Error checking " ++ obj ++ " at " ++ renderPos p
            , e
            , point p str
            ]
        Right x -> pure x

-- | Human-readable rendering of error location
renderPos ::
  Pos                   {- ^ error position             -} ->
  String                {- ^ rendered output            -}
renderPos p = "line " ++ show (posLine p) ++ " column " ++ show (posCol p)

-- | Point to the error in the line with an error.
point ::
  Pos                   {- ^ error position             -} ->
  String                {- ^ full input string          -} ->
  String                {- ^ rendered output            -}
point p str =
  lines str !! (posLine p - 1) ++ "\n" ++
  Data.List.replicate (posCol p - 1) ' ' ++ "^"

-- | Point to the end of the file
pointEnd ::
  String                {- ^ full input string          -} ->
  String                {- ^ rendered output            -}
pointEnd "" = "<<empty input>>"
pointEnd str = end ++ "\n" ++ (' ' <$ end) ++ "^"
  where
    end = last (lines str)

-- | Parse a permission set @x1:p1, x2:p2, ...@ for the variables in the
-- supplied context
parsePermsString ::
  Fail.MonadFail m =>
  String                {- ^ object name                -} ->
  PermEnv               {- ^ permission environment     -} ->
  ParsedCtx ctx         {- ^ parsed context             -} ->
  String                {- ^ input text                 -} ->
  m (MbValuePerms ctx)
parsePermsString nm env ctx =
  runParser nm env parseValuePerms (tcSortedMbValuePerms ctx)

-- | Parse a permission of the given type within the given context and with
-- the given named permission variables in scope
parsePermInCtxString ::
  Fail.MonadFail m =>
  String                {- ^ object name                -} ->
  PermEnv               {- ^ permission environment     -} ->
  ParsedCtx ctx         {- ^ parsed context             -} ->
  TypeRepr a            {- ^ expected permission type   -} ->
  String                {- ^ input text                 -} ->
  m (Mb ctx (ValuePerm a))
parsePermInCtxString nm env ctx tp =
  runParser nm env parseExpr (inParsedCtxM ctx . const . tcValPerm tp)

-- | Parse a sequence of atomic permissions within the given context and with
-- the given named permission variables in scope
parseAtomicPermsInCtxString ::
  Fail.MonadFail m =>
  String                {- ^ object name                -} ->
  PermEnv               {- ^ permission environment     -} ->
  ParsedCtx ctx         {- ^ parsed context             -} ->
  TypeRepr a            {- ^ expected permission type   -} ->
  String                {- ^ input text                 -} ->
  m (Mb ctx [AtomicPerm a])
parseAtomicPermsInCtxString nm env ctx tp =
  runParser nm env parseExpr (inParsedCtxM ctx . const . tcAtomicPerms tp)

-- | Parse a 'FunPerm' named by the first 'String' from the second 'String'
parseFunPermString ::
  Fail.MonadFail m =>
  String                {- ^ object name                -} ->
  PermEnv               {- ^ permission environment     -} ->
  CruCtx args           {- ^ argument types             -} ->
  TypeRepr ret          {- ^ return type                -} ->
  String                {- ^ input text                 -} ->
  m (SomeFunPerm args ret)
parseFunPermString nm env args ret =
  runParser nm env parseFunPerm (tcFunPerm args ret)

-- | Parse a type context @x1:tp1, x2:tp2, ...@ named by the first 'String' from
-- the second 'String' and return a 'ParsedCtx', which contains both the
-- variable names @xi@ and their types @tpi@
parseParsedCtxString ::
  Fail.MonadFail m =>
  String                {- ^ object name                -} ->
  PermEnv               {- ^ permission environment     -} ->
  String                {- ^ input text                 -} ->
  m (Some ParsedCtx)
parseParsedCtxString nm env = runParser nm env parseCtx tcCtx

-- | Parse a type context named by the first 'String' from the second 'String'
parseCtxString ::
  Fail.MonadFail m =>
  String                {- ^ object name                -} ->
  PermEnv               {- ^ permission environment     -} ->
  String                {- ^ input text                 -} ->
  m (Some CruCtx)
parseCtxString nm env str =
  fmapF parsedCtxCtx <$> parseParsedCtxString nm env str

-- | Parse a type named by the first 'String' from the second 'String'
parseTypeString ::
  Fail.MonadFail m =>
  String                {- ^ object name                -} ->
  PermEnv               {- ^ permission environment     -} ->
  String                {- ^ input text                 -} ->
  m (Some TypeRepr)
parseTypeString nm env = runParser nm env parseType tcType

-- | Parse an expression of a given type from a 'String'
parseExprInCtxString ::
  Fail.MonadFail m =>
  PermEnv -> TypeRepr a -> ParsedCtx ctx -> String -> m (Mb ctx (PermExpr a))
parseExprInCtxString env tp ctx =
  runParser (permPrettyString emptyPPInfo tp) env parseExpr
    (inParsedCtxM ctx . const . tcExpr tp)

-- | Parse a 'FunPerm' named by the first 'String' from the second 'String'.
-- The 'FunPerm' can either be standard Heapster syntax, which begins with an
-- open parenthesis (after optional whitespace), or it could be given in Rust
-- syntax, which begins with an angle bracket. The @w@ argument gives the bit
-- width of pointers in the current architecture.
parseFunPermStringMaybeRust ::
  (1 <= w, KnownNat w, Fail.MonadFail m) =>
  String                {- ^ object name                -} ->
  prx w                 {- ^ pointer bit-width proxy    -} ->
  PermEnv               {- ^ permission environment     -} ->
  CruCtx args           {- ^ argument types             -} ->
  TypeRepr ret          {- ^ return type                -} ->
  String                {- ^ input text                 -} ->
  m (SomeFunPerm args ret)
parseFunPermStringMaybeRust nm w env args ret str =
  case find (\c -> c == '<' || c == '(') str of
    Just '<' -> parseFunPermFromRust env w args ret str
    _ -> parseFunPermString nm env args ret str

-- | Parse a 'SomeNamedShape' from the given 'String'. This 'SomeNamedShape'
-- must be a valid Rust @struct@ or @enum@ declaration given in Rust syntax.
-- The @w@ argument gives the bit width of pointers in the current\
-- architecture.
parseRustTypeString ::
  (1 <= w, KnownNat w, Fail.MonadFail m) =>
  PermEnv               {- ^ permission environment     -} ->
  prx w                 {- ^ pointer bit-width proxy    -} ->
  String                {- ^ input text                 -} ->
  m (SomePartialNamedShape w)
parseRustTypeString = parseNamedShapeFromRustDecl
