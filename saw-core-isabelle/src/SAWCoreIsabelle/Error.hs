{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
module SAWCoreIsabelle.Error where
import           Data.List (intercalate)
import qualified Data.List.NonEmpty as NE

import qualified Cryptol.TypeCheck.AST as Cry
import           Cryptol.TypeCheck.PP (pretty, PP)
import qualified Cryptol.Parser.Position as Position
import qualified Cryptol.Utils.Ident as Cry

import qualified Language.Isabelle.Name as Name
import qualified SAWCoreIsabelle.Options as Options

data TranslationError =
    UnsupportedDecl Cry.Decl
  | UnsupportedExpr Cry.Expr
  | UnsupportedType Cry.Type
  | UnsupportedTypeDecl Cry.Name Cry.TySyn
  | UnsupportedEntity String
  | UnsupportedRecursion [Cry.Decl]
  | UnexpectedSignature Cry.Schema Cry.Expr
  | UnknownVariableIdent Int
  | UnsupportedMatchShape [[Cry.Match]]
  | TypeMismatch Cry.Type Cry.Type
  | UnexpectedPolymorphism Cry.Schema
  | TypeCheckFailure Cry.Expr
  | StubbedFunction Cry.Decl
  | MissingCryName Cry.Name
  | CryptolTypeOfError Cry.Expr String
  | ModuleTranslationFailure Cry.ModName
  | LocatedError Position.Range TranslationError
  | InnerErrors TranslationError [TranslationError]
  | MonadFailure String

stripLocation :: Position.Range -> TranslationError -> TranslationError
stripLocation rng = \case
  LocatedError rng' er | Position.rangeWithin rng rng' -> er
  InnerErrors er errs -> InnerErrors (stripLocation rng er) (map (stripLocation rng) errs)
  er -> er

joinRange :: Position.Range -> Position.Range -> Position.Range
joinRange rng1 rng2 = case (Position.source rng1, Position.source rng2) of
  ("", _) -> rng2
  (_,"") -> rng1
  _ -> if Position.rangeWithin rng1 rng2 then rng1 else rng2

addLocation :: Position.Range -> TranslationError -> TranslationError
addLocation rng er | rng == Position.emptyRange = stripLocation rng er
addLocation rng er = case er of
  LocatedError rng' er' -> LocatedError (joinRange rng rng') er'
  InnerErrors (LocatedError rng' er') ers -> 
    addLocation rng $ LocatedError rng' (InnerErrors er' ers)
  _ -> LocatedError rng (stripLocation rng er)

nontrivial :: TranslationError -> Bool
nontrivial = \case
  LocatedError _ e -> nontrivial e
  InnerErrors e es -> nontrivial e || any nontrivial es
  MonadFailure "" -> False
  _ -> True

innerErrors :: TranslationError -> [TranslationError] -> TranslationError
innerErrors er ers = case filter nontrivial ers of
  [] -> er
  ers' -> InnerErrors er ers'

data OuterTranslationError where
  OuterTranslationError :: Options.HasOptions => TranslationError -> OuterTranslationError

pp :: (Options.HasOptions, Show a, PP a) => a -> String
pp a = if Options.verbosity >= 3 then pretty a ++ "\n (" ++ show a ++ ")" else pretty a

ppList :: (Options.HasOptions, Show a, PP a) => [a] -> String
ppList a = intercalate "\n" $ map pp a

ppNames :: [Name.Name] -> String
ppNames nms = intercalate " " $ map Name.cleanName nms

flatErrors :: TranslationError -> [TranslationError]
flatErrors = \case
  InnerErrors e es -> flatErrors e ++ (concat $ map flatErrors es)
  LocatedError rng e -> fmap (addLocation rng) $ flatErrors e
  e | nontrivial e -> [e]
  _ -> []

simpleError :: TranslationError -> TranslationError
simpleError e = case NE.nonEmpty (flatErrors e) of
  Just es | NE.length es > 1 -> InnerErrors (NE.head es) [NE.last es]
  _ -> e

instance Show OuterTranslationError where
  show (OuterTranslationError er) = case er of
    UnsupportedDecl d -> "Unsupported cryptol declaration: " ++ pp d
    UnsupportedExpr e -> "Unsupported cryptol expression: " ++ pp e
    UnsupportedType t -> "Unsupported cryptol type: " ++ pp t
    UnsupportedTypeDecl nm t -> "Unsupported type declaration: " ++ pp nm ++ " = " ++ pp t
    UnsupportedEntity nm -> "Unsupported translation entity: " ++ show nm
    UnexpectedSignature s e -> "Unexpected signature: " ++ pp s ++ " for cryptol declaration: " ++ pp e
    UnsupportedRecursion ds -> "Unsupported recursive declarations:\n" ++ ppList ds
    UnknownVariableIdent idx -> "Unknown variable identifier: " ++ show idx
    UnsupportedMatchShape matches ->
      "Unsupported match shape: " ++ show (map length matches)
    TypeMismatch t1 t2 -> "Type mismatch: " ++ pp t1 ++ " vs. " ++ pp t2
    UnexpectedPolymorphism s -> "Unexpected polymorphic type: " ++ pp s
    TypeCheckFailure e -> "Failed to type check cryptol expression: " ++ pp e
    StubbedFunction d -> "Unexpected function stub: " ++ pp d
    MissingCryName nm -> "No entry in cryptol environment for name: " ++ pp nm
    CryptolTypeOfError e msg -> "Could not determine type of Cryptol expression: \n" 
      ++ pp e ++ "\n" ++ msg
    ModuleTranslationFailure mnm -> "Failed to translate Cryptol module: " ++ pp mnm
    LocatedError rng e -> pp rng ++ "\n" ++ showErr e
    InnerErrors e [] -> showErr e
    InnerErrors e es -> showErr e ++ "\n" ++ (intercalate "\n" $ map showErr es)
    MonadFailure msg -> msg

showErr :: Options.HasOptions => TranslationError -> String
showErr er = case Options.verbosity < 2 of
  True -> show (OuterTranslationError (simpleError er))
  False -> show (OuterTranslationError er)
