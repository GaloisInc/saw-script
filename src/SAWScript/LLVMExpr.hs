{- |
Module      : SAWScript.LLVMExpr
Description : Data structures for LLVM expressions and types.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module SAWScript.LLVMExpr
  (-- * LLVM Expressions
    LLVMExprF(..)
  , LLVMExpr
  , ProtoLLVMExpr(..)
  , ProtoLLVMField(..)
  , parseProtoLLVMExpr
  , ppProtoLLVMExpr
  , ppLLVMExpr
  , lssTypeOfLLVMExpr
  , updateLLVMExprType
  , isPtrLLVMExpr
  , isArgLLVMExpr
  , containsReturn
  , exprDepth
    -- * Logic expressions
  , LogicExpr(..)
  , logicExprLLVMExprs
  , useLogicExpr
  , asLLVMExpr
    -- * Mixed expressions
  , MixedExpr(..)
    -- * Actual type
  , LLVMActualType
  , isActualPtr
  , isPrimitiveType
  , logicTypeOfActual
  , cryptolTypeOfActual
  , ppActualType
  , SymbolLocation (..)
  ) where

-- Imports {{{2

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
-- import Data.Set (Set)
import Data.Functor.Identity
import qualified Data.Vector as Vector (toList)
import Text.Parsec as P
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))
import Text.Read

import qualified Verifier.LLVM.Codebase as LSS

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm

import qualified SAWScript.CongruenceClosure as CC

import qualified Cryptol.TypeCheck.AST as Cryptol

data SymbolLocation
   = Block LSS.SymBlockID
   | LineOffset Integer
   | LineExact Integer
  deriving (Show)

type Parser a = ParsecT String () Identity a

-- The result of parsing an LLVM expression, before type-checking
data ProtoLLVMExpr
  = PVar String
  | PArg Int
  | PDeref ProtoLLVMExpr
  | PField ProtoLLVMField ProtoLLVMExpr -- Recursive arg is _address_
  | PDirectField ProtoLLVMField ProtoLLVMExpr -- Recursive arg is _value_
  | PReturn
  -- PIndex ProtoLLVMExpr ProtoLLVMExpr
    deriving (Show)

data ProtoLLVMField
  = FieldIndex Int
  | FieldName String
    deriving Show

ppProtoLLVMExpr :: ProtoLLVMExpr -> Doc
ppProtoLLVMExpr (PVar x) = text x
ppProtoLLVMExpr PReturn = text "return"
ppProtoLLVMExpr (PArg n) = PP.string "args[" <> int n <> PP.string "]"
ppProtoLLVMExpr (PDeref e) = PP.text "*" <> PP.parens (ppProtoLLVMExpr e)
ppProtoLLVMExpr (PField n e) =
  PP.parens (ppProtoLLVMExpr e) <> text "->" <> ppProtoLLVMField n
ppProtoLLVMExpr (PDirectField n e) =
  PP.parens (ppProtoLLVMExpr e) <> text "." <> ppProtoLLVMField n
--ppProtoLLVMExpr (PIndex n e) =
--  ppProtoLLVMExpr e <> text "[" <> ppProtoLLVMExpr n <> text "]"

ppProtoLLVMField :: ProtoLLVMField -> Doc
ppProtoLLVMField (FieldIndex i) = int i
ppProtoLLVMField (FieldName  n) = PP.text n

parseProtoLLVMExpr :: String
                   -> Either ParseError ProtoLLVMExpr
parseProtoLLVMExpr = runIdentity . runParserT (parseExpr <* eof) () "expr"
  where
    parseExpr = parseDeref <|> parseFieldsExpr
    parseAExpr = P.choice
                 [ parseReturn
                 , parseArgs
                 , parseVar
                 , parseParens
                 ]
    alphaUnder = P.choice [P.letter, P.char '_']
    parseIdent = (:) <$> alphaUnder <*> P.many (P.choice [alphaUnder, P.digit])
    parseVar :: Parser ProtoLLVMExpr
    parseVar = PVar <$> try parseIdent
    parseParens :: Parser ProtoLLVMExpr
    parseParens = P.string "(" *> parseExpr <* P.string ")"
    parseReturn :: Parser ProtoLLVMExpr
    parseReturn = try (P.string "return") >> return PReturn
    parseDeref :: Parser ProtoLLVMExpr
    parseDeref = PDeref <$> (try (P.string "*") *> parseExpr)
    parseArgs :: Parser ProtoLLVMExpr
    parseArgs = do
      _ <- try (P.string "args[")
      ns <- many1 digit
      e <- case readMaybe ns of
             Just (n :: Int) -> return (PArg n)
             Nothing ->
               unexpected $ "Using `args` with non-numeric parameter: " ++ ns
      _ <- P.string "]"
      return e
    parseFieldsExpr :: Parser ProtoLLVMExpr
    parseFieldsExpr = do
      e <- parseAExpr
      fs <- many (parseDerefField <|> parseDirectField)
      return (foldl (flip ($)) e fs)
    parseDerefField :: Parser (ProtoLLVMExpr -> ProtoLLVMExpr)
    parseDerefField = do
      n <- try (P.string "->") *> parseField
      return (\e -> PField n e)
    parseDirectField :: Parser (ProtoLLVMExpr -> ProtoLLVMExpr)
    parseDirectField = do
      n <- P.string "." *> parseField
      return (\e -> PDirectField n e)

    parseField = FieldIndex . read <$> many1 digit
             <|> FieldName         <$> parseIdent

-- NB: the types listed in each of these should be the type of the
-- entire expression. So "Deref v tp" means "*v has type tp".
data LLVMExprF v
  = Arg Int LSS.Ident LLVMActualType
  | Global LSS.Symbol LLVMActualType
  | Deref v LLVMActualType
  -- | Index v v LLVMActualType
  | StructField v LSS.StructInfo Int LLVMActualType -- Recursive arg is _address_
  | StructDirectField v LSS.StructInfo Int LLVMActualType -- Recursive arg is _value_
  | ReturnValue LLVMActualType
  deriving (Functor, CC.Foldable, CC.Traversable)


instance CC.EqFoldable LLVMExprF where
  fequal (Arg i _ _)(Arg j _ _) = i == j
  fequal (Global x _)(Global y _) = x == y
  fequal (Deref e _) (Deref e' _) = e == e'
  fequal (StructField xr _ xi _) (StructField yr _ yi _) =
    xi == yi && (xr == yr)
  fequal (StructDirectField xr _ xi _) (StructDirectField yr _ yi _) =
    xi == yi && (xr == yr)
  fequal (ReturnValue _) (ReturnValue _) = True
  fequal _ _ = False

instance CC.OrdFoldable LLVMExprF where
  Arg i _ _  `fcompare` Arg i' _ _   = i `compare` i'
  Arg _ _ _  `fcompare` _            = LT
  _          `fcompare` Arg _ _ _    = GT
  Global n _ `fcompare` Global n' _  = n `compare` n'
  Global _ _ `fcompare` _            = LT
  _          `fcompare` Global _ _   = GT
  Deref e _  `fcompare` Deref e' _   = e `compare` e'
  Deref _ _  `fcompare` _            = LT
  _          `fcompare` Deref _ _    = GT
  StructField r1 _ f1 _ `fcompare` StructField r2 _ f2 _ =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r
  StructField _ _ _ _ `fcompare` _           = LT
  _          `fcompare` StructField _ _ _ _ = GT
  StructDirectField r1 _ f1 _ `fcompare` StructDirectField r2 _ f2 _ =
        case r1 `compare` r2 of
          EQ -> f1 `compare` f2
          r  -> r
  StructDirectField _ _ _ _ `fcompare` _           = LT
  _          `fcompare` StructDirectField _ _ _ _ = GT
  (ReturnValue _) `fcompare` (ReturnValue _) = EQ

instance CC.ShowFoldable LLVMExprF where
  fshow (Arg _ nm _) = show nm
  fshow (Global nm _) = show nm
  fshow (Deref e _) = "*(" ++ show e ++ ")"
  fshow (StructField r _ f _) = show r ++ "->" ++ show f
  fshow (StructDirectField r _ f _) = show r ++ "." ++ show f
  fshow (ReturnValue _) = "return"

-- | Typechecked LLVMExpr
type LLVMExpr = CC.Term LLVMExprF

exprDepth :: LLVMExpr -> Int
exprDepth = CC.foldTerm $ \e ->
  case e of
    Arg{}                     -> 0
    Global{}                  -> 0
    ReturnValue{}             -> 0
    Deref r _                 -> r+1
    StructField       r _ _ _ -> r+1
    StructDirectField r _ _ _ -> r

-- | Pretty print a LLVM expression.
ppLLVMExpr :: LLVMExpr -> Doc
ppLLVMExpr (CC.Term exprF) =
  case exprF of
    Arg _ nm _ -> LSS.ppIdent nm
    Global nm _ -> LSS.ppSymbol nm
    Deref e _ -> PP.char '*' <> PP.parens (ppLLVMExpr e)
    StructField r _ f _ -> ppLLVMExpr r <> text "->" <> text (show f)
    StructDirectField r _ f _ -> ppLLVMExpr r <> text "." <> text (show f)
    ReturnValue _ -> text "return"

-- | Returns LSS Type of LLVMExpr
lssTypeOfLLVMExpr :: LLVMExpr -> LSS.MemType
lssTypeOfLLVMExpr (CC.Term exprF) =
  case exprF of
    Arg _ _ tp -> tp
    Global _ tp -> tp
    Deref _ tp -> tp
    StructField _ _ _ tp -> tp
    StructDirectField _ _ _ tp -> tp
    ReturnValue tp -> tp

updateLLVMExprType :: LLVMExpr -> LSS.MemType -> LLVMExpr
updateLLVMExprType (CC.Term exprF) tp = CC.Term $
  case exprF of
    Arg i n _ -> Arg i n tp
    Global n _ -> Global n tp
    Deref e _ -> Deref e tp
    StructField r si i _ -> StructField r si i tp
    StructDirectField r si i _ -> StructDirectField r si i tp
    ReturnValue _ -> ReturnValue tp

asLLVMExpr :: Term -> Maybe String
asLLVMExpr (asExtCns -> Just ec) = Just (ecName ec)
asLLVMExpr _ = Nothing

-- | Returns true if expression is a pointer.
isPtrLLVMExpr :: LLVMExpr -> Bool
isPtrLLVMExpr = isActualPtr . lssTypeOfLLVMExpr

isArgLLVMExpr :: LLVMExpr -> Bool
isArgLLVMExpr (CC.Term (Arg _ _ _)) = True
isArgLLVMExpr _ = False

containsReturn :: LLVMExpr -> Bool
containsReturn (CC.Term e) =
  case e of
    Arg _ _ _ -> False
    Global _ _ -> False
    Deref pe _ -> containsReturn pe
    StructField pe _ _ _ -> containsReturn pe
    StructDirectField pe _ _ _ -> containsReturn pe
    ReturnValue _ -> True

-- LogicExpr {{{1

data LogicExpr =
  LogicExpr { -- | A term, possibly function type, which does _not_
              -- contain any external constant subexpressions.
              _leTerm :: Term
              -- | The LLVM expressions, if any, that the term should
              -- be applied to
            , leLLVMArgs :: [LLVMExpr]
            }
  deriving (Show)

useLogicExpr :: SharedContext -> LogicExpr -> [Term] -> IO Term
useLogicExpr sc (LogicExpr t _) args = scApplyAll sc t args

logicExprLLVMExprs :: LogicExpr -> [LLVMExpr]
logicExprLLVMExprs = leLLVMArgs

-- MixedExpr {{{1

-- | A logic or LLVM expression.
data MixedExpr
  = LogicE LogicExpr
  | LLVME LLVMExpr
  deriving (Show)

-- | Identifies concrete type of a LLVM expression. We can use normal
-- LLVM types to encode precise, actual types.
type LLVMActualType = LSS.MemType

isPrimitiveType :: LLVMActualType -> Bool
isPrimitiveType (LSS.IntType _) = True
isPrimitiveType LSS.FloatType = True
isPrimitiveType LSS.DoubleType = True
isPrimitiveType _ = False

-- | Returns true if this represents a reference.
isActualPtr :: LLVMActualType -> Bool
isActualPtr (LSS.PtrType _) = True
isActualPtr _ = False

-- | Returns logical type of actual type if it is an array or primitive
-- type, or an appropriately-sized bit vector for pointer types.
logicTypeOfActual :: LSS.DataLayout -> SharedContext -> LLVMActualType
                  -> IO (Maybe Term)
logicTypeOfActual _ sc (LSS.IntType w) = do
  bType <- scBoolType sc
  lTm <- scNat sc (fromIntegral w)
  Just <$> scVecType sc lTm bType
logicTypeOfActual _ sc LSS.FloatType = Just <$> scPrelude_Float sc
logicTypeOfActual _ sc LSS.DoubleType = Just <$> scPrelude_Double sc
logicTypeOfActual dl sc (LSS.ArrayType n ty) = do
  melTyp <- logicTypeOfActual dl sc ty
  case melTyp of
    Just elTyp -> do
      lTm <- scNat sc (fromIntegral n)
      Just <$> scVecType sc lTm elTyp
    Nothing -> return Nothing
logicTypeOfActual dl sc (LSS.PtrType _) = do
  bType <- scBoolType sc
  lTm <- scNat sc (fromIntegral (LSS.ptrBitwidth dl))
  Just <$> scVecType sc lTm bType
logicTypeOfActual dl sc (LSS.StructType si) = do
  let actuals = map LSS.fiType (Vector.toList (LSS.siFields si))
  melTyps <- mapM (logicTypeOfActual dl sc) actuals
  case sequence melTyps of
    Just elTyps -> Just <$> scTupleType sc elTyps
    Nothing -> return Nothing
logicTypeOfActual _ _ _ = return Nothing

-- | Returns Cryptol type of actual type if it is an array or primitive type.
cryptolTypeOfActual :: LLVMActualType -> Maybe Cryptol.Type
cryptolTypeOfActual (LSS.IntType w) =
  Just $ Cryptol.tSeq (Cryptol.tNum w) Cryptol.tBit
cryptolTypeOfActual (LSS.ArrayType n ty) = do
  elty <- cryptolTypeOfActual ty
  return $ Cryptol.tSeq (Cryptol.tNum n) elty
cryptolTypeOfActual (LSS.StructType si) = do
  let actuals = map LSS.fiType (Vector.toList (LSS.siFields si))
  eltys <- mapM cryptolTypeOfActual actuals
  return $ Cryptol.tTuple eltys
cryptolTypeOfActual _ = Nothing

ppActualType :: LLVMActualType -> Doc
ppActualType = LSS.ppMemType
