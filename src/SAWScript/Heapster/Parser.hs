{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.Heapster.Parser where

import Data.Type.Equality
import Text.Parsec
import Text.ParserCombinators.Parsec
import Control.Monad.Identity

import Data.Parameterized.Some
import Data.Parameterized.Context
import Data.Parameterized.Ctx
import Data.Parameterized.TraversableFC

import Lang.Crucible.Types

import SAWScript.Heapster.Permissions
import SAWScript.Heapster.Pretty

type ParserEnv ctx = Assignment (Typed StringF) ctx

data Typed f a = Typed (TypeRepr a) (f a)

lookupVar :: String -> ParserEnv ctx ->
             Maybe (Some (Typed (PermVar ctx)))
lookupVar _ (viewAssign -> AssignEmpty) = Nothing
lookupVar x (viewAssign -> AssignExtend asgn' (Typed tp (StringF y)))
  | x == y = Just $ Some $ Typed tp $
    PermVar (incSize $ size asgn') (nextIndex $ size asgn')
lookupVar x (viewAssign -> AssignExtend asgn' _) =
  do some_var <- lookupVar x asgn'
     case some_var of
       Some (Typed tp x) -> return $ Some $ Typed tp $ weakenPermVar1 x


type PermParseM s ctx = Parsec s (ParserEnv ctx)

parseVar :: Stream s Identity Char =>
            PermParseM s ctx (Some (Typed (PermVar ctx)))
parseVar =
  do spaces
     c <- letter
     cs <- many (alphaNum <|> char '_' <|> char '\'')
     let str = c:cs
     env <- getState
     case lookupVar str env of
       Just x -> return x
       Nothing -> unexpected ("Unknown variable: " ++ str)

parseVarOfType :: Stream s Identity Char =>
                  TypeRepr a -> PermParseM s ctx (PermVar ctx a)
parseVarOfType a =
  do some_x <- parseVar
     case some_x of
       Some (Typed b x)
         | Just Refl <- testEquality a b -> return x
       _ -> unexpected "Variable has incorrect type"

parseSplittingAtomic :: Stream s Identity Char =>
                        PermParseM s ctx (SplittingExpr ctx)
parseSplittingAtomic =
  spaces >>
  ((do _ <- char '('
       spl <- parseSplitting
       _ <- char ')'
       return spl) <|>
   (char 'W' >> return SplExpr_All) <|>
   (SplExpr_Var <$> parseVarOfType splittingTypeRepr))

parseSplitting :: Stream s Identity Char => PermParseM s ctx (SplittingExpr ctx)
parseSplitting =
  do spl1 <- parseSplittingAtomic
     spaces
     (char 'L' >> return (SplExpr_L spl1)) <|>
       (char 'R' >> return (SplExpr_R spl1)) <|>
       (do _ <- char '*'
           spl2 <- parseSplitting
           return $ SplExpr_Star spl1 spl2)
