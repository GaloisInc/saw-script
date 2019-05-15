{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.Heapster.Parser where

import Data.Functor.Product
import Data.Type.Equality
import Text.Parsec
-- import Text.ParserCombinators.Parsec
import Control.Monad.Identity
import Control.Monad.Reader

import Data.Parameterized.Some
import Data.Parameterized.Context
import Data.Parameterized.Ctx
import Data.Parameterized.TraversableFC
import Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel

import SAWScript.Heapster.Permissions
import SAWScript.Heapster.Pretty


integer :: Stream s Identity Char => PermParseM s Integer
integer = read <$> many1 digit

parseNatRepr :: Stream s Identity Char =>
                PermParseM s (Some (Product NatRepr (LeqProof 1)))
parseNatRepr =
  do i <- integer
     case someNat i of
       Just (Some w)
         | Left leq <- decideLeq knownNat w -> return (Some (Pair w leq))
       Just _ -> unexpected "Zero bitvector width not allowed"
       Nothing -> error "parseNatRepr: unexpected negative bitvector width"


data Typed f a = Typed (TypeRepr a) (f a)
type ParserEnv = Assignment (Typed StringF)

extendPEnv :: ParserEnv ctx -> String -> TypeRepr tp -> ParserEnv (ctx ::> tp)
extendPEnv env x tp = extend env (Typed tp (StringF x))

lookupVarName :: ParserEnv ctx -> PermVar ctx a -> String
lookupVarName env (PermVar _ ix) =
  case env ! ix of
    Typed _ (StringF nm) -> nm

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


type PermParseM s = Parsec s ()

parseIdent :: Stream s Identity Char => PermParseM s String
parseIdent =
  do spaces
     c <- letter
     cs <- many (alphaNum <|> char '_' <|> char '\'')
     return (c:cs)

parseVar :: Stream s Identity Char => ParserEnv ctx ->
            PermParseM s (Some (Typed (PermVar ctx)))
parseVar env =
  do str <- parseIdent
     case lookupVar str env of
       Just x -> return x
       Nothing -> unexpected ("Unknown variable: " ++ str)

parseVarOfType :: Stream s Identity Char => ParserEnv ctx ->
                  TypeRepr a -> PermParseM s (PermVar ctx a)
parseVarOfType env a =
  do some_x <- parseVar env
     case some_x of
       Some (Typed b x)
         | Just Refl <- testEquality a b -> return x
       _ -> unexpected "Variable has incorrect type"

parseInParens :: Stream s Identity Char =>
                 PermParseM s a -> PermParseM s a
parseInParens m =
  do spaces >> char '('
     ret <- m
     spaces >> char ')'
     return ret

parseStructFieldTypes :: Stream s Identity Char =>
                         PermParseM s (Some (Assignment TypeRepr))
parseStructFieldTypes =
  helper <$> reverse <$> sepBy parseType (spaces >> char ',')
  where
    helper :: [Some TypeRepr] -> Some (Assignment TypeRepr)
    helper [] = Some empty
    helper (Some tp:tps) =
      case helper tps of
        Some asgn -> Some $ extend asgn tp

parseType :: Stream s Identity Char => PermParseM s (Some TypeRepr)
parseType =
  spaces >>
  ((string "S" >> return (Some splittingTypeRepr)) <|>
   (do string "bv"
       space >> spaces
       w <- parseNatRepr
       case w of
         Some (Pair w LeqProof) -> return (Some $ BVRepr w)) <|>
   (do string "llvmptr"
       space >> spaces
       w <- parseNatRepr
       case w of
         Some (Pair w LeqProof) -> return (Some $ BVRepr w)) <|>
   (do string "struct"
       some_fld_tps <- parseInParens (parseStructFieldTypes)
       case some_fld_tps of
         Some fld_tps -> return $ Some $ StructRepr fld_tps) <?>
   "Cannot parse type")

parseSplittingAtomic :: Stream s Identity Char => ParserEnv ctx ->
                        PermParseM s (SplittingExpr ctx)
parseSplittingAtomic env =
  spaces >>
  ((parseInParens $ parseSplitting env) <|>
   (char 'W' >> return SplExpr_All) <|>
   (SplExpr_Var <$> parseVarOfType env splittingTypeRepr))

parseSplitting :: Stream s Identity Char => ParserEnv ctx ->
                  PermParseM s (SplittingExpr ctx)
parseSplitting env =
  do spl1 <- parseSplittingAtomic env
     spaces
     (char 'L' >> return (SplExpr_L spl1)) <|>
       (char 'R' >> return (SplExpr_R spl1)) <|>
       (do _ <- char '*'
           spl2 <- parseSplitting env
           return $ SplExpr_Star spl1 spl2)

parseBVExpr :: (1 <= w, Stream s Identity Char) =>
               ParserEnv ctx -> NatRepr w ->
               PermParseM s (PermExpr ctx (BVType w))
parseBVExpr env w =
  do spaces
     expr1 <-
       try (do i <- integer
               spaces >> char '*' >> spaces
               x <- parseVarOfType env (BVRepr w)
               return $ PExpr_BV w [BVFactor w i x] 0) <|>
       try (do x <- parseVarOfType env (BVRepr w)
               spaces >> char '*' >> spaces
               i <- integer
               return $ PExpr_BV w [BVFactor w i x] 0) <|>
       (do i <- integer
           return $ PExpr_BV w [] i) <|>
       (PExpr_Var <$> parseVarOfType env (BVRepr w))
     try (spaces >> char '+' >> spaces >>
          (addBVExprs w expr1 <$> parseBVExpr env w)) <|>
       return expr1

parseStructFields :: Stream s Identity Char => ParserEnv ctx -> CtxRepr args ->
                     PermParseM s (Assignment (PermExpr ctx) args)
parseStructFields _ (viewAssign -> AssignEmpty) = return empty
parseStructFields env (viewAssign ->
                   AssignExtend (viewAssign -> AssignEmpty) tp) =
  extend empty <$> parseExpr env tp
parseStructFields env (viewAssign -> AssignExtend tps' tp) =
  do args' <- parseStructFields env tps'
     spaces >> char ','
     arg <- parseExpr env tp
     return $ extend args' arg

parseExpr :: Stream s Identity Char => ParserEnv ctx -> TypeRepr a ->
             PermParseM s (PermExpr ctx a)
parseExpr env (BVRepr w) = parseBVExpr env w
parseExpr env tp@(StructRepr fld_tps) =
  spaces >>
  ((string "struct" >>
    parseInParens (PExpr_Struct fld_tps <$> parseStructFields env fld_tps)) <|>
   (PExpr_Var <$> parseVarOfType env tp))
parseExpr env tp@(LLVMPointerRepr w) =
  spaces >>
  ((string "llvmword" >>
    (PExpr_LLVMWord w <$> parseInParens (parseBVExpr env w))) <|>
   (do x <- parseVarOfType env tp
       try (do spaces >> char '+' >> spaces
               off <- parseBVExpr env w
               return $ PExpr_LLVMOffset w x off) <|>
         return (PExpr_Var x)))
parseExpr env (testEquality splittingTypeRepr -> Just Refl) =
  PExpr_Spl <$> parseSplitting env
parseExpr env tp =
  spaces >>
  ((PExpr_Var <$> parseVarOfType env tp) <?>
   ("Unexpected non-variable expression of type " ++ show tp))


parseLLVMShape :: (1 <= w, Stream s Identity Char) =>
                  ParserEnv ctx -> NatRepr w ->
                  PermParseM s (LLVMShapePerm ctx w)
parseLLVMShape env w =
  do spaces
     llvmFieldOffset <- integer
     spaces
     string "|->"
     spaces >> char '('
     llvmFieldSplitting <- parseSplitting env
     spaces >> char ','
     llvmFieldPerm <- parseValPerm env (LLVMPointerRepr w)
     spaces >> char ')'
     return $ LLVMFieldShapePerm $ LLVMFieldPerm { .. }

-- FIXME HERE: add support for array permissions!


parseValPermH :: Stream s Identity Char => ParserEnv ctx -> TypeRepr a ->
                 PermParseM s (ValuePerm ctx a)
parseValPermH env tp =
  do spaces
     p1 <-
       (parseInParens (parseValPerm env tp)) <|>
       (string "true" >> return ValPerm_True) <|>
       (string "eq" >> parseInParens (ValPerm_Eq <$> parseExpr env tp)) <|>
       (do string "exists" >> spaces
           var <- parseIdent
           spaces >> char ':'
           some_tp' <- parseType
           spaces >> char '.'
           case some_tp' of
             Some tp' ->
               do p <- parseValPerm (extendPEnv env var tp') tp
                  return $ ValPerm_Exists tp' p) <|>
       (do string "mu" >> spaces
           var <- parseIdent
           spaces >> char '.'
           ValPerm_Mu <$>
             parseValPerm (extendPEnv env var (valuePermRepr tp)) tp) <|>
       (ValPerm_Var <$> parseVarOfType env (valuePermRepr tp))
     spaces
     try (string "\\/" >> (ValPerm_Or p1 <$> parseValPerm env tp)) <|>
       return p1

parseValPerm :: Stream s Identity Char => ParserEnv ctx -> TypeRepr a ->
                PermParseM s (ValuePerm ctx a)
parseValPerm env tp@(LLVMPointerRepr w) =
  (do string "llvmptr"
      spaces
      maybe_free <-
        try (do char '['
                e <- parseExpr env (BVRepr w)
                spaces >> char ']'
                return $ Just e) <|>
        return Nothing
      shapes <-
        parseInParens (sepBy (parseLLVMShape env w) (spaces >> char '*'))
      return $ ValPerm_LLVMPtr w shapes maybe_free) <|>
  parseValPermH env tp
parseValPerm env tp = parseValPermH env tp


parseVarPerms :: Stream s Identity Char => ParserEnv ctx ->
                 MapF (PermVar ctx) (ValuePerm ctx) ->
                 PermParseM s (MapF (PermVar ctx) (ValuePerm ctx))
parseVarPerms env perms =
  do spaces
     some_x <- parseVar env
     spaces >> char ':'
     case some_x of
       Some (Typed tp x) ->
         do if MapF.member x perms then
              unexpected ("Variable " ++ lookupVarName env x ++ " occurs twice")
              else return ()
            p <- parseValPerm env tp
            let perms' = MapF.insert x p perms
            spaces
            (char ',' >> parseVarPerms env perms') <|> return perms'

parsePermSet :: Stream s Identity Char => ParserEnv ctx ->
                PermParseM s (PermSet ctx)
parsePermSet env =
  do perms <- parseVarPerms env MapF.empty
     return $ PermSet (fmapFC (\(Typed tp _) -> tp) env) $
       generatePermVar (size env) $ \x ->
       case MapF.lookup x perms of
         Just p -> p
         Nothing -> ValPerm_True

parseCtx :: Stream s Identity Char => ParserEnv ctx ->
            PermParseM s (Some ParserEnv)
parseCtx env =
  do spaces
     x <- parseIdent
     case lookupVar x env of
       Nothing -> return ()
       Just _ -> unexpected ("Variable " ++ x ++ " occurs twice")
     spaces >> char ':'
     some_tp <- parseType
     spaces
     case some_tp of
       Some tp ->
         let env' = extendPEnv env x tp in
         (char ',' >> parseCtx env') <|> return (Some env')
