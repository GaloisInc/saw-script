{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module SAWScript.Heapster.PermParser where

import Data.List
import Data.String
import Data.Maybe
import Data.Functor.Product
import Data.Functor.Compose
import Data.Type.Equality
import GHC.TypeLits
import Control.Monad.Identity
import Control.Monad.Reader
import Data.Binding.Hobbits

import Text.Parsec
import Text.Parsec.Error
-- import Text.ParserCombinators.Parsec

import Data.Parameterized.Context hiding ((:>), empty, take, zipWith, Empty)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Some

import Lang.Crucible.Types
import Lang.Crucible.LLVM.MemModel
import Lang.Crucible.FunctionHandle
-- import What4.FunctionName

import SAWScript.Heapster.CruUtil
import SAWScript.Heapster.Permissions


-- FIXME: maybe some of these should use unsafeMbTypeRepr for efficiency?
$(mkNuMatching [t| SourcePos |])
$(mkNuMatching [t| Message |])
$(mkNuMatching [t| ParseError |])
$(mkNuMatching [t| forall s u. (NuMatching s, NuMatching u) => State s u |])
$(mkNuMatching [t| forall s u a. (NuMatching s, NuMatching u, NuMatching a) =>
                Reply s u a |])
$(mkNuMatching [t| forall a. NuMatching a => Consumed a |])
$(mkNuMatching [t| forall a. NuMatching a => Identity a |])
$(mkNuMatching [t| forall f g a. NuMatching (f (g a)) => Compose f g a |])

instance Closable ParseError where
  toClosed = unsafeClose

instance Liftable ParseError where
  mbLift = unClosed . mbLift . fmap toClosed

instance Closable SourcePos where
  toClosed = unsafeClose

instance Liftable SourcePos where
  mbLift = unClosed . mbLift . fmap toClosed


----------------------------------------------------------------------
-- * The Parsing Monad and Parsing Utilities
----------------------------------------------------------------------

-- | An element of some representation type functor @f a@ along with a
-- 'TypeRepr' for @a@
data Typed f a = Typed (TypeRepr a) (f a)

-- | Try to cast an existential 'Typed' to a particular type
castTypedMaybe :: TypeRepr a -> Some (Typed f) -> Maybe (f a)
castTypedMaybe tp (Some (Typed tp' f))
  | Just Refl <- testEquality tp tp' = Just f
castTypedMaybe _ _ = Nothing

-- | A expression variable of some existentially quantified type
type SomeName = Some (Typed Name)

-- | A @newtype@-wrapped permission variable
newtype PermName a = PermName { unPermName :: PermVar a }

-- | A permission variable of some existentially quantified type
type SomePermName = Some (Typed PermName)

-- | A parsing environment, which includes variables and function names
data ParserEnv = ParserEnv {
  parserEnvExprVars :: [(String, SomeName)],
  parserEnvPermVars :: [(String, SomePermName)],
  parserEnvFuns :: [SomeHandle]
}

$(mkNuMatching [t| forall f a. NuMatching (f a) => Typed f a |])
$(mkNuMatching [t| forall a. PermName a |])
$(mkNuMatching [t| ParserEnv |])

instance NuMatchingAny1 PermName where
  nuMatchingAny1Proof = nuMatchingProof

instance NuMatchingAny1 f => NuMatchingAny1 (Typed f) where
  nuMatchingAny1Proof = nuMatchingProof

-- | Look up an expression variable by name in a 'ParserEnv'
lookupExprVar :: String -> ParserEnv -> Maybe SomeName
lookupExprVar str = lookup str . parserEnvExprVars

-- | Look up a permission variable by name in a 'ParserEnv'
lookupPermVar :: String -> ParserEnv -> Maybe SomePermName
lookupPermVar str = lookup str . parserEnvPermVars

-- | Look up a function handle by name in a 'ParserEnv'
lookupFun :: String -> ParserEnv -> Maybe SomeHandle
lookupFun str =
  find (\(SomeHandle h) -> handleName h == fromString str) . parserEnvFuns

instance BindState ParserEnv where
  bindState [nuP| ParserEnv evars pvars funs |] =
    ParserEnv
    (mapMaybe (\env_elem -> case env_elem of
                  [nuP| (str, Some (Typed tp mb_n)) |]
                    | Right n <- mbNameBoundP mb_n ->
                      Just (mbLift str, Some (Typed (mbLift tp) n))
                  _ -> Nothing)
     (mbList evars))
    (mapMaybe (\env_elem -> case env_elem of
                  [nuP| (str, Some (Typed tp (PermName mb_n))) |]
                    | Right n <- mbNameBoundP mb_n ->
                      Just (mbLift str, Some (Typed (mbLift tp) (PermName n)))
                  _ -> Nothing)
     (mbList pvars))
    (mbLift funs)
      
-- | The parsing monad is a 'Parsec' computation with a 'ParserEnv'
type PermParseM s = Parsec s ParserEnv

-- | Functors that support name-binding
--
-- FIXME: is this the right interface? Maybe should be related to 'MonadBind'?
{-
class (Functor f, NuMatchingAny1 f) => FunctorBind f where
  mbF :: NuMatching a => Mb ctx (f a) -> f (Mb ctx a)

instance FunctorBind Consumed where
  mbF [nuP| Consumed a |] = Consumed a
  mbF [nuP| Empty a |] = Empty a

instance (BindState s, BindState u) => FunctorBind (Reply s u) where
  mbF [nuP| Ok a s err |] = Ok a (bindState s) (mbLift err)
  mbF [nuP| Error err |] = Error (mbLift err)

instance FunctorBind Identity where
  mbF [nuP| Identity a |] = Identity a

instance (FunctorBind f, FunctorBind g) => FunctorBind (Compose f g) where
  mbF [nuP| Compose fga |] = Compose $ fmap mbF $ mbF fga
-}

instance (BindState s, BindState u) => BindState (State s u) where
  bindState [nuP| State s pos u |] =
    State (bindState s) (mbLift pos) (bindState u)

instance (BindState s, BindState u) => MonadBind (ParsecT s u Identity) where
  mbM mb_m = mkPT $ \s ->
    case fmap (flip runParsecT s) mb_m of
      [nuP| Identity (Consumed (Identity (Ok a s' err))) |] ->
        Identity (Consumed (Identity (Ok a (bindState s') (mbLift err))))
      [nuP| Identity (Consumed (Identity (Error err))) |] ->
        Identity (Consumed (Identity (Error (mbLift err))))
      [nuP| Identity (Consumed (Identity (Ok a s' err))) |] ->
        Identity (Empty (Identity (Ok a (bindState s') (mbLift err))))
      [nuP| Identity (Consumed (Identity (Error err))) |] ->
        Identity (Empty (Identity (Error (mbLift err))))

-- | Run a parsing computation in a context extended with an expression variable
withExprVar :: String -> TypeRepr tp -> ExprVar tp ->
               PermParseM s a -> PermParseM s a
withExprVar str tp x m =
  do env <- getState
     putState (env { parserEnvExprVars =
                       (str, Some (Typed tp x)) : parserEnvExprVars env})
     ret <- m
     putState env
     return ret

-- | Run a parsing computation in a context extended with a permission variable
withPermVar :: String -> TypeRepr tp -> PermVar tp ->
               PermParseM s a -> PermParseM s a
withPermVar str tp x m =
  do env <- getState
     putState (env { parserEnvPermVars =
                       (str, Some (Typed tp (PermName x)))
                       : parserEnvPermVars env})
     ret <- m
     putState env
     return ret

-- | Cast an existential 'Typed' to a particular type or raise an error
castTypedM :: Stream s Identity Char =>
              String -> TypeRepr a -> Some (Typed f) ->
              PermParseM s (f a)
castTypedM _ tp (Some (Typed tp' f))
  | Just Refl <- testEquality tp tp' = return f
castTypedM str _ _ = unexpected str

-- | Parse and skip at least one space
spaces1 :: Stream s Identity Char => PermParseM s ()
spaces1 = space >> spaces

-- | Apply a parsing computation to parse inside parentheses
parseInParens :: Stream s Identity Char =>
                 PermParseM s a -> PermParseM s a
parseInParens m =
  do spaces >> char '('
     ret <- m
     spaces >> char ')'
     return ret

-- | Apply a parsing computation to parse inside optional parentheses
parseInParensOpt :: Stream s Identity Char =>
                    PermParseM s a -> PermParseM s a
parseInParensOpt m = parseInParens m <|> m


----------------------------------------------------------------------
-- * Parsing Types
----------------------------------------------------------------------

-- | A 'NatRepr' for @1@
oneRepr :: NatRepr 1
oneRepr = knownRepr

-- | Parse a comma
comma :: Stream s Identity Char => PermParseM s ()
comma = char ',' >> return ()

-- | Parse an integer
integer :: Stream s Identity Char => PermParseM s Integer
integer = read <$> many1 digit

-- | Parse an integer to a 'NatRepr'
parseNatRepr :: Stream s Identity Char =>
                PermParseM s (Some (Product NatRepr (LeqProof 1)))
parseNatRepr =
  do i <- integer
     case someNat i of
       Just (Some w)
         | Left leq <- decideLeq oneRepr w -> return (Some (Pair w leq))
       Just _ -> unexpected "Zero bitvector width not allowed"
       Nothing -> error "parseNatRepr: unexpected negative bitvector width"

-- | Parse a Crucible type and build a @'KnownRepr' 'TypeRepr'@ instance for it
--
-- FIXME: we would not need to use a 'KnownReprObj' here if we changed
-- 'ValPerm_Exists' to take its type argument as a normal 'TypeRepr' instead of
-- as a 'WithKnownRepr' constraint
parseTypeKnown :: Stream s Identity Char =>
                  PermParseM s (Some (KnownReprObj TypeRepr))
parseTypeKnown =
  spaces >>
  (parseInParensOpt parseTypeKnown <|>
   (string "unit" >> return (Some $ mkKnownReprObj UnitRepr)) <|>
   (string "nat" >> return (Some $ mkKnownReprObj NatRepr)) <|>
   (do string "bv" >> spaces1
       w <- parseNatRepr
       case w of
         Some (Pair w LeqProof) ->
           withKnownNat w $ return (Some $ mkKnownReprObj $ BVRepr w)) <|>
   (do string "llvmptr" >> spaces1
       w <- parseNatRepr
       case w of
         Some (Pair w LeqProof) ->
           withKnownNat w $
           return (Some $ mkKnownReprObj $ LLVMPointerRepr w)) <|>
   (do string "llvmframe" >> spaces1
       w <- parseNatRepr
       case w of
         Some (Pair w LeqProof) ->
           withKnownNat w $
           return (Some $ mkKnownReprObj $ LLVMFrameRepr w)) <|>
   (do string "lifetime"
       return (Some $ mkKnownReprObj LifetimeRepr)) <|>
   (do string "permlist"
       return (Some $ mkKnownReprObj PermListRepr)) <|>
   (do string "struct"
       some_fld_tps <- parseInParens parseStructFieldTypesKnown
       case some_fld_tps of
         Some fld_tps@KnownReprObj ->
           return $ Some $ mkKnownReprObj $
           StructRepr $ unKnownReprObj fld_tps) <?>
   "Cannot parse type")

-- | Parse a comma-separated list of struct field types
parseStructFieldTypesKnown :: Stream s Identity Char =>
                              PermParseM s (Some (KnownReprObj
                                                  (Assignment TypeRepr)))
parseStructFieldTypesKnown =
  helper <$> reverse <$> sepBy parseTypeKnown (spaces >> char ',')
  where
    helper :: [Some (KnownReprObj TypeRepr)] ->
              Some (KnownReprObj (Assignment TypeRepr))
    helper [] = Some $ mkKnownReprObj Ctx.empty
    helper (Some tp@KnownReprObj : tps) =
      case helper tps of
        Some repr@KnownReprObj ->
          Some $ mkKnownReprObj $
          extend (unKnownReprObj repr) (unKnownReprObj tp)


-- | Parse a Crucible type as a 'TypeRepr'
parseType :: Stream s Identity Char => PermParseM s (Some TypeRepr)
parseType = mapSome unKnownReprObj <$> parseTypeKnown


----------------------------------------------------------------------
-- * Parsing Expressions
----------------------------------------------------------------------

-- | Parse a valid identifier as a 'String'
parseIdent :: Stream s Identity Char => PermParseM s String
parseIdent =
  do spaces
     c <- letter
     cs <- many (alphaNum <|> char '_' <|> char '\'')
     return (c:cs)

-- | Parse a valid identifier string as an expression variable
parseExprVarAndStr :: Stream s Identity Char => PermParseM s (String, SomeName)
parseExprVarAndStr =
  do str <- parseIdent
     env <- getState
     case lookupExprVar str env of
       Just x -> return (str, x)
       Nothing -> unexpected ("Unknown variable: " ++ str)

-- | Parse a valid identifier string as an expression variable
parseExprVar :: Stream s Identity Char => PermParseM s SomeName
parseExprVar = snd <$> parseExprVarAndStr

-- | Parse an identifier as an expression variable of a specific type
parseExprVarOfType :: Stream s Identity Char => TypeRepr a ->
                      PermParseM s (ExprVar a)
parseExprVarOfType tp =
  do (str, some_nm) <- parseExprVarAndStr
     castTypedM ("Variable of incorrect type: " ++ str) tp some_nm

-- | Parse an identifier as a permission variable of a specific type
parsePermVarOfType :: Stream s Identity Char => TypeRepr a ->
                      PermParseM s (PermVar a)
parsePermVarOfType tp =
  do str <- parseIdent
     env <- getState
     case lookupPermVar str env of
       Just some_perm_name ->
         unPermName <$>
         castTypedM ("Permission variable of incorrect type: "
                     ++ str) tp some_perm_name
       Nothing ->
         unexpected ("Unkown variable: " ++ str)

-- | Parse a single bitvector factor of the form @x*n@, @n*x@, @x@, or @n@,
-- where @x@ is a variable and @n@ is an integer. Note that this returns a
-- 'PermExpr' and not a 'BVFactor' because the latter does not include the
-- constant integer case @n@.
parseBVFactor :: (1 <= w, KnownNat w, Stream s Identity Char) =>
                 PermParseM s (PermExpr (BVType w))
parseBVFactor =
  spaces >>
  (try (do i <- integer
           spaces >> char '*' >> spaces
           x <- parseExprVarOfType knownRepr
           return $ PExpr_BV [BVFactor i x] 0)
   <|>
   try (do x <- parseExprVarOfType knownRepr
           spaces >> char '*' >> spaces
           i <- integer
           return $ PExpr_BV [BVFactor i x] 0)
   <|>
   try (do x <- parseExprVarOfType knownRepr
           return $ PExpr_BV [BVFactor 1 x] 0)
   <|>
   do i <- integer
      return $ PExpr_BV [] i)

-- | Parse a bitvector expression of the form
--
-- > f1 + ... + fn
--
-- where each @fi@ is a factor parsed by 'parseBVFactor'
parseBVExpr :: (1 <= w, KnownNat w, Stream s Identity Char) =>
               PermParseM s (PermExpr (BVType w))
parseBVExpr = foldr1 bvAdd <$> many1 parseBVFactor

-- | Parse an expression of a known type
parseExpr :: Stream s Identity Char => TypeRepr a ->
             PermParseM s (PermExpr a)
parseExpr UnitRepr =
  try (string "unit" >> return PExpr_Unit) <|>
  (PExpr_Var <$> parseExprVarOfType UnitRepr)
parseExpr NatRepr =
  (PExpr_Nat <$> integer) <|> (PExpr_Var <$> parseExprVarOfType NatRepr)
parseExpr (BVRepr w) = withKnownNat w parseBVExpr
parseExpr tp@(StructRepr fld_tps) =
  spaces >>
  ((string "struct" >>
    parseInParens (PExpr_Struct <$> parseExprs (mkCruCtx fld_tps))) <|>
   (PExpr_Var <$> parseExprVarOfType tp))
parseExpr LifetimeRepr =
  try (string "always" >> return PExpr_Always) <|>
  (PExpr_Var <$> parseExprVarOfType LifetimeRepr)
parseExpr tp@(LLVMPointerRepr w) =
  withKnownNat w $
  spaces >>
  (try (string "llvmword" >>
        (PExpr_LLVMWord <$> parseInParens parseBVExpr)) <|>
   (do x <- parseExprVarOfType tp
       try (do spaces >> char '+'
               off <- parseBVExpr
               return $ PExpr_LLVMOffset x off) <|>
         return (PExpr_Var x)))
parseExpr tp@(FunctionHandleRepr _ _) =
  do str <- parseIdent
     env <- getState
     case lookupExprVar str env of
       Just some_x ->
         PExpr_Var <$>
         castTypedM ("Variable of incorrect type: " ++ str) tp some_x
       Nothing ->
         case lookupFun str env of
           Just (SomeHandle hn)
             | Just Refl <- testEquality tp (handleType hn) ->
               return $ PExpr_Fun hn
           Just _ -> unexpected ("Function of incorrect type: " ++ str)
           Nothing ->
             unexpected ("Could not find variable or function: " ++ str)
parseExpr PermListRepr =
  -- FIXME: parse non-empty perm lists
  (string "[]" >> return PExpr_PermListNil) <|>
  (PExpr_Var <$> parseExprVarOfType PermListRepr)
parseExpr tp = PExpr_Var <$> parseExprVarOfType tp


-- | Parse a comma-separated list of expressions to a 'PermExprs'
parseExprs :: Stream s Identity Char => CruCtx ctx ->
              PermParseM s (PermExprs ctx)
parseExprs CruCtxNil = return PExprs_Nil
parseExprs (CruCtxCons CruCtxNil tp) =
  -- Special case for a 1-element context: do not parse a comma
  PExprs_Cons PExprs_Nil <$> parseExpr tp
parseExprs (CruCtxCons ctx tp) =
  do es <- parseExprs ctx
     spaces >> char ','
     e <- parseExpr tp
     return $ PExprs_Cons es e


----------------------------------------------------------------------
-- * Parsing Permissions
----------------------------------------------------------------------

-- | Parse a value permission of a known type
parseValPerm :: (Stream s Identity Char, BindState s) => TypeRepr a ->
                PermParseM s (ValuePerm a)
parseValPerm tp =
  do spaces
     p1 <-
       (parseInParens (parseValPerm tp)) <|>
       try (string "true" >> return ValPerm_True) <|>
       try (string "eq" >> parseInParens (ValPerm_Eq <$> parseExpr tp)) <|>
       try (do string "exists" >> spaces1
               var <- parseIdent
               spaces >> char ':'
               some_known_tp' <- parseTypeKnown
               spaces >> char '.'
               case some_known_tp' of
                 Some ktp'@KnownReprObj ->
                   fmap ValPerm_Exists $ mbM $ nu $ \z ->
                   withExprVar var (unKnownReprObj ktp') z $
                   parseValPerm tp) <|>
       try (do string "mu" >> spaces
               var <- parseIdent
               spaces >> char '.'
               fmap ValPerm_Mu $ mbM $ nu $ \p_x ->
                 withPermVar var tp p_x $ parseValPerm tp) <|>
       try (ValPerm_Var <$> parsePermVarOfType tp) <|>
       (ValPerm_Conj <$> parseAtomicPerms tp)
     spaces
     try (string "\\/" >> (ValPerm_Or p1 <$> parseValPerm tp)) <|>
       return p1

-- | Parse a @*@-separated list of atomic permissions
parseAtomicPerms :: (Stream s Identity Char, BindState s) => TypeRepr a ->
                    PermParseM s [AtomicPerm a]
parseAtomicPerms tp =
  do p1 <- parseAtomicPerm tp
     spaces
     try (string "*" >> (p1:) <$> parseAtomicPerms tp) <|> return [p1]

-- | Parse an atomic permission of a specific type
parseAtomicPerm :: (Stream s Identity Char, BindState s) => TypeRepr a ->
                   PermParseM s (AtomicPerm a)
parseAtomicPerm (LLVMPointerRepr w)
  | Left LeqProof <- decideLeq oneRepr w =
    withKnownNat w
    (try (Perm_LLVMField <$> parseLLVMFieldPerm False) <|>
     try (Perm_LLVMArray <$> parseLLVMArrayPerm) <|>
     try (string "free" >> (Perm_LLVMFree <$> parseInParens parseBVExpr)) <|>
     Perm_BVProp <$> parseBVProp)

-- | Parse a field permission @[l]ptr((rw,off) |-> p)@. If the 'Bool' flag is
-- 'True', the field permission is being parsed as part of an array permission,
-- so that @ptr@ and outer parentheses should be omitted.
parseLLVMFieldPerm :: (Stream s Identity Char, BindState s,
                       KnownNat w, 1 <= w) =>
                      Bool -> PermParseM s (LLVMFieldPerm w)
parseLLVMFieldPerm in_array =
  do l <- try (do string "["
                  l <- parseExpr knownRepr
                  string "]"
                  return l) <|> return PExpr_Always
     if in_array then spaces >> string "ptr" >> string "(" >> return ()
       else return ()
     spaces >> string "("
     llvmFieldRW <- (string "R" >> return Read) <|> (string "W" >> return Write)
     spaces >> comma >> spaces
     llvmFieldOffset <- parseBVExpr
     spaces >> string ")" >> spaces >> string "|->" >> spaces
     llvmFieldContents <- parseValPerm knownRepr
     if in_array then spaces >> string ")" >> return () else return ()
     return (LLVMFieldPerm {..})

-- | Parse an array permission @array(off,<len,*stride,[fp1,...])@
parseLLVMArrayPerm :: (Stream s Identity Char, BindState s,
                       KnownNat w, 1 <= w) =>
                      PermParseM s (LLVMArrayPerm w)
parseLLVMArrayPerm =
  do string "array("
     llvmArrayOffset <- parseBVExpr
     spaces >> comma >> spaces >> char '<'
     llvmArrayLen <- parseBVExpr
     spaces >> comma >> spaces >> char '*'
     llvmArrayStride <- integer
     spaces >> comma >> spaces >> char '['
     llvmArrayFields <- sepBy1 (parseLLVMFieldPerm True) (spaces >> comma)
     let llvmArrayBorrows = []
     return LLVMArrayPerm {..}

-- | Parse a 'BVProp'
parseBVProp :: (Stream s Identity Char, BindState s, KnownNat w, 1 <= w) =>
               PermParseM s (BVProp w)
parseBVProp =
  try (parseBVExpr >>= \e1 ->
        try (do spaces >> string "==" >> spaces
                e2 <- parseBVExpr
                return $ BVProp_Eq e1 e2) <|>
        try (do spaces >> string "/=" >> spaces
                e2 <- parseBVExpr
                return $ BVProp_Neq e1 e2) <|>
        try (do spaces1 >> string "in" >> spaces1
                rng <- parseBVRange
                return $ BVProp_InRange e1 rng) <|>
        try (do spaces1 >> string "not" >> spaces1 >> string "in" >> spaces1
                rng <- parseBVRange
                return $ BVProp_NotInRange e1 rng)) <|>
  do rng1 <- parseBVRange
     spaces
     mk_prop <-
       try (string "subset" >> return BVProp_RangeSubset) <|>
       (string "disjoint" >> return BVProp_RangesDisjoint)
     rng2 <- parseBVRange
     return $ mk_prop rng1 rng2

-- | Parse a 'BVRange' written as @{ off, len }@
parseBVRange :: (Stream s Identity Char, BindState s, KnownNat w, 1 <= w) =>
                PermParseM s (BVRange w)
parseBVRange =
  do spaces >> char '{'
     bvRangeOffset <- parseBVExpr
     spaces >> comma
     bvRangeLength <- parseBVExpr
     spaces >> char '}'
     return BVRange {..}

-- FIXME HERE NOW:
-- parse a DistPerms list x1:p1, x2:p2, ... where we know the types of the xi
-- parse inside a variable context (x1:tp1, ...).p
-- parse a fun perm (ctx).dist_perms -> dist_perms

{-
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
       (ValPerm_Var <$> parseExprVarOfType env (valuePermRepr tp))
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


parseExprVarPerms :: Stream s Identity Char => ParserEnv ctx ->
                 MapF (PermVar ctx) (ValuePerm ctx) ->
                 PermParseM s (MapF (PermVar ctx) (ValuePerm ctx))
parseExprVarPerms env perms =
  do spaces
     some_x <- parseExprVar env
     spaces >> char ':'
     case some_x of
       Some (Typed tp x) ->
         do if MapF.member x perms then
              unexpected ("Variable " ++ lookupVarName env x ++ " occurs twice")
              else return ()
            p <- parseValPerm env tp
            let perms' = MapF.insert x p perms
            spaces
            (char ',' >> parseExprVarPerms env perms') <|> return perms'

parsePermSet :: Stream s Identity Char => ParserEnv ctx ->
                PermParseM s (PermSet ctx)
parsePermSet env =
  do perms <- parseExprVarPerms env MapF.empty
     return $ PermSet (ctxOfEnv env) $
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

parsePermsInCtx1 :: String -> String ->
                    Either ParseError (Some (Product CtxRepr PermSet))
parsePermsInCtx1 ctx_str perms_str =
  case parse (parseCtx empty) "input" ctx_str of
    Left err -> Left err
    Right (Some env) ->
      case parse (parsePermSet env) "input" perms_str of
        Left err -> Left err
        Right permSet -> Right $ Some (Pair (ctxOfEnv env) permSet)

parsePermsInCtx2 :: String -> String -> String ->
                    Either ParseError (Some
                                       (Product CtxRepr
                                        (Product PermSet PermSet)))
parsePermsInCtx2 ctx_str perms1_str perms2_str =
  do some_env <- parse (parseCtx empty) "input" ctx_str
     case some_env of
       Some env ->
         do permSet1 <- parse (parsePermSet env) "input" perms1_str
            permSet2 <- parse (parsePermSet env) "input" perms2_str
            return $ Some $ Pair (ctxOfEnv env) (Pair permSet1 permSet2)
-}
