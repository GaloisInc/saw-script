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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}

module SAWScript.Heapster.PermParser where

import Data.List
import Data.String
import Data.Maybe
import Data.Functor.Product
import Data.Functor.Constant
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

-- | Run a parsing computation in a context extended with 0 or more expression
-- variables
withExprVars :: MapRList (Constant String) ctx -> CruCtx ctx ->
                MapRList Name ctx ->
                PermParseM s a -> PermParseM s a
withExprVars MNil CruCtxNil MNil m = m
withExprVars (xs :>: Constant x) (CruCtxCons ctx tp) (ns :>: n) m =
  withExprVars xs ctx ns $ withExprVar x tp n m

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


----------------------------------------------------------------------
-- * Parsing Permission Sets and Function Permissions
----------------------------------------------------------------------

-- | A sequence of variable names and their types
data ParsedCtx ctx =
  ParsedCtx (MapRList (Constant String) ctx) (CruCtx ctx)

-- | Remove the last variable in a 'ParsedCtx'
parsedCtxUncons :: ParsedCtx (ctx :> tp) -> ParsedCtx ctx
parsedCtxUncons (ParsedCtx (xs :>: _) (CruCtxCons ctx _)) = ParsedCtx xs ctx

-- | Add a variable name and type to a 'ParsedCtx'
consParsedCtx :: String -> TypeRepr tp -> ParsedCtx ctx ->
                 ParsedCtx (ctx :> tp)
consParsedCtx x tp (ParsedCtx xs ctx) =
  ParsedCtx (xs :>: Constant x) (CruCtxCons ctx tp)

-- | A 'ParsedCtx' with a single element
singletonParsedCtx :: String -> TypeRepr tp -> ParsedCtx (RNil :> tp)
singletonParsedCtx x tp =
  ParsedCtx (MNil :>: Constant x) (CruCtxCons CruCtxNil tp)

-- | Add a variable name and type to the beginning of an unknown 'ParsedCtx'
preconsSomeParsedCtx :: String -> Some TypeRepr -> Some ParsedCtx ->
                        Some ParsedCtx
preconsSomeParsedCtx x (Some (tp :: TypeRepr tp)) (Some (ParsedCtx ns tps)) =
  Some $ ParsedCtx
  (appendMapRList (MNil :>: (Constant x :: Constant String tp)) ns)
  (appendCruCtx (singletonCruCtx tp) tps)

mkArgsParsedCtx :: CruCtx ctx -> ParsedCtx ctx
mkArgsParsedCtx ctx = ParsedCtx (helper ctx) ctx where
  helper :: CruCtx ctx' -> MapRList (Constant String) ctx'
  helper CruCtxNil = MNil
  helper (CruCtxCons ctx tp) =
    helper ctx :>: Constant ("arg" ++ show (cruCtxLen ctx))

-- | Parse a typing context @x1:tp1, x2:tp2, ...@
parseCtx :: (Stream s Identity Char, BindState s) =>
            PermParseM s (Some ParsedCtx)
parseCtx =
  do x <- parseIdent
     spaces >> char ':'
     some_tp <- parseType
     try (do spaces >> comma
             some_ctx' <- parseCtx
             return $ preconsSomeParsedCtx x some_tp some_ctx')
       <|>
       (case some_tp of
           Some tp -> return (Some $ singletonParsedCtx x tp))

-- | Parse a sequence @x1:p1, x2:p2, ...@ of variables and their permissions
--
-- FIXME: not used
parseDistPerms :: (Stream s Identity Char, BindState s) =>
                  PermParseM s (Some DistPerms)
parseDistPerms =
  parseExprVar >>= \some_x ->
  case some_x of
    Some (Typed tp x) ->
      do p <- parseValPerm tp
         try (do spaces >> comma
                 some_dist_perms' <- parseDistPerms
                 case some_dist_perms' of
                   Some perms ->
                     return $ Some (DistPermsCons perms x p))
           <|>
           return (Some $ distPerms1 x p)

-- | Helper type for 'parseValuePerms'
data VarPermSpec a = VarPermSpec (Name a) (Maybe (ValuePerm a))

type VarPermSpecs = MapRList VarPermSpec

-- | Build a 'VarPermSpecs' from a list of names
mkVarPermSpecs :: MapRList Name ctx -> VarPermSpecs ctx
mkVarPermSpecs = mapMapRList (\n -> VarPermSpec n Nothing)

-- | Find a 'VarPermSpec' for a particular variable
findVarPermSpec :: Name (a :: CrucibleType) ->
                   VarPermSpecs ctx -> Maybe (Member ctx a)
findVarPermSpec _ MNil = Nothing
findVarPermSpec n (_ :>: VarPermSpec n' _)
  | Just Refl <- testEquality n n'
  = Just Member_Base
findVarPermSpec n (specs :>: _) = Member_Step <$> findVarPermSpec n specs

-- | Try to set the permission for a variable in a 'VarPermSpecs' list, raising
-- a parse error if the variable already has a permission or is one of the
-- expected variables
setVarSpecsPermM :: Stream s Identity Char =>
                    String -> Name tp -> ValuePerm tp -> VarPermSpecs ctx ->
                    PermParseM s (VarPermSpecs ctx)
setVarSpecsPermM _ n p var_specs
  | Just memb <- findVarPermSpec n var_specs
  , VarPermSpec _ Nothing <- mapRListLookup memb var_specs =
    return $ mapRListModify memb (const $ VarPermSpec n $ Just p) var_specs
setVarSpecsPermM var n _ var_specs
  | Just memb <- findVarPermSpec n var_specs =
    unexpected ("Variable " ++ var ++ " occurs more than once!")
setVarSpecsPermM var n _ var_specs =
    unexpected ("Unknown variable: " ++ var)

-- | Convert a 'VarPermSpecs' sequence to a sequence of permissions, using the
-- @true@ permission for any variables without permissions
varSpecsToPerms :: VarPermSpecs ctx -> ValuePerms ctx
varSpecsToPerms MNil = ValPerms_Nil
varSpecsToPerms (var_specs :>: VarPermSpec _ (Just p)) =
  ValPerms_Cons (varSpecsToPerms var_specs) p
varSpecsToPerms (var_specs :>: VarPermSpec _ Nothing) =
  ValPerms_Cons (varSpecsToPerms var_specs) ValPerm_True

-- | Parse a sequence @x1:p1, x2:p2, ...@ of variables and their permissions,
-- where each variable occurs at most once. The input list says which variables
-- can occur and which have already been seen. Return a sequence of the
-- permissions in the same order as the input list of variables.
parseSortedValuePerms :: (Stream s Identity Char, BindState s) =>
                         VarPermSpecs ctx ->
                         PermParseM s (ValuePerms ctx)
parseSortedValuePerms var_specs =
  try (spaces >> string "empty" >> return (varSpecsToPerms var_specs)) <|>
  (parseExprVarAndStr >>= \(var, some_n) ->
   case some_n of
     Some (Typed tp n) ->
       do spaces >> char ':'
          p <- parseValPerm tp
          var_specs' <- setVarSpecsPermM var n p var_specs
          try (spaces >> comma >> parseSortedValuePerms var_specs') <|>
            return (varSpecsToPerms var_specs'))

-- | Run a parsing computation inside a name-binding for expressions variables
-- given by a 'ParsedCtx'. Returning the results inside a name-binding.
inParsedCtxM :: (BindState s, NuMatching a) =>
                ParsedCtx ctx -> (MapRList Name ctx -> PermParseM s a) ->
                PermParseM s (Mb ctx a)
inParsedCtxM (ParsedCtx ids tps) f =
  mbM $ nuMulti (cruCtxProxies tps) $ \ns -> withExprVars ids tps ns (f ns)

-- | Parse a sequence @x1:p1, x2:p2, ...@ of variables and their permissions,
-- and sort the result into a 'ValuePerms' in a multi-binding that is in the
-- same order as the 'ParsedCtx' supplied on input
parseSortedMbValuePerms :: (Stream s Identity Char, BindState s) =>
                           ParsedCtx ctx -> PermParseM s (MbValuePerms ctx)
parseSortedMbValuePerms ctx =
  inParsedCtxM ctx $ \ns ->
  parseSortedValuePerms (mkVarPermSpecs ns)

-- | Parse a function permission of the form
--
-- > (x1:tp1, ...). arg1:p1, ... -o arg1:p1', ..., argn:pn', ret:p_ret
--
-- for some arbitrary context @x1:tp1, ...@ of ghost variables
parseFunPerm :: (Stream s Identity Char, BindState s) =>
                CruCtx args -> TypeRepr ret ->
                PermParseM s (SomeFunPerm args ret)
parseFunPerm args ret =
  parseInParens parseCtx >>= \some_ghosts_ctx ->
  case some_ghosts_ctx of
    Some ghosts_ctx@(ParsedCtx _ ghosts) ->
      do spaces >> char '.'
         let args_ctx = mkArgsParsedCtx args
         let ghosts_l_ctx = consParsedCtx "l" LifetimeRepr ghosts_ctx
         perms_in <-
           inParsedCtxM ghosts_l_ctx $ const $
           parseSortedMbValuePerms args_ctx
         spaces >> string "-o"
         perms_out <-
           inParsedCtxM ghosts_l_ctx $ const $
           parseSortedMbValuePerms (consParsedCtx "ret" ret args_ctx)
         return $ SomeFunPerm $ FunPerm ghosts args ret perms_in perms_out
