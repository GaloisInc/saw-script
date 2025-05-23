{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}

{- |
Module      : SAWCore.FiniteValue
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}
module SAWCore.FiniteValue where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
import Data.Traversable
#endif

import GHC.Generics (Generic)
import Control.Monad (replicateM, mzero)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Maybe
import qualified Control.Monad.State as S
import Data.List (intersperse)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as Text
import Numeric.Natural (Natural)

import Data.Foldable.WithIndex (ifoldrM)

import Prettyprinter hiding (Doc)

import Data.Aeson ( FromJSON(..), ToJSON(..), FromJSONKey(..), ToJSONKey(..) )
import qualified Data.Aeson as JSON

import SAWSupport.Pretty (SawDoc, PPOpts, defaultPPOpts, ppNat)

import qualified SAWCore.Recognizer as R
import SAWCore.SharedTerm
import SAWCore.TypedAST
import SAWCore.Term.Pretty

-- | Finite types that can be encoded as bits for a SAT/SMT solver.
data FiniteType
  = FTBit
  | FTVec Natural FiniteType
  | FTTuple [FiniteType]
  | FTRec (Map FieldName FiniteType)
  deriving (Eq, Show)

-- | Values inhabiting those finite types.
data FiniteValue
  = FVBit Bool
  | FVWord Natural Integer -- ^ a more efficient special case for 'FVVec FTBit _'.
  | FVVec FiniteType [FiniteValue]
  | FVTuple [FiniteValue]
  | FVRec (Map FieldName FiniteValue)
  deriving Eq

-- | First-order types that can be encoded in an SMT solver.
-- NB: The JSON encoding of this type, used for saw-script solver result caching,
-- assumes constructor names and argument orders will not change (though the
-- order and number of constructors may change) - see 'firstOrderJSONOptions'
data FirstOrderType
  = FOTBit
  | FOTInt
  | FOTIntMod Natural
  | FOTVec Natural FirstOrderType
  | FOTArray FirstOrderType FirstOrderType
  | FOTTuple [FirstOrderType]
  | FOTRec (Map FieldName FirstOrderType)
  deriving (Eq, Ord, Show, Generic)

-- | Values inhabiting those first-order types.
-- NB: The JSON encoding of this type, used for saw-script solver result caching,
-- assumes constructor names and argument orders will not change (though the
-- order and number of constructors may change) - see 'firstOrderJSONOptions'
--
-- The type argument of FOVArray is the key type; the value type is
-- derivable from the default value, which is the second argument. The third
-- argument is an assignment for all the entries that have non-default values.
--
-- FOVOpaqueArray is for arrays we get back from the solver only as a
-- function call that one can use for lookups. We can't do anything
-- with that (see Note [FOVArray] below) so we just treat it as an
-- opaque blob. The arguments are the key and value types, since we
-- do at least have that info.
data FirstOrderValue
  = FOVBit Bool
  | FOVInt Integer
  | FOVIntMod Natural Integer
  | FOVWord Natural Integer -- ^ a more efficient special case for 'FOVVec FOTBit _'.
  | FOVVec FirstOrderType [FirstOrderValue]
  | FOVArray FirstOrderType FirstOrderValue (Map FirstOrderValue FirstOrderValue)
  | FOVOpaqueArray FirstOrderType FirstOrderType
  | FOVTuple [FirstOrderValue]
  | FOVRec (Map FieldName FirstOrderValue)
  deriving (Eq, Ord, Generic)

--
-- Note [FOVArray]
-- ~~~~~~~~~~~~~~~
--
-- We only handle arrays that are:
--    - unidimensional
--    - made up of explicit concrete values
--
-- We could handle multidimensional arrays easily enough (the key type
-- and assignment keys just need to become lists) but for the moment
-- there's no use case.
--
-- The What4 interface can sometimes return an array that isn't made
-- up of explicit concrete values but is instead represented as a
-- function you can call to get values out for given keys. It is not
-- clear how we'd use this, since the primary thing we do with array
-- values that come back from the solver is print them as part of
-- models and without a way to know what keys are present a function
-- that just extracts values is fairly useless. If one of these pops
-- up, it comes back as FOVOpaqueArray and we treat it as an opaque
-- blob. Unfortuately this does happen (maybe we can improve What4 so
-- it happens less or maybe not at all, but that's not happening right
-- away) so we need to be able to handle it rather than erroring out
-- or crashing.
--
-- Note that trying to retain the function at this level is
-- problematic for a number of reasons:
--
--    1. It's not actually a first-order value, and calling it one is
--       borrowing trouble.
--
--    2. We need ToJSON and FromJSON instances for solver caching, and
--       there's no way to do that. Now, trying to stick one of these
--       objects in the solver cache is just not going to work no
--       matter how we handle it; but things are not structured so
--       that we can e.g. decline to cache values that contain
--       function-based arrays so that it's safe to stub out the
--       ToJSON and FromJSON instances with an error invocation. That
--       could doubtless be arranged, but it'll take work, possibly a
--       lot of work. As things stand, we _can_ stuff FOVOpaqueArray
--       into the solver cache, and it won't do anything useful when
--       we unstuff it later, but it won't crash.
--
--    3. FirstOrderValue needs Eq and Ord instances, at least but not
--       necessarily only for use by maps. At least one of those maps
--       (the one used in FOVArray) is restricted to not have array
--       values as keys; however, that's not an _explicit_ restriction
--       (e.g. in typechecking), it's a consequence of the things
--       What4 allows as array keys. To be halfway safe we'd need to
--       make it an explicit restriction, and in the current state of
--       SAW maintenance it's not really clear enough where we'd need
--       to enforce that to keep it safe. Also, there may be other
--       such maps about where arrays _can_ be keys, or for that
--       matter other comparisons. In principle you could have the
--       compiler find you all the uses by disabling the Eq and Ord
--       instances. But that doesn't work because the ToJSON and
--       FromJSON classes need them. The compiler then just fails on
--       those before telling you anything else.
--
-- Besides all the above, restrictions in What4 mean that array values
-- coming back from the solver via that interface are indexed only by
-- integers or bitvectors. At this layer, though, we can support any
-- FirstOrderValue.
--

toFirstOrderType :: FiniteType -> FirstOrderType
toFirstOrderType ft =
  case ft of
    FTBit      -> FOTBit
    FTVec n t  -> FOTVec n (toFirstOrderType t)
    FTTuple ts -> FOTTuple (map toFirstOrderType ts)
    FTRec tm   -> FOTRec (fmap toFirstOrderType tm)

toFirstOrderValue :: FiniteValue -> FirstOrderValue
toFirstOrderValue fv =
  case fv of
    FVBit b    -> FOVBit b
    FVWord w i -> FOVWord w i
    FVVec t vs -> FOVVec (toFirstOrderType t) (map toFirstOrderValue vs)
    FVTuple vs -> FOVTuple (map toFirstOrderValue vs)
    FVRec vm   -> FOVRec (fmap toFirstOrderValue vm)


toFiniteType :: FirstOrderType -> Maybe FiniteType
toFiniteType FOTBit        = pure FTBit
toFiniteType (FOTVec n t)  = FTVec n <$> toFiniteType t
toFiniteType (FOTTuple ts) = FTTuple <$> traverse toFiniteType ts
toFiniteType (FOTRec fs)   = FTRec   <$> traverse toFiniteType fs
toFiniteType FOTInt{}      = Nothing
toFiniteType FOTIntMod{}   = Nothing
toFiniteType FOTArray{}    = Nothing

instance Show FiniteValue where
  showsPrec p fv = showsPrec p (toFirstOrderValue fv)

instance Show FirstOrderValue where
  showsPrec _ fv =
    case fv of
      FOVBit b    -> shows b
      FOVInt i    -> shows i
      FOVIntMod _ i -> shows i
      FOVWord _ x -> shows x
      FOVVec _ vs -> showString "[" . commaSep (map shows vs) . showString "]"
      FOVArray _kty d vs ->
        let vs' = map showEntry $ Map.toAscList vs
            d' = showEntry ("<default>", d)
        in
        showString "[" . commaSep (vs' ++ [d']) . showString "]"
      FOVOpaqueArray _kty _vty ->
        showString "[ opaque array, sorry ]"
      FOVTuple vs -> showString "(" . commaSep (map shows vs) . showString ")"
      FOVRec vm   -> showString "{" . commaSep (map showField (Map.assocs vm)) . showString "}"
    where
      commaSep ss = foldr (.) id (intersperse (showString ",") ss)
      showEntry (k, v) = shows k . showString " := " . shows v
      showField (field, v) = showString (Text.unpack field) . showString " = " . shows v

ppFiniteValue :: PPOpts -> FiniteValue -> SawDoc
ppFiniteValue opts fv = ppFirstOrderValue opts (toFirstOrderValue fv)

ppFirstOrderValue :: PPOpts -> FirstOrderValue -> SawDoc
ppFirstOrderValue opts = loop
 where
 loop fv = case fv of
   FOVBit b
     | b         -> pretty "True"
     | otherwise -> pretty "False"
   FOVInt i      -> pretty i
   FOVIntMod _ i -> pretty i
   FOVWord _w i  -> ppNat opts i
   FOVVec _ xs   -> brackets (sep (punctuate comma (map loop xs)))
   FOVArray _kty d vs ->
      let ppEntry' k' v = k' <+> pretty ":=" <+> loop v
          ppEntry (k, v) = ppEntry' (loop k) v
          d' = ppEntry' (pretty "<default>") d
          vs' = map ppEntry $ Map.toAscList vs
      in
      brackets (nest 4 (sep (punctuate comma (vs' ++ [d']))))
   FOVOpaqueArray _kty _vty ->
      pretty "[ opaque array, sorry ]"
   FOVTuple xs   -> parens (nest 4 (sep (punctuate comma (map loop xs))))
   FOVRec xs     -> braces (sep (punctuate comma (map ppField (Map.toList xs))))
      where ppField (f,x) = pretty f <+> pretty '=' <+> loop x

-- | The options for JSON-serializing 'FirstOrderType's and 'FirstOrderValue's:
-- remove the @FOT@/@FOV@ prefixes and encode the different constructors as
-- two-element arrays. Thus, this encoding assumes constructor names and
-- argument orders will not change (though the order and number of constructors
-- may change).
firstOrderJSONOptions :: JSON.Options
firstOrderJSONOptions =
  JSON.defaultOptions { JSON.sumEncoding = JSON.TwoElemArray
                      , JSON.constructorTagModifier = dropFO }
  where dropFO ('F':'O':tv:cs) | tv `elem` ['T', 'V'] = cs
        dropFO cs = cs

instance FromJSON FirstOrderType where
  parseJSON = JSON.genericParseJSON firstOrderJSONOptions
instance FromJSON FirstOrderValue where
  parseJSON = JSON.genericParseJSON firstOrderJSONOptions
instance FromJSONKey FirstOrderValue

instance ToJSON FirstOrderType where
  toJSON = JSON.genericToJSON firstOrderJSONOptions
  toEncoding = JSON.genericToEncoding firstOrderJSONOptions
instance ToJSON FirstOrderValue where
  toJSON = JSON.genericToJSON firstOrderJSONOptions
  toEncoding = JSON.genericToEncoding firstOrderJSONOptions
instance ToJSONKey FirstOrderValue


-- | Smart constructor
fvVec :: FiniteType -> [FiniteValue] -> FiniteValue
fvVec t vs =
  case (t, traverse toBit vs) of
    (FTBit, Just bs) -> FVWord (fromIntegral (length bs)) (fromBits bs)
    _ -> FVVec t vs
  where
    toBit :: FiniteValue -> Maybe Bool
    toBit (FVBit b) = Just b
    toBit _ = Nothing

    fromBits :: [Bool] -> Integer
    fromBits = foldl (\n b -> 2*n + if b then 1 else 0) 0

-- | Smart constructor
fovVec :: FirstOrderType -> [FirstOrderValue] -> FirstOrderValue
fovVec t vs =
  case (t, traverse toBit vs) of
    (FOTBit, Just bs) -> FOVWord (fromIntegral (length bs)) (fromBits bs)
    _ -> FOVVec t vs
  where
    toBit :: FirstOrderValue -> Maybe Bool
    toBit (FOVBit b) = Just b
    toBit _ = Nothing

    fromBits :: [Bool] -> Integer
    fromBits = foldl (\n b -> 2*n + if b then 1 else 0) 0

finiteTypeOf :: FiniteValue -> FiniteType
finiteTypeOf fv =
  case fv of
    FVBit _    -> FTBit
    FVWord n _ -> FTVec n FTBit
    FVVec t vs -> FTVec (fromIntegral (length vs)) t
    FVTuple vs -> FTTuple (map finiteTypeOf vs)
    FVRec vm   -> FTRec (fmap finiteTypeOf vm)

firstOrderTypeOf :: FirstOrderValue -> FirstOrderType
firstOrderTypeOf fv =
  case fv of
    FOVBit _    -> FOTBit
    FOVInt _    -> FOTInt
    FOVIntMod n _ -> FOTIntMod n
    FOVWord n _ -> FOTVec n FOTBit
    FOVVec t vs -> FOTVec (fromIntegral (length vs)) t
    FOVArray tk d _vs -> FOTArray tk (firstOrderTypeOf d)
    FOVOpaqueArray tk tv -> FOTArray tk tv
    FOVTuple vs -> FOTTuple (map firstOrderTypeOf vs)
    FOVRec vm   -> FOTRec (fmap firstOrderTypeOf vm)

-- | Compute the number of bits in the type
sizeFiniteType :: FiniteType -> Int
sizeFiniteType x =
  case x of
    FTBit      -> 1
    FTVec n xs -> fromIntegral n * sizeFiniteType xs
    FTTuple xs -> sum (map sizeFiniteType xs)
    FTRec xm   -> sum (map sizeFiniteType (Map.elems xm))

asFiniteType :: SharedContext -> Term -> IO FiniteType
asFiniteType sc t = do
  t' <- scWhnf sc t
  case t' of
    (R.asBoolType -> Just ())
      -> return FTBit
    (R.isVecType return -> Just (n R.:*: tp))
      -> FTVec n <$> asFiniteType sc tp
    (R.asTupleType -> Just ts)
      -> FTTuple <$> traverse (asFiniteType sc) ts
    (R.asRecordType -> Just tm)
      -> FTRec <$> traverse (asFiniteType sc) tm
    _ -> fail $ "asFiniteType: unsupported argument type: " ++ scPrettyTerm defaultPPOpts t'

asFirstOrderType :: SharedContext -> Term -> IO FirstOrderType
asFirstOrderType sc t = maybe err pure =<< runMaybeT (asFirstOrderTypeMaybe sc t)
  where
    err =
      do t' <- scWhnf sc t
         fail ("asFirstOrderType: unsupported argument type: " ++ scPrettyTerm defaultPPOpts t')

asFirstOrderTypeMaybe :: SharedContext -> Term -> MaybeT IO FirstOrderType
asFirstOrderTypeMaybe sc t =
  do t' <- lift (scWhnf sc t)
     case t' of
       (R.asBoolType -> Just ())
         -> return FOTBit
       (R.asIntegerType -> Just ())
         -> return FOTInt
       (R.asIntModType -> Just n)
         -> return (FOTIntMod n)
       (R.isVecType return -> Just (n R.:*: tp))
         -> FOTVec n <$> asFirstOrderTypeMaybe sc tp
       (R.asArrayType -> Just (tp1 R.:*: tp2)) -> do
         tp1' <- asFirstOrderTypeMaybe sc tp1
         tp2' <- asFirstOrderTypeMaybe sc tp2
         return $ FOTArray tp1' tp2'
       (R.asTupleType -> Just ts)
         -> FOTTuple <$> traverse (asFirstOrderTypeMaybe sc) ts
       (R.asRecordType -> Just tm)
         -> FOTRec <$> traverse (asFirstOrderTypeMaybe sc) tm
       _ -> mzero


asFiniteTypePure :: Term -> Maybe FiniteType
asFiniteTypePure t =
  case t of
    (R.asBoolType -> Just ()) -> Just FTBit
    (R.isVecType return -> Just (n R.:*: tp)) -> FTVec n <$> asFiniteTypePure tp
    (R.asTupleType -> Just ts) -> FTTuple <$> traverse asFiniteTypePure ts
    (R.asRecordType -> Just tm) -> FTRec <$> traverse asFiniteTypePure tm
    _ -> Nothing

-- The definitions of the next two functions depend on the encoding of
-- tuples that we want to use. Maybe it is better not to include them
-- in this library, and we should have them in the SAWScript project
-- instead.

-- | Convert a finite type to a Term.
scFiniteType :: SharedContext -> FiniteType -> IO Term
scFiniteType sc ft = scFirstOrderType sc (toFirstOrderType ft)

-- | Convert a finite type to a Term.
scFirstOrderType :: SharedContext -> FirstOrderType -> IO Term
scFirstOrderType sc ft =
  case ft of
    FOTBit      -> scBoolType sc
    FOTInt      -> scIntegerType sc
    FOTIntMod n -> scIntModType sc =<< scNat sc n
    FOTVec n t  -> do n' <- scNat sc n
                      t' <- scFirstOrderType sc t
                      scVecType sc n' t'
    FOTArray t1 t2 -> do t1' <- scFirstOrderType sc t1
                         t2' <- scFirstOrderType sc t2
                         scArrayType sc t1' t2'
    FOTTuple ts -> scTupleType sc =<< traverse (scFirstOrderType sc) ts
    FOTRec tm   ->
      scRecordType sc =<< (Map.assocs <$> traverse (scFirstOrderType sc) tm)

-- | Convert a finite value to a SharedTerm.
scFiniteValue :: SharedContext -> FiniteValue -> IO Term
scFiniteValue sc fv = scFirstOrderValue sc (toFirstOrderValue fv)

-- | Convert a finite value to a SharedTerm.
scFirstOrderValue :: SharedContext -> FirstOrderValue -> IO Term
scFirstOrderValue sc fv =
  case fv of
    FOVBit b    -> scBool sc b
    FOVInt i
      | i >= 0  -> scNatToInt sc =<< scNat sc (fromInteger i)
      | True    -> scIntNeg sc =<< scNatToInt sc =<< scNat sc (fromInteger (- i))
    FOVIntMod 0 i ->
      do n' <- scNat sc 0
         scToIntMod sc n' =<< scFirstOrderValue sc (FOVInt i)
    FOVIntMod n i ->
      do n' <- scNat sc n
         i' <- scNatToInt sc =<< scNat sc (fromInteger (i `mod` toInteger n))
         scToIntMod sc n' i'
    FOVWord n x -> scBvConst sc n x
    FOVVec t vs -> do t' <- scFirstOrderType sc t
                      vs' <- traverse (scFirstOrderValue sc) vs
                      scVector sc t' vs'
    FOVArray tk d vs -> do
        -- first get the key and value types
        tk' <- scFirstOrderType sc tk
        tv' <- scFirstOrderType sc $ firstOrderTypeOf d
        -- convert the default value and make an array
        d' <- scFirstOrderValue sc d
        arr0 <- scArrayConstant sc tk' tv' d'
        -- now add each update to the array (monadic fold)
        let visit k v arr = do
              k' <- scFirstOrderValue sc k
              v' <- scFirstOrderValue sc v
              scArrayUpdate sc tk' tv' arr k' v'
        ifoldrM visit arr0 vs
    FOVOpaqueArray _tk _tv -> do
        fail "Cannot convert opaque array to SharedTerm"
    FOVTuple vs -> scTuple sc =<< traverse (scFirstOrderValue sc) vs
    FOVRec vm   -> scRecord sc =<< traverse (scFirstOrderValue sc) vm

-- Parsing values from lists of booleans ---------------------------------------

data Endianness
  = BigEndian
  | LittleEndian

readFiniteValue' :: Endianness -> FiniteType -> S.StateT [Bool] Maybe FiniteValue
readFiniteValue' en ft =
  case ft of
    FTBit      -> do bs <- S.get
                     case bs of
                       []      -> S.lift Nothing
                       b : bs' -> S.put bs' >> return (FVBit b)
    FTVec n t  -> (fvVec t . fixup) <$> replicateM (fromIntegral n) (readFiniteValue' en t)
                    where fixup = case (t, en) of
                                    (FTBit, LittleEndian) -> reverse
                                    _ -> id
    FTTuple ts -> FVTuple <$> traverse (readFiniteValue' en) ts
    FTRec tm   -> FVRec <$> traverse (readFiniteValue' en) tm

readFiniteValues :: [FiniteType] -> [Bool] -> Maybe [FiniteValue]
readFiniteValues ts bs = do
  (vs, rest) <- S.runStateT (traverse (readFiniteValue' BigEndian) ts) bs
  case rest of
    [] -> return vs
    _ -> Nothing

readFiniteValuesLE :: [FiniteType] -> [Bool] -> Maybe [FiniteValue]
readFiniteValuesLE ts bs = do
  (vs, rest) <- S.runStateT (traverse (readFiniteValue' LittleEndian) ts) bs
  case rest of
    [] -> return vs
    _ -> Nothing

readFiniteValue :: FiniteType -> [Bool] -> Maybe FiniteValue
readFiniteValue t bs = do
  (v, rest) <- S.runStateT (readFiniteValue' BigEndian t) bs
  case rest of
    [] -> return v
    _ -> Nothing
