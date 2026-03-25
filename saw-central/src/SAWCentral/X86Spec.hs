{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language ImplicitParams #-}
{-# Language PatternSynonyms #-}
{-# Language RankNTypes #-}
{-# Language TypeApplications #-}
{-# Language TypeOperators #-}
module SAWCentral.X86Spec
  ( Unit(..)
  , (*.)
  , freshRegister
  , mkGlobalMap
  ) where

import GHC.Natural(Natural)
import Control.Applicative ( (<|>) )
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad (MonadPlus(..), join)

import Data.Parameterized.NatRepr
import qualified Data.Parameterized.Context as Ctx

import Data.Foldable(foldlM)

import What4.Interface
          (natEq, freshNat, natLit, asNat, userSymbol, freshConstant)

import SAWCentral.Crucible.LLVM.CrucibleLLVM
  ( doPtrAddOffset
  , pattern LLVMPointerRepr
  , LLVMPtr
  , muxLLVMPtr
  , Bytes, toBytes
  , pattern LLVMPointer
  )
import qualified Lang.Crucible.LLVM.MemModel as Crucible

import Lang.Crucible.Backend (HasSymInterface(backendGetSym))
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Types (TypeRepr(..),BaseTypeRepr(..))

import Data.Macaw.Memory(RegionIndex)
import Data.Macaw.Symbolic (GlobalMap(..))

import SAWCentral.Crucible.Common (Sym)


data Unit = Bytes | Words | DWords | QWords | V128s | V256s deriving Show


(*.) :: Integer -> Unit -> Bytes
n *. u = toBytes (fromInteger n * bs)
  where bs = unitByteSize u natValue :: Natural

unitByteSize :: Unit -> (forall w. (1 <= w) => NatRepr w -> a) -> a
unitByteSize u k =
  case u of
    Bytes  -> k (knownNat @1)
    Words  -> k (knownNat @2)
    DWords -> k (knownNat @4)
    QWords -> k (knownNat @8)
    V128s  -> k (knownNat @16)
    V256s  -> k (knownNat @32)


--------------------------------------------------------------------------------

freshRegister :: Sym -> Ctx.Index ctx tp -> TypeRepr tp -> IO (RegValue' Sym tp)
freshRegister sym idx repr = RV <$> freshVal sym repr True ("reg" ++ show idx)

freshVal ::
  Sym -> TypeRepr t -> Bool {- ptrOK ?-}-> String -> IO (RegValue Sym t)
freshVal sym t ptrOk nm =
  case t of
    BoolRepr -> do
      sn <- symName nm
      freshConstant sym sn BaseBoolRepr
    LLVMPointerRepr w
      | ptrOk, Just Refl <- testEquality w (knownNat @64) -> do
          sn_base <- symName (nm ++ "_base")
          sn_off <- symName (nm ++ "_off")
          base <- freshNat sym sn_base
          off <- freshConstant sym sn_off (BaseBVRepr w)
          return (LLVMPointer base off)
      | otherwise -> do
          sn <- symName nm
          base <- natLit sym 0
          off <- freshConstant sym sn (BaseBVRepr w)
          return (LLVMPointer base off)
    it -> fail ("[freshVal] Unexpected type repr: " ++ show it)

  where
  symName s =
    case userSymbol ("macaw_" ++ s) of
      Left err -> error ("Invalid symbol name " ++ show s ++ ": " ++ show err)
      Right a -> return a


--------------------------------------------------------------------------------

-- | Implements a layer to map 'LLVMPtr's to their underlying allocations, as
-- tracked by the 'RegionIndex' map
--
-- NOTE: If the initial obvious mapping (where the concrete nat is in the map)
-- fails, there are two possibilities:
--
-- 1. The region ID is concrete but not in the map.  We should just pass it
--    through without modifying it, since it is a valid LLVM pointer
-- 2. The region ID is symbolic.  In this case, we need to generate a mux that
--    dispatches to the entries in the map when they match, or otherwise passes
--    the pointer through untouched.
--
-- If the region ID is concretely zero, it should be the case that the
-- 'RegionIndex' map would translate it into a real 'LLVMPtr' since the only map
-- entry (established in 'setupGlobals') is for 0.
mkGlobalMap ::
  (?memOpts::Crucible.MemOptions, Crucible.HasLLVMAnn Sym) =>
  Map RegionIndex (LLVMPtr Sym 64) ->
  GlobalMap Sym Crucible.Mem 64
mkGlobalMap rmap = GlobalMap $ \bak mem region off ->
  let
    sym = backendGetSym bak

    mapConcreteRegion = maybe mzero id (addOffset <$> thisRegion)
    thisRegion = join (findRegion <$> asNat region)
    findRegion r = Map.lookup (fromIntegral r) rmap
    addOffset p = doPtrAddOffset bak mem p off
      where ?ptrWidth = knownNat
    passThroughConcreteRegion =
      case asNat region of
        Nothing -> mzero
        Just _ -> return (LLVMPointer region off)
    -- If the symbolic nat is (symbolically) equal to any of the entries in the
    -- rmap, we need to do the translation; otherwise, we pass it through
    mapSymbolicRegion = foldlM muxSymbolicRegion (LLVMPointer region off) (Map.toList rmap)
    muxSymbolicRegion others (regionNum, basePtr) = do
      thisRegionNat <- natLit sym (fromIntegral regionNum)
      isEqRegion <- natEq sym thisRegionNat region
      adjustedPtr <- addOffset basePtr
      muxLLVMPtr sym isEqRegion adjustedPtr others

  in mapConcreteRegion <|> passThroughConcreteRegion <|> mapSymbolicRegion
