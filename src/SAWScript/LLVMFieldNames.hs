{- |
Module           : $Header$
Description      : This module interprets the DWARF information associated
                   with a function's argument and return types in order to
                   interpret field name references.
License          : BSD3
Stability        : provisional
Point-of-contact : emertens
-}
module SAWScript.LLVMFieldNames
  ( -- * Definition type analyzer
    Info(..), analyzeDefine, valMdToInfo

  -- * Metadata lookup
  , mkMdMap

  -- * Metadata lookup
  , derefInfo
  , fieldIndexByPosition
  , fieldIndexByName
  ) where

import           Control.Monad          ((<=<))
import           Data.IntMap            (IntMap)
import qualified Data.IntMap as IntMap
import           Data.List              (elemIndex)
import qualified Data.Map    as Map
import           Data.Word              (Word16)
import           Text.LLVM.AST

dbgKind :: String
dbgKind = "dbg"

dwarfPointer, dwarfStruct, dwarfTypedef, dwarfUnion, dwarfBasetype :: Word16
dwarfPointer  = 0x0f
dwarfStruct   = 0x13
dwarfTypedef  = 0x16
dwarfUnion    = 0x17
dwarfBasetype = 0x24

type MdMap = IntMap ValMd

data Info
  = Pointer Info
  | Structure [(String,Info)]
  | Union     [(String,Info)]
  | BaseType String
  | Unknown
  deriving Show

{-
import Text.Show.Pretty
import Data.Foldable

test =
  do test' "/Users/emertens/Source/saw/saw-script\
           \/examples/llvm/dotprod_struct.bc"
     test' "/Users/emertens/Desktop/temp.bc"

test' fn =
  do Right bc <- parseBitCodeFromFile fn
     let mdMap = mkMdMap bc
     traverse_ (putStrLn . ppShow . analyzeDefine mdMap) (modDefines bc)
-}

-- | Compute an 'IntMap' of the unnamed metadata in a module
mkMdMap :: Module -> IntMap ValMd
mkMdMap m = IntMap.fromList [ (umIndex md, umValues md) | md <- modUnnamedMd m ]

------------------------------------------------------------------------

getDebugInfo :: MdMap -> ValMd -> Maybe DebugInfo
getDebugInfo mdMap (ValMdRef i)    = getDebugInfo mdMap =<< IntMap.lookup i mdMap
getDebugInfo _ (ValMdDebugInfo di) = Just di
getDebugInfo _ _                   = Nothing


getList :: MdMap -> ValMd -> Maybe [Maybe ValMd]
getList mdMap (ValMdRef i) = getList mdMap =<< IntMap.lookup i mdMap
getList _ (ValMdNode di)   = Just di
getList _ _                = Nothing

------------------------------------------------------------------------

valMdToInfo :: MdMap -> ValMd -> Info
valMdToInfo mdMap val =
  maybe Unknown (debugInfoToInfo mdMap) (getDebugInfo mdMap val)


valMdToInfo' :: MdMap -> Maybe ValMd -> Info
valMdToInfo' = maybe Unknown . valMdToInfo


debugInfoToInfo :: MdMap -> DebugInfo -> Info
debugInfoToInfo mdMap (DebugInfoDerivedType dt)
  | didtTag dt == dwarfPointer  = Pointer (valMdToInfo' mdMap (didtBaseType dt))
  | didtTag dt == dwarfTypedef  =          valMdToInfo' mdMap (didtBaseType dt)
debugInfoToInfo _     (DebugInfoBasicType bt)
  | dibtTag bt == dwarfBasetype = BaseType (dibtName bt)
debugInfoToInfo mdMap (DebugInfoCompositeType ct)
  | dictTag ct == dwarfStruct   = maybe Unknown Structure (getFields mdMap ct)
  | dictTag ct == dwarfUnion    = maybe Unknown Union     (getFields mdMap ct)
debugInfoToInfo _ _             = Unknown


getFields :: MdMap -> DICompositeType -> Maybe [(String, Info)]
getFields mdMap ct =
  traverse (debugInfoToField mdMap <=< getDebugInfo mdMap)
       =<< sequence =<< getList mdMap =<< dictElements ct


debugInfoToField :: MdMap -> DebugInfo -> Maybe (String, Info)
debugInfoToField mdMap di =
  do DebugInfoDerivedType dt <- Just di
     fieldName               <- didtName dt
     Just (fieldName, valMdToInfo' mdMap (didtBaseType dt))


analyzeDefine ::
  IntMap ValMd {- ^ unnamed metadata      -} ->
  Define       {- ^ definition to inspect -} ->
  Maybe [Info] {- ^ structural information about return type and argument types -}
analyzeDefine mdMap def =
  do dbgMd <- Map.lookup dbgKind (defMetadata def)
     DebugInfoSubprogram     sp <- getDebugInfo mdMap dbgMd
     DebugInfoSubroutineType st <- getDebugInfo mdMap =<< dispType sp
     types                      <- getList mdMap =<< distTypeArray st
     let processType = maybe (BaseType "void") (valMdToInfo mdMap)
     return (map processType types)

------------------------------------------------------------------------

derefInfo :: Info -> Info
derefInfo (Pointer x) = x
derefInfo _           = Unknown

fieldIndexByPosition :: Int -> Info -> Info
fieldIndexByPosition i info =
  case info of
    Structure xs -> go xs
    Union     xs -> go xs
    _            -> error "bad find index"
  where
    go xs = case drop i xs of
              []  -> error "bad index"
              x:_ -> snd x

fieldIndexByName :: String -> Info -> Maybe Int
fieldIndexByName n info =
  case info of
    Structure xs -> go xs
    Union     xs -> go xs
    _            -> Nothing
  where
    go = elemIndex n . map fst
