{-# Language TransformListComp, MonadComprehensions #-}
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
    Info(..), computeFunctionTypes, valMdToInfo

  -- * Metadata lookup
  , mkMdMap

  -- * Metadata lookup
  , derefInfo
  , fieldIndexByPosition
  , fieldIndexByName
  ) where

import           Control.Applicative    ((<|>))
import           Control.Monad          ((<=<))
import           Data.IntMap            (IntMap)
import qualified Data.IntMap as IntMap
import           Data.List              (elemIndex)
import qualified Data.Map    as Map
import           Data.Maybe             (fromMaybe, listToMaybe, maybeToList)
import           Data.Word              (Word16)
import           Text.LLVM.AST

dbgKind :: String
dbgKind = "dbg"

llvmDbgCuKey :: String
llvmDbgCuKey = "llvm.dbg.cu"

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


-- | Compute the structures of a function's return and argument types
-- using DWARF information metadata of the LLVM module. Different
-- versions of LLVM make this information available via different
-- paths. This function attempts to support the variations.
computeFunctionTypes ::
  Module       {- ^ module to search                     -} ->
  Symbol       {- ^ function symbol                      -} ->
  Maybe [Info] {- ^ return and argument type information -}
computeFunctionTypes m sym =
  [ maybe (BaseType "void") (valMdToInfo mdMap) <$> types
     | let mdMap = mkMdMap m
     , sp <- findSubprogramViaDefine mdMap m sym
         <|> findSubprogramViaCu     mdMap m sym
     , DebugInfoSubroutineType st <- getDebugInfo mdMap =<< dispType sp
     , types                      <- getList mdMap      =<< distTypeArray st
     ]


-- | This method of computing argument type information works on at least LLVM 3.8
findSubprogramViaDefine ::
  IntMap ValMd       {- ^ unnamed metadata                             -} ->
  Module             {- ^ module to search                             -} ->
  Symbol             {- ^ function symbol to find                      -} ->
  Maybe DISubprogram {- ^ debug information related to function symbol -}
findSubprogramViaDefine mdMap m sym =
  [ sp
     | def                    <- modDefines m
     , defName def == sym
     , then listToMaybe ----- commits to a choice -----
     , dbgMd                  <- Map.lookup dbgKind (defMetadata def)
     , DebugInfoSubprogram sp <- getDebugInfo mdMap dbgMd
     ]


-- | This method of computing function debugging information works on LLVM 3.7
findSubprogramViaCu ::
  MdMap              {- ^ map of unnamed metadata                -} ->
  Module             {- ^ module to search                       -} ->
  Symbol             {- ^ function symbol to search for          -} ->
  Maybe DISubprogram {- ^ debugging information for given symbol -}
findSubprogramViaCu mdMap m (Symbol sym) = listToMaybe
  [ sp
    | md                      <- modNamedMd m
    , nmName md == llvmDbgCuKey
    , ref                     <- nmValues md
    , DebugInfoCompileUnit cu <- maybeToList  $ getDebugInfo mdMap $ ValMdRef ref
    , Just entry              <- fromMaybe [] $ getList mdMap =<< dicuSubprograms cu
    , DebugInfoSubprogram sp  <- maybeToList  $ getDebugInfo mdMap entry
    , dispName sp == Just sym
    ]


------------------------------------------------------------------------

-- | If the argument describes a pointer, return the information for the
-- type that it points do.
derefInfo ::
  Info {- ^ pointer type information                -} ->
  Info {- ^ type information of pointer's base type -}
derefInfo (Pointer x) = x
derefInfo _           = Unknown

-- | If the argument describes a composite type, returns the type of the
-- field by zero-based index into the list of fields.
fieldIndexByPosition ::
  Int  {- ^ zero-based field index               -} ->
  Info {- ^ composite type information           -} ->
  Info {- ^ type information for specified field -}
fieldIndexByPosition i info =
  case info of
    Structure xs -> go xs
    Union     xs -> go xs
    _            -> Unknown
  where
    go xs = case drop i xs of
              []  -> Unknown
              x:_ -> snd x

-- | If the argument describes a composite type, return the first, zero-based
-- index of the field in that type that matches the given name.
fieldIndexByName ::
  String    {- ^ field name                                  -} ->
  Info      {- ^ composite type info                         -} ->
  Maybe Int {- ^ zero-based index of field matching the name -}
fieldIndexByName n info =
  case info of
    Structure xs -> go xs
    Union     xs -> go xs
    _            -> Nothing
  where
    go = elemIndex n . map fst
