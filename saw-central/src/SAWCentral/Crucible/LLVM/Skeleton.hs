{- |
Module      : SAWCentral.Crucible.LLVM.Skeleton
Description : Inferring and using "skeletons" of LLVM specifications
Maintainer  : sbreese
Stability   : provisional
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}

module SAWCentral.Crucible.LLVM.Skeleton
  ( Location(..), locationLine, locationColumn
  , SizeGuess(..), sizeGuessElems, sizeGuessInitialized, sizeGuessSource
  , TypeSkeleton(..), typeSkelLLVMType, typeSkelIsPointer, typeSkelSizeGuesses
  , GlobalSkeleton(..), globSkelName, globSkelType, globSkelMutable, globSkelInitialized
  , ArgSkeleton(..), argSkelName, argSkelLoc, argSkelType
  , FunctionSkeleton(..), funSkelName, funSkelArgs, funSkelRet, funSkelCalls
  , ModuleSkeleton(..), modSkelGlobals, modSkelFunctions

  , moduleSkeleton
  ) where

import Control.Lens.TH

import Control.Arrow
import Control.Monad
import Control.Lens

import qualified Data.IntMap.Strict as IntMap
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Text.LLVM as LLVM
import qualified Text.LLVM.DebugUtils as LLVM

import SAWCentral.Panic (panic)

--------------------------------------------------------------------------------
-- ** Skeletons

data Location = Location
  { _locationLine :: Int
  , _locationColumn :: Maybe Int
  } deriving (Show, Eq, Ord)
makeLenses ''Location

data SizeGuess = SizeGuess
  { _sizeGuessElems :: Int
  , _sizeGuessInitialized :: Bool
  , _sizeGuessSource :: Text
  } deriving (Show, Eq, Ord)
makeLenses ''SizeGuess

data TypeSkeleton = TypeSkeleton
  { _typeSkelLLVMType :: LLVM.Type
  , _typeSkelIsPointer :: Bool
  , _typeSkelSizeGuesses :: [SizeGuess]
  } deriving (Show, Eq, Ord)
makeLenses ''TypeSkeleton

data GlobalSkeleton = GlobalSkeleton
  { _globSkelName :: Text
  , _globSkelType :: TypeSkeleton
  , _globSkelMutable :: Bool
  , _globSkelInitialized :: Bool
  } deriving (Show, Eq, Ord)
makeLenses ''GlobalSkeleton

data ArgSkeleton = ArgSkeleton
  { _argSkelName :: Maybe Text
  , _argSkelLoc :: Maybe Location
  , _argSkelType :: TypeSkeleton
  } deriving (Show, Eq, Ord)
makeLenses ''ArgSkeleton

data FunctionSkeleton = FunctionSkeleton
  { _funSkelName :: Text
  , _funSkelArgs :: [ArgSkeleton]
  , _funSkelRet :: TypeSkeleton
  , _funSkelCalls :: Set Text
  } deriving (Show, Eq, Ord)
makeLenses ''FunctionSkeleton

data ModuleSkeleton = ModuleSkeleton
  { _modSkelGlobals :: Map Text GlobalSkeleton
  , _modSkelFunctions :: Map Text FunctionSkeleton
  } deriving (Show, Eq, Ord)
makeLenses ''ModuleSkeleton

--------------------------------------------------------------------------------
-- ** Inferring skeletons

parseType :: LLVM.Type -> IO TypeSkeleton
parseType (LLVM.PtrTo t) = pure $ TypeSkeleton t True [SizeGuess 1 True "default guess of size 1"]
-- It is unclear how to combine opaque pointers with type skeletons due to the
-- lack of a pointee type. For now, we simply fail if we encounter one
-- (see #1877).
parseType LLVM.PtrOpaque =
  panic "SAWCentral.Crucible.LLVM.Skeleton.parseType"
        [ "Skeleton generation does not support opaque pointers"
        , "Please report this at: https://github.com/GaloisInc/saw-script/issues/1877"
        ]
parseType (LLVM.Array i t) = pure $ TypeSkeleton t True
  [ SizeGuess (fromIntegral i) True $ "default guess of size " <> Text.pack (show i)
  ]
parseType t = pure $ TypeSkeleton t False []

parseGlobal :: LLVM.Global -> IO GlobalSkeleton
parseGlobal LLVM.Global
  { LLVM.globalSym = LLVM.Symbol s
  , LLVM.globalType = t
  , LLVM.globalValue = v
  , LLVM.globalAttrs = LLVM.GlobalAttrs { LLVM.gaConstant = c }
  } = do
  ty <- parseType t
  pure GlobalSkeleton
    { _globSkelName = Text.pack s
    , _globSkelType = ty
    , _globSkelMutable = not c
    , _globSkelInitialized = isJust v
    }

parseArg :: LLVM.Typed LLVM.Ident -> (Maybe String, Maybe Location) -> IO ArgSkeleton
parseArg LLVM.Typed { LLVM.typedType = t } (nm, loc) = do
  ty <- parseType t
  pure ArgSkeleton
    { _argSkelName = Text.pack <$> nm
    , _argSkelLoc = loc
    , _argSkelType = ty
    }

stmtCalls :: [LLVM.Stmt] -> Set Text
stmtCalls [] = Set.empty
stmtCalls (LLVM.Result _ (LLVM.Call _ _ (LLVM.ValSymbol (LLVM.Symbol s)) _) _ _:stmts) =
  Set.insert (Text.pack s) $ stmtCalls stmts
stmtCalls (LLVM.Effect (LLVM.Call _ _ (LLVM.ValSymbol (LLVM.Symbol s)) _) _ _:stmts) =
  Set.insert (Text.pack s) $ stmtCalls stmts
stmtCalls (_:stmts) = stmtCalls stmts

-- | Infer locations of declarations by looking at either debug records (for
-- recent versions of LLVM) or debug-related intrinsic functions (for older
-- versions of LLVM.
stmtDebugDeclares :: [LLVM.Stmt] -> Map Int Location
stmtDebugDeclares [] = Map.empty
stmtDebugDeclares (LLVM.Result _ instr drs md:stmts)
  | LLVM.Call _ _
      (LLVM.ValSymbol (LLVM.Symbol s))
      [ _
      , LLVM.Typed
        { LLVM.typedValue =
          LLVM.ValMd (LLVM.ValMdDebugInfo (LLVM.DebugInfoLocalVariable LLVM.DILocalVariable { LLVM.dilvArg = a }))
        }
      , _
      ] <- instr
  , s == "llvm.dbg.declare" || s == "llvm.dbg.value"
  , Just (LLVM.ValMdLoc LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }) <- lookup "dbg" md
  = Map.insert (fromIntegral a) (Location (fromIntegral line) . Just $ fromIntegral col) $ stmtDebugDeclares stmts
  | otherwise
  = Map.union (debugRecordDeclares drs) (stmtDebugDeclares stmts)
stmtDebugDeclares (LLVM.Effect instr drs md:stmts)
  | LLVM.Call _ _
      (LLVM.ValSymbol (LLVM.Symbol s))
      [ _
      , LLVM.Typed
        { LLVM.typedValue =
          LLVM.ValMd (LLVM.ValMdDebugInfo (LLVM.DebugInfoLocalVariable LLVM.DILocalVariable { LLVM.dilvArg = a }))
        }
      , _
      ] <- instr
  , s == "llvm.dbg.declare" || s == "llvm.dbg.value"
  , Just (LLVM.ValMdLoc LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }) <- lookup "dbg" md
  = Map.insert (fromIntegral a) (Location (fromIntegral line) . Just $ fromIntegral col) $ stmtDebugDeclares stmts
  | otherwise
  = Map.union (debugRecordDeclares drs) (stmtDebugDeclares stmts)

-- | Infer locations of declarations by looking at @#dbg_declare@ and
-- @#dbg_value@ debug records.
debugRecordDeclares :: [LLVM.DebugRecord] -> Map Int Location
debugRecordDeclares [] = Map.empty
debugRecordDeclares
  (LLVM.DebugRecordDeclare
    (LLVM.DbgRecDeclare
      { LLVM.drdLocation =
          LLVM.ValMdLoc
            LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }
      , LLVM.drdLocalVariable =
          LLVM.ValMdDebugInfo
            (LLVM.DebugInfoLocalVariable
              LLVM.DILocalVariable { LLVM.dilvArg = a })
      }):drs) =
  Map.insert
    (fromIntegral a)
    (Location (fromIntegral line) (Just (fromIntegral col)))
    (debugRecordDeclares drs)
debugRecordDeclares
  (LLVM.DebugRecordValue
    (LLVM.DbgRecValue
      { LLVM.drvLocation =
          LLVM.ValMdLoc
            LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }
      , LLVM.drvLocalVariable =
          LLVM.ValMdDebugInfo
            (LLVM.DebugInfoLocalVariable
              LLVM.DILocalVariable { LLVM.dilvArg = a })
      }):drs) =
  Map.insert
    (fromIntegral a)
    (Location (fromIntegral line) (Just (fromIntegral col)))
    (debugRecordDeclares drs)
debugRecordDeclares (_:drs) = debugRecordDeclares drs

defineName :: LLVM.Define -> Text
defineName LLVM.Define { LLVM.defName = LLVM.Symbol s } = Text.pack s

parseDefine :: LLVM.Module -> LLVM.Define -> IO FunctionSkeleton
parseDefine _ LLVM.Define { LLVM.defVarArgs = True } =
  fail "Skeleton generation does not support varargs"
parseDefine m d@LLVM.Define
  { LLVM.defName = LLVM.Symbol s
  , LLVM.defArgs = args
  , LLVM.defBody = body
  , LLVM.defRetType = ret
  } = do
  let stmts = mconcat $ LLVM.bbStmts <$> body
  let argNames = LLVM.debugInfoArgNames m d
  let debugDeclares = stmtDebugDeclares stmts
  argSkels <- zipWithM parseArg args $ (flip IntMap.lookup argNames &&& flip Map.lookup debugDeclares) <$> [1, 2..]
  retTy <- parseType ret
  pure FunctionSkeleton
    { _funSkelName = Text.pack s
    , _funSkelArgs = argSkels
    , _funSkelRet = retTy
    , _funSkelCalls = Set.intersection
      (Set.fromList $ defineName <$> LLVM.modDefines m)
      (stmtCalls stmts)
    }

moduleSkeleton :: LLVM.Module -> IO ModuleSkeleton
moduleSkeleton ast = do
  globs <- mapM parseGlobal $ LLVM.modGlobals ast
  funs <- mapM (parseDefine ast) $ LLVM.modDefines ast
  pure $ ModuleSkeleton
    { _modSkelGlobals = Map.fromList $ (\g -> (g ^. globSkelName, g)) <$> globs
    , _modSkelFunctions = Map.fromList $ (\f -> (f ^. funSkelName, f)) <$> funs
    }
