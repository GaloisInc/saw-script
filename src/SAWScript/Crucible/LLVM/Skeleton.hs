{- |
Module      : SAWScript.Crucible.LLVM.Skeleton
Description : Inferring and using "skeletons" of LLVM specifications
Maintainer  : sbreese
Stability   : provisional
-}

{-# Language TemplateHaskell #-}
{-# Language OverloadedStrings #-}
{-# Language RecordWildCards #-}

module SAWScript.Crucible.LLVM.Skeleton where

import Control.Lens.TH

import Control.Arrow
import Control.Monad
import Control.Lens

import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import qualified Text.LLVM as LLVM

--------------------------------------------------------------------------------
-- ** Skeletons

data Location = Location
  { _locationLine :: Int
  , _locationColumn :: Maybe Int
  } deriving (Show, Eq, Ord)
makeLenses ''Location

data SizeGuess = SizeGuess
  { _sizeGuessElems :: Int
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
  , _globSkelLoc :: Maybe Location
  , _globSkelType :: TypeSkeleton
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
  , _funSkelLoc :: Maybe Location
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
parseType (LLVM.PtrTo t) = pure $ TypeSkeleton t True [SizeGuess 1 "default guess of size 1"]
parseType (LLVM.Array i t) = pure $ TypeSkeleton t True
  [ SizeGuess (fromIntegral i) $ "default guess of size " <> Text.pack (show i)
  ]
parseType t = pure $ TypeSkeleton t False []

debugInfoGlobalLines :: LLVM.Module -> Map Text Int
debugInfoGlobalLines = go . LLVM.modUnnamedMd
  where
    go :: [LLVM.UnnamedMd] -> Map Text Int
    go (LLVM.UnnamedMd
         { LLVM.umValues = LLVM.ValMdDebugInfo
           (LLVM.DebugInfoGlobalVariable LLVM.DIGlobalVariable
             { LLVM.digvName = Just n
             , LLVM.digvLine = l
             }
           )
         }:xs) = Map.insert (Text.pack n) (fromIntegral l) $ go xs
    go (_:xs) = go xs
    go [] = Map.empty

parseGlobal :: Map Text Int -> LLVM.Global -> IO GlobalSkeleton
parseGlobal ls LLVM.Global
  { LLVM.globalSym = LLVM.Symbol s
  , LLVM.globalType = t
  , LLVM.globalValue = v
  } = do
  let nm = Text.pack s
  ty <- parseType t
  pure GlobalSkeleton
    { _globSkelName = Text.pack s
    , _globSkelLoc = flip Location Nothing <$> Map.lookup nm ls
    , _globSkelType = ty
    , _globSkelInitialized = isJust v
    }

parseArg :: LLVM.Typed LLVM.Ident -> (Maybe Text, Maybe Location) -> IO ArgSkeleton
parseArg LLVM.Typed { LLVM.typedType = t } (nm, loc) = do
  ty <- parseType t
  pure ArgSkeleton
    { _argSkelName = nm
    , _argSkelLoc = loc
    , _argSkelType = ty
    }

stmtCalls :: [LLVM.Stmt] -> Set Text
stmtCalls [] = Set.empty
stmtCalls (LLVM.Result _ (LLVM.Call _ _ (LLVM.ValSymbol (LLVM.Symbol s)) _) _:stmts) =
  Set.insert (Text.pack s) $ stmtCalls stmts
stmtCalls (LLVM.Effect (LLVM.Call _ _ (LLVM.ValSymbol (LLVM.Symbol s)) _) _:stmts) =
  Set.insert (Text.pack s) $ stmtCalls stmts
stmtCalls (_:stmts) = stmtCalls stmts

stmtDebugDeclares :: [LLVM.Stmt] -> Map Int Location
stmtDebugDeclares [] = Map.empty
stmtDebugDeclares
  (LLVM.Result _
    (LLVM.Call _ _
      (LLVM.ValSymbol (LLVM.Symbol s))
      [ _
      , LLVM.Typed
        { LLVM.typedValue =
          LLVM.ValMd (LLVM.ValMdDebugInfo (LLVM.DebugInfoLocalVariable LLVM.DILocalVariable { LLVM.dilvArg = a }))
        }
      , _
      ]) md:stmts)
  | s == "llvm.dbg.declare" || s == "llvm.dbg.value"
  , Just (LLVM.ValMdLoc LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }) <- lookup "dbg" md
  = Map.insert (fromIntegral a) (Location (fromIntegral line) . Just $ fromIntegral col) $ stmtDebugDeclares stmts
stmtDebugDeclares
  (LLVM.Effect 
    (LLVM.Call _ _
      (LLVM.ValSymbol (LLVM.Symbol s))
      [ _
      , LLVM.Typed
        { LLVM.typedValue =
          LLVM.ValMd (LLVM.ValMdDebugInfo (LLVM.DebugInfoLocalVariable LLVM.DILocalVariable { LLVM.dilvArg = a }))
        }
      , _
      ]) md:stmts)
  | s == "llvm.dbg.declare" || s == "llvm.dbg.value"
  , Just (LLVM.ValMdLoc LLVM.DebugLoc { LLVM.dlLine = line, LLVM.dlCol = col }) <- lookup "dbg" md
  = Map.insert (fromIntegral a) (Location (fromIntegral line) . Just $ fromIntegral col) $ stmtDebugDeclares stmts
stmtDebugDeclares (_:stmts) = stmtDebugDeclares stmts

defineName :: LLVM.Define -> Text
defineName LLVM.Define { LLVM.defName = LLVM.Symbol s } = Text.pack s

debugInfoArgNames :: LLVM.Module -> LLVM.Define -> Map Int Text
debugInfoArgNames m d =
  case Map.lookup "dbg" $ LLVM.defMetadata d of
    Just (LLVM.ValMdRef s) -> scopeArgs s
    _ -> Map.empty
  where
    scopeArgs :: Int -> Map Int Text
    scopeArgs s = go $ LLVM.modUnnamedMd m
      where go :: [LLVM.UnnamedMd] -> Map Int Text
            go [] = Map.empty
            go (LLVM.UnnamedMd
                 { LLVM.umValues =
                   LLVM.ValMdDebugInfo
                     (LLVM.DebugInfoLocalVariable
                       LLVM.DILocalVariable
                       { LLVM.dilvScope = Just (LLVM.ValMdRef s')
                       , LLVM.dilvArg = a
                       , LLVM.dilvName = Just n
                       })}:xs) =
              if s == s' then Map.insert (fromIntegral a) (Text.pack n) $ go xs else go xs
            go (_:xs) = go xs

debugInfoDefineLines :: LLVM.Module -> Map Text Int
debugInfoDefineLines = go . LLVM.modUnnamedMd
  where
    go :: [LLVM.UnnamedMd] -> Map Text Int
    go (LLVM.UnnamedMd
         { LLVM.umValues = LLVM.ValMdDebugInfo
           (LLVM.DebugInfoSubprogram LLVM.DISubprogram
             { LLVM.dispName = Just n
             , LLVM.dispIsDefinition = True
             , LLVM.dispLine = l
             }
           )
         }:xs) = Map.insert (Text.pack n) (fromIntegral l) $ go xs
    go (_:xs) = go xs
    go [] = Map.empty

parseDefine :: Map Text Int -> LLVM.Module -> LLVM.Define -> IO FunctionSkeleton
parseDefine _ _ LLVM.Define { LLVM.defVarArgs = True } = undefined
parseDefine ls m d@LLVM.Define
  { LLVM.defName = LLVM.Symbol s
  , LLVM.defArgs = args
  , LLVM.defBody = body
  , LLVM.defRetType = ret
  } = do
  let stmts = mconcat $ LLVM.bbStmts <$> body
  let argNames = debugInfoArgNames m d
  let debugDeclares = stmtDebugDeclares stmts
  argSkels <- zipWithM parseArg args $ (flip Map.lookup argNames &&& flip Map.lookup debugDeclares) <$> [1, 2..]
  retTy <- parseType ret
  pure FunctionSkeleton
    { _funSkelName = Text.pack s
    , _funSkelLoc = flip Location Nothing <$> Map.lookup (Text.pack s) ls
    , _funSkelArgs = argSkels
    , _funSkelRet = retTy
    , _funSkelCalls = Set.intersection
      (Set.fromList $ defineName <$> LLVM.modDefines m)
      (stmtCalls stmts)
    }

moduleSkeleton :: LLVM.Module -> IO ModuleSkeleton
moduleSkeleton ast = do
  globs <- mapM (parseGlobal $ debugInfoGlobalLines ast) $ LLVM.modGlobals ast
  funs <- mapM (parseDefine (debugInfoDefineLines ast) ast) $ LLVM.modDefines ast
  pure $ ModuleSkeleton
    { _modSkelGlobals = Map.fromList $ (\g -> (g ^. globSkelName, g)) <$> globs
    , _modSkelFunctions = Map.fromList $ (\f -> (f ^. funSkelName, f)) <$> funs
    }
