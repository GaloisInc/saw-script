{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{- |
Module      : SAWCore.UnionFind
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.UnionFind (
    AssertResult(..)
  , assertSucceeded
  -- * Class operations
  , Class
  , UnionFind
  , empty
  , Action
  , runAction
  , classRep
  , freshClass
  , areEqual
  , setEqual
  , setUnequal
  -- * Class descriptions
  , readClassDesc
  , writeClassDesc
  , modifyClassDesc
  ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative)
#endif
import Control.Monad.State.Strict
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Types {{{1

type ClassIndex = Int

-- | Equivalence class in union find structure.
newtype Class d = Class ClassIndex

data ClassState d = NonRep !ClassIndex
                  | Rep {
                       _classNeqs :: [ClassIndex] -- ^ Classes not equal to this class
                     , _classSize :: !Int -- ^ Size of class
                     , _classDesc :: d -- ^ Class descriptor
                     }

data UnionFind d = UFS {
         ufsCount :: !Int
       , ufsMap :: !(Map ClassIndex (ClassState d))
       }

-- | Returns union find struct with no classes.
empty :: UnionFind d
empty = UFS { ufsCount = 0, ufsMap = Map.empty }

-- | Monad with scoped union find support.
newtype Action d a = UF { _unUF :: State (UnionFind d) a }
  deriving (Functor, Applicative, Monad)

-- | Runs union find computation.
runAction :: UnionFind d -> Action d a -> (a, UnionFind d)
runAction s (UF m) = runState m s

-- Class operations {{{1

-- | Get class description
classRep :: Class d -> Action d (Class d)
classRep (Class r) = UF $ do
  m <- gets ufsMap
  let impl i prev = do
        case Map.lookup i m of
          Nothing -> error $ "classRep: Illegal index " ++ show i
          Just (NonRep next) -> impl next (i:prev)
          Just Rep{} -> do
            let updateRep ma j = Map.insert j (NonRep i) ma
            modify $ \s -> s { ufsMap = foldl' updateRep (ufsMap s) prev }
            return (Class i)
  impl r []

-- | Look up an equivalence class in a union find structure's map. This checks
-- the invariant that the index of the class exists in the map and is associated
-- with a 'Rep', not a 'NonRep'. If this invariant is violated, this function
-- will throw an error.
lookupClassRep :: Class d -> UnionFind d -> ([ClassIndex], Int, d)
lookupClassRep (Class rC) uf =
  case Map.lookup rC (ufsMap uf) of
    Just (Rep ne sz d) ->
      (ne, sz, d)
    Just (NonRep i) ->
      errorBecause $ unlines
        [ "not associated with a class representative,"
        , "but rather an element with index " ++ show i
        ]
    Nothing ->
      errorBecause "not found in map"
  where
    errorBecause msg = error $
      "lookupClassRep: Equivalence class index " ++ show rC ++ " " ++ msg

-- | Creates a new class with the given descriptor.
freshClass :: d -> Action d (Class d)
freshClass d = UF $ do
  UFS { ufsCount = c, ufsMap = m } <- get
  put UFS { ufsCount = c + 1, ufsMap = Map.insert c (Rep [] 1 d) m }
  return $ Class c

-- | Return true if two classes are equal.
areEqual :: Class d -> Class d -> Action d Bool
areEqual cx cy = do
  Class rx <- classRep cx
  Class ry <- classRep cy
  return (rx == ry)

toClassIdx :: Class d -> ClassIndex
toClassIdx (Class c) = c

data AssertResult = AssertSuccess | AssertFailed | AssertRedundant
  deriving (Eq, Show)

assertSucceeded :: AssertResult -> Bool
assertSucceeded AssertSuccess = True
assertSucceeded AssertFailed = False
assertSucceeded AssertRedundant = True

-- | Attempt to set two equivalence classes to be equal.
-- Returns true if attempt succeeded, and false is classes are
-- previously set inequal.
setEqual :: Class d
         -> Class d
         -> d -- ^ Descriptor for union class.
         -> Action d AssertResult
setEqual x y d = do
  xc@(Class xr) <- classRep x
  yc@(Class yr) <- classRep y
  if xr == yr
    then return AssertRedundant
    else do
      uf <- UF get
      let (xne, xsz, _xd) = lookupClassRep xc uf
      let (yne, ysz, _yd) = lookupClassRep yc uf
      xElts <- fmap (map toClassIdx) $ mapM classRep (map Class xne)
      yElts <- fmap (map toClassIdx) $ mapM classRep (map Class yne)
      if xr `elem` yElts || yr `elem` xElts
        then return AssertFailed
        else do
          let neqs = Set.toList $ Set.fromList $ xElts ++ yElts
          UF $ modify $ \s ->
            if xsz < ysz
              then do
                s { ufsMap =
                      Map.insert xr (NonRep yr) $
                        Map.insert yr (Rep neqs (xsz + ysz) d) $
                         ufsMap s }
              else do
                s { ufsMap =
                      Map.insert xr (Rep neqs (xsz + ysz) d) $
                        Map.insert yr (NonRep xr) $
                         ufsMap s }
          return AssertSuccess

-- | Attempt to set two equivalence classes to be unequal.
-- Returns true if attempt succeeded, and false is classes are
-- previously set equal.
setUnequal :: Class d -> Class d -> Action d AssertResult
setUnequal x y = do
  xc@(Class xr) <- classRep x
  yc@(Class yr) <- classRep y
  if xr == yr
    then return AssertFailed
    else do
      uf <- UF get
      let (xne, xsz, xd) = lookupClassRep xc uf
      let (yne, _,   _)  = lookupClassRep yc uf
      xElts <- fmap (map toClassIdx) $ mapM classRep (map Class xne)
      yElts <- fmap (map toClassIdx) $ mapM classRep (map Class yne)
      if xr `elem` yElts || yr `elem` xElts
       then return AssertRedundant
       else do
         UF $ modify $ \s -> s { ufsMap = Map.insert xr (Rep (yr:xne) xsz xd) (ufsMap s) }
         return AssertSuccess

-- Class descriptions {{{1

-- | Get a class description
readClassDesc :: Class d -> Action d d
readClassDesc c = do
  rCls <- classRep c
  s <- UF get
  let (_, _, desc) = lookupClassRep rCls s
  return desc

-- | Set a class description
writeClassDesc :: Class d -> d -> Action d ()
writeClassDesc c d = do
  rCls@(Class rC) <- classRep c
  UF $ modify $ \s ->
    let (dis, sz, _) = lookupClassRep rCls s
     in s { ufsMap = Map.insert rC (Rep dis sz d) (ufsMap s) }

-- | Modify a class description
modifyClassDesc :: Class d -> (d -> d) -> Action d ()
modifyClassDesc c fn = do
  rCls@(Class rC) <- classRep c
  UF $ modify $ \s ->
    let (dis, sz, desc) = lookupClassRep rCls s
     in s { ufsMap = Map.insert rC (Rep dis sz (fn desc)) (ufsMap s) }
