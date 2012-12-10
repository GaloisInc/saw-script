{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.TypeCheck where

import SAWScript.AST
import SAWScript.Unify

import SAWScript.LiftPoly (runLS, assignVar,ModuleGen)

import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad

import Data.List
import Data.Monoid
import Data.Maybe
import qualified Data.Foldable as Fold
import qualified Data.Traversable as Trav

import qualified Debug.Trace as Debug

typeCheck :: ModuleGen -> Err (Module LType)
typeCheck (m@(Module ds mb),gen) = case res of
  Left es   -> Left $ intercalate "\n" ("TypeCheck:" : (es ++ [ "in:" , show m ]))
  Right [r] -> Right r
  Right rs  -> Left $ intercalate "\n" ("TypeCheck: Ambiguous typing:" : map show rs)
  where
    res = fromStream Nothing Nothing $ fmap fst $ runStateT (runGoalM goal) (gen,emptyS)
    goal = runReaderT
             (do m' <- tCheck m
                 liftReader (Trav.traverse walkStar m'))
             env
    env = Fold.foldMap buildEnv ds

type TC a = ReaderT Env (GoalM LType) a

-- Env {{{

data Env = Env
  { lEnv :: [(Name,LType)]
  , pEnv :: [(Name,PType)]
  } deriving Show

instance Monoid Env where
  mempty = Env [] []
  mappend (Env l1 p1) (Env l2 p2) = Env (l1 ++ l2) (p1 ++ p2)

buildEnv :: TopStmt LType -> Env
buildEnv s = case s of
  TypeDef n pt     -> Env { pEnv = [(n,pt)] , lEnv = [] }
  TopTypeDecl n pt -> Env { pEnv = [(n,pt)] , lEnv = [] }
  TopLet nes       -> Env { pEnv = []       , lEnv = map (fmap decor) $ nes }
  Import _ _ _     -> mempty

extendType :: Name -> LType -> TC a -> TC a
extendType n lt m = local (\e -> e { lEnv = (n,lt) : lEnv e }) m

extendPoly :: Name -> PType -> TC a -> TC a
extendPoly n pt m = local (\e -> e { pEnv = (n,pt) : pEnv e }) m

-- }}}

class TypeCheck f where
  tCheck :: f -> TC f -- possibly (f CType)

instance TypeCheck (Module LType) where
  tCheck (Module ds mb) = do
    ds' <- mapM tCheck ds
    mb' <- tCheck mb
    return (Module ds' mb')

instance TypeCheck (TopStmt LType) where
  tCheck ts = case ts of
    TopLet nes -> let (ns,es) = unzip nes in do
                    es' <- mapM tCheck es
                    return (TopLet $ zip ns es')
    _          -> return ts

instance TypeCheck [BlockStmt LType] where
  tCheck mb = case mb of
    []    -> return []
    s:mb' -> case s of
      Bind Nothing c e   -> do e' <- tCheck e
                               rest <- tCheck mb'
                               return (Bind Nothing c e' : rest)
      Bind (Just n) c e  -> do e' <- tCheck e
                               let et = decor e'
                               rest <- extendType n et $ tCheck mb'
                               return (Bind (Just n) c e' : rest)
      BlockTypeDecl n pt -> do rest <- extendPoly n pt $ tCheck mb'
                               return (BlockTypeDecl n pt : rest)
      BlockLet nes       -> let (ns,es) = unzip nes in do
                               es' <- mapM tCheck es
                               rest <- (compose $ uncurry extendType) (zip ns $ map decor es') $ tCheck mb'
                               return (BlockLet (zip ns es') : rest)

instance TypeCheck (Expr LType) where
  tCheck e = case e of
    Bit b t            -> t `typeEqual` bit   >>= \(u,v) -> u === v>> return (Bit b t)
    Quote s t          -> t `typeEqual` quote >>= \(u,v) -> u === v>> return (Quote s t)
    Z i t              -> t `typeEqual` z     >>= \(u,v) -> u === v>> return (Z i t)
    Array es t         -> do es' <- mapM tCheck es
                             let l = i $ length es
                                 ts = map decor es'
                             liftReader (case ts of
                                           [] -> fresh $ \a -> t === array a l
                                           at:ts' -> mapM_ (=== at) ts' >> t === array at l)
                             return (Array es' t)
    Block ss t         -> do ss' <- tCheck ss
                             let cs = mapMaybe context ss'
                             liftReader (do (c,bt) <- finalStmtType $ last ss'
                                            assert (all (== c) cs) ("Inconsistent contexts: " ++ show cs)
                                            t === block c bt)
                             return (Block ss' t)
    Tuple es t         -> do es' <- mapM tCheck es
                             let ts = map decor es'
                             liftReader (t === tuple ts)
                             return (Tuple es' t)
    Record nes t       -> do let (ns,es) = unzip nes
                             es' <- mapM tCheck es
                             let ts = map decor es'
                             liftReader (t === record (zip ns ts))
                             return (Record (zip ns es') t)
    Index ar ix t      -> do ar' <- tCheck ar
                             ix' <- tCheck ix
                             let at = decor ar'
                             let it = decor ix'
                             liftReader (fresh $ \l -> do
                                           at === array t l
                                           it === z)
                             return (Index ar' ix' t)
    Lookup r n t       -> do r' <- tCheck r
                             let rt = decor r'
                             liftReader (rt `subtype` record [(n,t)])
                             return (Lookup r' n t)
    Var n t            -> do foundT <- asks (lookup n . lEnv)
                             foundP <- asks (lookup n . pEnv)
                             liftReader (case foundT of
                                           Just lt -> t === lt
                                           Nothing -> case foundP of
                                             Just pt -> do lt <- instantiate pt
                                                           t === lt
                                             Nothing -> fail ("Unbound variable: " ++ n))
                             return (Var n t)
    Function an at b t -> do b' <- extendType an at $ tCheck b
                             let bt = decor b'
                             liftReader (t === function at bt)
                             return (Function an at b' t)
    Application f v t  -> do f' <- tCheck f
                             v' <- tCheck v
                             let ft = decor f'
                             let vt = decor v'
                             liftReader (do ft === function vt t)
                             return (Application f' v' t)
    LetBlock nes b     -> do let (ns,es) = unzip nes
                             es' <- mapM tCheck es
                             let ts = map decor es'
                             b' <- (compose $ uncurry extendType) (zip ns ts) $ tCheck b
                             return (LetBlock (zip ns es') b')

typeEqual :: LType -> LType -> TC (LType,LType)
typeEqual u v = do
  u' <- resolveSyn u
  v' <- resolveSyn v
  return (u',v')

resolveSyn :: LType -> TC LType
resolveSyn u = mcond
  [ do Syn n <- match u; return n :>: do foundP <- asks $ lookup n . pEnv
                                         liftReader $
                                           case foundP of
                                             Just pt -> instantiate pt
                                             Nothing -> fail ("Unbound type variable: " ++ n)
  , Else                           $  return u
  ]

subtype :: LType -> LType -> Goal LType
subtype t1 t2 = 
  do Record' nts1 <- matchGoal t1
     Record' nts2 <- matchGoal t2
     conj [ disj [ guard (n1 == n2) >> (t1 === t2)
                   | (n1,t1) <- nts1
                 ]
            | (n2,t2) <- nts2
          ]

matchGoal :: (g :<: f) => Mu f -> GoalM (Mu f) (g (Mu f))
matchGoal x = maybe mzero return (match x)

instantiate :: PType -> GoalM LType LType
instantiate = fmap fst . flip runLS [] . assignVar

compose :: (a -> b -> b) -> [a] -> b -> b
compose f as = case as of
  []    -> id
  a:as' -> f a . compose f as'

finalStmtType :: BlockStmt LType -> GoalM LType (Context,LType)
finalStmtType s = case s of
  Bind Nothing c e -> return (c,decor e)
  _                -> fail ("Final statement of do block must be an expression: " ++ show s)

liftReader :: (Monad m) => m a -> ReaderT r m a
liftReader m = ReaderT $ \r -> m

