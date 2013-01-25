{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.TypeCheck where

import SAWScript.Compiler

import SAWScript.AST
import SAWScript.Unify

import SAWScript.LiftPoly (runLS,assignVar)

import Control.Applicative
import Control.Arrow
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Control.Monad

import Data.List
import Data.Monoid
import Data.Maybe
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import qualified Debug.Trace as Debug

typeCheck :: Compiler (Module LType,Int) (Module LType)
typeCheck = compiler "TypeCheck" $ \(m,gen) ->
  case runGoal gen $ getGoal m of
    Left es   -> fail $ unlines es
    Right [r] -> return r
    Right rs  -> fail $ unlines ("Ambiguous typing:" : map show rs)
  where
  getGoal m@(Module ds _) = flip runReaderT (env ds) (tCheck m >>= liftReader . T.traverse walkStar)
  runGoal gen = fromStream Nothing Nothing . fmap fst . flip runStateT (gen,emptyS) . runGoalM
  env ds = F.foldMap buildEnv ds

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
    Unit t             -> t `typeEqual` unit  >> return (Unit t)
    Bit b t            -> t `typeEqual` bit   >> return (Bit b t)
    Quote s t          -> t `typeEqual` quote >> return (Quote s t)
    Z i t              -> t `typeEqual` z     >> return (Z i t)
    Array es t         -> do es' <- mapM tCheck es
                             let l = i $ length es
                                 ts = map decor es'
                             case ts of
                               []     -> do a <- liftReader newLVar
                                            t `typeEqual` array a l
                               at:ts' -> mapM_ (typeEqual at) ts' >> t `typeEqual` array at l
                             return (Array es' t)
    Block ss t         -> do ss' <- tCheck ss
                             let cs = mapMaybe context ss'
                             (c,bt) <- finalStmtType $ last ss'
                             liftReader $ assert (all (== c) cs) ("Inconsistent contexts: " ++ show cs)
                             t `typeEqual` block c bt
                             return (Block ss' t)
    Tuple es t         -> do es' <- mapM tCheck es
                             let ts = map decor es'
                             t `typeEqual` tuple ts
                             return (Tuple es' t)
    Record nes t       -> do let (ns,es) = unzip nes
                             es' <- mapM tCheck es
                             let ts = map decor es'
                             t `typeEqual` record (zip ns ts)
                             return (Record (zip ns es') t)
    Index ar ix t      -> do ar' <- tCheck ar
                             ix' <- tCheck ix
                             let at = decor ar'
                             let it = decor ix'
                             l <- liftReader newLVar
                             at `typeEqual` array t l
                             it `typeEqual` z
                             return (Index ar' ix' t)
    Lookup r n t       -> do r' <- tCheck r
                             let rt = decor r'
                             liftReader (rt `subtype` record [(n,t)])
                             return (Lookup r' n t)
    Var n t            -> do foundT <- asks (lookup n . lEnv)
                             foundP <- asks (lookup n . pEnv)
                             case foundT of
                               Just lt -> t `typeEqual` lt
                               Nothing -> case foundP of
                                 Just pt -> do lt <- liftReader $ instantiate pt
                                               t `typeEqual` lt
                                 Nothing -> liftReader $ fail ("Unbound variable: " ++ n)
                             return (Var n t)
    Function an at b t -> do b' <- extendType an at $ tCheck b
                             let bt = decor b'
                             t `typeEqual` function at bt
                             return (Function an at b' t)
    Application f v t  -> do f' <- tCheck f
                             v' <- tCheck v
                             let ft = decor f'
                             let vt = decor v'
                             ft `typeEqual` function vt t
                             return (Application f' v' t)
    LetBlock nes b     -> do let (ns,es) = unzip nes
                             es' <- mapM tCheck es
                             let ts = map decor es'
                             b' <- (compose $ uncurry extendType) (zip ns ts) $ tCheck b
                             return (LetBlock (zip ns es') b')

typeEqual :: LType -> LType -> TC ()
typeEqual u v = liftReader $ u === v
{-
  u' <- resolveSyn u
  v' <- resolveSyn v
  liftReader (u' === v')

resolveSyn :: LType -> TC LType
resolveSyn u = mcond
  [ (do Syn n <- match u; return n) :>: \n -> do foundP <- asks $ lookup n . pEnv
                                                 liftReader $
                                                   case foundP of
                                                     Just pt -> instantiate pt
                                                     Nothing -> fail ("Unbound type variable: " ++ n)
  , Else                           $  return u
  ]
-}

subtype :: LType -> LType -> Goal LType
subtype t1 t2 = 
  do Record' nts1 <- matchGoal t1
     Record' nts2 <- matchGoal t2
     conj [ disj [ guard (n1 == n2) >> t1 === t2
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

finalStmtType :: BlockStmt LType -> TC (Context,LType)
finalStmtType s = case s of
  Bind Nothing c e -> return (c,decor e)
  _                -> liftReader $ fail ("Final statement of do block must be an expression: " ++ show s)

liftReader :: (Monad m) => m a -> ReaderT r m a
liftReader m = ReaderT $ \r -> m

