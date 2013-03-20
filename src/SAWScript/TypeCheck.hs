{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}

module SAWScript.TypeCheck where

import SAWScript.Compiler (Compiler (..), compiler)

import SAWScript.AST
import SAWScript.Unify

import SAWScript.LiftPoly (instantiateType,Lifted(..))

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

typeCheck :: Compiler Lifted (Module LType)
typeCheck = compiler "TypeCheck" $ \(Lifted m gen env) ->
  case instantiateGoal gen $ getGoal env m of
    Left es   -> fail $ unlines es
    Right [r] -> return r
    Right rs  -> fail $ unlines ("Ambiguous typing:" : map show rs)

getGoal :: [(Name,GoalM LType LType)] -> Module LType -> GoalM LType (Module LType)
getGoal env m@(Module ds _) = flip runReaderT (newPolyEnv env <> F.foldMap buildEnv ds) $ do
  (Module ds' mn') <- tCheck m
  logic (Module <$> mapM resolve ds' <*> resolve mn')

instantiateGoal :: Int -> GoalM LType a -> Either [String] [a]
instantiateGoal gen = fromStream Nothing Nothing . fmap fst . flip runStateT (gen,emptyS) . runGoalM

logic :: GoalM LType a -> TC a
logic = ReaderT . const

resolve :: (T.Traversable t) => t LType -> GoalM LType (t LType)
resolve = T.traverse walkStar

type TC a = ReaderT TCEnv (GoalM LType) a

-- Env {{{

data TCEnv = TCEnv
  { exprEnv :: [(Name,Expr LType)]
  , polyEnv :: [(Name,GoalM LType LType)]
  } deriving (Show)

instance Monoid TCEnv where
  mempty = TCEnv mempty mempty
  mappend e1 e2 = TCEnv (exprEnv e1 <> exprEnv e2) (polyEnv e1 <> polyEnv e2)

newPolyEnv :: [(Name,GoalM LType LType)] -> TCEnv
newPolyEnv = TCEnv []

exprPair :: Name -> Expr LType -> TCEnv
exprPair n e = TCEnv [(n,e)] []

polyPair :: Name -> GoalM LType LType -> TCEnv
polyPair n g = TCEnv [] [(n,g)]

buildEnv :: TopStmt LType -> TCEnv
buildEnv s = case s of
  TopTypeDecl n pt -> polyPair n $ instantiateType pt
  TopBind n e      -> exprPair n e
  _                -> mempty

extendType :: Name -> Expr LType -> TC a -> TC a
extendType n e m = local (exprPair n e <>) m

lookupExpr :: Name -> TC (Maybe (Expr LType))
lookupExpr n = asks $ lookup n . exprEnv

extendPoly :: Name -> PType -> TC a -> TC a
extendPoly n pt m = local (polyPair n (instantiateType pt) <>) m

lookupPoly :: Name -> TC (Maybe (GoalM LType LType))
lookupPoly n = asks $ lookup n . polyEnv

-- }}}

class TypeCheck f where
  tCheck :: f -> TC f

instance TypeCheck (Module LType) where
  tCheck (Module ds mn) = do
    ds' <- mapM tCheck ds
    mn' <- tCheck mn
    return (Module ds' mn')

instance TypeCheck (TopStmt LType) where
  tCheck ts = case ts of
    TopBind n e -> do e' <- tCheck e
                      return (TopBind n e')
    _           -> return ts

instance TypeCheck [BlockStmt LType] where
  tCheck mb = case mb of
    []    -> return []
    s:mb' -> case s of
      Bind Nothing c e   -> do e' <- tCheck e
                               rest <- tCheck mb'
                               return (Bind Nothing c e' : rest)
      Bind (Just n) c e  -> do e' <- tCheck e
                               rest <- extendType n e' $ tCheck mb'
                               return (Bind (Just n) c e' : rest)
      BlockTypeDecl n pt -> do rest <- extendPoly n pt $ tCheck mb'
                               return (BlockTypeDecl n pt : rest)
      BlockLet nes       -> let (ns,es) = unzip nes in do
                               es' <- mapM tCheck es
                               rest <- (compose $ uncurry extendType) (zip ns es') $ tCheck mb'
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
                               []     -> do a <- logic newLVar
                                            t `typeEqual` array a l
                               at:ts' -> mapM_ (typeEqual at) ts' >> t `typeEqual` array at l
                             return (Array es' t)
    Block ss t         -> do ss' <- tCheck ss
                             let cs = mapMaybe context ss'
                             (c,bt) <- finalStmtType $ last ss'
                             logic $ assert (all (== c) cs) ("Inconsistent contexts: " ++ show cs)
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
                             l <- logic newLVar
                             at `typeEqual` array t l
                             it `typeEqual` z
                             return (Index ar' ix' t)
    Lookup r n t       -> do r' <- tCheck r
                             let rt = decor r'
                             logic (rt `subtype` record [(n,t)])
                             return (Lookup r' n t)
    Var n t            -> do foundE <- fmap decor <$> lookupExpr n
                             foundT <- lookupPoly n
                             case (foundT,foundE) of
                               (Just g,_) -> do
                                 lt <- logic g
                                 t `typeEqual` lt
                               (_,Just lt) -> t `typeEqual` lt
                               (Nothing,Nothing) -> logic $ fail ("Unbound variable: " ++ n)
                             return (Var n t)
    Function an at b t -> do b' <- extendType an (Var an at) $ tCheck b
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
                             b' <- (compose $ uncurry extendType) (zip ns es') $ tCheck b
                             return (LetBlock (zip ns es') b')

whenJust :: Monad m => (a -> m ()) -> Maybe a -> m ()
whenJust f m = case m of
  Just a  -> f a
  Nothing -> return ()

typeEqual :: LType -> LType -> TC ()
typeEqual u v = logic $ u === v

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

compose :: (a -> b -> b) -> [a] -> b -> b
compose f as = case as of
  []    -> id
  a:as' -> f a . compose f as'

finalStmtType :: BlockStmt LType -> TC (Context,LType)
finalStmtType s = case s of
  Bind Nothing c e -> return (c,decor e)
  _                -> logic $ fail ("Final statement of do block must be an expression: " ++ show s)

