{-# LANGUAGE MultiParamTypeClasses, KindSignatures #-}

module SAWScript.LiftPoly where

import SAWScript.AST

import Control.Monad.State
import Control.Applicative
import Control.Arrow (first,second)

type LS = State (Int,[(Name,Int)])

liftPoly :: Module PType -> Module LType
liftPoly m = evalState (lp m) (0,[])

class LiftPoly (a :: * -> *) where
  lp :: a PType -> LS (a LType)

instance LiftPoly Module where
  lp m = pure Module <*> (mapM (saveEnv . lp) $ declarations m) <*> (mapM (saveEnv . lp) $ main m)

instance LiftPoly TopStmt where
  lp s = case s of
    Import n is n'  -> pure $ Import n is n'
    TopLet bs       -> TopLet                <$> lBinds bs
    TypeDef n t     -> TypeDef n                           <$> assignVar t
    TopTypeDecl n t -> TopTypeDecl n                       <$> assignVar t

instance LiftPoly BlockStmt where
  lp s = case s of
    Bind mn e         -> Bind mn           <$> lp e
    BlockLet bs       -> BlockLet          <$> lBinds bs
    BlockTypeDecl n t -> BlockTypeDecl n                 <$> assignVar t

instance LiftPoly Expr where
  lp e = case e of
    Bit b t               -> Bit b   <$> assignVar t
    Quote s t             -> Quote s <$> assignVar t
    Z i t                 -> Z i     <$> assignVar t

    Array es t            -> Array  <$> mapM lp es <*> assignVar t
    Block ss t            -> Block  <$> mapM lp ss <*> assignVar t
    Tuple es t            -> Tuple  <$> mapM lp es <*> assignVar t
    Record fs t           -> Record <$> lBinds  fs <*> assignVar t

    Index a i t           -> Index  <$> lp a <*> lp i   <*> assignVar t
    Lookup r f t          -> Lookup <$> lp r <*> pure f <*> assignVar t

    Var n t               -> Var n                                    <$> assignVar t
    Function an at body t -> Function an <$> assignVar at <*> lp body <*> assignVar t
    Application f v t     -> Application <$> lp f         <*> lp v    <*> assignVar t

    LetBlock bs body      -> LetBlock <$> lBinds bs <*> lp body

assignVar :: PType -> LS LType
assignVar pt = case pt of
  NoAnn   -> newLVar
  Poly n  -> do mi <- gets2 (lookup n)
                case mi of
                  Just i  -> return (LVar i)
                  Nothing -> do x@(LVar i) <- newLVar
                                extendEnv n i
                                return x
  Annot t -> Term <$> fixmapM assignVar t

newLVar :: LS LType
newLVar = do
  n <- get1
  modify1 succ
  return (LVar n)

extendEnv :: Name -> Int -> LS ()
extendEnv n i = modify2 ((n,i):)

lBinds :: [(Name,Expr PType)] -> LS [(Name,Expr LType)]
lBinds = onSnd lp

lArgs :: [(Name,PType)] -> LS [(Name,LType)]
lArgs = onSnd assignVar

saveEnv = save2

-- Helpers

onSnd :: Monad m => (b -> m c) -> [(a,b)] -> m [(a,c)]
onSnd f xs = let (as,bs) = unzip xs in
  mapM f bs >>= return . zip as

save1 :: State (a,b) r -> State (a,b) r
save1 m = do
  s1 <- get1
  a <- m
  put1 s1
  return a

save2 :: State (a,b) r -> State (a,b) r
save2 m = do
  s2 <- get2
  a <- m
  put2 s2
  return a

modify1 :: (a -> a) -> State (a,b) ()
modify1 f = modify $ first f

modify2 :: (b -> b) -> State (a,b) ()
modify2 f = modify $ second f

gets1 :: (a -> c) -> State (a,b) c
gets1 f = gets (f . fst)

gets2 :: (b -> c) -> State (a,b) c
gets2 f = gets (f . snd)

get1 = gets1 id
get2 = gets2 id

put1 s = modify1 $ const s
put2 s = modify2 $ const s

-- Test Data

-- liftPoly m1 == liftPoly m2, since Poly environment is not saved between module-level statements, both top and block.

m1 = Module
  { declarations =
    [ Import "Foo" Nothing Nothing
    , TypeDef "Test" (Annot Bit')
    , TopTypeDecl "map4" (Annot (Function' (Annot (Function' (Poly "a") (Poly "b"))) (Annot (Function' (Annot (Array' (Poly "a") 4)) (Annot (Array' (Poly "b") 4))))))
    , TopTypeDecl "a1" (Annot (Array' (Annot Z') 4))
    , TopTypeDecl "plus1" (Annot (Function' (Annot Z') (Annot Z')))
    ]
  , main = 
    [ Bind Nothing (Application (Var "map4" NoAnn) (Var "a1" NoAnn) NoAnn)
    ]
  }

m2 = Module
  { declarations =
    [ Import "Foo" Nothing Nothing
    , TypeDef "Test" (Annot Bit')
    , TopTypeDecl "map4" (Annot (Function' (Annot (Function' (Poly "a") (Poly "b"))) (Annot (Function' (Annot (Array' (Poly "a") 4)) (Annot (Array' (Poly "b") 4))))))
    , TopTypeDecl "a1" (Annot (Array' (Annot Z') 4))
    , TopTypeDecl "plus1" (Annot (Function' (Annot Z') (Annot Z')))
    ]
  , main = 
    [ Bind Nothing (Application (Var "map4" NoAnn) (Var "a1" NoAnn) (Poly "b"))
    ]
  }

