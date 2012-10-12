
import Data.List (intercalate)

---------------
-- Test Data --
---------------

t1 = BitLit $ int8 10
t2 = Bag [("x",BitLit $ int8 7)]
t3 = Func [("x",BitLitT)] (Var ["x"])
t4 = App t3 [t1]
t5 = App t3 [t2]
t6 = Func [("x",BitLitT),("y",BitLitT)] (Var ["x"])
t7 = Bag [("main",Cmd $ Seq (Return t1) "x" (Return $ Var ["x"]))]

-----------------
-- Expressions --
-----------------

data Expr
  = BitLit Bits
  | Bag [(String,Expr)]
  | Cmd Cmd
  | Var [String]
  | Func [(String,ExprType)] Expr
  | App Expr [Expr]
  deriving Eq

data Cmd
  = Return Expr
  | Seq Cmd String Cmd
  deriving Eq

newtype Bits = Bits [Bool] deriving Eq

instance Show Expr where
  show e = case e of
    BitLit bs    -> show bs
    Bag b        -> wrapLoose '{' '}' " , " showPair b
      where
        showPair (s,e) = s ++ " = " ++ show e
    Var ss       -> intercalate "." ss
    Cmd c        -> "[" ++ show c ++ "]"
    App e1 e2    -> showCall (e1:e2)
      where
        showCall :: [Expr] -> String
        showCall as = wrapClose '(' ')' " " show as
    Func args e  -> "(\\" ++ showArgs args ++ " -> " ++ show e ++ ")"
      where
        showArgs :: [(String,ExprType)] -> String
        showArgs = wrapLoose '(' ')' " , " showPair
        showPair (name,et) = name ++ " :: " ++ show et

instance Show Cmd where
  show c = case c of
    Return e    -> "return " ++ show e
    Seq c1 s c2 -> s ++ " <- " ++ show c1 ++ "; " ++ show c2

instance Show Bits where
  show (Bits bs) = cs `seq` ("0b" ++ cs)
    where
      cs            = concat $ map bitToString bs
      bitToString b = case b of
        True  -> "1"
        False -> "0"

-----------
-- Types --
-----------

data ExprType
  = BitLitT
  | BagT [(String,ExprType)]
  | CmdT CmdType
  | FuncT [(String,ExprType)] ExprType
  deriving Eq

data CmdType
  = RetT ExprType
  deriving Eq

instance Show ExprType where
  show et = case et of
    BitLitT -> "BitLit"
    BagT bt -> wrapLoose '{' '}' " , " showPair bt
    CmdT ct -> show ct
    FuncT [et1] et -> "(" ++ (show $ snd et1) ++ " -> " ++ show et ++ ")"
    FuncT ets et -> "(" ++ (wrapClose '(' ')' ", " show $ map snd ets) ++ " -> " ++ show et ++ ")"
    where
      showPair (s,et) = s ++ " :: " ++ show et

instance Show CmdType where
  show (RetT et) = "(Cmd " ++ show et ++ ")"

type Env = [(String,ExprType)]
emptyEnv = []
extendEnv = (++)

data Exc a = Success a | Failure String
instance Show a => Show (Exc a) where
  show e = case e of
    Failure err -> "Error: " ++ err
    Success a -> show a
instance Functor Exc where
  fmap f e = case e of
    Success a -> Success $ f a
    Failure e -> Failure e
instance Monad Exc where
  return = Success
  m >>= f = case m of
    Success a -> f a
    Failure e -> Failure e
failure = Failure

typeOf :: Expr -> Exc ExprType
typeOf = typeOfExpr emptyEnv

typeOfExpr :: Env -> Expr -> Exc ExprType
typeOfExpr env e = case e of
  BitLit b   -> return BitLitT
  Bag b      -> do bt <- mapM (\(s,e)->do et <- typeOfExpr env e; return (s,et)) b
                   return (BagT bt)
  Var []     -> failure "empty reference"
  Var [s]    -> case lookup s env of
                  Just a -> return a
                  Nothing -> failure ("unbound var: " ++ s)
  Var (s:ss) -> case lookup s env of
                  Just a -> typeOfExpr env (Var ss) 
                  Nothing -> failure ("unbound var: " ++ s)
  Cmd c      -> do ct <- typeOfCmd env c
                   return (CmdT ct)
  Func as e  -> do et <- typeOfExpr (extendEnv env as) e
                   return (FuncT as et)
  App e es   -> do t <- typeOfExpr env e
                   ets <- mapM (typeOfExpr env) es
                   case t of
                      FuncT ets' et -> if matchArgTypes (map snd ets') ets then return et else failure "type mismatch"
                      _             -> failure ("not a function: " ++ show e)
    where
      matchArgTypes :: [ExprType] -> [ExprType] -> Bool
      matchArgTypes must has = all (`elem` has) must
                   
typeOfCmd :: Env -> Cmd -> Exc CmdType
typeOfCmd env c = case c of
  Return e    -> do et <- typeOfExpr env e
                    return (RetT et)
  Seq c1 x c2 -> do (RetT et1) <- typeOfCmd env c1
                    typeOfCmd ((x,et1):env) c2

-------------
-- Helpers --
-------------

int8 = fromInt 8

int16 = fromInt 16

fromInt :: Int -> Int -> Bits
fromInt size n
  | n < 0           = error "must be non-negative"
  | n >= (2 ^ size) = error "insufficient bitfield size"
  | otherwise       = Bits $ pad size $ reverse $ fromInt' n
  where
    fromInt' :: Int -> [Bool]
    fromInt' n = case n of
      0 -> []
      _  | odd n     -> True : fromInt' ((n - 1) `div` 2)
         | otherwise -> False : fromInt' (n `div` 2)
    pad :: Int -> [Bool] -> [Bool]
    pad n bs = if l >= n
                  then bs
                  else (replicate (n - l) False) ++ bs
      where l = length bs

wrapClose f s sep as = wrap False f s sep as
wrapLoose f s sep as = wrap True f s sep as

wrap :: Show a => Bool -> Char -> Char -> String -> (a -> String) -> [a] -> String
wrap loose f s sep sf as = case as of
  []      -> [f,s]
  (a:as') -> let (_:r@(n:rest)) = wrap loose f s sep sf as' in
               (if loose then [f,' '] else [f]) ++
                 sf a ++
                 if n == s
                   then (if loose then " " ++ r else r)
                   else sep ++ (if loose then rest else r)

