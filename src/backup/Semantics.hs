
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
  | Var Name
  | Func [(String,ExprType)] Expr
  | App Expr [Expr]
  deriving Eq

data Name
  = Name String
  | In String Name
  deriving Eq

data Cmd
  = Return Expr
  | Seq Cmd String Cmd
  deriving Eq

newtype Bits = Bits ![Bool] deriving Eq

instance Show Expr where
  show e = case e of
    BitLit bs    -> show bs
    Bag b        -> wrapLoose '{' '}' " , " showPair b
      where
        showPair (s,e) = s ++ " = " ++ show e
    Var n        -> show n
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

instance Show Name where
  show n = case n of
    Name s -> s
    In r n -> r ++ "." ++ show n

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
  | CmdT ExprType
  | FuncT [(String,ExprType)] ExprType
  deriving Eq

instance Show ExprType where
  show et = case et of
    BitLitT -> "BitLit"
    BagT bt -> wrapLoose '{' '}' " , " showPair bt
    CmdT ct -> "(Cmd " ++ show ct ++ ")"
    FuncT [et1] et -> "(" ++ (show $ snd et1) ++ " -> " ++ show et ++ ")"
    FuncT ets et -> "(" ++ (wrapClose '(' ')' ", " show $ map snd ets) ++ " -> " ++ show et ++ ")"
    where
      showPair (s,et) = s ++ " :: " ++ show et

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
typeOf = typeOf emptyEnv

typeOf :: Env -> Expr -> Exc ExprType
typeOf env e = case e of
  BitLit b     -> return BitLitT
  Bag b        -> do bt <- mapM (\(s,e)->do et <- typeOf env e; return (s,et)) b
                     return (BagT bt)
  Var (Name n) -> case lookup n env of
                    Just a -> return a
                    Nothing -> failure ("unbound var: " ++ n)
  -- FIXME
  Var (In r n) -> case lookup r env of
                    Just a -> typeOf env (Var n)
                    Nothing -> failure ("unbound var: " ++ r)
  Cmd c        -> do ct <- typeOfCmd env c
                     return (CmdT ct)
  Func as e    -> do et <- typeOf (extendEnv env as) e
                     return (FuncT as et)
  App e es     -> do t <- typeOf env e
                     ets <- mapM (typeOf env) es
                     case t of
                        FuncT ets' et -> if matchArgTypes ets $ map snd ets'
                                           then return et
                                           else failure "type mismatch"
                        _             -> failure ("not a function: " ++ show e)

matchArgTypes :: [ExprType] -> [ExprType] -> Bool
matchArgTypes has exp = case (has,exp) of
  ([],[])         -> True
  (h:has',e:exp') -> (h `matchType` e) && (matchArgTypes has' exp')
  _               -> False

-- FIXME
matchType :: ExprType -> ExprType -> Bool
matchType = undefined

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

