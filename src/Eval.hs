
type Name = String
type Label = Maybe Name

newtype Bits = Bits [Bool] deriving (Eq,Show)

type ExprType = ()

data Expr
  = BitLiteral Bits
  | DM [(Label,Expr)]
  | Var Name
--  | Func Name (Maybe ExprType) Expr
  | Func Name Expr
  | App Expr Expr
  deriving (Eq,Show)

type Env = [(Name,Expr)]

data Eval a = Eval (Env -> (a,Env))

instance Functor Eval where
  fmap f (Eval m) = Eval $ \e -> let (a,e') = m e in (f a,e')

instance Monad Eval where
  return a = Eval $ \e -> (a,e)
  (Eval m) >>= f = Eval $ \e ->
    let (a,e') = m e in
      let (Eval m') = f a in
        m' e' 

eval :: Env -> Expr -> Expr
eval env e = case e of
  BitLiteral b  -> BitLiteral b
  DM es         -> DM $ evalDM env es
  Var n         -> case lookup n env of
                     Just a  -> a
                     Nothing -> error ("unbound var: " ++ n)
  Func x body -> Func x body
  App e1 e2     -> let e1' = eval env e1 in
                     let e2' = eval env e2 in
                       case e1' of
                         Func x body -> eval (extend x e2' env) body
                         _             -> error "application of non-function"

evalDM :: Env -> [(Label,Expr)] -> [(Label,Expr)]
evalDM env es = case es of
  []                   -> []
  ((na@(Nothing),e):es') -> let e' = eval env e in
                            (na,e') : evalDM env es'
  ((na@(Just n),e):es')  -> let e' = eval env e in
                            (na,e') : evalDM (extend n e' env) es'

extend :: Name -> Expr -> Env -> Env
extend x a env = (x,a) : env

