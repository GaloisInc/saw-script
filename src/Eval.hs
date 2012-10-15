
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

data Eval a = Eval (Env -> (Either String (a,Env)))

runEval :: Env -> Expr -> Either String Expr
runEval env e = let (Eval m) = evalM e in
  case m env of
    Left err    -> Left err
    Right (e,_) -> Right e

instance Functor Eval where
  fmap f (Eval m) = Eval $ \e ->
    let mae = m e in
      case mae of
        Right (a,e') -> Right (f a,e')
        Left err     -> Left err

instance Monad Eval where
  return a       = Eval $ \e -> Right (a,e)
  (Eval m) >>= f = Eval $ \e ->
    let mae = m e in
      case mae of
        Right (a,e') -> let (Eval m') = f a in m' e'
        Left err     -> Left err

get :: Eval Env
get = Eval $ \e -> Right (e,e)
put :: Env -> Eval ()
put e' = Eval $ \e -> Right ((),e')
failure :: String -> Eval a
failure err = Eval $ \e -> Left err

evalM :: Expr -> Eval Expr
evalM e = case e of
  BitLiteral b -> return (BitLiteral b)
  DM es        -> do saved <- get
                     es' <- evalMDM es
                     put saved
                     return (DM es')
  Var n        -> lookupM n
  Func x body  -> return (Func x body)
  App e1 e2    -> do saved <- get
                     e2' <- evalM e2
                     put saved
                     e1' <- evalM e1
                     case e1' of
                       Func x body -> do extendM x e2'
                                         body' <- evalM body
                                         put saved
                                         return body'
                       _           -> failure "Application of non-procedure"

evalMDM :: [(Label,Expr)] -> Eval [(Label,Expr)]
evalMDM es = case es of
  []                -> return []
  ((Nothing,e):es') -> do e' <- evalM e
                          evalMDM es'
  ((Just n,e):es')  -> do e' <- evalM e
                          extendM n e'
                          evalMDM es'

extendM :: Name -> Expr -> Eval ()
extendM x a = do e <- get
                 put ((x,a):e)

lookupM :: Name -> Eval Expr
lookupM n = do
  env <- get
  case lookup n env of
    Just a  -> return a
    Nothing -> failure ("unbound var: " ++ n)

------------------------------------

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

