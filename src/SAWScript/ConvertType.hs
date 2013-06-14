{-# LANGUAGE TypeOperators #-}

module SAWScript.ConvertType where

import SAWScript.Compiler

import SAWScript.AST
import SAWScript.Unify

import Control.Applicative
import Control.Monad
import qualified Data.Traversable as T

convertType :: Compiler (ModuleSimple TCheckT TCheckT) ValidModule
convertType = groundType >=> defixType >=> condenseDefix

varNames :: [String]
varNames = drop 1 (("" : names') ++ ((++) <$> varNames <*> names'))
  where
  names' = [ [c] | c <- ['a'..'z'] ]

-- groundTypeF {{{

groundType :: Compiler (ModuleSimple TCheckT TCheckT) (ModuleSimple FullT FullT)
groundType = compiler "GroundType" $ \(Module nm ee te ds) ->
  Module nm <$> T.traverse (traverseFA groundTypeF) ee <*> traverseFA groundTypeF te <*> pure ds

class Functor f => Groundable f where
  groundTypeF :: f FullT -> Err FullT

instance (Groundable f, Groundable g) => Groundable (f :+: g) where
  groundTypeF cp = case cp of
    Inl e -> groundTypeF e
    Inr e -> groundTypeF e

instance Groundable Logic where
  groundTypeF x = fail ("non-ground type: " ++ render x)

instance Groundable ContextF where
  groundTypeF = return . inject

instance Groundable TypeF where
  groundTypeF = return . inject

instance Groundable Poly where
  groundTypeF = return . inject

instance Groundable I where
  groundTypeF = return . inject

-- }}}

-- defixType {{{

data Defix
  = Int Integer
  | Ctx Context
  | Typ Type
  deriving (Show)

typs :: [Defix] -> [Type]
typs ds = [ t | (Typ t) <- ds ]

isTyp :: Defix -> Bool
isTyp (Typ _) = True
isTyp _ = False

allTyps :: [Defix] -> Bool
allTyps = all isTyp

defixType :: Compiler (ModuleSimple FullT FullT) (ModuleSimple Defix Defix)
defixType = compiler "DefixType" $ \(Module nm ee te ds) ->
  Module nm <$> T.traverse (traverseFA defixTypeF) ee <*> traverseFA defixTypeF te <*> pure ds

class Functor f => Defixable f where
  defixTypeF :: f Defix -> Err Defix

instance (Defixable f, Defixable g) => Defixable (f :+: g) where
  defixTypeF cp = case cp of
    Inl e -> defixTypeF e
    Inr e -> defixTypeF e

instance Defixable TypeF where
  defixTypeF typ = case typ of
    UnitF                           -> return $ Typ UnitT
    BitF                            -> return $ Typ BitT
    ZF                              -> return $ Typ ZT
    QuoteF                          -> return $ Typ QuoteT
    ArrayF (Typ t) (Int l)          -> return $ Typ $ ArrayT t l
    BlockF (Ctx c) (Typ t)          -> return $ Typ $ BlockT c t
    TupleF ts
      | allTyps ts                  -> return $ Typ $ TupleT $ typs ts
    RecordF nts
      | allTyps $ map snd nts       -> let (ns,ts) = unzip nts in
                                         return $ Typ $ RecordT $ zip ns $ typs ts
    FunctionF (Typ at) (Typ bt)     -> return $ Typ $ FunctionT at bt
    _                               -> fail $ "Bad type: " ++ show typ

instance Defixable ContextF where
  defixTypeF c = return $ Ctx $ case c of
    CryptolSetupContext -> CryptolSetup
    JavaSetupContext    -> JavaSetup
    LLVMSetupContext    -> LLVMSetup
    ProofScriptContext  -> ProofScript
    TopLevelContext     -> TopLevel

instance Defixable Poly where
  defixTypeF typ = case typ of
    PVar n          -> return $ Typ $ TypVar n
    PAbs ns (Typ t) -> return $ Typ $ TypAbs ns t
    _               -> fail $ "Bad type: " ++ show typ

instance Defixable I where
  defixTypeF (I x) = return $ Int x

-- }}}

-- condenseDefix {{{

condenseDefix :: Compiler (ModuleSimple Defix Defix) ValidModule
condenseDefix = compiler "RemoveEither" $ \(Module nm ee te ds) ->
  Module nm <$> T.traverse (T.traverse condense) ee <*> T.traverse condense te <*> pure ds

condense :: Defix -> Err Type
condense (Typ t) = return t
condense d  = fail ("nonsense type: " ++ show d)

-- }}}

{-
-- reifyDeclarations {{{

reifyDeclarations :: Compiler (ModuleSimple TCheckT Type) (ModuleSimple ResolvedT Type)
reifyDeclarations = compiler "ReifyDeclarations" $ \(Module mname ds mn) ->
  Module mname <$> mapM runRDecs ds <*> pure mn
  where
  runRDecs = return . flip evalState initRState . traverseFA reifyDeclarationsF

type RD = State ReifyState

class Functor f => ReifyDecs f where
  reifyDeclarationsF :: f ResolvedT -> RD ResolvedT

data ReifyState = ReifyState
  { reifyGen :: [String]
  , reifyEnv :: [(Index,ResolvedT)]
  }

initRState :: ReifyState
initRState = ReifyState
  { reifyGen = varNames
  , reifyEnv = []
  }

instance (ReifyDecs f, ReifyDecs g) => ReifyDecs (f :+: g) where
  reifyDeclarationsF cp = case cp of
    Inl e -> reifyDeclarationsF e
    Inr e -> reifyDeclarationsF e

instance ReifyDecs I where
  reifyDeclarationsF (I n) = return $ i n

instance ReifyDecs TypeF where
  reifyDeclarationsF typ = case typ of
    UnitF           -> return unit
    BitF            -> return bit
    ZF              -> return z
    QuoteF          -> return quote
    ArrayF ar t     -> return $ array ar t
    BlockF c t      -> return $ block c t
    TupleF ts       -> return $ tuple ts
    RecordF nts     -> return $ record nts
    FunctionF at bt -> return $ function at bt

instance ReifyDecs Syn where
  reifyDeclarationsF (Syn n) = return $ syn n

instance ReifyDecs Logic where
  reifyDeclarationsF (LV n) = do
    mt <- gets $ lookupEnv n . reifyEnv
    case mt of
      Just t -> return t
      Nothing -> newVar n

newVar :: Index -> RD ResolvedT
newVar ix = do
  n <- gets $ head . reifyGen
  let v = pVar n
  modify $ \(ReifyState g e) -> ReifyState (tail g) ((ix,v):e)
  return v

-- }}}
-}

