{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module SAWCoreIsabelle.Translate 
  ( translateModuleIO
  , translateSingleExprIO
  , translateName
  , translateType
  , importModuleDeps
  , withSchemaExpr
  , translateExpr
  , modToTheoryPure
  ) where

import Prelude hiding (log)

import           Control.Applicative ((<|>))
import           Control.Exception (SomeException, catch, evaluate)
import           Control.DeepSeq
import           Control.Monad.Error.Class (throwError, tryError)
import           Control.Monad.RWS (asks)
import           Control.Monad (forM_, forM, when, void)
import qualified Control.Monad.IO.Class as IO
import qualified Data.Text as T
import qualified Data.Map as Map
import           Data.Maybe (isJust, fromMaybe, mapMaybe, catMaybes)

import qualified Cryptol.TypeCheck.AST as Cry
import qualified Cryptol.TypeCheck.TypeOf as Cry
import qualified Cryptol.ModuleSystem.Name as Cry
import           Cryptol.Utils.Ident (ModName, modNameToText)
import qualified Cryptol.Utils.Ident as Cry
import qualified Cryptol.Utils.RecordMap as Cry
import qualified Cryptol.Parser.Position as Position
import qualified Cryptol.TypeCheck.Solve as Cry
import qualified Cryptol.TypeCheck.Solver.Types as Cry
import qualified Cryptol.TypeCheck.Solver.Numeric.Fin as Cry

import           Language.Isabelle.Builtins
import qualified Language.Isabelle.Binding as Binding
import qualified Language.Isabelle.Expr as Expr
import           Language.Isabelle.Expr (Expr, Type)
import qualified Language.Isabelle.Decl as Decl
import qualified Language.Isabelle.Name as Name
import qualified Language.Isabelle.Theory as Theory
import qualified Language.Isabelle.Syntax as Syntax

import qualified SAWCoreIsabelle.Error as Error
import           SAWCoreIsabelle.Error (TranslationError(..), pp)
import           SAWCoreIsabelle.IsaM
import qualified SAWCoreIsabelle.Options as Options
import qualified SAWCoreIsabelle.CryptolDeps as Deps
import qualified Data.Set as Set
import qualified Cryptol.ModuleSystem.Env as Cry
import Cryptol.IR.TraverseNames
import Data.List (nub)

doTranslation ::
  Options.HasOptions =>
  Deps.CryptolDeps ->
  [Cry.ModName] ->
  Name.TheoryName ->
  IsaM () ->
  IO ([Error.TranslationError], Theory.Theory)
doTranslation cryEnv imports thyNm f = do
  env <- initIsaEnv cryEnv Nothing thyNm
  (st, iout) <- execIsaM env $ do
    addDecl (Decl.Import cryThy)
    mapM_ importModName imports
    f
  return $ (outWarns iout, stThy st)

translateModuleIO ::
  Options.HasOptions =>
  Deps.CryptolDeps ->
  [Cry.ModName] ->
  Cry.Module ->
  IO ([Error.TranslationError], Theory.Theory)
translateModuleIO cryEnv imports crymod  = do
  let thyNm = modToTheoryPure (Cry.mName crymod)
  doTranslation cryEnv imports thyNm $ 
    translateModule crymod

translateSingleExprIO ::
  Options.HasOptions =>
  Deps.CryptolDeps ->
  Name.Name ->
  Cry.Expr ->
  IO ([Error.TranslationError], Theory.Theory)
translateSingleExprIO deps nm e = do
  let usedNames = Deps.foldMapNames (\nm_ -> case Deps.nameToModName nm_ of
        Nothing -> Set.empty
        Just mnm -> Set.singleton mnm) e
  doTranslation deps (Set.toList usedNames) (Name.nmThy nm) $ translateSingleExpr nm e

importModuleDeps :: TraverseNames t => t -> IsaM ()
importModuleDeps = fmap void . traverseNames $ \nm -> case Deps.nameToModName nm of
  Just mnm -> importModName mnm >> return nm
  Nothing -> return nm

importModName :: ModName -> IsaM ()
importModName mnm = do
  thynm <- modToTheory mnm
  addDecl (Decl.Import thynm)

modToTheory :: ModName -> IsaM Name.TheoryName
modToTheory mnm = return $ modToTheoryPure mnm

modToTheoryPure :: ModName -> Name.TheoryName
modToTheoryPure mnm = case T.unpack $ modNameToText mnm of
  "Main" -> Name.TheoryName "Main_" False
  str -> Name.TheoryName str False

-- | Unwrap nominal structs as type synonyms for the purposes
-- of translation
nominalToSyn :: Cry.NominalType -> Maybe Cry.TySyn
nominalToSyn nt | Cry.Struct sc <- Cry.ntDef nt = Just $ Cry.TySyn 
  { Cry.tsName = Cry.ntName nt 
  , Cry.tsParams = Cry.ntParams nt
  , Cry.tsConstraints = Cry.ntConstraints nt
  , Cry.tsDef = Cry.TRec (Cry.ntFields sc)
  , Cry.tsDoc = Cry.ntDoc nt
  }
nominalToSyn _ = Nothing

translateModule :: Cry.Module -> IsaM ()
translateModule m = do
  deps <- asks envCryDeps
  let mpos = case Map.lookup (Cry.mName m) (Deps.moduleDeps deps) of
        Just (lm, _) | Cry.InFile fp <- Cry.lmFilePath lm -> 
          Just (Position.emptyRange { Position.source = fp })
        _ -> Nothing
  maybeWith withPosition mpos $ 
    rethrow' (Error.ModuleTranslationFailure (Cry.mName m)) $ do

    let nomsyns = zip (Map.toList $ Map.mapMaybe nominalToSyn (Cry.mNominalTypes m)) (repeat True)

    let syns = zip (Map.toList $ Cry.mTySyns m) (repeat False)
    forM_ (syns ++ nomsyns) $ \((nm,tysyn),isNom) -> do
      catchMaybe (translateTySynDecl nm tysyn isNom) $ \e -> do
        warn e
        addDecl (Decl.Commented ("Translation failure: " ++ Error.showErr e) Decl.NoDecl)
    forM_ (Cry.mDecls m) $ \d -> do
      catchMaybe (translateDeclGroup (Deps.stripProofApps d)) $ \e -> do
        warn e
        addDecl (Decl.Commented ("Translation failure: " ++ Error.showErr e) Decl.NoDecl)

translateSingleExpr :: Name.Name -> Cry.Expr -> IsaM ()
translateSingleExpr nm e = do
  (args,body) <- translateAbs e
  t' <- translateType =<< typeOf e
  let b = Binding.Binding nm t'
  addDecl (Decl.Definition False b args body [])


translateRecordType :: Cry.RecordMap Cry.Ident Cry.Type -> IsaM Type
translateRecordType rm = do
  args <- forM (Cry.canonicalFields rm) $ \(fieldNm, fieldTp) -> do
    fieldTp' <- translateType fieldTp
    return $ (fieldNm, fieldTp')
  addDecl $ Decl.RecordDecl (map (Cry.unpackIdent . fst) args)
  let flds = map fst (Cry.canonicalFields rm)
  args' <- forM args $ \(nm,tp) -> do
    return (recordField flds nm, tp)
  return $ tRecord args'


translateTySynDecl :: Cry.Name -> Cry.TySyn -> Bool -> IsaM ()
translateTySynDecl nm tysyn fromNominal = rethrow' (UnsupportedTypeDecl nm tysyn) $ do
  let tparams = Cry.tsParams tysyn
  {- NOTE: we don't need to include the constraints in the 
     translated output, because
     Cryptol will enforce that they are present in any signatures
     using this type synonym.
  -}
  withTParams tparams $ do
    t' <- translateType (Cry.tsDef tysyn)
    nm' <- translateName nm
    targs <- mapM translateTParam tparams
    addDecl $ Decl.TypeSyn targs nm' t'
    when fromNominal $ do
      {- we need to create a dummy constructor if this synonym was
         originally a nominal type -}
      cnm <- translateName (Cry.tsName tysyn)
      guards <- mapM translateType (Cry.tsConstraints tysyn)
      let ct = tAbs targs (tGuard guards (tFun t' t'))
      let b = Binding.Binding cnm ct
      let x = Name.SimpleName "x"
      addDecl $ Decl.Definition False b [Binding.Binding x t'] (Expr.ConstrainT (Expr.Var x) t') []

translateSchema :: Cry.Schema -> IsaM Type
translateSchema s = do
  tyArgs <- mapM translateTParam (Cry.sVars s)
  guards <- mapM translateType (Cry.sProps s)
  body <- translateType (Cry.sType s)
  return $ tAbs tyArgs (tGuard guards body)

isStubbedFnName :: Options.HasOptions => Binding.Binding -> Bool
isStubbedFnName b = elem (Name.qualifiedIdent b) Options.functionStubs

translateDeclGroup :: Cry.DeclGroup -> IsaM ()
translateDeclGroup = \case
  Cry.Recursive ds -> do
    bodies <- fmap (zip (map Cry.dName ds)) $ mapM translateDecl ds
    let toRecMap (_, (b,mbody)) = case mbody of
          Right _ -> Just (Binding.bindName b, Binding.bindName (Decl.asRecImpl b))
          _ -> Nothing
    let recMap = Map.fromList $ mapMaybe toRecMap bodies
    let fixRecs = Expr.mapNames (\nm -> fromMaybe nm (Map.lookup nm recMap))  

    bs <- fmap catMaybes $ forM bodies $ \(crynm, (b,mbody)) -> do
      case mbody of
        Right (args, body)  -> do
          addDecl (Decl.Commented "Recursive call stub (to be overridden)" $ (Decl.ConstDecl False (Decl.asRecImpl b)))
          addDecl (Decl.Commented "Recursive call schema" $ Decl.Definition False (Decl.asRecSpec b) args (fixRecs body) [])
          return (Just (crynm, Binding.bindName b))
        Left (StubbedFunction{}) | isStubbedFnName b -> do
          addDecl (Decl.Commented ("Stubbed Function") (Decl.ConstDecl False b))
          return Nothing
        Left er | Options.keepGoing -> do
          addDecl (Decl.Commented ("Incomplete translation: " ++ Error.showErr er) (Decl.ConstDecl False b))
          return Nothing
        Left er -> throwError er
    addDecl (Decl.FixpointLocale (map snd bs))
    mapM_ (\(crynm,isanm) -> addHashDecl crynm isanm) bs

  Cry.NonRecursive d -> do
    (b,mbody) <- translateDecl d
    case mbody of
      Left (StubbedFunction{}) -> addDecl (Decl.ConstDecl False b)
      Left er -> addDecl (Decl.Commented ("Incomplete translation: " ++ Error.showErr er) (Decl.ConstDecl False b))
      Right (args, body) -> do
        addDecl (Decl.Definition False b args body [])
        addHashDecl (Cry.dName d) (Binding.bindName b)

stripETAbs :: Cry.Expr -> ([Cry.TParam], Cry.Expr)
stripETAbs = \case
  Cry.ETAbs t e ->
    let (ts,e') = stripETAbs e
    in (t:ts,e')
  e -> ([],e)

withTParams :: [Cry.TParam] -> IsaM a -> IsaM a
withTParams tps f = do
  tps' <- mapM go tps
  withNames tps' f
  where
    go :: Cry.TParam -> IsaM (Int, Name.Name)
    go tp = withPosition (Cry.tvarSource $ Cry.tpInfo tp) $ do
      nm' <- case Cry.tvarDesc (Cry.tpInfo tp) of
        Cry.TVFromSignature nm -> translateName nm
        _ -> simpleNameType "'"
      return (Cry.tpUnique tp, nm')

addGuards :: [Cry.Prop] -> Cry.Schema -> Cry.Schema
addGuards gs s = s { Cry.sProps = nub $ Cry.sProps s ++ gs}

extraGuard :: Cry.Ctxt -> Cry.TParam -> IsaM (Maybe (Cry.Prop))
extraGuard ctx tv = case Cry.tpKind tv of
  Cry.KNum -> case Cry.cryIsFinType ctx tp of
    Cry.SolvedIf [] -> return Nothing
    _ -> do
      let rng = Cry.tvarSource $ Cry.tpInfo tv
      Options.log (-1) $  "[warning] at " ++ pp rng ++ "\n Type parameter is not constrained to fin: " ++ pp tp
      return $ Just $ Cry.TCon (Cry.PC Cry.PFin) [tp]
  Cry.KType -> return $ Just $ Cry.TCon (Cry.PC Cry.PEq) [tp]
  _ -> return Nothing
  where
    tp = Cry.TVar (Cry.TVBound tv)

withDeclBinding :: Cry.Decl -> (Binding.Binding -> Cry.Expr -> IsaM a) -> IsaM a
withDeclBinding d f = rethrow' (UnsupportedDecl d) $ case Cry.dDefinition d of
  Cry.DPrim -> throwError $ UnsupportedEntity $ "DeclDef.DPrim"
  Cry.DForeign{} -> throwError $ UnsupportedEntity $ "DeclDef.Foreign"
  Cry.DExpr e -> do
    let (tparams, body) = stripETAbs e
    let props = Cry.sProps (Cry.dSignature d)
    let ctx = Cry.buildSolverCtxt props
    guards <- catMaybes <$> mapM (extraGuard ctx) tparams

    case tparams == (Cry.sVars (Cry.dSignature d)) of
      True -> withTParams tparams $ do
        nm <- translateName (Cry.dName d)
        t <- translateSchema (addGuards guards (Cry.dSignature d))
        f (Binding.Binding nm t) body
      False -> throwError $ UnexpectedSignature (Cry.dSignature d) e


withSchemaExpr :: Cry.Schema -> Cry.Expr -> (Type -> Expr -> IsaM a) -> IsaM a
withSchemaExpr s e f = do
  let (tparams, body) = stripETAbs e

  let props = Cry.sProps s
  let ctx = Cry.buildSolverCtxt props
  guards <- catMaybes <$> mapM (extraGuard ctx) (Cry.sVars s)
  let s' = addGuards guards s

  case tparams == (Cry.sVars s') of
    True -> withTParams tparams $ do
      t <- translateSchema s'
      body' <- translateExpr body
      f t body'
    False | null tparams -> withTParams (Cry.sVars s') $ do
      t <- translateSchema s'
      tparams' <- mapM translateTParam (Cry.sVars s')
      body' <- translateExpr body
      f t (tApp body' tparams')
    _ -> throwError $ UnexpectedSignature s' e

translateDecl :: Cry.Decl -> IsaM (Binding.Binding, Either TranslationError ([Binding.Binding], Expr))
translateDecl d = withDeclBinding d $ \b body -> do
  case isStubbedFnName b of
    True -> return (b, Left $ StubbedFunction d)
    False -> do
      res <- (tryError $ translateAbs body)
      return $ (b, res)

-- | Returns Undefined if translation fails
translateDecl' :: Cry.Decl -> IsaM (Binding.Binding, Expr)
translateDecl' d = withDeclBinding d $ \b body -> (tryError $ translateExpr body) >>= \case
  Left err -> return $ (b, Expr.Undefined (Binding.bindType b) (Error.showErr err))
  Right body' -> return $ (b, body')

nameToVar :: Name.Name -> IsaM Expr
nameToVar nm = return $ Expr.Var nm

{-
bindingToVar :: Binding.Binding -> IsaM Expr
bindingToVar b = nameToVar (Binding.bindName b)
-}

pathToTheory :: Cry.ModPath -> IsaM Name.TheoryName
pathToTheory = \case
  Cry.TopModule mnm -> do
    thynm <- modToTheory mnm
    cthy <- curTheory
    if (thynm == cthy || isBuiltinThy thynm) then
      return thynm
    else 
      return $ thynm { Name.thyQualified = True}
  Cry.Nested{} -> throwError $ UnsupportedEntity $ "ModPath.Nested"

isBinOp :: Cry.Name -> Bool
isBinOp nm = isJust (Cry.nameFixity nm)

translateName :: Cry.Name -> IsaM Name.Name
translateName nm = do
  let ident = Cry.nameIdent nm
  k <- case Cry.nameNamespace nm of
    Cry.NSType -> return $ Name.Typ
    Cry.NSValue -> return $ Name.Term
    Cry.NSConstructor -> return $ Name.Term
    Cry.NSModule -> throwError $ UnsupportedEntity $ "Namespace.NSModule"

  thynm <- case Cry.nameInfo nm of
    Cry.GlobalName _ on -> pathToTheory (Cry.ogModule on)
    Cry.LocalName{} -> curTheory
  let syn = case Cry.nameFixity nm of
        Just{} -> Syntax.InfixSyn (Cry.unpackIdent ident)
        Nothing -> Syntax.NoSyn
  let isaIdent = case (k, Cry.nameInfo nm) of
        (Name.Typ, Cry.LocalName{}) -> "'" ++ Cry.unpackIdent ident
        _ -> Cry.unpackIdent ident
  return $ Name.Name thynm isaIdent syn k


translateTParam :: Cry.TParam -> IsaM Expr
translateTParam tp = withPosition (Cry.tvarSource $ Cry.tpInfo tp) $ do
  nm <- lookupName (Cry.tpUnique tp)
  nameToVar nm



translateTCon :: Cry.TCon -> [Cry.Type] -> IsaM Type
translateTCon tc es = case (tc, es) of
  (Cry.PC Cry.PEqual, [e1, e2]) -> tEquals <$> translateType e1 <*> translateType e2
  (Cry.PC Cry.PLiteral, [e1, e2]) -> tLiteral <$> translateType e1 <*> translateType e2
  (Cry.PC Cry.PFin, [e1]) -> tFinite <$> translateType e1
  (Cry.PC Cry.PGeq, [e1,e2]) -> tGeq <$> translateType e1 <*> translateType e2
  (Cry.PC Cry.PSignedCmp, [t]) -> tSignedCmp <$> translateType t
  (Cry.PC Cry.PRing, [t]) -> tRing <$> translateType t
  (Cry.PC Cry.PIntegral, [t]) -> tIntegral <$> translateType t
  (Cry.PC Cry.PEq, [t]) -> tEq <$> translateType t
  (Cry.PC Cry.PLogic, [t]) -> tLogic <$> translateType t
  (Cry.PC Cry.PCmp, [t]) -> tCmp <$> translateType t
  (Cry.PC Cry.PAnd, [t1,t2]) -> tAnd <$> translateType t1 <*> translateType t2
  (Cry.PC Cry.PZero, [t]) -> tZero <$> translateType t

  (Cry.TC (Cry.TCNum i), []) -> return $ Expr.IntLit i
  (Cry.TC Cry.TCBit, []) -> return $ tBit
  _ | Just e1 <- asWordType (Cry.TCon tc es) -> tWord <$> translateType e1
  (Cry.TC Cry.TCSeq, [e1, e2]) -> tSeq <$> translateType e1 <*> translateType e2
  (Cry.TC Cry.TCInteger, []) -> return $ tInt
  (Cry.TC Cry.TCInf, []) | Options.keepGoing -> do
    warn (UnsupportedType (Cry.TCon tc es))
    mkUnsupportedT "Inf"

  (Cry.TC Cry.TCFun, [e1,e2]) -> tFun <$> translateType e1 <*> translateType e2
  (Cry.TC (Cry.TCTuple _), _) -> tTuple <$> mapM translateType es
  (Cry.TC Cry.TCIntMod, [t]) -> tZ <$> translateType t
  
  (Cry.TF Cry.TCWidth, [e1]) -> tWidth <$> translateType e1
  (Cry.TF Cry.TCMul, [e1, e2]) -> tMul <$> translateType e1 <*> translateType e2
  (Cry.TF Cry.TCMod, [e1, e2]) -> tMod <$> translateType e1 <*> translateType e2
  (Cry.TF Cry.TCSub, [e1, e2]) -> tMinus <$> translateType e1 <*> translateType e2
  (Cry.TF Cry.TCDiv, [e1, e2]) -> tDiv <$> translateType e1 <*> translateType e2
  (Cry.TF Cry.TCAdd, [t1, t2]) -> tAdd <$> translateType t1 <*> translateType t2
  (Cry.TF Cry.TCExp, [t1, t2]) -> tExp <$> translateType t1 <*> translateType t2
  (Cry.TF Cry.TCLenFromThenTo, [x,y,z]) -> 
    tFromThenTo <$> translateType x <*> translateType y <*> translateType z
  (Cry.TF Cry.TCMin, [t1,t2]) -> tMin <$> translateType t1 <*> translateType t2
  (Cry.TF Cry.TCMax, [t1,t2]) -> tMax <$> translateType t1 <*> translateType t2
  _ -> throwError $ UnsupportedType $ Cry.TCon tc es

translateType :: Cry.Type -> IsaM Type
translateType = rethrow UnsupportedType $ \case
  Cry.TCon tc args -> translateTCon tc args
  Cry.TVar (Cry.TVFree _ _ _ tinfo) -> case Cry.tvarDesc tinfo of
    Cry.TVFromSignature nm -> nameToVar =<< translateName nm
    ts -> throwError $ UnsupportedEntity $ "! TypeSource.TVFromSignature: " ++ (show ts)
  Cry.TVar (Cry.TVBound tp) -> translateTParam tp
  Cry.TUser userT args _ -> do
    userT' <- translateName userT
    args' <- mapM translateType args
    return $ Expr.Ctr args' userT'
  Cry.TRec r -> translateRecordType r
  Cry.TNominal nt args -> do
    userT' <- translateName (Cry.ntName nt)
    args' <- mapM translateType args
    return $ Expr.Ctr args' userT'

collectTApps :: Cry.Expr -> (Cry.Expr,[Cry.Type])
collectTApps = \case
  Cry.ETApp e t -> let (e', ts) = collectTApps e in (e',ts ++ [t])
  e -> (e,[])

unNumber :: Cry.Expr -> [Cry.Type] -> Maybe (Integer, Cry.Type)
unNumber e ts = case (e,ts) of
  (Cry.EVar nm, [t1, t2]) 
    | Cry.GlobalName{} <- Cry.nameInfo nm, "number" <- Cry.nameIdent nm
    , Cry.TCon (Cry.TC (Cry.TCNum i)) [] <- t1 ->
      Just (i, t2)
  _ -> Nothing

debugEnable :: Options.HasOptions => Bool
debugEnable = Options.verbosity >= 3

_debug :: String -> IsaM ()
_debug msg = if debugEnable then (IO.liftIO $ putStrLn $ "[DEBUG]: " ++ msg ++ "\n") else return ()


mkUnsupportedT :: String -> IsaM Type
mkUnsupportedT nm = do
  base <- simpleNameType (nm ++ "'")
  addDecl (Decl.TypeDecl [] base)
  lhs <- simpleNameType nm
  let rhs = tUnsupported (Expr.Var base)
  addDecl (Decl.TypeSyn [] lhs rhs)
  addDecl (Decl.Import unsupportedThy)
  return (Expr.Var lhs)

mkUndefined :: Error.TranslationError  -> IsaM (Type -> Expr)
mkUndefined  err = do
  warn err
  return $ \tp -> Expr.Undefined tp (Error.showErr err)

listAbs :: [(Cry.Name,Cry.Type)] -> Cry.Expr -> Cry.Expr
listAbs ((nm,t):xs) e = Cry.EAbs nm t (listAbs xs e)
listAbs [] e = e

stripAbs :: Cry.Expr -> ([(Cry.Name,Cry.Type)], Cry.Expr)
stripAbs = \case
  Cry.EAbs nm t e ->
    let (hdr, e') = stripAbs e
    in ((nm,t):hdr, e')
  -- lift abstractions out of where-bindings if there are no
  -- name clashes. It's unclear if clashes of this kind 
  -- are actually possible in
  -- practice, so this is mostly for safety.
  Cry.EWhere e decls -> 
    let 
      (hdr, e') = stripAbs e
      go ((nm,t):args) = if Deps.containsName nm decls then
        ([], listAbs ((nm,t):args) e')
        else 
          let (hdr_, e_) = go args
          in ((nm,t):hdr_, e_)
      go [] = ([], e')
      (hdr', body) = go hdr
    in (hdr', Cry.EWhere body decls)

  e -> ([],e)

stripApp :: Cry.Expr -> (Cry.Expr, [Cry.Expr])
stripApp = \case
  Cry.EApp e arg ->
    let (e', args) = stripApp e
    in (e', args ++ [arg])
  e -> (e, [])

typeOf :: Cry.Expr -> IsaM (Cry.Type)
typeOf e = do
  tyEnv <- asks envTypeEnv
  (IO.liftIO $ (Right <$> go tyEnv e) 
    `catch` (\(er :: SomeException) -> return $ Left $ Error.CryptolTypeOfError e (show er))) >>= \case
    Right s -> return $ Cry.sType s
    Left er -> throwError er
  where
    go :: Map.Map Cry.Name Cry.Schema -> Cry.Expr -> IO Cry.Schema
    go tyEnv e_top = evaluate $!! (Cry.fastSchemaOf tyEnv e_top)

translateAbs :: Cry.Expr -> IsaM ([Binding.Binding], Expr)
translateAbs e = do
  let (hdr, body) = stripAbs e
  hdr' <- forM hdr $ \(nm,t) -> do
    nm' <- translateName nm
    t' <- translateType t
    return $ Binding.Binding nm' t'
  let hdr_schem = map (\(nm, t) -> (nm, Cry.tMono t)) hdr
  body' <- withBindings hdr_schem $ translateExpr body
  return $ (hdr', body')

absExpr :: [Binding.Binding] -> Expr -> Expr
absExpr binds e = eAbs (map (\b -> bind (Binding.bindName b) (Binding.bindType b)) binds) e

translateMatches ::
  Type {-^ target seq elems -} ->
  Cry.Expr ->
  [Cry.Match] ->
  IsaM (Maybe Type, Expr)
translateMatches _ e_final [] = do
  e_final' <- translateExpr e_final
  return (Nothing, e_final')
translateMatches outer_elemT e_final (Cry.Let d:ms) = do
  withDeclBinding d $ \b body -> do
    body' <- translateExpr body
    (len, result) <- translateMatches outer_elemT e_final ms
    return $ (len, letExpr [(b,body')] result)
translateMatches outer_elemT e ((Cry.From nm lenT elemT body):ms) = do
  elemT' <- translateType elemT
  nm' <- translateName nm
  body' <- translateExpr body
  lenT' <- translateType lenT
  withBindings [(nm, Cry.tMono elemT)] $ do
    (m_inner_len, match_body) <- translateMatches outer_elemT e ms
    case m_inner_len of
      Just inner_len -> do
        let target_len = (tMul lenT' inner_len)
        let s = seqConcatMap inner_len elemT' lenT' outer_elemT (nm', match_body) body'
        return (Just target_len, s)
      Nothing -> do
        return $ (Just lenT', seqCompr1 lenT' elemT' outer_elemT (nm', match_body) body')
{-
tupleType :: [Cry.Type] -> Cry.Type
tupleType tys = Cry.TCon (Cry.TC (Cry.TCTuple (length tys))) tys
-}

matchToTuple :: [Cry.Match] -> [(Cry.Schema, Cry.Name)]
matchToTuple ms = map go ms
  where
    go :: Cry.Match -> (Cry.Schema, Cry.Name)
    go = \case
      Cry.From nm _ elemT _ -> (Cry.tMono elemT, nm)
      Cry.Let d -> (Cry.dSignature d, Cry.dName d)

toMono :: Cry.Schema -> IsaM Cry.Type
toMono s = case Cry.isMono s of
  Just t -> return t
  Nothing -> throwError $ UnexpectedPolymorphism s

asWordType :: Cry.Type -> Maybe Cry.Type
asWordType (Cry.TCon (Cry.TC Cry.TCSeq) [e1, (Cry.TCon (Cry.TC Cry.TCBit) [])]) = Just e1
asWordType _ = Nothing

-- Concrete values of this type should be printed as hex
isHexType :: Cry.Type -> Bool
isHexType t = isJust (asWordType t)

recordField :: [Cry.Ident] -> Cry.Ident -> Name.Name
recordField flds field = 
  let rnm = Decl.recordName (map Cry.unpackIdent flds)
  in Name.Name (Name.nmThy rnm) (Cry.unpackIdent field) Syntax.NoSyn Name.Term

isRec :: Cry.Type -> Maybe (Cry.RecordMap Cry.Ident Cry.Type)
isRec t = Cry.tIsRec t <|> do
  (nt,_) <- Cry.tIsNominal t
  Cry.Struct sc <- return $ Cry.ntDef nt
  return $ Cry.ntFields sc

translateExpr :: Cry.Expr -> IsaM (Expr)
translateExpr = rethrow UnsupportedExpr $ \case
  Cry.EList es (Cry.TCon (Cry.TC Cry.TCBit) []) -> do
    es' <- mapM translateExpr es
    return $ constrain (wordFromBits es') (tWord (Expr.IntLit (fromIntegral (length es))))

  Cry.EList es t -> do
    es' <- mapM translateExpr es
    t' <- translateType t
    let es'' = map (\e_ -> coerceToExpr e_ t') es'
    return $ constrain (seqExpr es'') (tSeq (Expr.IntLit (fromIntegral (length es))) t')

  Cry.ETuple es -> tupleExpr <$> mapM translateExpr es
  Cry.ERec rm -> do
    let flds = map fst (Cry.canonicalFields rm)
    args <- forM (Cry.canonicalFields rm) $ \(fieldNm, fieldExpr) -> do
      fieldTp' <- translateExpr fieldExpr
      return $ (recordField flds fieldNm, fieldTp')
    return $ recordCtr args

  Cry.ESel e sel -> do
    case sel of
      Cry.ListSel i _ -> (Cry.tIsSeq <$> typeOf e) >>= \case
        Just (lenT, elemT) -> do
          lenT' <- translateType lenT
          elemT' <- translateType elemT
          e' <- translateExpr e
          return $ seqSel lenT' elemT' tInt  e' (constrain (Expr.IntLit (fromIntegral i)) tInt)
        Nothing -> throwError $ UnsupportedEntity $ "Expr.ESel." ++ show sel
      Cry.TupleSel i _ -> (Cry.tIsTuple <$> typeOf e) >>= \case 
        Just ts -> do
          let len = length ts
          x <- simpleNameExpr "x"
          e' <- translateExpr e
          t' <- translateType (ts !! i)
          return $ constrain (tupleSelect x e' i len) t'
        Nothing -> throwError $ UnsupportedEntity $ "Expr.ESel." ++ show sel
      Cry.RecordSel field (Just flds) -> do
        e' <- translateExpr e
        -- Qualify record accessors to handle name clashes
        return $ appExpr (Expr.Var (recordField flds field)) [e']
      Cry.RecordSel field Nothing -> (isRec <$> typeOf e) >>= \case 
        Just rm -> translateExpr (Cry.ESel e (Cry.RecordSel field (Just (map fst (Cry.canonicalFields rm)))))
        Nothing -> do
          throwError $ UnsupportedEntity $ "Cry.RecordSel: unexpected source record type"

  Cry.ESet{} -> throwError $ UnsupportedEntity $ "Expr.ESet"

  Cry.EIf p eT eF -> do
    p' <- translateExpr p
    eT' <- translateExpr eT
    eF' <- translateExpr eF
    return $ ifExpr p' eT' eF'

  Cry.ECase{} -> throwError $ UnsupportedEntity $ "Cry.ECase"

  (Cry.EComp _lenT elemT e [inner_matches]) -> do
    elemT' <- translateType elemT
    (_, result) <- translateMatches elemT' e inner_matches
    return result
  (Cry.EComp _lenT elemT e matches) -> do
    elemT' <- translateType elemT
    let 
      go :: [Cry.Match] -> IsaM ([(Cry.Name, Cry.Schema)], ((Type,Type), Expr))
      go inner_matches = do
        let (matchSchems, matchNms) = unzip $ matchToTuple inner_matches
        matchTs <- mapM toMono matchSchems
        matchTs' <- mapM translateType matchTs
        (mslen, result) <- translateMatches (tTuple matchTs') (Cry.ETuple (map Cry.EVar matchNms)) inner_matches
        case mslen of
          Nothing -> throwError $ UnsupportedMatchShape matches
          Just slen -> return (zip matchNms matchSchems, ((slen, (tTuple matchTs')), result))
    (match_names, match_bodies) <- unzip <$> (mapM go matches)
    let ((len_final, elem_final), body) = seqZipMany match_bodies
    withBindings (concat match_names) $ do
      e' <- translateExpr e
      nms' <- forM match_names $ \nms -> forM nms $ \(nm,schem) -> do
        nm' <- translateName nm
        nmT <- toMono schem >>= translateType
        return (nm',nmT)
      return $ seqCompr1' len_final elem_final elemT' (tupleAbs nms' e') body

  Cry.EVar nm  -> nameToVar =<< translateName nm
  Cry.ETAbs{} -> throwError $ UnsupportedEntity $ "Cry.ETAbs"

  et@Cry.ETApp{} -> do
    let (e,ts) = collectTApps et
    case unNumber e ts of
      Just (i,t) -> do
        t' <- translateType t
        return $ constrain (Expr.IntLitCtr i (isHexType t)) t'
      _ -> do
        ts' <- mapM translateType ts
        e' <- translateExpr e
        let ret = tApp e' ts'
        case e of 
          Cry.EVar nm | Just{} <- Cry.nameFixity nm ->
            return $ unOp ret
          _ -> return ret

  Cry.EApp (Cry.EApp e1 e2) e3 |
    (Cry.EVar nm,ts) <- collectTApps e1,
    isBinOp nm
    -> do
    nm' <- translateName nm
    ts' <- mapM translateType ts
    let e1' = tApp (Expr.Var nm') ts'

    e2' <- translateExpr e2
    e3' <- translateExpr e3

    return $ Expr.BinOp e2' e1' e3'

  e@(Cry.EApp{}) -> do
    let (e1, args) = stripApp e
    e1' <- translateExpr e1
    args' <- mapM translateExpr args
    case e1' of
      {- adds an empty type argument for user-made definitions with
         arguments in order to invoke the implicit argument coercion
         parser -}
      Expr.Var nm 
        | not (isBuiltinName nm)
        , not (null args) -> 
          return $ appExpr (Expr.TApp e1' []) args'
      _ -> return $ appExpr e1' args'

  e@(Cry.EAbs{}) -> do
    (binds,body) <- translateAbs e
    return $ absExpr binds body

  Cry.ELocated r e -> withPosition r $ translateExpr e
  -- do we need proofs?
  Cry.EProofAbs _ e -> translateExpr e
  Cry.EProofApp e -> translateExpr e
  Cry.EWhere body grps -> withDeclGroups grps $ do
    let f grp = case grp of
          -- a let-binding inside a recursive block is deemed recursive
          -- regardless if it actually has mutually recursive bindings
          -- in general this can be detected by examining the bindings themselves,
          -- but this handles the common case where only one binding exists
          Cry.Recursive [d] -> (:[]) <$> translateDecl' d
          Cry.Recursive ds | Options.keepGoing -> do
            undef <- mkUndefined (UnsupportedRecursion ds)
            forM ds $ \d -> withDeclBinding d $ \b _ ->
              return (b, undef (Binding.bindType b))
          Cry.Recursive ds -> do
            throwError $ UnsupportedRecursion ds
          Cry.NonRecursive d -> (:[]) <$> translateDecl' d
    binds <- concat <$> mapM f grps
    body' <- translateExpr body
    return $ letExpr binds body'
  Cry.EPropGuards [g] _ -> translateGuards Nothing [g]
  -- if we have multiple branches, we need to coerce each into
  -- the target type, in case the branches disagree on the Isabelle type
  Cry.EPropGuards gs t -> do
    t' <- translateType t
    translateGuards (Just t') gs

maybeCoerce :: Maybe Type -> Expr -> Expr
maybeCoerce Nothing e = e
maybeCoerce (Just t) e = coerceToExpr e t

translateGuards :: Maybe Type -> [([Cry.Type], Cry.Expr)] -> IsaM (Expr)
translateGuards outerT [(ts,e)] = do
  e' <- translateExpr e
  ts' <- mapM translateType ts
  return $ eAssuming ts' (maybeCoerce outerT e')
translateGuards outerT ((ts,e):gs) = do
  gs' <- translateGuards outerT gs
  e' <- translateExpr e
  ts' <- mapM translateType ts
  return $ ifExpr (eHolds ts') (maybeCoerce outerT e') gs'
translateGuards _ [] = throwError $ UnsupportedEntity $ "Expr.EPropGuards: empty"






