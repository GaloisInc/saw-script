{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.Cryptol where

import Control.Applicative
import Control.Monad (join)
import Data.List (findIndex)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromJust)
import Data.Traversable hiding (sequence)

import qualified Cryptol.TypeCheck.AST as C
import qualified Cryptol.Prims.Syntax as P
import Cryptol.TypeCheck.TypeOf (fastTypeOf, fastSchemaOf)

import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST (mkSort)

unimplemented :: Monad m => String -> m a
unimplemented name = fail ("unimplemented: " ++ name)

--------------------------------------------------------------------------------
-- Type Environments

data Env s = Env
  { envT :: Map Int (SharedTerm s)     -- ^ Type variables are referenced by unique id
  , envE :: Map C.QName (SharedTerm s) -- ^ Term variables are referenced by name
  , envP :: Map C.Prop (SharedTerm s)  -- ^ Bound propositions are referenced implicitly by their types
  , envC :: Map C.QName C.Schema       -- ^ Cryptol type environment
  }

emptyEnv :: Env s
emptyEnv = Env Map.empty Map.empty Map.empty Map.empty

liftTerm :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
liftTerm sc = incVars sc 0 1

-- | Increment dangling bound variables of all types in environment.
liftEnv :: SharedContext s -> Env s -> IO (Env s)
liftEnv sc env =
  Env <$> traverse (liftTerm sc) (envT env)
      <*> traverse (liftTerm sc) (envE env)
      <*> traverse (liftTerm sc) (envP env)
      <*> pure (envC env)

bindTParam :: SharedContext s -> C.TParam -> Env s -> IO (Env s)
bindTParam sc tp env = do
  env' <- liftEnv sc env
  v <- scLocalVar sc 0
  return $ env' { envT = Map.insert (C.tpUnique tp) v (envT env') }

bindQName :: SharedContext s -> C.QName -> C.Schema -> Env s -> IO (Env s)
bindQName sc qname schema env = do
  env' <- liftEnv sc env
  v <- scLocalVar sc 0
  return $ env' { envE = Map.insert qname v (envE env'), envC = Map.insert qname schema (envC env') }

bindProp :: SharedContext s -> C.Prop -> Env s -> IO (Env s)
bindProp sc prop env = do
  env' <- liftEnv sc env
  v <- scLocalVar sc 0
  return $ env' { envP = Map.insert prop v (envP env') }

--------------------------------------------------------------------------------

importKind :: SharedContext s -> C.Kind -> IO (SharedTerm s)
importKind sc kind =
  case kind of
    C.KType       -> scDataTypeApp sc "Cryptol.KType" []
    C.KNum        -> scDataTypeApp sc "Cryptol.Num" []
    C.KProp       -> scSort sc (mkSort 0)
    (C.:->) k1 k2 -> join $ scFun sc <$> importKind sc k1 <*> importKind sc k2

importTFun :: SharedContext s -> C.TFun -> IO (SharedTerm s)
importTFun sc tf =
  case tf of
    C.TCWidth         -> scGlobalDef sc "Cryptol.tcWidth"
    C.TCLg2           -> scGlobalDef sc "Cryptol.tcLg2"
    C.TCAdd           -> scGlobalDef sc "Cryptol.tcAdd"
    C.TCSub           -> scGlobalDef sc "Cryptol.tcSub"
    C.TCMul           -> scGlobalDef sc "Cryptol.tcMul"
    C.TCDiv           -> scGlobalDef sc "Cryptol.tcDiv"
    C.TCMod           -> scGlobalDef sc "Cryptol.tcMod"
    C.TCExp           -> scGlobalDef sc "Cryptol.tcExp"
    C.TCMin           -> scGlobalDef sc "Cryptol.tcMin"
    C.TCMax           -> scGlobalDef sc "Cryptol.tcMax"
    C.TCLenFromThen   -> scGlobalDef sc "Cryptol.tcLenFromThen"
    C.TCLenFromThenTo -> scGlobalDef sc "Cryptol.tcLenFromThenTo"

importType :: SharedContext s -> Env s -> C.Type -> IO (SharedTerm s)
importType sc env ty =
  case ty of
    C.TVar tvar ->
      case tvar of
        C.TVFree{} {- Int Kind (Set TVar) Doc -} -> unimplemented "TVFree"
        C.TVBound i _k   -> case Map.lookup i (envT env) of
                              Just t -> return t
                              Nothing -> fail "internal error: importType TVBound"
    C.TUser _ _ t  -> go t
    C.TRec fs      -> importTCTuple sc env (map snd fs)
    C.TCon tcon tyargs ->
      case tcon of
        C.TC tc ->
          case tc of
            C.TCNum n    -> scCtorApp sc "Cryptol.TCNum" =<< sequence [scNat sc (fromInteger n)]
            C.TCInf      -> scCtorApp sc "Cryptol.TCInf" []
            C.TCBit      -> scCtorApp sc "Cryptol.TCBit" []
            C.TCSeq      -> scCtorApp sc "Cryptol.TCSeq" =<< traverse go tyargs
            C.TCFun      -> scCtorApp sc "Cryptol.TCFun" =<< traverse go tyargs
            C.TCTuple _n -> importTCTuple sc env tyargs
            C.TCNewtype (C.UserTC _qn _k) -> unimplemented "TCNewtype" -- ^ user-defined, @T@
        C.PC pc ->
          case pc of
            C.PEqual         -> scGlobalApply sc "Cryptol.PEqual" =<< traverse go tyargs -- ^ @_ == _@
            C.PNeq           -> scGlobalApply sc "Cryptol.PNeq"   =<< traverse go tyargs -- ^ @_ /= _@
            C.PGeq           -> scGlobalApply sc "Cryptol.PGeq"   =<< traverse go tyargs -- ^ @_ >= _@
            C.PFin           -> scDataTypeApp sc "Cryptol.PFin"   =<< traverse go tyargs -- ^ @fin _@
            C.PHas _selector -> unimplemented "PHas"
            C.PArith         -> scDataTypeApp sc "Cryptol.PArith" =<< traverse go tyargs -- ^ @Arith _@
            C.PCmp           -> scDataTypeApp sc "Cryptol.PCmp"   =<< traverse go tyargs -- ^ @Cmp _@
        C.TF tf ->
          do tf' <- importTFun sc tf
             tyargs' <- traverse go tyargs
             scApplyAll sc tf' tyargs'
  where
    go = importType sc env

importTCTuple :: SharedContext s -> Env s -> [C.Type] -> IO (SharedTerm s)
importTCTuple _sc _env [] = unimplemented "TCTuple []"
importTCTuple sc env [t] = importType sc env t
importTCTuple sc env (t : ts) =
  scCtorApp sc "Cryptol.TCPair" =<< sequence [importType sc env t, importTCTuple sc env ts]

nameToString :: C.Name -> String
nameToString (C.Name s) = s
nameToString (C.NewName p i) = show p ++ show i

qnameToString :: C.QName -> String
qnameToString (C.QName _ name) = nameToString name

tparamToString :: C.TParam -> String
--tparamToString tp = maybe "_" qnameToString (C.tpName tp)
tparamToString tp = maybe ("u" ++ show (C.tpUnique tp)) qnameToString (C.tpName tp)

importPropsType :: SharedContext s -> Env s -> [C.Prop] -> C.Type -> IO (SharedTerm s)
importPropsType sc env [] ty = do
  t <- importType sc env ty
  scGlobalApply sc "Cryptol.ty" [t]
importPropsType sc env (prop : props) ty = do
  p <- importType sc env prop
  t <- importPropsType sc env props ty
  scFun sc p t

importPolyType :: SharedContext s -> Env s -> [C.TParam] -> [C.Prop] -> C.Type -> IO (SharedTerm s)
importPolyType sc env [] props ty = importPropsType sc env props ty
importPolyType sc env (tp : tps) props ty = do
  k <- importKind sc (C.tpKind tp)
  env' <- bindTParam sc tp env
  t <- importPolyType sc env' tps props ty
  scPi sc (tparamToString tp) k t

importSchema :: SharedContext s -> Env s -> C.Schema -> IO (SharedTerm s)
importSchema sc env (C.Forall tparams props ty) = importPolyType sc env tparams props ty

proveProp :: SharedContext s -> Env s -> C.Prop -> IO (SharedTerm s)
proveProp sc env prop =
  case prop of
    (C.pIsFin -> Just (C.tIsNum -> Just n))
      -> scCtorApp sc "Cryptol.PFinNum" =<< sequence [scNat sc (fromInteger n)]
    (C.pIsFin -> Just (tIsWidth -> Just n))
      -> scGlobalApply sc "Cryptol.pfinWidth" =<< sequence [ty n, pr (C.pFin n)]
    (C.pIsFin -> Just (tIsSub -> Just (m, n)))
      -> scGlobalApply sc "Cryptol.pfinSub" =<< sequence [ty m, ty n, pr (C.pFin m), pr (C.pFin n)]
    (C.pIsFin -> Just (tIsMax -> Just (m, n)))
      -> scGlobalApply sc "Cryptol.pfinMax" =<< sequence [ty m, ty n, pr (C.pFin m), pr (C.pFin n)]
    (C.pIsArith -> Just (C.tIsSeq -> Just (n, C.tIsBit -> True)))
      -> scCtorApp sc "Cryptol.PArithWord" =<< sequence [ty n, pr (C.pFin n)]
    (C.pIsArith -> Just (C.tIsSeq -> Just (n, t))) | definitelyNotBit t
      -> scCtorApp sc "Cryptol.PArithSeq" =<< sequence [ty n, ty t, pr (C.pArith t)]
    (C.pIsArith -> Just (C.tIsTuple -> Just [t1, t2]))
      -> scCtorApp sc "Cryptol.PArithPair" =<< sequence [ty t1, ty t2, pr (C.pArith t1), pr (C.pArith t2)]
    (C.pIsCmp -> Just (C.tIsBit -> True))
      -> scCtorApp sc "Cryptol.PCmpBit" []
    (C.pIsCmp -> Just (C.tIsSeq -> Just (n, t)))
      -> scCtorApp sc "Cryptol.PCmpSeq" =<< sequence [ty n, ty t, pr (C.pFin n), pr (C.pCmp t)]
    (C.pIsCmp -> Just (C.tIsTuple -> Just [t1, t2]))
      -> scCtorApp sc "Cryptol.PCmpPair" =<< sequence [ty t1, ty t2, pr (C.pCmp t1), pr (C.pCmp t2)]
    -- FIXME: handle arbitrary sized tuples and records
    _ -> case Map.lookup prop (envP env) of
           Just prf -> return prf
           Nothing -> scGlobalApply sc "Cryptol.eProofApp" =<< sequence [ty prop]
  where
    ty = importType sc env
    pr = proveProp sc env
    definitelyNotBit t =
      case t of
        C.TCon tc _    -> tc /= C.TC C.TCBit
        C.TVar _       -> False
        C.TUser _ _ t1 -> definitelyNotBit t1
        C.TRec _       -> True

-- | Convert built-in constants to SAWCore.
importECon :: SharedContext s -> P.ECon -> IO (SharedTerm s)
importECon sc econ =
  case econ of
    P.ECTrue        -> scBool sc True
    P.ECFalse       -> scBool sc False
    P.ECDemote      -> scGlobalDef sc "Cryptol.ecDemote"      -- ^ Converts a numeric type into its corresponding value.
                                                     -- { val, bits } (fin val, fin bits, bits >= width val) => [bits]
    P.ECPlus        -> scGlobalDef sc "Cryptol.ecPlus"        -- {a} (Arith a) => a -> a -> a
    P.ECMinus       -> scGlobalDef sc "Cryptol.ecMinus"       -- {a} (Arith a) => a -> a -> a
    P.ECMul         -> scGlobalDef sc "Cryptol.ecMul"         -- {a} (Arith a) => a -> a -> a
    P.ECDiv         -> scGlobalDef sc "Cryptol.ecDiv"         -- {a} (Arith a) => a -> a -> a
    P.ECMod         -> scGlobalDef sc "Cryptol.ecMod"         -- {a} (Arith a) => a -> a -> a
    P.ECExp         -> scGlobalDef sc "Cryptol.ecExp"         -- {a} (Arith a) => a -> a -> a
    P.ECLg2         -> scGlobalDef sc "Cryptol.ecLg2"         -- {a} (Arith a) => a -> a
    P.ECNeg         -> scGlobalDef sc "Cryptol.ecNeg"         -- {a} (Arith a) => a -> a
    P.ECLt          -> scGlobalDef sc "Cryptol.ecLt"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECGt          -> scGlobalDef sc "Cryptol.ecGt"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECLtEq        -> scGlobalDef sc "Cryptol.ecLtEq"        -- {a} (Cmp a) => a -> a -> Bit
    P.ECGtEq        -> scGlobalDef sc "Cryptol.ecGtEq"        -- {a} (Cmp a) => a -> a -> Bit
    P.ECEq          -> scGlobalDef sc "Cryptol.ecEq"          -- {a} (Cmp a) => a -> a -> Bit
    P.ECNotEq       -> scGlobalDef sc "Cryptol.ecNotEq"       -- {a} (Cmp a) => a -> a -> Bit
    P.ECFunEq       -> scGlobalDef sc "Cryptol.ecFunEq"       -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
    P.ECFunNotEq    -> scGlobalDef sc "Cryptol.ecFunNotEq"    -- {a b} (Cmp b) => (a -> b) -> (a -> b) -> a -> Bit
    P.ECMin         -> scGlobalDef sc "Cryptol.ecMin"         -- {a} (Cmp a) => a -> a -> a
    P.ECMax         -> scGlobalDef sc "Cryptol.ecMax"         -- {a} (Cmp a) => a -> a -> a
    P.ECAnd         -> scGlobalDef sc "Cryptol.ecAnd"         -- {a} a -> a -> a        -- Bits a
    P.ECOr          -> scGlobalDef sc "Cryptol.ecOr"          -- {a} a -> a -> a        -- Bits a
    P.ECXor         -> scGlobalDef sc "Cryptol.ecXor"         -- {a} a -> a -> a        -- Bits a
    P.ECCompl       -> scGlobalDef sc "Cryptol.ecCompl"       -- {a} a -> a             -- Bits a
    P.ECZero        -> scGlobalDef sc "Cryptol.ecZero"        -- {a} a                  -- Bits a
    P.ECShiftL      -> scGlobalDef sc "Cryptol.ecShiftL"      -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECShiftR      -> scGlobalDef sc "Cryptol.ecShiftR"      -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECRotL        -> scGlobalDef sc "Cryptol.ecRotL"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECRotR        -> scGlobalDef sc "Cryptol.ecRotR"        -- {m,n,a} (fin m) => [m] a -> [n] -> [m] a
    P.ECCat         -> scGlobalDef sc "Cryptol.ecCat"         -- {a,b,d} (fin a) => [a] d -> [b] d -> [a + b] d
    P.ECSplitAt     -> scGlobalDef sc "Cryptol.ecSplitAt"     -- {a,b,c} (fin a) => [a+b] c -> ([a]c,[b]c)
    P.ECJoin        -> scGlobalDef sc "Cryptol.ecJoin"        -- {a,b,c} (fin b) => [a][b]c -> [a * b]c
    P.ECSplit       -> scGlobalDef sc "Cryptol.ecSplit"       -- {a,b,c} (fin b) => [a * b] c -> [a][b] c
    P.ECReverse     -> scGlobalDef sc "Cryptol.ecReverse"     -- {a,b} (fin a) => [a] b -> [a] b
    P.ECTranspose   -> scGlobalDef sc "Cryptol.ecTranspose"   -- {a,b,c} [a][b]c -> [b][a]c
    P.ECAt          -> scGlobalDef sc "Cryptol.ecAt"          -- {n,a,i} (fin i) => [n]a -> [i] -> a
    P.ECAtRange     -> scGlobalDef sc "Cryptol.ecAtRange"     -- {n,a,m,i} (fin i) => [n]a -> [m][i] -> [m]a
    P.ECAtBack      -> scGlobalDef sc "Cryptol.ecAtBack"      -- {n,a,i} (fin n, fin i) => [n]a -> [i] -> a
    P.ECAtRangeBack -> scGlobalDef sc "Cryptol.ecAtRangeBack" -- {n,a,m,i} (fin n, fin i) => [n]a -> [m][i] -> [m]a
    P.ECFromThen    -> scGlobalDef sc "Cryptol.ecFromThen"
                               -- fromThen : {first,next,bits,len}
                               --             ( fin first, fin next, fin bits
                               --             , bits >= width first, bits >= width next
                               --             , lengthFromThen first next bits == len
                               --             )
                               --          => [len] [bits]
    P.ECFromTo      -> scGlobalDef sc "Cryptol.ecFromTo"
                               -- fromTo : {first, last, bits}
                               --           ( fin last, fin bits, last >== first, bits >== width last)
                               --        => [1 + (last - first)] [bits]
    P.ECFromThenTo  -> scGlobalDef sc "Cryptol.ecFromThenTo"
    P.ECInfFrom     -> scGlobalDef sc "Cryptol.ecInfFrom"     -- {a} (fin a) => [a] -> [inf][a]
    P.ECInfFromThen -> scGlobalDef sc "Cryptol.ecInfFromThen" -- {a} (fin a) => [a] -> [a] -> [inf][a]
    P.ECError       -> scGlobalDef sc "Cryptol.ecError"       -- {at,len} (fin len) => [len][8] -> at -- Run-time error
    P.ECPMul        -> scGlobalDef sc "Cryptol.ecPMul"        -- {a,b} (fin a, fin b) => [a] -> [b] -> [max 1 (a + b) - 1]
    P.ECPDiv        -> scGlobalDef sc "Cryptol.ecPDiv"        -- {a,b} (fin a, fin b) => [a] -> [b] -> [a]
    P.ECPMod        -> scGlobalDef sc "Cryptol.ecPMod"        -- {a,b} (fin a, fin b) => [a] -> [b+1] -> [b]
    P.ECRandom      -> scGlobalDef sc "Cryptol.ecRandom"      -- {a} => [32] -> a -- Random values

importExpr :: SharedContext s -> Env s -> C.Expr -> IO (SharedTerm s)
importExpr sc env expr =
  case expr of
    C.ECon econ                 -> importECon sc econ -- ^ Built-in constant
    C.EList es t                -> do t' <- ty t
                                      n' <- scNat sc (fromIntegral (length es))
                                      es' <- traverse go es
                                      v' <- scVector sc t' es'
                                      scGlobalApply sc "Cryptol.eList" [t', n', v']
    C.ETuple es                 -> scNestedTuple sc =<< traverse go es
    C.ERec fs                   -> scNestedTuple sc =<< traverse go (map snd fs)
    C.ESel e sel                ->           -- ^ Elimination for tuple/record/list
      case sel of
        C.TupleSel i (Just l)   -> scNestedSelector sc i l =<< go e
        C.TupleSel _ Nothing    -> unimplemented "TupleSel Nothing"
        C.RecordSel x (Just xs) -> scNestedSelector sc i l =<< go e
                                     where i = fromJust (findIndex (== x) xs) + 1
                                           l = length xs
        C.RecordSel x Nothing   -> case C.tNoUser (fastTypeOf (envC env) e) of
                                     C.TRec fs -> importExpr sc env (C.ESel e (C.RecordSel x (Just (map fst fs))))
                                     _ -> fail "Expected record type"
        C.ListSel i _maybeLen   -> do let t = fastTypeOf (envC env) e
                                      (n, a) <- case C.tIsSeq t of
                                                  Just (n, a) -> return (n, a)
                                                  Nothing -> fail "ListSel: not a list type"
                                      a' <- importType sc env a
                                      n' <- importType sc env n
                                      e' <- importExpr sc env e
                                      i' <- scNat sc (fromIntegral i)
                                      scGlobalApply sc "Cryptol.eListSel" [a', n', e', i']
    C.EIf e1 e2 e3              -> do t' <- importType sc env (fastTypeOf (envC env) e2)
                                      e1' <- importExpr sc env e1
                                      e2' <- importExpr sc env e2
                                      e3' <- importExpr sc env e3
                                      scGlobalApply sc "Cryptol.eIf" [t', e1', e2', e3']
    C.EComp t e mss             -> importComp sc env t e mss
    C.EVar qname                    ->
      case Map.lookup qname (envE env) of
        Just e'                     -> return e'
        Nothing                     -> fail "internal error: unknown variable"
    C.ETAbs tp e                    -> do k <- importKind sc (C.tpKind tp)
                                          env' <- bindTParam sc tp env
                                          e' <- importExpr sc env' e
                                          scLambda sc (tparamToString tp) k e'
    C.ETApp e t                     -> join $ scApply sc <$> go e <*> ty t
    C.EApp e1 e2                    -> join $ scApply sc <$> go e1 <*> go e2
    C.EAbs x t e                    -> do t' <- ty t
                                          env' <- bindQName sc x (C.Forall [] [] t) env
                                          e' <- importExpr sc env' e
                                          scEAbs sc (qnameToString x) t' e'
    C.EProofAbs prop e1             -> do p <- importType sc env prop
                                          env' <- bindProp sc prop env
                                          e <- importExpr sc env' e1
                                          scLambda sc "_P" p e
    C.EProofApp e1                  -> case fastSchemaOf (envC env) e1 of
                                         C.Forall [] (p1 : _) _ ->
                                           do e <- importExpr sc env e1
                                              prf <- proveProp sc env p1
                                              scApply sc e prf
                                         s -> fail $ "EProofApp: invalid type: " ++ show (e1, s)
    C.ECast e1 t2                   -> do let t1 = fastTypeOf (envC env) e1
                                          t1' <- ty t1
                                          t2' <- ty t2
                                          e1' <- go e1
                                          scGlobalApply sc "Cryptol.eCast" [t1', t2', e1']
    C.EWhere e dgs                  -> do env' <- importDeclGroups sc env dgs
                                          importExpr sc env' e
  where
    go = importExpr sc env
    ty = importType sc env

-- | Creates the term \(x::ty a) -> e
scEAbs :: SharedContext s -> String -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scEAbs sc x a e =
  do t <- scGlobalApply sc "Cryptol.ty" [a]
     scLambda sc x t e

scNestedTuple :: SharedContext s -> [SharedTerm s] -> IO (SharedTerm s)
scNestedTuple _sc [] = unimplemented "ETuple []"
scNestedTuple _sc [x] = return x
scNestedTuple sc (x : xs) =
  do y <- scNestedTuple sc xs
     scTuple sc [x, y]

scNestedSelector :: SharedContext s -> Int -> Int -> SharedTerm s -> IO (SharedTerm s)
scNestedSelector sc i l t
  | i <= 1    = if i < l then scTupleSelector sc t 1 else return t
  | otherwise = scTupleSelector sc t 2 >>= scNestedSelector sc (i - 1) (l - 1)

-- | Currently this imports declaration groups by inlining all the
-- definitions. (With subterm sharing, this is not as bad as it might
-- seem.) We might want to think about generating let or where
-- expressions instead.
importDeclGroups :: SharedContext s -> Env s -> [C.DeclGroup] -> IO (Env s)
importDeclGroups _sc env [] = return env
importDeclGroups sc env (C.Recursive [decl] : dgs) =
  do env1 <- bindQName sc (C.dName decl) (C.dSignature decl) env
     t' <- importSchema sc env (C.dSignature decl)
     e' <- importExpr sc env1 (C.dDefinition decl)
     f' <- scLambda sc (qnameToString (C.dName decl)) t' e'
     rhs <- scGlobalApply sc "Cryptol.fix" [t', f']
     let env' = env { envE = Map.insert (C.dName decl) rhs (envE env)
                    , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env) }
     importDeclGroups sc env' dgs
importDeclGroups _sc _env (C.Recursive decls : _) = unimplemented $ "Recursive: " ++ show (map C.dName decls)
importDeclGroups sc env (C.NonRecursive decl : dgs) =
  do rhs <- importExpr sc env (C.dDefinition decl)
     let env' = env { envE = Map.insert (C.dName decl) rhs (envE env)
                    , envC = Map.insert (C.dName decl) (C.dSignature decl) (envC env) }
     importDeclGroups sc env' dgs

--------------------------------------------------------------------------------
-- List comprehensions

importComp :: SharedContext s -> Env s -> C.Type -> C.Expr -> [[C.Match]] -> IO (SharedTerm s)
importComp sc env listT expr mss =
  do let zipAll [] = fail "zero-branch list comprehension"
         zipAll [branch] =
           do (xs, len, ty, args) <- importMatches sc env branch
              m <- importType sc env len
              a <- importType sc env ty
              return (xs, m, a, [args])
         zipAll (branch : branches) =
           do (xs, len, ty, args) <- importMatches sc env branch
              m <- importType sc env len
              a <- importType sc env ty
              (ys, n, b, argss) <- zipAll branches
              zs <- scGlobalApply sc "Cryptol.zip" [a, b, m, n, xs, ys]
              mn <- scGlobalApply sc "Cryptol.tcMin" [m, n]
              ab <- scCtorApp sc "Cryptol.TCPair" [a, b]
              return (zs, mn, ab, args : argss)
     (xs, n, a, argss) <- zipAll mss
     let (_, elemT) = fromJust (C.tIsSeq listT)
     f <- lambdaTuples sc env elemT expr argss
     b <- importType sc env elemT
     ys <- scGlobalApply sc "Cryptol.map" [a, b, n, f, xs]
     -- The resulting type might not match the annotation, so we coerce
     t1 <- scCtorApp sc "Cryptol.TCSeq" [n, b]
     t2 <- importType sc env listT
     scGlobalApply sc "Cryptol.eCast" [t1, t2, ys]

lambdaTuples :: SharedContext s -> Env s -> C.Type -> C.Expr -> [[(C.QName, C.Type)]] -> IO (SharedTerm s)
lambdaTuples sc env _ty expr [] = importExpr sc env expr
lambdaTuples sc env ty expr (args : argss) =
  do f <- lambdaTuple sc env ty expr argss args
     if null args || null argss
       then return f
       else do a <- importType sc env (tNestedTuple (map snd args))
               b <- importType sc env (tNestedTuple (map (tNestedTuple . map snd) argss))
               c <- importType sc env ty
               scGlobalApply sc "Cryptol.uncurry" [a, b, c, f]

lambdaTuple :: SharedContext s -> Env s -> C.Type -> C.Expr -> [[(C.QName, C.Type)]] -> [(C.QName, C.Type)] -> IO (SharedTerm s)
lambdaTuple sc env ty expr argss [] = lambdaTuples sc env ty expr argss
lambdaTuple sc env ty expr argss ((x, t) : args) =
  do a <- importType sc env t
     env' <- bindQName sc x (C.Forall [] [] t) env
     e <- lambdaTuple sc env' ty expr argss args
     f <- scEAbs sc (qnameToString x) a e
     if null args
        then return f
        else do b <- importType sc env (tNestedTuple (map snd args))
                c <- importType sc env ty
                scGlobalApply sc "Cryptol.uncurry" [a, b, c, f]

tNestedTuple :: [C.Type] -> C.Type
tNestedTuple [] = C.tTuple []
tNestedTuple [t] = t
tNestedTuple (t : ts) = C.tTuple [t, tNestedTuple ts]


-- | Returns the shared term, length type, element tuple type, bound
-- variables.
importMatches :: SharedContext s -> Env s -> [C.Match]
              -> IO (SharedTerm s, C.Type, C.Type, [(C.QName, C.Type)])
importMatches _sc _env [] = fail "importMatches: empty comprehension branch"

importMatches sc env [C.From qname _ty expr] = do
  (len, ty) <- case C.tIsSeq (fastTypeOf (envC env) expr) of
                 Just x -> return x
                 Nothing -> fail $ "internal error: From: " ++ show (fastTypeOf (envC env) expr)
  xs <- importExpr sc env expr
  return (xs, len, ty, [(qname, ty)])

importMatches sc env (C.From qname _ty1 expr : matches) = do
  (len1, ty1) <- case C.tIsSeq (fastTypeOf (envC env) expr) of
                   Just x -> return x
                   Nothing -> fail $ "internal error: From: " ++ show (fastTypeOf (envC env) expr)
  m <- importType sc env len1
  a <- importType sc env ty1
  xs <- importExpr sc env expr
  env' <- bindQName sc qname (C.Forall [] [] ty1) env
  (body, len2, ty2, args) <- importMatches sc env' matches
  n <- importType sc env len2
  b <- importType sc env ty2
  f <- scEAbs sc (qnameToString qname) a body
  result <- scGlobalApply sc "Cryptol.from" [a, b, m, n, xs, f]
  return (result, (C..*.) len1 len2, C.tTuple [ty1, ty2], (qname, ty1) : args)

importMatches sc env [C.Let decl] =
  do e <- importExpr sc env (C.dDefinition decl)
     ty1 <- case C.dSignature decl of
              C.Forall [] [] ty1 -> return ty1
              _ -> unimplemented "polymorphic Let"
     a <- importType sc env ty1
     result <- scGlobalApply sc "Cryptol.single" [a, e]
     return (result, C.tOne, ty1, [(C.dName decl, ty1)])

importMatches sc env (C.Let decl : matches) =
  do e <- importExpr sc env (C.dDefinition decl)
     ty1 <- case C.dSignature decl of
              C.Forall [] [] ty1 -> return ty1
              _ -> unimplemented "polymorphic Let"
     a <- importType sc env ty1
     env' <- bindQName sc (C.dName decl) (C.dSignature decl) env
     (body, len, ty2, args) <- importMatches sc env' matches
     n <- importType sc env len
     b <- importType sc env ty2
     f <- scEAbs sc (qnameToString (C.dName decl)) a body
     result <- scGlobalApply sc "Cryptol.mlet" [a, b, n, e, f]
     return (result, len, C.tTuple [ty1, ty2], (C.dName decl, ty1) : args)

tIsWidth :: C.Type -> Maybe C.Type
tIsWidth ty = case C.tNoUser ty of
                C.TCon (C.TF C.TCWidth) [t1] -> Just t1
                _                            -> Nothing

tIsSub :: C.Type -> Maybe (C.Type, C.Type)
tIsSub ty = case C.tNoUser ty of
              C.TCon (C.TF C.TCSub) [t1, t2] -> Just (t1, t2)
              _                              -> Nothing

tIsMax :: C.Type -> Maybe (C.Type, C.Type)
tIsMax ty = case C.tNoUser ty of
              C.TCon (C.TF C.TCMax) [t1, t2] -> Just (t1, t2)
              _                              -> Nothing
