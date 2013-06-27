{-# LANGUAGE TemplateHaskell #-}
module SAWScript.Prelude where

import SAWScript.AST hiding (Name)
import SAWScript.NewAST

import Verifier.SAW.ParserUtils hiding (ModuleName, preludeName)
import Verifier.SAW.Prelude

import qualified Data.Map as M
import Language.Haskell.TH.Syntax hiding (Name)

$(runDecWriter $ do
  let prelName = returnQ $ VarE (mkName "preludeModule")
  preludeExp <- defineImport prelName preludeModule
  prelude <- defineModuleFromFile
               [ preludeExp ]
               "ssPreludeModule"
               "prelude/prelude.sawcore"
  declareSharedModuleFns "SAWScriptPrelude" (decVal prelude)
 )

preludeName :: ModuleName
preludeName = ModuleName [] "Prelude"


preludeEnv :: [(ResolvedName, Schema)]
preludeEnv = map qualify $
  [ ( "return"
    , Forall ["m", "a"]
             (tFun (boundVar "a") (tBlock (boundVar "m") (boundVar "a")))
    )
  , ( "bitSequence"
    , Forall ["n"] (tFun tZ (tArray (boundVar "n") tBool))
    )
  , ( "read_aig" , Forall [] (tFun tString (topLevel term)) )
  , ( "read_sbv" , Forall [] (tFun tString (topLevel term)) )
  , ( "write_aig"
    , Forall [] (tFun tString (tFun term (topLevel tUnit)))
    )
  , ( "write_smtlib1"
    , Forall [] (tFun tString (tFun term (topLevel tUnit)))
    )
  , ( "write_smtlib2"
    , Forall [] (tFun tString (tFun term (topLevel tUnit)))
    )
  , ( "equal"
    , Forall [] (tFun term (tFun term (topLevel term)))
    )
  , ( "negate"
    , Forall [] (tFun term (topLevel term))
    )
  , ( "prove"
    , Forall [] (tFun (proofScript proofResult) (tFun term (topLevel tUnit)))
    )
  , ( "sat"
    , Forall [] (tFun (proofScript proofResult) (tFun term (topLevel tUnit)))
    )
  , ( "abc"
    , Forall [] (proofScript proofResult)
    )
  , ( "java_pure"
    , Forall [] (javaSetup tUnit)
    )
  , ( "java_extract"
    , Forall [] (tFun tString
                 (tFun tString
                  (tFun (javaSetup tUnit) (topLevel term))))
    )
  , ( "llvm_pure", Forall [] (llvmSetup tUnit) )
  , ( "llvm_extract"
    , Forall [] (tFun tString
                 (tFun tString
                  (tFun (llvmSetup tUnit) (topLevel term))))
    )
  , ( "print"
    , Forall ["a"]
             (tFun (boundVar "a") (topLevel (tTuple [])))
    )
  ]
  where topLevel = tBlock (tContext TopLevel)
        llvmSetup = tBlock (tContext LLVMSetup)
        javaSetup = tBlock (tContext JavaSetup)
        term =  TyCon (AbstractCon "Term") []
        proofScript = tBlock (tContext ProofScript)
        proofResult = TyCon (AbstractCon "ProofScript") []
        boundVar = TyVar . BoundVar
        tUnit = tTuple []
        qualify (n, ty) = (TopLevelName preludeName n, ty)
