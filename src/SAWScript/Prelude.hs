{-# LANGUAGE TemplateHaskell #-}
module SAWScript.Prelude where

import SAWScript.AST hiding (Name)
import SAWScript.NewAST

import Verifier.SAW.ParserUtils hiding (ModuleName, preludeName)
import Verifier.SAW.Prelude

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
  , ( "read_aig" , Forall ["a"] (tFun tString (topLevel (boundVar "a"))) )
  , ( "read_sbv" , Forall ["a"] (tFun tString (topLevel (boundVar "a"))) )
  , ( "write_aig"
    , Forall ["a"] (tFun tString (tFun (boundVar "a") (topLevel tUnit)))
    )
  , ( "write_smtlib1"
    , Forall ["a"] (tFun tString (tFun (boundVar "a") (topLevel tUnit)))
    )
  , ( "write_smtlib2"
    , Forall ["a"] (tFun tString (tFun (boundVar "a") (topLevel tUnit)))
    )
  , ( "write_core"
    , Forall ["a"] (tFun tString (tFun (boundVar "a") (topLevel tUnit)))
    )
  , ( "read_core"
    , Forall ["a"] (tFun tString (topLevel (boundVar "a")))
    )
  , ( "equal"
    , Forall [] (tFun term (tFun term (topLevel term)))
    )
  , ( "not"
    , Forall [] (tFun tBool tBool)
    )
  , ( "and"
    , Forall [] (tFun tBool (tFun tBool tBool))
    )
  , ( "or"
    , Forall [] (tFun tBool (tFun tBool tBool))
    )
  , ( "eq"
    , Forall ["a"] (tFun (boundVar "a") (tFun (boundVar "a") tBool))
    )
  , ( "negate"
    , Forall [] (tFun term (topLevel term))
    )
  , ( "prove"
    , Forall ["a"] (tFun (proofScript proofResult) (tFun (boundVar "a") (topLevel tUnit)))
    )
  , ( "sat"
    , Forall ["a"] (tFun (proofScript proofResult) (tFun (boundVar "a") (topLevel tUnit)))
    )
  , ( "rewrite"
    , Forall ["a"] (tFun tUnit (tFun (boundVar "a") (topLevel (boundVar "a"))))
    -- TODO: add simpset argument (for now just use default rewrite rules)
    )
  , ( "abc"
    , Forall [] (proofScript proofResult)
    )
  , ( "java_pure"
    , Forall [] (javaSetup tUnit)
    )
  , ( "java_extract"
    , Forall ["a"] (tFun tString
                    (tFun tString
                     (tFun (javaSetup tUnit) (topLevel (boundVar "a")))))
    )
  , ( "llvm_pure", Forall [] (llvmSetup tUnit) )
  , ( "llvm_extract"
    , Forall ["a"] (tFun tString
                    (tFun tString
                     (tFun (llvmSetup tUnit) (topLevel (boundVar "a")))))
    )
  , ( "print"
    , Forall ["a"] (tFun (boundVar "a") (topLevel tUnit))
    )
  , ( "print_type"
    , Forall ["a"] (tFun (boundVar "a") (topLevel tUnit))
    )
  , ( "print_term"
    , Forall ["a"] (tFun (boundVar "a") (topLevel tUnit))
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
