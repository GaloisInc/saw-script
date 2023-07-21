{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Test.SAWT.Interpret (tests) where

import Control.Exception (SomeException, try)
import Data.List.NonEmpty (NonEmpty ((:|)))
import SAWScript.AST (Stmt)
import SAWScript.Lexer qualified as SAW
import SAWScript.Parser qualified as SAW
import SAWScript.Value (isVUnit)
import SAWT
  ( resetSAWEnv,
    runSAWTDefault,
  )
import SAWT.Interpret
  ( interpretSAWScript,
    interpretSAWStmt,
    interpretSAWStmtCache,
    tryInterpretSAWStmt,
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertFailure, testCase)
import Text.Printf (printf)

tests :: TestTree
tests =
  testGroup
    "Test.SAWT.Interpret"
    [ testCase "print 3" testInterpretPrint,
      testCase "bind and print" testInterpretBindPrint,
      testCase "use unbound variable, error via exception" testInterpretUnboundTry,
      testCase "use unbound variable, error via Either" testInterpretUnboundEither,
      testCase "statement interpretation w/ cache hit" testInterpretCacheHit,
      testCase "statement interpretation w/ populated cache miss" testInterpretCacheMiss,
      testCase "statement interpretation w/ empty cache miss" testInterpretCacheEmpty,
      testCase "script interpretation expecting cache hit" testInterpretScriptCacheHit,
      testCase "script interpretation w/ populated cache miss" testInterpretScriptCacheMiss
    ]

testInterpretPrint :: Assertion
testInterpretPrint =
  do
    let p = parseStmt "print 3"
    (val, output) <- runSAWTDefault (interpretSAWStmt p)
    case (val, output) of
      (_, Just "3\n") | isVUnit val -> pure ()
      (_, Just out) -> assertFailure (printf "value was %s, output was \"%s\"" (show val) out)
      (_, Nothing) -> assertFailure (printf "value was %s, generated no output" (show val))

testInterpretBindPrint :: Assertion
testInterpretBindPrint =
  do
    let b = parseStmt "let x = 3"
    let p = parseStmt "print x"
    (val, output) <- runSAWTDefault (interpretSAWStmt b >> interpretSAWStmt p)
    case (val, output) of
      (_, Just "3\n") | isVUnit val -> pure ()
      (_, Just out) ->
        assertFailure (printf "value was %s, output was \"%s\"" (show val) out)
      (_, Nothing) ->
        assertFailure (printf "value was %s, generated no output" (show val))

testInterpretUnboundTry :: Assertion
testInterpretUnboundTry =
  do
    let p = parseStmt "print x"
    result <- try (runSAWTDefault (interpretSAWStmt p))
    case result of
      Left (_e :: SomeException) -> pure ()
      Right (val, Just out) ->
        assertFailure (printf "value was %s, output was \"%s\"" (show val) out)
      Right (val, Nothing) ->
        assertFailure (printf "value was %s, no output" (show val))

testInterpretUnboundEither :: Assertion
testInterpretUnboundEither =
  do
    let p = parseStmt "print x"
    runSAWTDefault (tryInterpretSAWStmt p) >>= \case
      Left _err -> pure ()
      Right (val, Just out) ->
        assertFailure (printf "value was %s, output was \"%s\"" (show val) out)
      Right (val, Nothing) ->
        assertFailure (printf "value was %s, no output" (show val))

-- | Ensure cache lookup succeeds on same statements in same context
testInterpretCacheHit :: Assertion
testInterpretCacheHit =
  do
    let p = parseStmt "print 3"
    res <- runSAWTDefault $
      do
        missRes <- interpretSAWStmtCache p
        resetSAWEnv
        hitRes <- interpretSAWStmtCache p
        pure $ resultSimilarity missRes hitRes
    case res of
      Left err -> assertFailure err
      Right () -> pure ()
  where
    resultSimilarity (missHit, missVal, missOutM) (hitHit, hitVal, hitOutM) =
      let success =
            and
              [ not missHit,
                hitHit,
                isVUnit missVal,
                isVUnit hitVal,
                missOutM == hitOutM
              ]
       in if success
            then Right ()
            else
              Left $
                unlines
                  [ printf "miss statement hit: %s" (show missHit),
                    printf "miss statement val: %s" (show missVal),
                    printf "miss statement out: %s" (show missOutM),
                    printf "hit statement hit: %s" (show hitHit),
                    printf "hit statement val: %s" (show hitVal),
                    printf "hit statement out: %s" (show hitOutM)
                  ]

-- | Ensure cache lookup fails on different statements in same context
testInterpretCacheMiss :: Assertion
testInterpretCacheMiss =
  do
    let p1 = parseStmt "print 3"
        p2 = parseStmt "print 4"
    res <- runSAWTDefault $
      do
        (hit1, _, _) <- interpretSAWStmtCache p1
        resetSAWEnv
        (hit2, _, _) <- interpretSAWStmtCache p2
        pure $ if hit1 || hit2 then Left "unexpected cache hit" else Right ()
    case res of
      Left err -> assertFailure err
      Right () -> pure ()

-- | Ensure `interpretSAWStmt` doesn't populate the cache
testInterpretCacheEmpty :: Assertion
testInterpretCacheEmpty =
  do
    let p = parseStmt "print 3"
    res <- runSAWTDefault $
      do
        _ <- interpretSAWStmt p
        resetSAWEnv
        (hit, _, _) <- interpretSAWStmtCache p
        pure $ if hit then Left "unexpected cache hit" else Right ()
    case res of
      Left err -> assertFailure err
      Right () -> pure ()

-- | Ensure cache lookup succeeds on same script
testInterpretScriptCacheHit :: Assertion
testInterpretScriptCacheHit =
  do
    let script = parseStmt "print 3" :| []
    res <- runSAWTDefault $
      do
        res1 <- interpretSAWScript False script
        res2 <- interpretSAWScript False script
        pure $ resultSimilarity res1 res2
    case res of
      Left err -> assertFailure err
      Right () -> pure ()
  where
    resultSimilarity (missHits, missVal, missOutM) (hitHits, hitVal, hitOutM) =
      let success =
            and
              [ missHits + 1 == hitHits,
                isVUnit missVal,
                isVUnit hitVal,
                missOutM == hitOutM
              ]
       in if success
            then Right ()
            else
              Left $
                unlines
                  [ printf "miss statement hits: %i" missHits,
                    printf "miss statement val: %s" (show missVal),
                    printf "miss statement out: %s" (show missOutM),
                    printf "hit statement hits: %i" hitHits,
                    printf "hit statement val: %s" (show hitVal),
                    printf "hit statement out: %s" (show hitOutM)
                  ]

-- | Ensure cache lookup fails on different scripts
testInterpretScriptCacheMiss :: Assertion
testInterpretScriptCacheMiss =
  do
    let script1 = parseStmt "print 3" :| []
        script2 = parseStmt "print 4" :| []
    res <- runSAWTDefault $
      do
        (hits1, _, _) <- interpretSAWScript False script1
        (hits2, _, _) <- interpretSAWScript False script2
        pure $ if hits1 + hits2 > 0 then Left "unexpected cache hit" else Right ()
    case res of
      Left err -> assertFailure err
      Right () -> pure ()

-- testSplitCheckpoint :: Assertion
-- testSplitCheckpoint =
--   do
--     let b1 = parseStmt "let x = 3"
--         b2 = parseStmt "let y = 4"
--         context = mkContext [b1, b2]
--     checkpoint <- runSAWTDefault $
--       do
--         void (interpretSAWStmtCheckpoint b1)
--         void (interpretSAWStmtCheckpoint b2)

--         (val, outM) <- interpretSAWStmt b2
--         rememberSAWCheckpoint val outM
--     undefined

-- checkpoints = addCheckpoint context

-- Partial
parseStmt :: String -> Stmt
parseStmt src =
  either (error . show) id (SAW.parseStmt (SAW.lexSAW "<Test.SAWT.Interpret>" src))
