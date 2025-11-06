{-# LANGUAGE LambdaCase #-}

module SAWScript.AutoMatch.JVM where

import qualified Language.JVM.Parser as JVM

--import SAWCentral.Builtins
--import SAWCentral.Options
import SAWScript.AutoMatch.Declaration
import SAWScript.AutoMatch.Interaction
import SAWScript.AutoMatch.Util

import Control.Monad
import Control.Monad.Free
import Data.Either
import qualified Data.Text as Text

-- | Parse a Java class into a list of declarations
--   Yields an Interaction so that we can talk to the user about what went wrong
getDeclsJVM :: JVM.Class -> IO (Interaction (Maybe [Decl]))
getDeclsJVM cls = return $ do

   let (untranslateable, translations) =
         partitionEithers . for (JVM.classMethods cls) $ \method ->
            maybe (Left $ JVM.methodName method) Right $ do
               returnType <- jssTypeToStdType =<< JVM.methodReturnType method
               argTypes <- mapM jssTypeToStdType $ JVM.methodParameterTypes method
               let argIndices = map (JVM.localIndexOfParameter method) [0 .. length argTypes - 1]
               tableEntries <- forM argIndices $ JVM.lookupLocalVariableByIdx method 0
               let getname name = Text.pack $ JVM.localName name
                   args = zipWith Arg (map getname tableEntries) argTypes
               return $ Decl (Text.pack $ JVM.methodName method) returnType args

   when (not . null $ untranslateable) $ do
      separator ThinSep
      liftF . flip Warning () $ "No translation for the following signatures in " ++ JVM.unClassName (JVM.className cls) ++ ".class:"
      bulleted $ map (("'" ++) . (++ "'")) untranslateable

   return $ Just translations

   where

      jssTypeToStdType = \case
         JVM.ArrayType _    -> Nothing -- TODO: Handle array types
         JVM.BooleanType    -> Just $ TCon (TC TCBit) []
         JVM.ByteType       -> Just $ bitSeqType 8
         JVM.CharType       -> Just $ bitSeqType 16 -- TODO: Not sure about this equivalence
         JVM.ClassType _str -> Nothing -- TODO: Support classes as records?
         JVM.DoubleType     -> Nothing -- We don't support floating point types
         JVM.FloatType      -> Nothing -- We don't support floating point types
         JVM.IntType        -> Just $ bitSeqType 32
         JVM.LongType       -> Just $ bitSeqType 64
         JVM.ShortType      -> Just $ bitSeqType 16
