{-# OPTIONS_GHC -w #-}
module SAWScript.Parser ( parseLine, parseFile ) where

import Data.List ( head )

import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST

-- parser produced by Happy Version 1.18.9

data HappyAbsSyn t5 t6 t7 t8 t9 t10 t11 t12
	= HappyTerminal (T.Token AlexPosn)
	| HappyErrorToken Int
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 t12

action_0 (13) = happyShift action_3
action_0 (14) = happyShift action_7
action_0 (18) = happyShift action_8
action_0 (19) = happyShift action_9
action_0 (20) = happyShift action_10
action_0 (22) = happyShift action_11
action_0 (5) = happyGoto action_4
action_0 (6) = happyGoto action_12
action_0 _ = happyFail

action_1 (13) = happyShift action_3
action_1 (14) = happyShift action_7
action_1 (18) = happyShift action_8
action_1 (19) = happyShift action_9
action_1 (20) = happyShift action_10
action_1 (22) = happyShift action_11
action_1 (5) = happyGoto action_4
action_1 (6) = happyGoto action_5
action_1 (10) = happyGoto action_6
action_1 _ = happyReduce_17

action_2 (13) = happyShift action_3
action_2 _ = happyFail

action_3 (25) = happyShift action_19
action_3 (12) = happyGoto action_26
action_3 _ = happyReduce_24

action_4 (13) = happyShift action_3
action_4 (14) = happyShift action_7
action_4 (18) = happyShift action_15
action_4 (19) = happyShift action_16
action_4 (20) = happyShift action_10
action_4 (22) = happyShift action_11
action_4 (5) = happyGoto action_25
action_4 _ = happyReduce_9

action_5 (24) = happyShift action_24
action_5 _ = happyReduce_18

action_6 (27) = happyAccept
action_6 _ = happyFail

action_7 (13) = happyShift action_3
action_7 (14) = happyShift action_7
action_7 (18) = happyShift action_15
action_7 (19) = happyShift action_16
action_7 (20) = happyShift action_10
action_7 (22) = happyShift action_11
action_7 (5) = happyGoto action_23
action_7 _ = happyFail

action_8 (19) = happyShift action_21
action_8 (20) = happyShift action_22
action_8 (11) = happyGoto action_20
action_8 _ = happyFail

action_9 (16) = happyShift action_18
action_9 (25) = happyShift action_19
action_9 (12) = happyGoto action_17
action_9 _ = happyReduce_24

action_10 (13) = happyShift action_3
action_10 (14) = happyShift action_7
action_10 (18) = happyShift action_15
action_10 (19) = happyShift action_16
action_10 (20) = happyShift action_10
action_10 (22) = happyShift action_11
action_10 (5) = happyGoto action_14
action_10 _ = happyFail

action_11 (13) = happyShift action_3
action_11 (14) = happyShift action_7
action_11 (18) = happyShift action_8
action_11 (19) = happyShift action_9
action_11 (20) = happyShift action_10
action_11 (22) = happyShift action_11
action_11 (5) = happyGoto action_4
action_11 (6) = happyGoto action_5
action_11 (10) = happyGoto action_13
action_11 _ = happyReduce_17

action_12 (27) = happyAccept
action_12 _ = happyFail

action_13 (23) = happyShift action_37
action_13 _ = happyFail

action_14 (13) = happyShift action_3
action_14 (14) = happyShift action_7
action_14 (18) = happyShift action_15
action_14 (19) = happyShift action_16
action_14 (20) = happyShift action_10
action_14 (21) = happyShift action_36
action_14 (22) = happyShift action_11
action_14 (5) = happyGoto action_25
action_14 _ = happyFail

action_15 (19) = happyShift action_31
action_15 (20) = happyShift action_22
action_15 (11) = happyGoto action_20
action_15 _ = happyFail

action_16 (25) = happyShift action_19
action_16 (12) = happyGoto action_17
action_16 _ = happyReduce_24

action_17 _ = happyReduce_6

action_18 (13) = happyShift action_3
action_18 (14) = happyShift action_7
action_18 (18) = happyShift action_15
action_18 (19) = happyShift action_16
action_18 (20) = happyShift action_10
action_18 (22) = happyShift action_11
action_18 (5) = happyGoto action_35
action_18 _ = happyFail

action_19 (19) = happyShift action_34
action_19 (7) = happyGoto action_33
action_19 _ = happyFail

action_20 (17) = happyShift action_32
action_20 _ = happyFail

action_21 (19) = happyShift action_31
action_21 (20) = happyShift action_22
action_21 (11) = happyGoto action_30
action_21 _ = happyReduce_20

action_22 (19) = happyShift action_29
action_22 _ = happyFail

action_23 (13) = happyShift action_3
action_23 (14) = happyShift action_7
action_23 (15) = happyShift action_28
action_23 (18) = happyShift action_15
action_23 (19) = happyShift action_16
action_23 (20) = happyShift action_10
action_23 (22) = happyShift action_11
action_23 (5) = happyGoto action_25
action_23 _ = happyFail

action_24 (13) = happyShift action_3
action_24 (14) = happyShift action_7
action_24 (18) = happyShift action_8
action_24 (19) = happyShift action_9
action_24 (20) = happyShift action_10
action_24 (22) = happyShift action_11
action_24 (5) = happyGoto action_4
action_24 (6) = happyGoto action_5
action_24 (10) = happyGoto action_27
action_24 _ = happyReduce_17

action_25 (13) = happyShift action_3
action_25 (14) = happyShift action_7
action_25 (18) = happyShift action_15
action_25 (19) = happyShift action_16
action_25 (20) = happyShift action_10
action_25 (22) = happyShift action_11
action_25 (5) = happyGoto action_25
action_25 _ = happyReduce_8

action_26 _ = happyReduce_2

action_27 _ = happyReduce_19

action_28 (13) = happyShift action_3
action_28 (14) = happyShift action_7
action_28 (18) = happyShift action_15
action_28 (19) = happyShift action_16
action_28 (20) = happyShift action_10
action_28 (22) = happyShift action_11
action_28 (5) = happyGoto action_44
action_28 (8) = happyGoto action_45
action_28 (9) = happyGoto action_46
action_28 _ = happyFail

action_29 (25) = happyShift action_43
action_29 _ = happyFail

action_30 (17) = happyReduce_21
action_30 (25) = happyShift action_19
action_30 (12) = happyGoto action_42
action_30 _ = happyReduce_24

action_31 (19) = happyShift action_31
action_31 (20) = happyShift action_22
action_31 (11) = happyGoto action_41
action_31 _ = happyReduce_20

action_32 (13) = happyShift action_3
action_32 (14) = happyShift action_7
action_32 (18) = happyShift action_15
action_32 (19) = happyShift action_16
action_32 (20) = happyShift action_10
action_32 (22) = happyShift action_11
action_32 (5) = happyGoto action_40
action_32 _ = happyFail

action_33 _ = happyReduce_25

action_34 (17) = happyShift action_39
action_34 _ = happyReduce_12

action_35 (13) = happyShift action_3
action_35 (14) = happyShift action_7
action_35 (18) = happyShift action_15
action_35 (19) = happyShift action_16
action_35 (20) = happyShift action_10
action_35 (22) = happyShift action_11
action_35 (5) = happyGoto action_25
action_35 _ = happyReduce_10

action_36 _ = happyReduce_7

action_37 (25) = happyShift action_19
action_37 (12) = happyGoto action_38
action_37 _ = happyReduce_24

action_38 _ = happyReduce_5

action_39 (19) = happyShift action_34
action_39 (7) = happyGoto action_53
action_39 _ = happyFail

action_40 (13) = happyShift action_3
action_40 (14) = happyShift action_7
action_40 (18) = happyShift action_15
action_40 (19) = happyShift action_16
action_40 (20) = happyShift action_10
action_40 (22) = happyShift action_11
action_40 (25) = happyShift action_19
action_40 (5) = happyGoto action_25
action_40 (12) = happyGoto action_52
action_40 _ = happyReduce_24

action_41 _ = happyReduce_21

action_42 (16) = happyShift action_51
action_42 _ = happyFail

action_43 (19) = happyShift action_34
action_43 (7) = happyGoto action_50
action_43 _ = happyFail

action_44 (13) = happyShift action_3
action_44 (14) = happyShift action_7
action_44 (17) = happyShift action_49
action_44 (18) = happyShift action_15
action_44 (19) = happyShift action_16
action_44 (20) = happyShift action_10
action_44 (22) = happyShift action_11
action_44 (5) = happyGoto action_25
action_44 _ = happyFail

action_45 (26) = happyShift action_48
action_45 _ = happyReduce_15

action_46 (25) = happyShift action_19
action_46 (12) = happyGoto action_47
action_46 _ = happyReduce_24

action_47 _ = happyReduce_4

action_48 (13) = happyShift action_3
action_48 (14) = happyShift action_7
action_48 (18) = happyShift action_15
action_48 (19) = happyShift action_16
action_48 (20) = happyShift action_10
action_48 (22) = happyShift action_11
action_48 (5) = happyGoto action_44
action_48 (8) = happyGoto action_45
action_48 (9) = happyGoto action_57
action_48 _ = happyFail

action_49 (13) = happyShift action_3
action_49 (14) = happyShift action_7
action_49 (18) = happyShift action_15
action_49 (19) = happyShift action_16
action_49 (20) = happyShift action_10
action_49 (22) = happyShift action_11
action_49 (5) = happyGoto action_56
action_49 _ = happyFail

action_50 (21) = happyShift action_55
action_50 _ = happyFail

action_51 (13) = happyShift action_3
action_51 (14) = happyShift action_7
action_51 (18) = happyShift action_15
action_51 (19) = happyShift action_16
action_51 (20) = happyShift action_10
action_51 (22) = happyShift action_11
action_51 (5) = happyGoto action_54
action_51 _ = happyFail

action_52 _ = happyReduce_3

action_53 _ = happyReduce_13

action_54 (13) = happyShift action_3
action_54 (14) = happyShift action_7
action_54 (18) = happyShift action_15
action_54 (19) = happyShift action_16
action_54 (20) = happyShift action_10
action_54 (22) = happyShift action_11
action_54 (5) = happyGoto action_25
action_54 _ = happyReduce_11

action_55 (19) = happyShift action_31
action_55 (20) = happyShift action_22
action_55 (11) = happyGoto action_58
action_55 _ = happyReduce_22

action_56 (13) = happyShift action_3
action_56 (14) = happyShift action_7
action_56 (18) = happyShift action_15
action_56 (19) = happyShift action_16
action_56 (20) = happyShift action_10
action_56 (22) = happyShift action_11
action_56 (5) = happyGoto action_25
action_56 _ = happyReduce_14

action_57 _ = happyReduce_16

action_58 _ = happyReduce_23

happyReduce_2 = happySpecReduce_2  5 happyReduction_2
happyReduction_2 (HappyAbsSyn12  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn5
		 (Pattern (parsePattern (T.tokStr happy_var_1)) happy_var_2
	)
happyReduction_2 _ _  = notHappyAtAll 

happyReduce_3 = happyReduce 5 5 happyReduction_3
happyReduction_3 ((HappyAbsSyn12  happy_var_5) `HappyStk`
	(HappyAbsSyn5  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Func (parseArrowType (T.tokStr happy_var_1)) happy_var_2 happy_var_4 happy_var_5
	) `HappyStk` happyRest

happyReduce_4 = happyReduce 5 5 happyReduction_4
happyReduction_4 ((HappyAbsSyn12  happy_var_5) `HappyStk`
	(HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn5  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Switch happy_var_2 happy_var_4 happy_var_5
	) `HappyStk` happyRest

happyReduce_5 = happyReduce 4 5 happyReduction_5
happyReduction_5 ((HappyAbsSyn12  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn10  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (DM happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_6 = happySpecReduce_2  5 happyReduction_6
happyReduction_6 (HappyAbsSyn12  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn5
		 (Var (T.tokStr happy_var_1) happy_var_2
	)
happyReduction_6 _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_3  5 happyReduction_7
happyReduction_7 _
	(HappyAbsSyn5  happy_var_2)
	_
	 =  HappyAbsSyn5
		 (happy_var_2
	)
happyReduction_7 _ _ _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_2  5 happyReduction_8
happyReduction_8 (HappyAbsSyn5  happy_var_2)
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn5
		 (App happy_var_1 happy_var_2 Nothing
	)
happyReduction_8 _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_1  6 happyReduction_9
happyReduction_9 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn6
		 ((Nothing, happy_var_1)
	)
happyReduction_9 _  = notHappyAtAll 

happyReduce_10 = happySpecReduce_3  6 happyReduction_10
happyReduction_10 (HappyAbsSyn5  happy_var_3)
	_
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn6
		 ((Just (T.tokStr happy_var_1), happy_var_3)
	)
happyReduction_10 _ _ _  = notHappyAtAll 

happyReduce_11 = happyReduce 6 6 happyReduction_11
happyReduction_11 ((HappyAbsSyn5  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn12  happy_var_4) `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	(HappyTerminal happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 ((Just (T.tokStr happy_var_2), Func (parseArrowType (T.tokStr happy_var_1)) happy_var_3 happy_var_6 happy_var_4)
	) `HappyStk` happyRest

happyReduce_12 = happySpecReduce_1  7 happyReduction_12
happyReduction_12 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn7
		 (TypeVariable (T.tokStr happy_var_1)
	)
happyReduction_12 _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_3  7 happyReduction_13
happyReduction_13 (HappyAbsSyn7  happy_var_3)
	_
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn7
		 (Arrow (TypeVariable (T.tokStr happy_var_1)) happy_var_3
	)
happyReduction_13 _ _ _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_3  8 happyReduction_14
happyReduction_14 (HappyAbsSyn5  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn8
		 ((happy_var_1, happy_var_3)
	)
happyReduction_14 _ _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  9 happyReduction_15
happyReduction_15 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn9
		 ([happy_var_1]
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_3  9 happyReduction_16
happyReduction_16 (HappyAbsSyn9  happy_var_3)
	_
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_1 : happy_var_3
	)
happyReduction_16 _ _ _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_0  10 happyReduction_17
happyReduction_17  =  HappyAbsSyn10
		 ([]
	)

happyReduce_18 = happySpecReduce_1  10 happyReduction_18
happyReduction_18 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn10
		 ([happy_var_1]
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_3  10 happyReduction_19
happyReduction_19 (HappyAbsSyn10  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn10
		 (happy_var_1 : happy_var_3
	)
happyReduction_19 _ _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  11 happyReduction_20
happyReduction_20 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn11
		 ([((T.tokStr happy_var_1), Nothing)]
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_2  11 happyReduction_21
happyReduction_21 (HappyAbsSyn11  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn11
		 (((T.tokStr happy_var_1), Nothing) : happy_var_2
	)
happyReduction_21 _ _  = notHappyAtAll 

happyReduce_22 = happyReduce 5 11 happyReduction_22
happyReduction_22 (_ `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 ([((T.tokStr happy_var_2), Just happy_var_4)]
	) `HappyStk` happyRest

happyReduce_23 = happyReduce 6 11 happyReduction_23
happyReduction_23 ((HappyAbsSyn11  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn7  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn11
		 (((T.tokStr happy_var_2), Just happy_var_4) : happy_var_6
	) `HappyStk` happyRest

happyReduce_24 = happySpecReduce_0  12 happyReduction_24
happyReduction_24  =  HappyAbsSyn12
		 (Nothing
	)

happyReduce_25 = happySpecReduce_2  12 happyReduction_25
happyReduction_25 (HappyAbsSyn7  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (Just happy_var_2
	)
happyReduction_25 _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 27 27 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	T.Pattern _ _ -> cont 13;
	T.Keyword _ "case" -> cont 14;
	T.Keyword _ "of" -> cont 15;
	T.InfixOp _ "=" -> cont 16;
	T.InfixOp _ "->" -> cont 17;
	T.ArrowType _ _ -> cont 18;
	T.Identifier _ _ -> cont 19;
	T.OutfixL _ "(" -> cont 20;
	T.OutfixR _ ")" -> cont 21;
	T.OutfixL _ "{" -> cont 22;
	T.OutfixR _ "}" -> cont 23;
	T.InfixOp _ ";" -> cont 24;
	T.InfixOp _ ":" -> cont 25;
	T.InfixOp _ "|" -> cont 26;
	_ -> happyError' (tk:tks)
	}

happyError_ 27 tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

happyThen :: () => Either String a -> (a -> Either String b) -> Either String b
happyThen = (>>=)
happyReturn :: () => a -> Either String a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Either String a
happyReturn1 = \a tks -> (return) a
happyError' :: () => [(T.Token AlexPosn)] -> Either String a
happyError' = parseError

parseDecl tks = happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn6 z -> happyReturn z; _other -> notHappyAtAll })

parseDecls tks = happySomeParser where
  happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn10 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


-- Additional Parsing

-- Warning: Assumes input matching \'[0-1]*
parsePattern :: String -> Pattern
parsePattern ('\'':bits) = Literal (map (\c -> c == '1') bits)

parseArrowType :: String -> ArrowType
parseArrowType "let" = Let
parseArrowType "fun" = Fun
parseArrowType "inj" = Inj
parseArrowType "sur" = Sur
parseArrowType "iso" = Iso

-- Error Handling

parseError tokens = Left ("Parse error: " ++ (show . head $ tokens))

-- Toplevel Parse

parseLine :: String -> Either String (Maybe String, Expr (Maybe SAWType))
parseLine s = parseDecl . alexScanTokens $ s

parseFile :: FilePath -> Either String (Maybe String, Expr (Maybe SAWType))
parseFile f = Right (Just f, DM [] Nothing) --TODO
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "<built-in>" #-}
{-# LINE 1 "<command-line>" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp 

{-# LINE 30 "templates/GenericTemplate.hs" #-}








{-# LINE 51 "templates/GenericTemplate.hs" #-}

{-# LINE 61 "templates/GenericTemplate.hs" #-}

{-# LINE 70 "templates/GenericTemplate.hs" #-}

infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is (1), it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
	happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
	 (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action

{-# LINE 148 "templates/GenericTemplate.hs" #-}

-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Int ->                    -- token number
         Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k - ((1) :: Int)) sts of
	 sts1@(((st1@(HappyState (action))):(_))) ->
        	let r = fn stk in  -- it doesn't hurt to always seq here...
       		happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
        happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
       happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))
       where (sts1@(((st1@(HappyState (action))):(_)))) = happyDrop k ((st):(sts))
             drop_stk = happyDropStk k stk





             new_state = action


happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n - ((1) :: Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n - ((1)::Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction

{-# LINE 246 "templates/GenericTemplate.hs" #-}
happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery ((1) is the error token)

-- parse error if we are in recovery and we fail again
happyFail (1) tk old_st _ stk@(x `HappyStk` _) =
     let (i) = (case x of { HappyErrorToken (i) -> i }) in
--	trace "failing" $ 
        happyError_ i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  (1) tk old_st (((HappyState (action))):(sts)) 
						(saved_tok `HappyStk` _ `HappyStk` stk) =
--	trace ("discarding state, depth " ++ show (length stk))  $
	action (1) (1) tk (HappyState (action)) sts ((saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail  i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
	action (1) (1) tk (HappyState (action)) sts ( (HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--	happySeq = happyDoSeq
-- otherwise it emits
-- 	happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.

{-# LINE 312 "templates/GenericTemplate.hs" #-}
{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
