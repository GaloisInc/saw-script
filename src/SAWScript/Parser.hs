{-# OPTIONS_GHC -w #-}
module SAWScript.Parser ( parse ) where

import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST

-- parser produced by Happy Version 1.18.9

data HappyAbsSyn 
	= HappyTerminal (T.Token AlexPosn)
	| HappyErrorToken Int
	| HappyAbsSyn4 (Statement (Maybe Type))
	| HappyAbsSyn5 (Declaration (Maybe Type))
	| HappyAbsSyn7 ((Name, Maybe Type))
	| HappyAbsSyn8 (Expr (Maybe Type))
	| HappyAbsSyn13 ((Name, Expr (Maybe Type)))
	| HappyAbsSyn14 (Type)
	| HappyAbsSyn15 (Maybe Type)
	| HappyAbsSyn16 ([Declaration (Maybe Type)])
	| HappyAbsSyn17 ([(Name, Maybe Type)])
	| HappyAbsSyn19 ([Statement (Maybe Type)])
	| HappyAbsSyn20 ([Expr (Maybe Type)])
	| HappyAbsSyn22 ([(Name, Expr (Maybe Type))])
	| HappyAbsSyn24 ([Name])

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Int 
	-> (T.Token AlexPosn)
	-> HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> m HappyAbsSyn)
	-> [HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(T.Token AlexPosn)] -> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62,
 action_63,
 action_64,
 action_65,
 action_66,
 action_67,
 action_68,
 action_69,
 action_70,
 action_71,
 action_72,
 action_73,
 action_74,
 action_75,
 action_76,
 action_77,
 action_78,
 action_79,
 action_80,
 action_81,
 action_82,
 action_83,
 action_84,
 action_85,
 action_86,
 action_87,
 action_88,
 action_89,
 action_90,
 action_91,
 action_92,
 action_93,
 action_94,
 action_95,
 action_96,
 action_97,
 action_98,
 action_99,
 action_100,
 action_101,
 action_102,
 action_103,
 action_104,
 action_105,
 action_106,
 action_107,
 action_108,
 action_109,
 action_110,
 action_111,
 action_112,
 action_113,
 action_114,
 action_115,
 action_116,
 action_117,
 action_118,
 action_119,
 action_120,
 action_121,
 action_122,
 action_123,
 action_124 :: () => Int -> ({-HappyReduction (HappyIdentity) = -}
	   Int 
	-> (T.Token AlexPosn)
	-> HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)
	-> [HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)

happyReduce_1,
 happyReduce_2,
 happyReduce_3,
 happyReduce_4,
 happyReduce_5,
 happyReduce_6,
 happyReduce_7,
 happyReduce_8,
 happyReduce_9,
 happyReduce_10,
 happyReduce_11,
 happyReduce_12,
 happyReduce_13,
 happyReduce_14,
 happyReduce_15,
 happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27,
 happyReduce_28,
 happyReduce_29,
 happyReduce_30,
 happyReduce_31,
 happyReduce_32,
 happyReduce_33,
 happyReduce_34,
 happyReduce_35,
 happyReduce_36,
 happyReduce_37,
 happyReduce_38,
 happyReduce_39,
 happyReduce_40,
 happyReduce_41,
 happyReduce_42,
 happyReduce_43,
 happyReduce_44,
 happyReduce_45,
 happyReduce_46,
 happyReduce_47,
 happyReduce_48,
 happyReduce_49,
 happyReduce_50,
 happyReduce_51,
 happyReduce_52,
 happyReduce_53,
 happyReduce_54,
 happyReduce_55,
 happyReduce_56,
 happyReduce_57,
 happyReduce_58,
 happyReduce_59,
 happyReduce_60,
 happyReduce_61 :: () => ({-HappyReduction (HappyIdentity) = -}
	   Int 
	-> (T.Token AlexPosn)
	-> HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)
	-> [HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)

action_0 (26) = happyShift action_9
action_0 (28) = happyShift action_10
action_0 (30) = happyShift action_11
action_0 (32) = happyShift action_12
action_0 (33) = happyShift action_13
action_0 (41) = happyShift action_14
action_0 (43) = happyShift action_15
action_0 (45) = happyShift action_16
action_0 (50) = happyShift action_17
action_0 (51) = happyShift action_18
action_0 (52) = happyShift action_19
action_0 (53) = happyShift action_20
action_0 (4) = happyGoto action_3
action_0 (8) = happyGoto action_4
action_0 (9) = happyGoto action_5
action_0 (10) = happyGoto action_6
action_0 (11) = happyGoto action_7
action_0 (12) = happyGoto action_8
action_0 _ = happyFail

action_1 (28) = happyShift action_2
action_1 _ = happyFail

action_2 (53) = happyShift action_46
action_2 (5) = happyGoto action_44
action_2 (16) = happyGoto action_55
action_2 _ = happyFail

action_3 (54) = happyAccept
action_3 _ = happyFail

action_4 _ = happyReduce_5

action_5 _ = happyReduce_13

action_6 (28) = happyShift action_35
action_6 (30) = happyShift action_11
action_6 (33) = happyShift action_13
action_6 (41) = happyShift action_14
action_6 (43) = happyShift action_15
action_6 (45) = happyShift action_16
action_6 (50) = happyShift action_17
action_6 (51) = happyShift action_18
action_6 (52) = happyShift action_19
action_6 (53) = happyShift action_36
action_6 (9) = happyGoto action_54
action_6 (11) = happyGoto action_7
action_6 (12) = happyGoto action_50
action_6 _ = happyReduce_14

action_7 _ = happyReduce_15

action_8 (28) = happyShift action_35
action_8 (30) = happyShift action_11
action_8 (33) = happyShift action_13
action_8 (41) = happyShift action_14
action_8 (43) = happyShift action_15
action_8 (45) = happyShift action_16
action_8 (47) = happyShift action_51
action_8 (48) = happyShift action_52
action_8 (49) = happyShift action_53
action_8 (50) = happyShift action_17
action_8 (51) = happyShift action_18
action_8 (52) = happyShift action_19
action_8 (53) = happyShift action_36
action_8 (9) = happyGoto action_49
action_8 (11) = happyGoto action_7
action_8 (12) = happyGoto action_50
action_8 _ = happyReduce_16

action_9 (53) = happyShift action_48
action_9 (6) = happyGoto action_47
action_9 _ = happyFail

action_10 (53) = happyShift action_46
action_10 (5) = happyGoto action_44
action_10 (16) = happyGoto action_45
action_10 _ = happyFail

action_11 (41) = happyShift action_42
action_11 (53) = happyShift action_43
action_11 (7) = happyGoto action_40
action_11 (18) = happyGoto action_41
action_11 _ = happyFail

action_12 (53) = happyShift action_39
action_12 _ = happyFail

action_13 (45) = happyShift action_38
action_13 _ = happyFail

action_14 (28) = happyShift action_35
action_14 (30) = happyShift action_11
action_14 (33) = happyShift action_13
action_14 (41) = happyShift action_14
action_14 (43) = happyShift action_15
action_14 (45) = happyShift action_16
action_14 (50) = happyShift action_17
action_14 (51) = happyShift action_18
action_14 (52) = happyShift action_19
action_14 (53) = happyShift action_36
action_14 (8) = happyGoto action_37
action_14 (9) = happyGoto action_5
action_14 (10) = happyGoto action_6
action_14 (11) = happyGoto action_7
action_14 (12) = happyGoto action_8
action_14 _ = happyFail

action_15 (28) = happyShift action_35
action_15 (30) = happyShift action_11
action_15 (33) = happyShift action_13
action_15 (41) = happyShift action_14
action_15 (43) = happyShift action_15
action_15 (45) = happyShift action_16
action_15 (50) = happyShift action_17
action_15 (51) = happyShift action_18
action_15 (52) = happyShift action_19
action_15 (53) = happyShift action_36
action_15 (8) = happyGoto action_32
action_15 (9) = happyGoto action_5
action_15 (10) = happyGoto action_6
action_15 (11) = happyGoto action_7
action_15 (12) = happyGoto action_8
action_15 (20) = happyGoto action_33
action_15 (21) = happyGoto action_34
action_15 _ = happyReduce_50

action_16 (51) = happyShift action_30
action_16 (53) = happyShift action_31
action_16 (13) = happyGoto action_27
action_16 (22) = happyGoto action_28
action_16 (23) = happyGoto action_29
action_16 _ = happyReduce_54

action_17 (39) = happyShift action_22
action_17 (15) = happyGoto action_26
action_17 _ = happyReduce_40

action_18 (39) = happyShift action_22
action_18 (15) = happyGoto action_25
action_18 _ = happyReduce_40

action_19 (39) = happyShift action_22
action_19 (15) = happyGoto action_24
action_19 _ = happyReduce_40

action_20 (39) = happyShift action_22
action_20 (40) = happyShift action_23
action_20 (15) = happyGoto action_21
action_20 _ = happyReduce_40

action_21 _ = happyReduce_25

action_22 (34) = happyShift action_80
action_22 (43) = happyShift action_81
action_22 (47) = happyShift action_82
action_22 (53) = happyShift action_83
action_22 (14) = happyGoto action_84
action_22 _ = happyFail

action_23 (34) = happyShift action_80
action_23 (43) = happyShift action_81
action_23 (47) = happyShift action_82
action_23 (53) = happyShift action_83
action_23 (14) = happyGoto action_79
action_23 _ = happyFail

action_24 _ = happyReduce_24

action_25 _ = happyReduce_23

action_26 _ = happyReduce_22

action_27 (38) = happyShift action_78
action_27 _ = happyReduce_56

action_28 (46) = happyShift action_77
action_28 _ = happyFail

action_29 _ = happyReduce_55

action_30 (39) = happyShift action_76
action_30 _ = happyFail

action_31 (39) = happyShift action_75
action_31 _ = happyFail

action_32 (38) = happyShift action_74
action_32 _ = happyReduce_52

action_33 (44) = happyShift action_73
action_33 _ = happyFail

action_34 _ = happyReduce_51

action_35 (53) = happyShift action_46
action_35 (5) = happyGoto action_44
action_35 (16) = happyGoto action_72
action_35 _ = happyFail

action_36 (39) = happyShift action_22
action_36 (15) = happyGoto action_21
action_36 _ = happyReduce_40

action_37 (42) = happyShift action_71
action_37 _ = happyFail

action_38 (26) = happyShift action_9
action_38 (28) = happyShift action_10
action_38 (30) = happyShift action_11
action_38 (32) = happyShift action_12
action_38 (33) = happyShift action_13
action_38 (41) = happyShift action_14
action_38 (43) = happyShift action_15
action_38 (45) = happyShift action_16
action_38 (50) = happyShift action_17
action_38 (51) = happyShift action_18
action_38 (52) = happyShift action_19
action_38 (53) = happyShift action_20
action_38 (4) = happyGoto action_69
action_38 (8) = happyGoto action_4
action_38 (9) = happyGoto action_5
action_38 (10) = happyGoto action_6
action_38 (11) = happyGoto action_7
action_38 (12) = happyGoto action_8
action_38 (19) = happyGoto action_70
action_38 _ = happyReduce_48

action_39 (35) = happyShift action_68
action_39 _ = happyFail

action_40 (41) = happyShift action_42
action_40 (53) = happyShift action_43
action_40 (7) = happyGoto action_40
action_40 (18) = happyGoto action_67
action_40 _ = happyReduce_46

action_41 (39) = happyShift action_22
action_41 (15) = happyGoto action_66
action_41 _ = happyReduce_40

action_42 (53) = happyShift action_65
action_42 _ = happyFail

action_43 _ = happyReduce_11

action_44 (29) = happyShift action_64
action_44 _ = happyReduce_42

action_45 (31) = happyShift action_63
action_45 _ = happyReduce_1

action_46 (41) = happyShift action_42
action_46 (53) = happyShift action_43
action_46 (7) = happyGoto action_40
action_46 (17) = happyGoto action_61
action_46 (18) = happyGoto action_62
action_46 _ = happyReduce_44

action_47 _ = happyReduce_4

action_48 (27) = happyShift action_59
action_48 (41) = happyShift action_60
action_48 _ = happyReduce_7

action_49 _ = happyReduce_17

action_50 (47) = happyShift action_51
action_50 (48) = happyShift action_52
action_50 (49) = happyShift action_53
action_50 _ = happyReduce_16

action_51 (28) = happyShift action_35
action_51 (30) = happyShift action_11
action_51 (33) = happyShift action_13
action_51 (41) = happyShift action_14
action_51 (43) = happyShift action_15
action_51 (45) = happyShift action_16
action_51 (50) = happyShift action_17
action_51 (51) = happyShift action_18
action_51 (52) = happyShift action_19
action_51 (53) = happyShift action_36
action_51 (8) = happyGoto action_58
action_51 (9) = happyGoto action_5
action_51 (10) = happyGoto action_6
action_51 (11) = happyGoto action_7
action_51 (12) = happyGoto action_8
action_51 _ = happyFail

action_52 (53) = happyShift action_57
action_52 _ = happyFail

action_53 (28) = happyShift action_35
action_53 (30) = happyShift action_11
action_53 (33) = happyShift action_13
action_53 (41) = happyShift action_14
action_53 (43) = happyShift action_15
action_53 (45) = happyShift action_16
action_53 (50) = happyShift action_17
action_53 (51) = happyShift action_18
action_53 (52) = happyShift action_19
action_53 (53) = happyShift action_36
action_53 (8) = happyGoto action_56
action_53 (9) = happyGoto action_5
action_53 (10) = happyGoto action_6
action_53 (11) = happyGoto action_7
action_53 (12) = happyGoto action_8
action_53 _ = happyFail

action_54 _ = happyReduce_18

action_55 _ = happyFail

action_56 _ = happyReduce_21

action_57 (39) = happyShift action_22
action_57 (15) = happyGoto action_108
action_57 _ = happyReduce_40

action_58 (44) = happyShift action_107
action_58 _ = happyFail

action_59 (53) = happyShift action_106
action_59 _ = happyFail

action_60 (53) = happyShift action_105
action_60 (24) = happyGoto action_103
action_60 (25) = happyGoto action_104
action_60 _ = happyReduce_58

action_61 (39) = happyShift action_22
action_61 (15) = happyGoto action_102
action_61 _ = happyReduce_40

action_62 _ = happyReduce_45

action_63 (28) = happyShift action_35
action_63 (30) = happyShift action_11
action_63 (33) = happyShift action_13
action_63 (41) = happyShift action_14
action_63 (43) = happyShift action_15
action_63 (45) = happyShift action_16
action_63 (50) = happyShift action_17
action_63 (51) = happyShift action_18
action_63 (52) = happyShift action_19
action_63 (53) = happyShift action_36
action_63 (8) = happyGoto action_101
action_63 (9) = happyGoto action_5
action_63 (10) = happyGoto action_6
action_63 (11) = happyGoto action_7
action_63 (12) = happyGoto action_8
action_63 _ = happyFail

action_64 (53) = happyShift action_46
action_64 (5) = happyGoto action_44
action_64 (16) = happyGoto action_100
action_64 _ = happyFail

action_65 (39) = happyShift action_99
action_65 _ = happyFail

action_66 (36) = happyShift action_98
action_66 _ = happyFail

action_67 _ = happyReduce_47

action_68 (34) = happyShift action_80
action_68 (43) = happyShift action_81
action_68 (47) = happyShift action_82
action_68 (53) = happyShift action_83
action_68 (14) = happyGoto action_97
action_68 _ = happyFail

action_69 (37) = happyShift action_96
action_69 _ = happyFail

action_70 (46) = happyShift action_95
action_70 _ = happyFail

action_71 _ = happyReduce_26

action_72 (31) = happyShift action_63
action_72 _ = happyFail

action_73 (39) = happyShift action_22
action_73 (15) = happyGoto action_94
action_73 _ = happyReduce_40

action_74 (28) = happyShift action_35
action_74 (30) = happyShift action_11
action_74 (33) = happyShift action_13
action_74 (41) = happyShift action_14
action_74 (43) = happyShift action_15
action_74 (45) = happyShift action_16
action_74 (50) = happyShift action_17
action_74 (51) = happyShift action_18
action_74 (52) = happyShift action_19
action_74 (53) = happyShift action_36
action_74 (8) = happyGoto action_32
action_74 (9) = happyGoto action_5
action_74 (10) = happyGoto action_6
action_74 (11) = happyGoto action_7
action_74 (12) = happyGoto action_8
action_74 (21) = happyGoto action_93
action_74 _ = happyFail

action_75 (28) = happyShift action_35
action_75 (30) = happyShift action_11
action_75 (33) = happyShift action_13
action_75 (41) = happyShift action_14
action_75 (43) = happyShift action_15
action_75 (45) = happyShift action_16
action_75 (50) = happyShift action_17
action_75 (51) = happyShift action_18
action_75 (52) = happyShift action_19
action_75 (53) = happyShift action_36
action_75 (8) = happyGoto action_92
action_75 (9) = happyGoto action_5
action_75 (10) = happyGoto action_6
action_75 (11) = happyGoto action_7
action_75 (12) = happyGoto action_8
action_75 _ = happyFail

action_76 (28) = happyShift action_35
action_76 (30) = happyShift action_11
action_76 (33) = happyShift action_13
action_76 (41) = happyShift action_14
action_76 (43) = happyShift action_15
action_76 (45) = happyShift action_16
action_76 (50) = happyShift action_17
action_76 (51) = happyShift action_18
action_76 (52) = happyShift action_19
action_76 (53) = happyShift action_36
action_76 (8) = happyGoto action_91
action_76 (9) = happyGoto action_5
action_76 (10) = happyGoto action_6
action_76 (11) = happyGoto action_7
action_76 (12) = happyGoto action_8
action_76 _ = happyFail

action_77 (39) = happyShift action_22
action_77 (15) = happyGoto action_90
action_77 _ = happyReduce_40

action_78 (51) = happyShift action_30
action_78 (53) = happyShift action_31
action_78 (13) = happyGoto action_27
action_78 (23) = happyGoto action_89
action_78 _ = happyFail

action_79 _ = happyReduce_2

action_80 _ = happyReduce_34

action_81 (34) = happyShift action_80
action_81 (43) = happyShift action_81
action_81 (47) = happyShift action_82
action_81 (52) = happyShift action_88
action_81 (53) = happyShift action_83
action_81 (14) = happyGoto action_87
action_81 _ = happyFail

action_82 (34) = happyShift action_80
action_82 (43) = happyShift action_81
action_82 (47) = happyShift action_82
action_82 (52) = happyShift action_86
action_82 (53) = happyShift action_83
action_82 (14) = happyGoto action_85
action_82 _ = happyFail

action_83 _ = happyReduce_35

action_84 _ = happyReduce_41

action_85 (44) = happyShift action_119
action_85 _ = happyFail

action_86 (44) = happyShift action_118
action_86 _ = happyFail

action_87 (44) = happyShift action_117
action_87 _ = happyFail

action_88 (44) = happyShift action_116
action_88 _ = happyFail

action_89 _ = happyReduce_57

action_90 _ = happyReduce_28

action_91 _ = happyReduce_33

action_92 _ = happyReduce_32

action_93 _ = happyReduce_53

action_94 _ = happyReduce_27

action_95 _ = happyReduce_29

action_96 (26) = happyShift action_9
action_96 (28) = happyShift action_10
action_96 (30) = happyShift action_11
action_96 (32) = happyShift action_12
action_96 (33) = happyShift action_13
action_96 (41) = happyShift action_14
action_96 (43) = happyShift action_15
action_96 (45) = happyShift action_16
action_96 (50) = happyShift action_17
action_96 (51) = happyShift action_18
action_96 (52) = happyShift action_19
action_96 (53) = happyShift action_20
action_96 (4) = happyGoto action_69
action_96 (8) = happyGoto action_4
action_96 (9) = happyGoto action_5
action_96 (10) = happyGoto action_6
action_96 (11) = happyGoto action_7
action_96 (12) = happyGoto action_8
action_96 (19) = happyGoto action_115
action_96 _ = happyReduce_48

action_97 _ = happyReduce_3

action_98 (28) = happyShift action_35
action_98 (30) = happyShift action_11
action_98 (33) = happyShift action_13
action_98 (41) = happyShift action_14
action_98 (43) = happyShift action_15
action_98 (45) = happyShift action_16
action_98 (50) = happyShift action_17
action_98 (51) = happyShift action_18
action_98 (52) = happyShift action_19
action_98 (53) = happyShift action_36
action_98 (8) = happyGoto action_114
action_98 (9) = happyGoto action_5
action_98 (10) = happyGoto action_6
action_98 (11) = happyGoto action_7
action_98 (12) = happyGoto action_8
action_98 _ = happyFail

action_99 (34) = happyShift action_80
action_99 (43) = happyShift action_81
action_99 (47) = happyShift action_82
action_99 (53) = happyShift action_83
action_99 (14) = happyGoto action_113
action_99 _ = happyFail

action_100 _ = happyReduce_43

action_101 _ = happyReduce_20

action_102 (35) = happyShift action_112
action_102 _ = happyFail

action_103 (42) = happyShift action_111
action_103 _ = happyFail

action_104 _ = happyReduce_59

action_105 (38) = happyShift action_110
action_105 _ = happyReduce_60

action_106 _ = happyReduce_9

action_107 (39) = happyShift action_22
action_107 (15) = happyGoto action_109
action_107 _ = happyReduce_40

action_108 _ = happyReduce_30

action_109 _ = happyReduce_31

action_110 (53) = happyShift action_105
action_110 (25) = happyGoto action_123
action_110 _ = happyFail

action_111 (27) = happyShift action_122
action_111 _ = happyReduce_8

action_112 (28) = happyShift action_35
action_112 (30) = happyShift action_11
action_112 (33) = happyShift action_13
action_112 (41) = happyShift action_14
action_112 (43) = happyShift action_15
action_112 (45) = happyShift action_16
action_112 (50) = happyShift action_17
action_112 (51) = happyShift action_18
action_112 (52) = happyShift action_19
action_112 (53) = happyShift action_36
action_112 (8) = happyGoto action_121
action_112 (9) = happyGoto action_5
action_112 (10) = happyGoto action_6
action_112 (11) = happyGoto action_7
action_112 (12) = happyGoto action_8
action_112 _ = happyFail

action_113 (42) = happyShift action_120
action_113 _ = happyFail

action_114 _ = happyReduce_19

action_115 _ = happyReduce_49

action_116 _ = happyReduce_37

action_117 _ = happyReduce_39

action_118 _ = happyReduce_36

action_119 _ = happyReduce_38

action_120 _ = happyReduce_12

action_121 _ = happyReduce_6

action_122 (53) = happyShift action_124
action_122 _ = happyFail

action_123 _ = happyReduce_61

action_124 _ = happyReduce_10

happyReduce_1 = happySpecReduce_2  4 happyReduction_1
happyReduction_1 (HappyAbsSyn16  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (Declarations happy_var_2
	)
happyReduction_1 _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_3  4 happyReduction_2
happyReduction_2 (HappyAbsSyn14  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn4
		 (ForwardDecl happy_var_1 happy_var_3
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happyReduce 4 4 happyReduction_3
happyReduction_3 ((HappyAbsSyn14  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Typedef happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_4 = happySpecReduce_2  4 happyReduction_4
happyReduction_4 (HappyAbsSyn4  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (happy_var_2
	)
happyReduction_4 _ _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_1  4 happyReduction_5
happyReduction_5 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn4
		 (Command happy_var_1
	)
happyReduction_5 _  = notHappyAtAll 

happyReduce_6 = happyReduce 5 5 happyReduction_6
happyReduction_6 ((HappyAbsSyn8  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_3) `HappyStk`
	(HappyAbsSyn17  happy_var_2) `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Declaration happy_var_1 happy_var_2 happy_var_5 happy_var_3
	) `HappyStk` happyRest

happyReduce_7 = happySpecReduce_1  6 happyReduction_7
happyReduction_7 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn4
		 (Import happy_var_1 Nothing Nothing
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happyReduce 4 6 happyReduction_8
happyReduction_8 (_ `HappyStk`
	(HappyAbsSyn24  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Import happy_var_1 (Just happy_var_3) Nothing
	) `HappyStk` happyRest

happyReduce_9 = happySpecReduce_3  6 happyReduction_9
happyReduction_9 (HappyTerminal (T.Identifier _ happy_var_3))
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn4
		 (Import happy_var_1 Nothing (Just happy_var_3)
	)
happyReduction_9 _ _ _  = notHappyAtAll 

happyReduce_10 = happyReduce 6 6 happyReduction_10
happyReduction_10 ((HappyTerminal (T.Identifier _ happy_var_6)) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn24  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Import happy_var_1 (Just happy_var_3) (Just happy_var_6)
	) `HappyStk` happyRest

happyReduce_11 = happySpecReduce_1  7 happyReduction_11
happyReduction_11 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn7
		 ((happy_var_1, Nothing)
	)
happyReduction_11 _  = notHappyAtAll 

happyReduce_12 = happyReduce 5 7 happyReduction_12
happyReduction_12 (_ `HappyStk`
	(HappyAbsSyn14  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn7
		 ((happy_var_2, Just happy_var_4)
	) `HappyStk` happyRest

happyReduce_13 = happySpecReduce_1  8 happyReduction_13
happyReduction_13 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (happy_var_1
	)
happyReduction_13 _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_1  8 happyReduction_14
happyReduction_14 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (happy_var_1
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  9 happyReduction_15
happyReduction_15 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (happy_var_1
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happySpecReduce_1  9 happyReduction_16
happyReduction_16 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (happy_var_1
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_2  10 happyReduction_17
happyReduction_17 (HappyAbsSyn8  happy_var_2)
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (Application happy_var_1 happy_var_2 Nothing
	)
happyReduction_17 _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_2  10 happyReduction_18
happyReduction_18 (HappyAbsSyn8  happy_var_2)
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (Application happy_var_1 happy_var_2 Nothing
	)
happyReduction_18 _ _  = notHappyAtAll 

happyReduce_19 = happyReduce 5 11 happyReduction_19
happyReduction_19 ((HappyAbsSyn8  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn15  happy_var_3) `HappyStk`
	(HappyAbsSyn17  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (uncurryFunction happy_var_2 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_20 = happyReduce 4 11 happyReduction_20
happyReduction_20 ((HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn16  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (LetBlock happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_21 = happySpecReduce_3  11 happyReduction_21
happyReduction_21 (HappyAbsSyn8  happy_var_3)
	(HappyTerminal (T.Infix      _ happy_var_2))
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (Application (Application (Var happy_var_2 Nothing ) happy_var_1 Nothing) happy_var_3 Nothing
	)
happyReduction_21 _ _ _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_2  12 happyReduction_22
happyReduction_22 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal (T.Bitfield   _ happy_var_1))
	 =  HappyAbsSyn8
		 (Array (bitsOfString happy_var_1) happy_var_2
	)
happyReduction_22 _ _  = notHappyAtAll 

happyReduce_23 = happySpecReduce_2  12 happyReduction_23
happyReduction_23 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal (T.String     _ happy_var_1))
	 =  HappyAbsSyn8
		 (Quote happy_var_1 happy_var_2
	)
happyReduction_23 _ _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_2  12 happyReduction_24
happyReduction_24 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal (T.Integer    _ happy_var_1))
	 =  HappyAbsSyn8
		 (Z (read happy_var_1) happy_var_2
	)
happyReduction_24 _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_2  12 happyReduction_25
happyReduction_25 (HappyAbsSyn15  happy_var_2)
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn8
		 (Var happy_var_1 happy_var_2
	)
happyReduction_25 _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_3  12 happyReduction_26
happyReduction_26 _
	(HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (happy_var_2
	)
happyReduction_26 _ _ _  = notHappyAtAll 

happyReduce_27 = happyReduce 4 12 happyReduction_27
happyReduction_27 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Array happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_28 = happyReduce 4 12 happyReduction_28
happyReduction_28 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Record happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_29 = happyReduce 4 12 happyReduction_29
happyReduction_29 (_ `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Procedure happy_var_3 Nothing
	) `HappyStk` happyRest

happyReduce_30 = happyReduce 4 12 happyReduction_30
happyReduction_30 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_3)) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Lookup happy_var_1 happy_var_3 happy_var_4
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 5 12 happyReduction_31
happyReduction_31 ((HappyAbsSyn15  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Index happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_32 = happySpecReduce_3  13 happyReduction_32
happyReduction_32 (HappyAbsSyn8  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn13
		 ((happy_var_1, happy_var_3)
	)
happyReduction_32 _ _ _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_3  13 happyReduction_33
happyReduction_33 (HappyAbsSyn8  happy_var_3)
	_
	(HappyTerminal (T.String     _ happy_var_1))
	 =  HappyAbsSyn13
		 ((happy_var_1, happy_var_3)
	)
happyReduction_33 _ _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_1  14 happyReduction_34
happyReduction_34 _
	 =  HappyAbsSyn14
		 (Z'
	)

happyReduce_35 = happySpecReduce_1  14 happyReduction_35
happyReduction_35 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn14
		 (Var' happy_var_1
	)
happyReduction_35 _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_3  14 happyReduction_36
happyReduction_36 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn14
		 (Array' Bit' (read happy_var_2)
	)
happyReduction_36 _ _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_3  14 happyReduction_37
happyReduction_37 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn14
		 (Array' Bit' (read happy_var_2)
	)
happyReduction_37 _ _ _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_3  14 happyReduction_38
happyReduction_38 _
	(HappyAbsSyn14  happy_var_2)
	_
	 =  HappyAbsSyn14
		 (Array' happy_var_2 Nothing
	)
happyReduction_38 _ _ _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_3  14 happyReduction_39
happyReduction_39 _
	(HappyAbsSyn14  happy_var_2)
	_
	 =  HappyAbsSyn14
		 (Array' happy_var_2 Nothing
	)
happyReduction_39 _ _ _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_0  15 happyReduction_40
happyReduction_40  =  HappyAbsSyn15
		 (Nothing
	)

happyReduce_41 = happySpecReduce_2  15 happyReduction_41
happyReduction_41 (HappyAbsSyn14  happy_var_2)
	_
	 =  HappyAbsSyn15
		 (Just happy_var_2
	)
happyReduction_41 _ _  = notHappyAtAll 

happyReduce_42 = happySpecReduce_1  16 happyReduction_42
happyReduction_42 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn16
		 ([happy_var_1]
	)
happyReduction_42 _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_3  16 happyReduction_43
happyReduction_43 (HappyAbsSyn16  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn16
		 (happy_var_1:happy_var_3
	)
happyReduction_43 _ _ _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_0  17 happyReduction_44
happyReduction_44  =  HappyAbsSyn17
		 ([]
	)

happyReduce_45 = happySpecReduce_1  17 happyReduction_45
happyReduction_45 (HappyAbsSyn17  happy_var_1)
	 =  HappyAbsSyn17
		 (happy_var_1
	)
happyReduction_45 _  = notHappyAtAll 

happyReduce_46 = happySpecReduce_1  18 happyReduction_46
happyReduction_46 (HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn17
		 ([happy_var_1]
	)
happyReduction_46 _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_2  18 happyReduction_47
happyReduction_47 (HappyAbsSyn17  happy_var_2)
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn17
		 (happy_var_1:happy_var_2
	)
happyReduction_47 _ _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_0  19 happyReduction_48
happyReduction_48  =  HappyAbsSyn19
		 ([]
	)

happyReduce_49 = happySpecReduce_3  19 happyReduction_49
happyReduction_49 (HappyAbsSyn19  happy_var_3)
	_
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn19
		 (happy_var_1:happy_var_3
	)
happyReduction_49 _ _ _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_0  20 happyReduction_50
happyReduction_50  =  HappyAbsSyn20
		 ([]
	)

happyReduce_51 = happySpecReduce_1  20 happyReduction_51
happyReduction_51 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1
	)
happyReduction_51 _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_1  21 happyReduction_52
happyReduction_52 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn20
		 ([happy_var_1]
	)
happyReduction_52 _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_3  21 happyReduction_53
happyReduction_53 (HappyAbsSyn20  happy_var_3)
	_
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1:happy_var_3
	)
happyReduction_53 _ _ _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_0  22 happyReduction_54
happyReduction_54  =  HappyAbsSyn22
		 ([]
	)

happyReduce_55 = happySpecReduce_1  22 happyReduction_55
happyReduction_55 (HappyAbsSyn22  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1
	)
happyReduction_55 _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_1  23 happyReduction_56
happyReduction_56 (HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn22
		 ([happy_var_1]
	)
happyReduction_56 _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_3  23 happyReduction_57
happyReduction_57 (HappyAbsSyn22  happy_var_3)
	_
	(HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1:happy_var_3
	)
happyReduction_57 _ _ _  = notHappyAtAll 

happyReduce_58 = happySpecReduce_0  24 happyReduction_58
happyReduction_58  =  HappyAbsSyn24
		 ([]
	)

happyReduce_59 = happySpecReduce_1  24 happyReduction_59
happyReduction_59 (HappyAbsSyn24  happy_var_1)
	 =  HappyAbsSyn24
		 (happy_var_1
	)
happyReduction_59 _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_1  25 happyReduction_60
happyReduction_60 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn24
		 ([happy_var_1]
	)
happyReduction_60 _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_3  25 happyReduction_61
happyReduction_61 (HappyAbsSyn24  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn24
		 (happy_var_1:happy_var_3
	)
happyReduction_61 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 54 54 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	T.Keyword    _ "import" -> cont 26;
	T.Keyword    _ "as" -> cont 27;
	T.Keyword    _ "let" -> cont 28;
	T.Keyword    _ "and" -> cont 29;
	T.Keyword    _ "fun" -> cont 30;
	T.Keyword    _ "in" -> cont 31;
	T.Keyword    _ "type" -> cont 32;
	T.Keyword    _ "do" -> cont 33;
	T.Keyword    _ "integer" -> cont 34;
	T.Infix      _ "=" -> cont 35;
	T.Infix      _ "->" -> cont 36;
	T.Infix      _ ";" -> cont 37;
	T.Infix      _ "," -> cont 38;
	T.Infix      _ ":" -> cont 39;
	T.Infix      _ "::" -> cont 40;
	T.OutfixL    _ "(" -> cont 41;
	T.OutfixR    _ ")" -> cont 42;
	T.OutfixL    _ "[" -> cont 43;
	T.OutfixR    _ "]" -> cont 44;
	T.OutfixL    _ "{" -> cont 45;
	T.OutfixR    _ "}" -> cont 46;
	T.Postfix    _ "[" -> cont 47;
	T.Postfix    _ "." -> cont 48;
	T.Infix      _ happy_dollar_dollar -> cont 49;
	T.Bitfield   _ happy_dollar_dollar -> cont 50;
	T.String     _ happy_dollar_dollar -> cont 51;
	T.Integer    _ happy_dollar_dollar -> cont 52;
	T.Identifier _ happy_dollar_dollar -> cont 53;
	_ -> happyError' (tk:tks)
	}

happyError_ 54 tk tks = happyError' tks
happyError_ _ tk tks = happyError' (tk:tks)

newtype HappyIdentity a = HappyIdentity a
happyIdentity = HappyIdentity
happyRunIdentity (HappyIdentity a) = a

instance Monad HappyIdentity where
    return = HappyIdentity
    (HappyIdentity p) >>= q = q p

happyThen :: () => HappyIdentity a -> (a -> HappyIdentity b) -> HappyIdentity b
happyThen = (>>=)
happyReturn :: () => a -> HappyIdentity a
happyReturn = (return)
happyThen1 m k tks = (>>=) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> HappyIdentity a
happyReturn1 = \a tks -> (return) a
happyError' :: () => [(T.Token AlexPosn)] -> HappyIdentity a
happyError' = HappyIdentity . parseError

parse tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


parseError :: [T.Token a] -> b
parseError _ = error "Parse error"

bitsOfString :: String -> [Expr (Maybe Type)]
bitsOfString = (map (\b -> Bit b (Just Bit'))) . (map (/='0'))

uncurryFunction :: [(Name, Maybe Type)] -> Maybe Type -> Expr (Maybe Type) -> Expr (Maybe Type)
uncurryFunction [a]    mt e = Function a e mt
uncurryFunction (a:as) mt e = Function a (uncurryFunction as mt e) Nothing
{-# LINE 1 "templates/GenericTemplate.hs" #-}
{-# LINE 1 "templates/GenericTemplate.hs" #-}
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
