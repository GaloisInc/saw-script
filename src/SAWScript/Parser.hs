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
	| HappyAbsSyn11 ((Name, Expr (Maybe Type)))
	| HappyAbsSyn12 (Type)
	| HappyAbsSyn13 (Maybe Type)
	| HappyAbsSyn14 ([Declaration (Maybe Type)])
	| HappyAbsSyn15 ([(Name, Maybe Type)])
	| HappyAbsSyn17 ([Statement (Maybe Type)])
	| HappyAbsSyn18 ([Expr (Maybe Type)])
	| HappyAbsSyn20 ([(Name, Expr (Maybe Type))])
	| HappyAbsSyn22 ([Name])

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
 action_120 :: () => Int -> ({-HappyReduction (HappyIdentity) = -}
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
 happyReduce_58 :: () => ({-HappyReduction (HappyIdentity) = -}
	   Int 
	-> (T.Token AlexPosn)
	-> HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)
	-> [HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)

action_0 (24) = happyShift action_7
action_0 (26) = happyShift action_8
action_0 (28) = happyShift action_9
action_0 (30) = happyShift action_10
action_0 (31) = happyShift action_11
action_0 (39) = happyShift action_12
action_0 (41) = happyShift action_13
action_0 (43) = happyShift action_14
action_0 (48) = happyShift action_15
action_0 (49) = happyShift action_16
action_0 (50) = happyShift action_17
action_0 (51) = happyShift action_18
action_0 (4) = happyGoto action_3
action_0 (8) = happyGoto action_4
action_0 (9) = happyGoto action_5
action_0 (10) = happyGoto action_6
action_0 _ = happyFail

action_1 (26) = happyShift action_2
action_1 _ = happyFail

action_2 (51) = happyShift action_45
action_2 (5) = happyGoto action_43
action_2 (14) = happyGoto action_52
action_2 _ = happyFail

action_3 (52) = happyAccept
action_3 _ = happyFail

action_4 _ = happyReduce_5

action_5 _ = happyReduce_13

action_6 (26) = happyShift action_33
action_6 (28) = happyShift action_9
action_6 (31) = happyShift action_11
action_6 (39) = happyShift action_12
action_6 (41) = happyShift action_13
action_6 (43) = happyShift action_14
action_6 (45) = happyShift action_49
action_6 (46) = happyShift action_50
action_6 (47) = happyShift action_51
action_6 (48) = happyShift action_15
action_6 (49) = happyShift action_16
action_6 (50) = happyShift action_17
action_6 (51) = happyShift action_34
action_6 (8) = happyGoto action_48
action_6 (9) = happyGoto action_5
action_6 (10) = happyGoto action_6
action_6 _ = happyReduce_14

action_7 (51) = happyShift action_47
action_7 (6) = happyGoto action_46
action_7 _ = happyFail

action_8 (51) = happyShift action_45
action_8 (5) = happyGoto action_43
action_8 (14) = happyGoto action_44
action_8 _ = happyFail

action_9 (39) = happyShift action_41
action_9 (51) = happyShift action_42
action_9 (7) = happyGoto action_38
action_9 (15) = happyGoto action_39
action_9 (16) = happyGoto action_40
action_9 _ = happyReduce_41

action_10 (51) = happyShift action_37
action_10 _ = happyFail

action_11 (43) = happyShift action_36
action_11 _ = happyFail

action_12 (26) = happyShift action_33
action_12 (28) = happyShift action_9
action_12 (31) = happyShift action_11
action_12 (39) = happyShift action_12
action_12 (41) = happyShift action_13
action_12 (43) = happyShift action_14
action_12 (48) = happyShift action_15
action_12 (49) = happyShift action_16
action_12 (50) = happyShift action_17
action_12 (51) = happyShift action_34
action_12 (8) = happyGoto action_35
action_12 (9) = happyGoto action_5
action_12 (10) = happyGoto action_6
action_12 _ = happyFail

action_13 (26) = happyShift action_33
action_13 (28) = happyShift action_9
action_13 (31) = happyShift action_11
action_13 (39) = happyShift action_12
action_13 (41) = happyShift action_13
action_13 (43) = happyShift action_14
action_13 (48) = happyShift action_15
action_13 (49) = happyShift action_16
action_13 (50) = happyShift action_17
action_13 (51) = happyShift action_34
action_13 (8) = happyGoto action_30
action_13 (9) = happyGoto action_5
action_13 (10) = happyGoto action_6
action_13 (18) = happyGoto action_31
action_13 (19) = happyGoto action_32
action_13 _ = happyReduce_47

action_14 (49) = happyShift action_28
action_14 (51) = happyShift action_29
action_14 (11) = happyGoto action_25
action_14 (20) = happyGoto action_26
action_14 (21) = happyGoto action_27
action_14 _ = happyReduce_51

action_15 (37) = happyShift action_20
action_15 (13) = happyGoto action_24
action_15 _ = happyReduce_37

action_16 (37) = happyShift action_20
action_16 (13) = happyGoto action_23
action_16 _ = happyReduce_37

action_17 (37) = happyShift action_20
action_17 (13) = happyGoto action_22
action_17 _ = happyReduce_37

action_18 (37) = happyShift action_20
action_18 (38) = happyShift action_21
action_18 (13) = happyGoto action_19
action_18 _ = happyReduce_37

action_19 _ = happyReduce_22

action_20 (32) = happyShift action_76
action_20 (41) = happyShift action_77
action_20 (45) = happyShift action_78
action_20 (51) = happyShift action_79
action_20 (12) = happyGoto action_80
action_20 _ = happyFail

action_21 (32) = happyShift action_76
action_21 (41) = happyShift action_77
action_21 (45) = happyShift action_78
action_21 (51) = happyShift action_79
action_21 (12) = happyGoto action_75
action_21 _ = happyFail

action_22 _ = happyReduce_21

action_23 _ = happyReduce_20

action_24 _ = happyReduce_19

action_25 (36) = happyShift action_74
action_25 _ = happyReduce_53

action_26 (44) = happyShift action_73
action_26 _ = happyFail

action_27 _ = happyReduce_52

action_28 (37) = happyShift action_72
action_28 _ = happyFail

action_29 (37) = happyShift action_71
action_29 _ = happyFail

action_30 (36) = happyShift action_70
action_30 _ = happyReduce_49

action_31 (42) = happyShift action_69
action_31 _ = happyFail

action_32 _ = happyReduce_48

action_33 (51) = happyShift action_45
action_33 (5) = happyGoto action_43
action_33 (14) = happyGoto action_68
action_33 _ = happyFail

action_34 (37) = happyShift action_20
action_34 (13) = happyGoto action_19
action_34 _ = happyReduce_37

action_35 (40) = happyShift action_67
action_35 _ = happyFail

action_36 (24) = happyShift action_7
action_36 (26) = happyShift action_8
action_36 (28) = happyShift action_9
action_36 (30) = happyShift action_10
action_36 (31) = happyShift action_11
action_36 (39) = happyShift action_12
action_36 (41) = happyShift action_13
action_36 (43) = happyShift action_14
action_36 (48) = happyShift action_15
action_36 (49) = happyShift action_16
action_36 (50) = happyShift action_17
action_36 (51) = happyShift action_18
action_36 (4) = happyGoto action_65
action_36 (8) = happyGoto action_4
action_36 (9) = happyGoto action_5
action_36 (10) = happyGoto action_6
action_36 (17) = happyGoto action_66
action_36 _ = happyReduce_45

action_37 (33) = happyShift action_64
action_37 _ = happyFail

action_38 (39) = happyShift action_41
action_38 (51) = happyShift action_42
action_38 (7) = happyGoto action_38
action_38 (16) = happyGoto action_63
action_38 _ = happyReduce_43

action_39 (37) = happyShift action_20
action_39 (13) = happyGoto action_62
action_39 _ = happyReduce_37

action_40 _ = happyReduce_42

action_41 (51) = happyShift action_61
action_41 _ = happyFail

action_42 _ = happyReduce_11

action_43 (27) = happyShift action_60
action_43 _ = happyReduce_39

action_44 (29) = happyShift action_59
action_44 _ = happyReduce_1

action_45 (39) = happyShift action_41
action_45 (51) = happyShift action_42
action_45 (7) = happyGoto action_38
action_45 (15) = happyGoto action_58
action_45 (16) = happyGoto action_40
action_45 _ = happyReduce_41

action_46 _ = happyReduce_4

action_47 (25) = happyShift action_56
action_47 (39) = happyShift action_57
action_47 _ = happyReduce_7

action_48 _ = happyReduce_15

action_49 (26) = happyShift action_33
action_49 (28) = happyShift action_9
action_49 (31) = happyShift action_11
action_49 (39) = happyShift action_12
action_49 (41) = happyShift action_13
action_49 (43) = happyShift action_14
action_49 (48) = happyShift action_15
action_49 (49) = happyShift action_16
action_49 (50) = happyShift action_17
action_49 (51) = happyShift action_34
action_49 (8) = happyGoto action_55
action_49 (9) = happyGoto action_5
action_49 (10) = happyGoto action_6
action_49 _ = happyFail

action_50 (51) = happyShift action_54
action_50 _ = happyFail

action_51 (26) = happyShift action_33
action_51 (28) = happyShift action_9
action_51 (31) = happyShift action_11
action_51 (39) = happyShift action_12
action_51 (41) = happyShift action_13
action_51 (43) = happyShift action_14
action_51 (48) = happyShift action_15
action_51 (49) = happyShift action_16
action_51 (50) = happyShift action_17
action_51 (51) = happyShift action_34
action_51 (8) = happyGoto action_53
action_51 (9) = happyGoto action_5
action_51 (10) = happyGoto action_6
action_51 _ = happyFail

action_52 _ = happyFail

action_53 _ = happyReduce_18

action_54 (37) = happyShift action_20
action_54 (13) = happyGoto action_104
action_54 _ = happyReduce_37

action_55 (42) = happyShift action_103
action_55 _ = happyFail

action_56 (51) = happyShift action_102
action_56 _ = happyFail

action_57 (51) = happyShift action_101
action_57 (22) = happyGoto action_99
action_57 (23) = happyGoto action_100
action_57 _ = happyReduce_55

action_58 (37) = happyShift action_20
action_58 (13) = happyGoto action_98
action_58 _ = happyReduce_37

action_59 (26) = happyShift action_33
action_59 (28) = happyShift action_9
action_59 (31) = happyShift action_11
action_59 (39) = happyShift action_12
action_59 (41) = happyShift action_13
action_59 (43) = happyShift action_14
action_59 (48) = happyShift action_15
action_59 (49) = happyShift action_16
action_59 (50) = happyShift action_17
action_59 (51) = happyShift action_34
action_59 (8) = happyGoto action_97
action_59 (9) = happyGoto action_5
action_59 (10) = happyGoto action_6
action_59 _ = happyFail

action_60 (51) = happyShift action_45
action_60 (5) = happyGoto action_43
action_60 (14) = happyGoto action_96
action_60 _ = happyFail

action_61 (37) = happyShift action_95
action_61 _ = happyFail

action_62 (34) = happyShift action_94
action_62 _ = happyFail

action_63 _ = happyReduce_44

action_64 (32) = happyShift action_76
action_64 (41) = happyShift action_77
action_64 (45) = happyShift action_78
action_64 (51) = happyShift action_79
action_64 (12) = happyGoto action_93
action_64 _ = happyFail

action_65 (35) = happyShift action_92
action_65 _ = happyFail

action_66 (44) = happyShift action_91
action_66 _ = happyFail

action_67 _ = happyReduce_24

action_68 (29) = happyShift action_59
action_68 _ = happyFail

action_69 (37) = happyShift action_20
action_69 (13) = happyGoto action_90
action_69 _ = happyReduce_37

action_70 (26) = happyShift action_33
action_70 (28) = happyShift action_9
action_70 (31) = happyShift action_11
action_70 (39) = happyShift action_12
action_70 (41) = happyShift action_13
action_70 (43) = happyShift action_14
action_70 (48) = happyShift action_15
action_70 (49) = happyShift action_16
action_70 (50) = happyShift action_17
action_70 (51) = happyShift action_34
action_70 (8) = happyGoto action_30
action_70 (9) = happyGoto action_5
action_70 (10) = happyGoto action_6
action_70 (19) = happyGoto action_89
action_70 _ = happyFail

action_71 (26) = happyShift action_33
action_71 (28) = happyShift action_9
action_71 (31) = happyShift action_11
action_71 (39) = happyShift action_12
action_71 (41) = happyShift action_13
action_71 (43) = happyShift action_14
action_71 (48) = happyShift action_15
action_71 (49) = happyShift action_16
action_71 (50) = happyShift action_17
action_71 (51) = happyShift action_34
action_71 (8) = happyGoto action_88
action_71 (9) = happyGoto action_5
action_71 (10) = happyGoto action_6
action_71 _ = happyFail

action_72 (26) = happyShift action_33
action_72 (28) = happyShift action_9
action_72 (31) = happyShift action_11
action_72 (39) = happyShift action_12
action_72 (41) = happyShift action_13
action_72 (43) = happyShift action_14
action_72 (48) = happyShift action_15
action_72 (49) = happyShift action_16
action_72 (50) = happyShift action_17
action_72 (51) = happyShift action_34
action_72 (8) = happyGoto action_87
action_72 (9) = happyGoto action_5
action_72 (10) = happyGoto action_6
action_72 _ = happyFail

action_73 (37) = happyShift action_20
action_73 (13) = happyGoto action_86
action_73 _ = happyReduce_37

action_74 (49) = happyShift action_28
action_74 (51) = happyShift action_29
action_74 (11) = happyGoto action_25
action_74 (21) = happyGoto action_85
action_74 _ = happyFail

action_75 _ = happyReduce_2

action_76 _ = happyReduce_31

action_77 (32) = happyShift action_76
action_77 (41) = happyShift action_77
action_77 (45) = happyShift action_78
action_77 (50) = happyShift action_84
action_77 (51) = happyShift action_79
action_77 (12) = happyGoto action_83
action_77 _ = happyFail

action_78 (32) = happyShift action_76
action_78 (41) = happyShift action_77
action_78 (45) = happyShift action_78
action_78 (50) = happyShift action_82
action_78 (51) = happyShift action_79
action_78 (12) = happyGoto action_81
action_78 _ = happyFail

action_79 _ = happyReduce_32

action_80 _ = happyReduce_38

action_81 (42) = happyShift action_115
action_81 _ = happyFail

action_82 (42) = happyShift action_114
action_82 _ = happyFail

action_83 (42) = happyShift action_113
action_83 _ = happyFail

action_84 (42) = happyShift action_112
action_84 _ = happyFail

action_85 _ = happyReduce_54

action_86 _ = happyReduce_23

action_87 _ = happyReduce_30

action_88 _ = happyReduce_29

action_89 _ = happyReduce_50

action_90 _ = happyReduce_25

action_91 _ = happyReduce_26

action_92 (24) = happyShift action_7
action_92 (26) = happyShift action_8
action_92 (28) = happyShift action_9
action_92 (30) = happyShift action_10
action_92 (31) = happyShift action_11
action_92 (39) = happyShift action_12
action_92 (41) = happyShift action_13
action_92 (43) = happyShift action_14
action_92 (48) = happyShift action_15
action_92 (49) = happyShift action_16
action_92 (50) = happyShift action_17
action_92 (51) = happyShift action_18
action_92 (4) = happyGoto action_65
action_92 (8) = happyGoto action_4
action_92 (9) = happyGoto action_5
action_92 (10) = happyGoto action_6
action_92 (17) = happyGoto action_111
action_92 _ = happyReduce_45

action_93 _ = happyReduce_3

action_94 (26) = happyShift action_33
action_94 (28) = happyShift action_9
action_94 (31) = happyShift action_11
action_94 (39) = happyShift action_12
action_94 (41) = happyShift action_13
action_94 (43) = happyShift action_14
action_94 (48) = happyShift action_15
action_94 (49) = happyShift action_16
action_94 (50) = happyShift action_17
action_94 (51) = happyShift action_34
action_94 (8) = happyGoto action_110
action_94 (9) = happyGoto action_5
action_94 (10) = happyGoto action_6
action_94 _ = happyFail

action_95 (32) = happyShift action_76
action_95 (41) = happyShift action_77
action_95 (45) = happyShift action_78
action_95 (51) = happyShift action_79
action_95 (12) = happyGoto action_109
action_95 _ = happyFail

action_96 _ = happyReduce_40

action_97 _ = happyReduce_17

action_98 (33) = happyShift action_108
action_98 _ = happyFail

action_99 (40) = happyShift action_107
action_99 _ = happyFail

action_100 _ = happyReduce_56

action_101 (36) = happyShift action_106
action_101 _ = happyReduce_57

action_102 _ = happyReduce_9

action_103 (37) = happyShift action_20
action_103 (13) = happyGoto action_105
action_103 _ = happyReduce_37

action_104 _ = happyReduce_27

action_105 _ = happyReduce_28

action_106 (51) = happyShift action_101
action_106 (23) = happyGoto action_119
action_106 _ = happyFail

action_107 (25) = happyShift action_118
action_107 _ = happyReduce_8

action_108 (26) = happyShift action_33
action_108 (28) = happyShift action_9
action_108 (31) = happyShift action_11
action_108 (39) = happyShift action_12
action_108 (41) = happyShift action_13
action_108 (43) = happyShift action_14
action_108 (48) = happyShift action_15
action_108 (49) = happyShift action_16
action_108 (50) = happyShift action_17
action_108 (51) = happyShift action_34
action_108 (8) = happyGoto action_117
action_108 (9) = happyGoto action_5
action_108 (10) = happyGoto action_6
action_108 _ = happyFail

action_109 (40) = happyShift action_116
action_109 _ = happyFail

action_110 _ = happyReduce_16

action_111 _ = happyReduce_46

action_112 _ = happyReduce_34

action_113 _ = happyReduce_36

action_114 _ = happyReduce_33

action_115 _ = happyReduce_35

action_116 _ = happyReduce_12

action_117 _ = happyReduce_6

action_118 (51) = happyShift action_120
action_118 _ = happyFail

action_119 _ = happyReduce_58

action_120 _ = happyReduce_10

happyReduce_1 = happySpecReduce_2  4 happyReduction_1
happyReduction_1 (HappyAbsSyn14  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (Declarations happy_var_2
	)
happyReduction_1 _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_3  4 happyReduction_2
happyReduction_2 (HappyAbsSyn12  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn4
		 (ForwardDecl happy_var_1 happy_var_3
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happyReduce 4 4 happyReduction_3
happyReduction_3 ((HappyAbsSyn12  happy_var_4) `HappyStk`
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
	(HappyAbsSyn13  happy_var_3) `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
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
	(HappyAbsSyn22  happy_var_3) `HappyStk`
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
	(HappyAbsSyn22  happy_var_3) `HappyStk`
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
	(HappyAbsSyn12  happy_var_4) `HappyStk`
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

happyReduce_15 = happySpecReduce_2  8 happyReduction_15
happyReduction_15 (HappyAbsSyn8  happy_var_2)
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (Application happy_var_1 happy_var_2 Nothing
	)
happyReduction_15 _ _  = notHappyAtAll 

happyReduce_16 = happyReduce 5 9 happyReduction_16
happyReduction_16 ((HappyAbsSyn8  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn13  happy_var_3) `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Function happy_var_2 happy_var_5 happy_var_3
	) `HappyStk` happyRest

happyReduce_17 = happyReduce 4 9 happyReduction_17
happyReduction_17 ((HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn14  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (LetBlock happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_18 = happySpecReduce_3  9 happyReduction_18
happyReduction_18 (HappyAbsSyn8  happy_var_3)
	(HappyTerminal (T.Infix      _ happy_var_2))
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn8
		 (Application (Application (Var happy_var_2 Nothing ) happy_var_1 Nothing) happy_var_3 Nothing
	)
happyReduction_18 _ _ _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_2  10 happyReduction_19
happyReduction_19 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (T.Bitfield   _ happy_var_1))
	 =  HappyAbsSyn8
		 (Bitfield (bitsOfString happy_var_1) happy_var_2
	)
happyReduction_19 _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_2  10 happyReduction_20
happyReduction_20 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (T.String     _ happy_var_1))
	 =  HappyAbsSyn8
		 (Quote happy_var_1 happy_var_2
	)
happyReduction_20 _ _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_2  10 happyReduction_21
happyReduction_21 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (T.Integer    _ happy_var_1))
	 =  HappyAbsSyn8
		 (Z (read happy_var_1) happy_var_2
	)
happyReduction_21 _ _  = notHappyAtAll 

happyReduce_22 = happySpecReduce_2  10 happyReduction_22
happyReduction_22 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn8
		 (Var happy_var_1 happy_var_2
	)
happyReduction_22 _ _  = notHappyAtAll 

happyReduce_23 = happyReduce 4 10 happyReduction_23
happyReduction_23 ((HappyAbsSyn13  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Record happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_24 = happySpecReduce_3  10 happyReduction_24
happyReduction_24 _
	(HappyAbsSyn8  happy_var_2)
	_
	 =  HappyAbsSyn8
		 (happy_var_2
	)
happyReduction_24 _ _ _  = notHappyAtAll 

happyReduce_25 = happyReduce 4 10 happyReduction_25
happyReduction_25 ((HappyAbsSyn13  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn18  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Array happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_26 = happyReduce 4 10 happyReduction_26
happyReduction_26 (_ `HappyStk`
	(HappyAbsSyn17  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Procedure happy_var_3 Nothing
	) `HappyStk` happyRest

happyReduce_27 = happyReduce 4 10 happyReduction_27
happyReduction_27 ((HappyAbsSyn13  happy_var_4) `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_3)) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Lookup happy_var_1 happy_var_3 happy_var_4
	) `HappyStk` happyRest

happyReduce_28 = happyReduce 5 10 happyReduction_28
happyReduction_28 ((HappyAbsSyn13  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Index happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_29 = happySpecReduce_3  11 happyReduction_29
happyReduction_29 (HappyAbsSyn8  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn11
		 ((happy_var_1, happy_var_3)
	)
happyReduction_29 _ _ _  = notHappyAtAll 

happyReduce_30 = happySpecReduce_3  11 happyReduction_30
happyReduction_30 (HappyAbsSyn8  happy_var_3)
	_
	(HappyTerminal (T.String     _ happy_var_1))
	 =  HappyAbsSyn11
		 ((happy_var_1, happy_var_3)
	)
happyReduction_30 _ _ _  = notHappyAtAll 

happyReduce_31 = happySpecReduce_1  12 happyReduction_31
happyReduction_31 _
	 =  HappyAbsSyn12
		 (Z'
	)

happyReduce_32 = happySpecReduce_1  12 happyReduction_32
happyReduction_32 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn12
		 (Var' happy_var_1
	)
happyReduction_32 _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_3  12 happyReduction_33
happyReduction_33 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn12
		 (Bitfield' (read happy_var_2)
	)
happyReduction_33 _ _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_3  12 happyReduction_34
happyReduction_34 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn12
		 (Bitfield' (read happy_var_2)
	)
happyReduction_34 _ _ _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_3  12 happyReduction_35
happyReduction_35 _
	(HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (Array' happy_var_2 Nothing
	)
happyReduction_35 _ _ _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_3  12 happyReduction_36
happyReduction_36 _
	(HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (Array' happy_var_2 Nothing
	)
happyReduction_36 _ _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_0  13 happyReduction_37
happyReduction_37  =  HappyAbsSyn13
		 (Nothing
	)

happyReduce_38 = happySpecReduce_2  13 happyReduction_38
happyReduction_38 (HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn13
		 (Just happy_var_2
	)
happyReduction_38 _ _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_1  14 happyReduction_39
happyReduction_39 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn14
		 ([happy_var_1]
	)
happyReduction_39 _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_3  14 happyReduction_40
happyReduction_40 (HappyAbsSyn14  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_1:happy_var_3
	)
happyReduction_40 _ _ _  = notHappyAtAll 

happyReduce_41 = happySpecReduce_0  15 happyReduction_41
happyReduction_41  =  HappyAbsSyn15
		 ([]
	)

happyReduce_42 = happySpecReduce_1  15 happyReduction_42
happyReduction_42 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 (happy_var_1
	)
happyReduction_42 _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_1  16 happyReduction_43
happyReduction_43 (HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn15
		 ([happy_var_1]
	)
happyReduction_43 _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_2  16 happyReduction_44
happyReduction_44 (HappyAbsSyn15  happy_var_2)
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn15
		 (happy_var_1:happy_var_2
	)
happyReduction_44 _ _  = notHappyAtAll 

happyReduce_45 = happySpecReduce_0  17 happyReduction_45
happyReduction_45  =  HappyAbsSyn17
		 ([]
	)

happyReduce_46 = happySpecReduce_3  17 happyReduction_46
happyReduction_46 (HappyAbsSyn17  happy_var_3)
	_
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn17
		 (happy_var_1:happy_var_3
	)
happyReduction_46 _ _ _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_0  18 happyReduction_47
happyReduction_47  =  HappyAbsSyn18
		 ([]
	)

happyReduce_48 = happySpecReduce_1  18 happyReduction_48
happyReduction_48 (HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1
	)
happyReduction_48 _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_1  19 happyReduction_49
happyReduction_49 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn18
		 ([happy_var_1]
	)
happyReduction_49 _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_3  19 happyReduction_50
happyReduction_50 (HappyAbsSyn18  happy_var_3)
	_
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1:happy_var_3
	)
happyReduction_50 _ _ _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_0  20 happyReduction_51
happyReduction_51  =  HappyAbsSyn20
		 ([]
	)

happyReduce_52 = happySpecReduce_1  20 happyReduction_52
happyReduction_52 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1
	)
happyReduction_52 _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_1  21 happyReduction_53
happyReduction_53 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn20
		 ([happy_var_1]
	)
happyReduction_53 _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_3  21 happyReduction_54
happyReduction_54 (HappyAbsSyn20  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1:happy_var_3
	)
happyReduction_54 _ _ _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_0  22 happyReduction_55
happyReduction_55  =  HappyAbsSyn22
		 ([]
	)

happyReduce_56 = happySpecReduce_1  22 happyReduction_56
happyReduction_56 (HappyAbsSyn22  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1
	)
happyReduction_56 _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_1  23 happyReduction_57
happyReduction_57 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn22
		 ([happy_var_1]
	)
happyReduction_57 _  = notHappyAtAll 

happyReduce_58 = happySpecReduce_3  23 happyReduction_58
happyReduction_58 (HappyAbsSyn22  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn22
		 (happy_var_1:happy_var_3
	)
happyReduction_58 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 52 52 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	T.Keyword    _ "import" -> cont 24;
	T.Keyword    _ "as" -> cont 25;
	T.Keyword    _ "let" -> cont 26;
	T.Keyword    _ "and" -> cont 27;
	T.Keyword    _ "fun" -> cont 28;
	T.Keyword    _ "in" -> cont 29;
	T.Keyword    _ "type" -> cont 30;
	T.Keyword    _ "do" -> cont 31;
	T.Keyword    _ "integer" -> cont 32;
	T.Infix      _ "=" -> cont 33;
	T.Infix      _ "->" -> cont 34;
	T.Infix      _ ";" -> cont 35;
	T.Infix      _ "," -> cont 36;
	T.Infix      _ ":" -> cont 37;
	T.Infix      _ "::" -> cont 38;
	T.OutfixL    _ "(" -> cont 39;
	T.OutfixR    _ ")" -> cont 40;
	T.OutfixL    _ "[" -> cont 41;
	T.OutfixR    _ "]" -> cont 42;
	T.OutfixL    _ "{" -> cont 43;
	T.OutfixR    _ "}" -> cont 44;
	T.Postfix    _ "[" -> cont 45;
	T.Postfix    _ "." -> cont 46;
	T.Infix      _ happy_dollar_dollar -> cont 47;
	T.Bitfield   _ happy_dollar_dollar -> cont 48;
	T.String     _ happy_dollar_dollar -> cont 49;
	T.Integer    _ happy_dollar_dollar -> cont 50;
	T.Identifier _ happy_dollar_dollar -> cont 51;
	_ -> happyError' (tk:tks)
	}

happyError_ 52 tk tks = happyError' tks
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

bitsOfString :: String -> [Bool]
bitsOfString = map (/='0')
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
