{-# OPTIONS_GHC -w #-}
module SAWScript.Parser ( parse ) where

import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST
import SAWScript.FixFunctor

-- parser produced by Happy Version 1.18.9

data HappyAbsSyn 
	= HappyTerminal (T.Token AlexPosn)
	| HappyErrorToken Int
	| HappyAbsSyn4 (TopStmt MPType)
	| HappyAbsSyn5 (BlockStmt MPType)
	| HappyAbsSyn6 ((Name, Expr MPType))
	| HappyAbsSyn8 ((Name, MPType))
	| HappyAbsSyn9 (Expr MPType)
	| HappyAbsSyn15 (CType)
	| HappyAbsSyn16 (PType)
	| HappyAbsSyn17 (MPType)
	| HappyAbsSyn18 ([(Name, Expr MPType)])
	| HappyAbsSyn19 ([(Name, MPType)])
	| HappyAbsSyn21 ([TopStmt MPType])
	| HappyAbsSyn22 ([BlockStmt MPType])
	| HappyAbsSyn23 ([Expr MPType])
	| HappyAbsSyn27 ([Name])

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
 action_124,
 action_125,
 action_126,
 action_127,
 action_128,
 action_129,
 action_130,
 action_131,
 action_132,
 action_133 :: () => Int -> ({-HappyReduction (HappyIdentity) = -}
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
 happyReduce_61,
 happyReduce_62,
 happyReduce_63,
 happyReduce_64,
 happyReduce_65,
 happyReduce_66,
 happyReduce_67,
 happyReduce_68 :: () => ({-HappyReduction (HappyIdentity) = -}
	   Int 
	-> (T.Token AlexPosn)
	-> HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)
	-> [HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)

action_0 (29) = happyShift action_4
action_0 (31) = happyShift action_2
action_0 (35) = happyShift action_5
action_0 (56) = happyShift action_6
action_0 (4) = happyGoto action_3
action_0 _ = happyFail

action_1 (31) = happyShift action_2
action_1 _ = happyFail

action_2 (56) = happyShift action_13
action_2 (6) = happyGoto action_11
action_2 (18) = happyGoto action_12
action_2 _ = happyFail

action_3 (57) = happyAccept
action_3 _ = happyFail

action_4 (56) = happyShift action_10
action_4 (7) = happyGoto action_9
action_4 _ = happyFail

action_5 (56) = happyShift action_8
action_5 _ = happyFail

action_6 (43) = happyShift action_7
action_6 _ = happyFail

action_7 (37) = happyShift action_24
action_7 (46) = happyShift action_25
action_7 (50) = happyShift action_26
action_7 (56) = happyShift action_27
action_7 (15) = happyGoto action_23
action_7 _ = happyFail

action_8 (38) = happyShift action_22
action_8 _ = happyFail

action_9 _ = happyReduce_4

action_10 (30) = happyShift action_20
action_10 (44) = happyShift action_21
action_10 _ = happyReduce_10

action_11 (32) = happyShift action_19
action_11 _ = happyReduce_47

action_12 _ = happyReduce_1

action_13 (44) = happyShift action_17
action_13 (56) = happyShift action_18
action_13 (8) = happyGoto action_14
action_13 (19) = happyGoto action_15
action_13 (20) = happyGoto action_16
action_13 _ = happyReduce_49

action_14 (44) = happyShift action_17
action_14 (56) = happyShift action_18
action_14 (8) = happyGoto action_14
action_14 (20) = happyGoto action_39
action_14 _ = happyReduce_51

action_15 (42) = happyShift action_38
action_15 (17) = happyGoto action_37
action_15 _ = happyReduce_45

action_16 _ = happyReduce_50

action_17 (56) = happyShift action_36
action_17 _ = happyFail

action_18 _ = happyReduce_14

action_19 (56) = happyShift action_13
action_19 (6) = happyGoto action_11
action_19 (18) = happyGoto action_35
action_19 _ = happyFail

action_20 (56) = happyShift action_34
action_20 _ = happyFail

action_21 (56) = happyShift action_33
action_21 (27) = happyGoto action_31
action_21 (28) = happyGoto action_32
action_21 _ = happyReduce_65

action_22 (37) = happyShift action_24
action_22 (46) = happyShift action_25
action_22 (50) = happyShift action_26
action_22 (56) = happyShift action_27
action_22 (15) = happyGoto action_30
action_22 _ = happyFail

action_23 _ = happyReduce_2

action_24 _ = happyReduce_37

action_25 (55) = happyShift action_29
action_25 _ = happyFail

action_26 (55) = happyShift action_28
action_26 _ = happyFail

action_27 _ = happyReduce_38

action_28 (47) = happyShift action_50
action_28 _ = happyFail

action_29 (47) = happyShift action_49
action_29 _ = happyFail

action_30 _ = happyReduce_3

action_31 (45) = happyShift action_48
action_31 _ = happyFail

action_32 _ = happyReduce_66

action_33 (41) = happyShift action_47
action_33 _ = happyReduce_67

action_34 _ = happyReduce_12

action_35 _ = happyReduce_48

action_36 (42) = happyShift action_46
action_36 _ = happyFail

action_37 (38) = happyShift action_45
action_37 _ = happyFail

action_38 (37) = happyShift action_41
action_38 (46) = happyShift action_42
action_38 (50) = happyShift action_43
action_38 (56) = happyShift action_44
action_38 (16) = happyGoto action_40
action_38 _ = happyFail

action_39 _ = happyReduce_52

action_40 _ = happyReduce_46

action_41 _ = happyReduce_41

action_42 (55) = happyShift action_70
action_42 _ = happyFail

action_43 (55) = happyShift action_69
action_43 _ = happyFail

action_44 _ = happyReduce_42

action_45 (31) = happyShift action_59
action_45 (33) = happyShift action_60
action_45 (36) = happyShift action_61
action_45 (44) = happyShift action_62
action_45 (46) = happyShift action_63
action_45 (48) = happyShift action_64
action_45 (53) = happyShift action_65
action_45 (54) = happyShift action_66
action_45 (55) = happyShift action_67
action_45 (56) = happyShift action_68
action_45 (9) = happyGoto action_54
action_45 (10) = happyGoto action_55
action_45 (11) = happyGoto action_56
action_45 (12) = happyGoto action_57
action_45 (13) = happyGoto action_58
action_45 _ = happyFail

action_46 (37) = happyShift action_41
action_46 (46) = happyShift action_42
action_46 (50) = happyShift action_43
action_46 (56) = happyShift action_44
action_46 (16) = happyGoto action_53
action_46 _ = happyFail

action_47 (56) = happyShift action_33
action_47 (28) = happyGoto action_52
action_47 _ = happyFail

action_48 (30) = happyShift action_51
action_48 _ = happyReduce_11

action_49 _ = happyReduce_40

action_50 _ = happyReduce_39

action_51 (56) = happyShift action_96
action_51 _ = happyFail

action_52 _ = happyReduce_68

action_53 (45) = happyShift action_95
action_53 _ = happyFail

action_54 _ = happyReduce_9

action_55 _ = happyReduce_16

action_56 (31) = happyShift action_59
action_56 (33) = happyShift action_60
action_56 (36) = happyShift action_61
action_56 (44) = happyShift action_62
action_56 (46) = happyShift action_63
action_56 (48) = happyShift action_64
action_56 (53) = happyShift action_65
action_56 (54) = happyShift action_66
action_56 (55) = happyShift action_67
action_56 (56) = happyShift action_68
action_56 (10) = happyGoto action_94
action_56 (12) = happyGoto action_57
action_56 (13) = happyGoto action_90
action_56 _ = happyReduce_17

action_57 _ = happyReduce_18

action_58 (31) = happyShift action_59
action_58 (33) = happyShift action_60
action_58 (36) = happyShift action_61
action_58 (44) = happyShift action_62
action_58 (46) = happyShift action_63
action_58 (48) = happyShift action_64
action_58 (50) = happyShift action_91
action_58 (51) = happyShift action_92
action_58 (52) = happyShift action_93
action_58 (53) = happyShift action_65
action_58 (54) = happyShift action_66
action_58 (55) = happyShift action_67
action_58 (56) = happyShift action_68
action_58 (10) = happyGoto action_89
action_58 (12) = happyGoto action_57
action_58 (13) = happyGoto action_90
action_58 _ = happyReduce_19

action_59 (56) = happyShift action_13
action_59 (6) = happyGoto action_11
action_59 (18) = happyGoto action_88
action_59 _ = happyFail

action_60 (44) = happyShift action_17
action_60 (56) = happyShift action_18
action_60 (8) = happyGoto action_14
action_60 (20) = happyGoto action_87
action_60 _ = happyFail

action_61 (48) = happyShift action_86
action_61 _ = happyFail

action_62 (31) = happyShift action_59
action_62 (33) = happyShift action_60
action_62 (36) = happyShift action_61
action_62 (44) = happyShift action_62
action_62 (46) = happyShift action_63
action_62 (48) = happyShift action_64
action_62 (53) = happyShift action_65
action_62 (54) = happyShift action_66
action_62 (55) = happyShift action_67
action_62 (56) = happyShift action_68
action_62 (9) = happyGoto action_85
action_62 (10) = happyGoto action_55
action_62 (11) = happyGoto action_56
action_62 (12) = happyGoto action_57
action_62 (13) = happyGoto action_58
action_62 _ = happyFail

action_63 (31) = happyShift action_59
action_63 (33) = happyShift action_60
action_63 (36) = happyShift action_61
action_63 (44) = happyShift action_62
action_63 (46) = happyShift action_63
action_63 (48) = happyShift action_64
action_63 (53) = happyShift action_65
action_63 (54) = happyShift action_66
action_63 (55) = happyShift action_67
action_63 (56) = happyShift action_68
action_63 (9) = happyGoto action_82
action_63 (10) = happyGoto action_55
action_63 (11) = happyGoto action_56
action_63 (12) = happyGoto action_57
action_63 (13) = happyGoto action_58
action_63 (23) = happyGoto action_83
action_63 (24) = happyGoto action_84
action_63 _ = happyReduce_57

action_64 (54) = happyShift action_80
action_64 (56) = happyShift action_81
action_64 (14) = happyGoto action_77
action_64 (25) = happyGoto action_78
action_64 (26) = happyGoto action_79
action_64 _ = happyReduce_61

action_65 (42) = happyShift action_38
action_65 (17) = happyGoto action_76
action_65 _ = happyReduce_45

action_66 (42) = happyShift action_38
action_66 (17) = happyGoto action_75
action_66 _ = happyReduce_45

action_67 (42) = happyShift action_38
action_67 (17) = happyGoto action_74
action_67 _ = happyReduce_45

action_68 (42) = happyShift action_38
action_68 (17) = happyGoto action_73
action_68 _ = happyReduce_45

action_69 (47) = happyShift action_72
action_69 _ = happyFail

action_70 (47) = happyShift action_71
action_70 _ = happyFail

action_71 _ = happyReduce_44

action_72 _ = happyReduce_43

action_73 _ = happyReduce_28

action_74 _ = happyReduce_27

action_75 _ = happyReduce_26

action_76 _ = happyReduce_25

action_77 (41) = happyShift action_113
action_77 _ = happyReduce_63

action_78 (49) = happyShift action_112
action_78 _ = happyFail

action_79 _ = happyReduce_62

action_80 (42) = happyShift action_111
action_80 _ = happyFail

action_81 (42) = happyShift action_110
action_81 _ = happyFail

action_82 (41) = happyShift action_109
action_82 _ = happyReduce_59

action_83 (47) = happyShift action_108
action_83 _ = happyFail

action_84 _ = happyReduce_58

action_85 (45) = happyShift action_107
action_85 _ = happyFail

action_86 (31) = happyShift action_105
action_86 (33) = happyShift action_60
action_86 (36) = happyShift action_61
action_86 (44) = happyShift action_62
action_86 (46) = happyShift action_63
action_86 (48) = happyShift action_64
action_86 (53) = happyShift action_65
action_86 (54) = happyShift action_66
action_86 (55) = happyShift action_67
action_86 (56) = happyShift action_106
action_86 (5) = happyGoto action_102
action_86 (9) = happyGoto action_103
action_86 (10) = happyGoto action_55
action_86 (11) = happyGoto action_56
action_86 (12) = happyGoto action_57
action_86 (13) = happyGoto action_58
action_86 (22) = happyGoto action_104
action_86 _ = happyReduce_55

action_87 (42) = happyShift action_38
action_87 (17) = happyGoto action_101
action_87 _ = happyReduce_45

action_88 (34) = happyShift action_100
action_88 _ = happyFail

action_89 _ = happyReduce_20

action_90 (50) = happyShift action_91
action_90 (51) = happyShift action_92
action_90 (52) = happyShift action_93
action_90 _ = happyReduce_19

action_91 (31) = happyShift action_59
action_91 (33) = happyShift action_60
action_91 (36) = happyShift action_61
action_91 (44) = happyShift action_62
action_91 (46) = happyShift action_63
action_91 (48) = happyShift action_64
action_91 (53) = happyShift action_65
action_91 (54) = happyShift action_66
action_91 (55) = happyShift action_67
action_91 (56) = happyShift action_68
action_91 (9) = happyGoto action_99
action_91 (10) = happyGoto action_55
action_91 (11) = happyGoto action_56
action_91 (12) = happyGoto action_57
action_91 (13) = happyGoto action_58
action_91 _ = happyFail

action_92 (56) = happyShift action_98
action_92 _ = happyFail

action_93 (31) = happyShift action_59
action_93 (33) = happyShift action_60
action_93 (36) = happyShift action_61
action_93 (44) = happyShift action_62
action_93 (46) = happyShift action_63
action_93 (48) = happyShift action_64
action_93 (53) = happyShift action_65
action_93 (54) = happyShift action_66
action_93 (55) = happyShift action_67
action_93 (56) = happyShift action_68
action_93 (9) = happyGoto action_97
action_93 (10) = happyGoto action_55
action_93 (11) = happyGoto action_56
action_93 (12) = happyGoto action_57
action_93 (13) = happyGoto action_58
action_93 _ = happyFail

action_94 _ = happyReduce_21

action_95 _ = happyReduce_15

action_96 _ = happyReduce_13

action_97 _ = happyReduce_24

action_98 (42) = happyShift action_38
action_98 (17) = happyGoto action_128
action_98 _ = happyReduce_45

action_99 (47) = happyShift action_127
action_99 _ = happyFail

action_100 (31) = happyShift action_59
action_100 (33) = happyShift action_60
action_100 (36) = happyShift action_61
action_100 (44) = happyShift action_62
action_100 (46) = happyShift action_63
action_100 (48) = happyShift action_64
action_100 (53) = happyShift action_65
action_100 (54) = happyShift action_66
action_100 (55) = happyShift action_67
action_100 (56) = happyShift action_68
action_100 (9) = happyGoto action_126
action_100 (10) = happyGoto action_55
action_100 (11) = happyGoto action_56
action_100 (12) = happyGoto action_57
action_100 (13) = happyGoto action_58
action_100 _ = happyFail

action_101 (39) = happyShift action_125
action_101 _ = happyFail

action_102 (40) = happyShift action_124
action_102 _ = happyFail

action_103 _ = happyReduce_5

action_104 (49) = happyShift action_123
action_104 _ = happyFail

action_105 (56) = happyShift action_13
action_105 (6) = happyGoto action_11
action_105 (18) = happyGoto action_122
action_105 _ = happyFail

action_106 (38) = happyShift action_120
action_106 (42) = happyShift action_38
action_106 (43) = happyShift action_121
action_106 (17) = happyGoto action_73
action_106 _ = happyReduce_45

action_107 _ = happyReduce_29

action_108 (42) = happyShift action_38
action_108 (17) = happyGoto action_119
action_108 _ = happyReduce_45

action_109 (31) = happyShift action_59
action_109 (33) = happyShift action_60
action_109 (36) = happyShift action_61
action_109 (44) = happyShift action_62
action_109 (46) = happyShift action_63
action_109 (48) = happyShift action_64
action_109 (53) = happyShift action_65
action_109 (54) = happyShift action_66
action_109 (55) = happyShift action_67
action_109 (56) = happyShift action_68
action_109 (9) = happyGoto action_82
action_109 (10) = happyGoto action_55
action_109 (11) = happyGoto action_56
action_109 (12) = happyGoto action_57
action_109 (13) = happyGoto action_58
action_109 (24) = happyGoto action_118
action_109 _ = happyFail

action_110 (31) = happyShift action_59
action_110 (33) = happyShift action_60
action_110 (36) = happyShift action_61
action_110 (44) = happyShift action_62
action_110 (46) = happyShift action_63
action_110 (48) = happyShift action_64
action_110 (53) = happyShift action_65
action_110 (54) = happyShift action_66
action_110 (55) = happyShift action_67
action_110 (56) = happyShift action_68
action_110 (9) = happyGoto action_117
action_110 (10) = happyGoto action_55
action_110 (11) = happyGoto action_56
action_110 (12) = happyGoto action_57
action_110 (13) = happyGoto action_58
action_110 _ = happyFail

action_111 (31) = happyShift action_59
action_111 (33) = happyShift action_60
action_111 (36) = happyShift action_61
action_111 (44) = happyShift action_62
action_111 (46) = happyShift action_63
action_111 (48) = happyShift action_64
action_111 (53) = happyShift action_65
action_111 (54) = happyShift action_66
action_111 (55) = happyShift action_67
action_111 (56) = happyShift action_68
action_111 (9) = happyGoto action_116
action_111 (10) = happyGoto action_55
action_111 (11) = happyGoto action_56
action_111 (12) = happyGoto action_57
action_111 (13) = happyGoto action_58
action_111 _ = happyFail

action_112 (42) = happyShift action_38
action_112 (17) = happyGoto action_115
action_112 _ = happyReduce_45

action_113 (54) = happyShift action_80
action_113 (56) = happyShift action_81
action_113 (14) = happyGoto action_77
action_113 (26) = happyGoto action_114
action_113 _ = happyFail

action_114 _ = happyReduce_64

action_115 _ = happyReduce_31

action_116 _ = happyReduce_36

action_117 _ = happyReduce_35

action_118 _ = happyReduce_60

action_119 _ = happyReduce_30

action_120 (31) = happyShift action_59
action_120 (33) = happyShift action_60
action_120 (36) = happyShift action_61
action_120 (44) = happyShift action_62
action_120 (46) = happyShift action_63
action_120 (48) = happyShift action_64
action_120 (53) = happyShift action_65
action_120 (54) = happyShift action_66
action_120 (55) = happyShift action_67
action_120 (56) = happyShift action_68
action_120 (9) = happyGoto action_133
action_120 (10) = happyGoto action_55
action_120 (11) = happyGoto action_56
action_120 (12) = happyGoto action_57
action_120 (13) = happyGoto action_58
action_120 _ = happyFail

action_121 (37) = happyShift action_24
action_121 (46) = happyShift action_25
action_121 (50) = happyShift action_26
action_121 (56) = happyShift action_27
action_121 (15) = happyGoto action_132
action_121 _ = happyFail

action_122 (34) = happyShift action_100
action_122 _ = happyReduce_8

action_123 _ = happyReduce_32

action_124 (31) = happyShift action_105
action_124 (33) = happyShift action_60
action_124 (36) = happyShift action_61
action_124 (44) = happyShift action_62
action_124 (46) = happyShift action_63
action_124 (48) = happyShift action_64
action_124 (53) = happyShift action_65
action_124 (54) = happyShift action_66
action_124 (55) = happyShift action_67
action_124 (56) = happyShift action_106
action_124 (5) = happyGoto action_102
action_124 (9) = happyGoto action_103
action_124 (10) = happyGoto action_55
action_124 (11) = happyGoto action_56
action_124 (12) = happyGoto action_57
action_124 (13) = happyGoto action_58
action_124 (22) = happyGoto action_131
action_124 _ = happyReduce_55

action_125 (31) = happyShift action_59
action_125 (33) = happyShift action_60
action_125 (36) = happyShift action_61
action_125 (44) = happyShift action_62
action_125 (46) = happyShift action_63
action_125 (48) = happyShift action_64
action_125 (53) = happyShift action_65
action_125 (54) = happyShift action_66
action_125 (55) = happyShift action_67
action_125 (56) = happyShift action_68
action_125 (9) = happyGoto action_130
action_125 (10) = happyGoto action_55
action_125 (11) = happyGoto action_56
action_125 (12) = happyGoto action_57
action_125 (13) = happyGoto action_58
action_125 _ = happyFail

action_126 _ = happyReduce_23

action_127 (42) = happyShift action_38
action_127 (17) = happyGoto action_129
action_127 _ = happyReduce_45

action_128 _ = happyReduce_33

action_129 _ = happyReduce_34

action_130 _ = happyReduce_22

action_131 _ = happyReduce_56

action_132 _ = happyReduce_7

action_133 _ = happyReduce_6

happyReduce_1 = happySpecReduce_2  4 happyReduction_1
happyReduction_1 (HappyAbsSyn18  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (TopLet happy_var_2
	)
happyReduction_1 _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_3  4 happyReduction_2
happyReduction_2 (HappyAbsSyn15  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn4
		 (TopTypeDecl happy_var_1 happy_var_3
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happyReduce 4 4 happyReduction_3
happyReduction_3 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (TypeDef happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_4 = happySpecReduce_2  4 happyReduction_4
happyReduction_4 (HappyAbsSyn4  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (happy_var_2
	)
happyReduction_4 _ _  = notHappyAtAll 

happyReduce_5 = happySpecReduce_1  5 happyReduction_5
happyReduction_5 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn5
		 (Bind Nothing happy_var_1
	)
happyReduction_5 _  = notHappyAtAll 

happyReduce_6 = happySpecReduce_3  5 happyReduction_6
happyReduction_6 (HappyAbsSyn9  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn5
		 (Bind (Just happy_var_1) happy_var_3
	)
happyReduction_6 _ _ _  = notHappyAtAll 

happyReduce_7 = happySpecReduce_3  5 happyReduction_7
happyReduction_7 (HappyAbsSyn15  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn5
		 (BlockTypeDecl happy_var_1 happy_var_3
	)
happyReduction_7 _ _ _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_2  5 happyReduction_8
happyReduction_8 (HappyAbsSyn18  happy_var_2)
	_
	 =  HappyAbsSyn5
		 (BlockLet happy_var_2
	)
happyReduction_8 _ _  = notHappyAtAll 

happyReduce_9 = happyReduce 5 6 happyReduction_9
happyReduction_9 ((HappyAbsSyn9  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_3) `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn6
		 ((happy_var_1, uncurryFunction happy_var_2 happy_var_3 happy_var_5)
	) `HappyStk` happyRest

happyReduce_10 = happySpecReduce_1  7 happyReduction_10
happyReduction_10 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn4
		 (Import happy_var_1 Nothing Nothing
	)
happyReduction_10 _  = notHappyAtAll 

happyReduce_11 = happyReduce 4 7 happyReduction_11
happyReduction_11 (_ `HappyStk`
	(HappyAbsSyn27  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Import happy_var_1 (Just happy_var_3) Nothing
	) `HappyStk` happyRest

happyReduce_12 = happySpecReduce_3  7 happyReduction_12
happyReduction_12 (HappyTerminal (T.Identifier _ happy_var_3))
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn4
		 (Import happy_var_1 Nothing (Just happy_var_3)
	)
happyReduction_12 _ _ _  = notHappyAtAll 

happyReduce_13 = happyReduce 6 7 happyReduction_13
happyReduction_13 ((HappyTerminal (T.Identifier _ happy_var_6)) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_1)) `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Import happy_var_1 (Just happy_var_3) (Just happy_var_6)
	) `HappyStk` happyRest

happyReduce_14 = happySpecReduce_1  8 happyReduction_14
happyReduction_14 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn8
		 ((happy_var_1, Nothing)
	)
happyReduction_14 _  = notHappyAtAll 

happyReduce_15 = happyReduce 5 8 happyReduction_15
happyReduction_15 (_ `HappyStk`
	(HappyAbsSyn16  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 ((happy_var_2, Just happy_var_4)
	) `HappyStk` happyRest

happyReduce_16 = happySpecReduce_1  9 happyReduction_16
happyReduction_16 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_1
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_1  9 happyReduction_17
happyReduction_17 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_1
	)
happyReduction_17 _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_1  10 happyReduction_18
happyReduction_18 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_1
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_1  10 happyReduction_19
happyReduction_19 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_1
	)
happyReduction_19 _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_2  11 happyReduction_20
happyReduction_20 (HappyAbsSyn9  happy_var_2)
	(HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (Application happy_var_1 happy_var_2 Nothing
	)
happyReduction_20 _ _  = notHappyAtAll 

happyReduce_21 = happySpecReduce_2  11 happyReduction_21
happyReduction_21 (HappyAbsSyn9  happy_var_2)
	(HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (Application happy_var_1 happy_var_2 Nothing
	)
happyReduction_21 _ _  = notHappyAtAll 

happyReduce_22 = happyReduce 5 12 happyReduction_22
happyReduction_22 ((HappyAbsSyn9  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn17  happy_var_3) `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (uncurryFunction happy_var_2 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_23 = happyReduce 4 12 happyReduction_23
happyReduction_23 ((HappyAbsSyn9  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn18  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (LetBlock happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_24 = happySpecReduce_3  12 happyReduction_24
happyReduction_24 (HappyAbsSyn9  happy_var_3)
	(HappyTerminal (T.Infix      _ happy_var_2))
	(HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn9
		 (Application (Application (Var happy_var_2 Nothing ) happy_var_1 Nothing) happy_var_3 Nothing
	)
happyReduction_24 _ _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_2  13 happyReduction_25
happyReduction_25 (HappyAbsSyn17  happy_var_2)
	(HappyTerminal (T.Bitfield   _ happy_var_1))
	 =  HappyAbsSyn9
		 (Array (bitsOfString happy_var_1) happy_var_2
	)
happyReduction_25 _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_2  13 happyReduction_26
happyReduction_26 (HappyAbsSyn17  happy_var_2)
	(HappyTerminal (T.String     _ happy_var_1))
	 =  HappyAbsSyn9
		 (Quote happy_var_1 happy_var_2
	)
happyReduction_26 _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_2  13 happyReduction_27
happyReduction_27 (HappyAbsSyn17  happy_var_2)
	(HappyTerminal (T.Integer    _ happy_var_1))
	 =  HappyAbsSyn9
		 (Z (read happy_var_1) happy_var_2
	)
happyReduction_27 _ _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_2  13 happyReduction_28
happyReduction_28 (HappyAbsSyn17  happy_var_2)
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn9
		 (Var happy_var_1 happy_var_2
	)
happyReduction_28 _ _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_3  13 happyReduction_29
happyReduction_29 _
	(HappyAbsSyn9  happy_var_2)
	_
	 =  HappyAbsSyn9
		 (happy_var_2
	)
happyReduction_29 _ _ _  = notHappyAtAll 

happyReduce_30 = happyReduce 4 13 happyReduction_30
happyReduction_30 ((HappyAbsSyn17  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn23  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (Array happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_31 = happyReduce 4 13 happyReduction_31
happyReduction_31 ((HappyAbsSyn17  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn18  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (Record happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_32 = happyReduce 4 13 happyReduction_32
happyReduction_32 (_ `HappyStk`
	(HappyAbsSyn22  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (Block happy_var_3 Nothing
	) `HappyStk` happyRest

happyReduce_33 = happyReduce 4 13 happyReduction_33
happyReduction_33 ((HappyAbsSyn17  happy_var_4) `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_3)) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (Lookup happy_var_1 happy_var_3 happy_var_4
	) `HappyStk` happyRest

happyReduce_34 = happyReduce 5 13 happyReduction_34
happyReduction_34 ((HappyAbsSyn17  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn9  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn9
		 (Index happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_35 = happySpecReduce_3  14 happyReduction_35
happyReduction_35 (HappyAbsSyn9  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn6
		 ((happy_var_1, happy_var_3)
	)
happyReduction_35 _ _ _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_3  14 happyReduction_36
happyReduction_36 (HappyAbsSyn9  happy_var_3)
	_
	(HappyTerminal (T.String     _ happy_var_1))
	 =  HappyAbsSyn6
		 ((happy_var_1, happy_var_3)
	)
happyReduction_36 _ _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_1  15 happyReduction_37
happyReduction_37 _
	 =  HappyAbsSyn15
		 (z
	)

happyReduce_38 = happySpecReduce_1  15 happyReduction_38
happyReduction_38 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn15
		 (syn happy_var_1
	)
happyReduction_38 _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_3  15 happyReduction_39
happyReduction_39 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn15
		 (array bit (read happy_var_2)
	)
happyReduction_39 _ _ _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_3  15 happyReduction_40
happyReduction_40 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn15
		 (array bit (read happy_var_2)
	)
happyReduction_40 _ _ _  = notHappyAtAll 

happyReduce_41 = happySpecReduce_1  16 happyReduction_41
happyReduction_41 _
	 =  HappyAbsSyn16
		 (z
	)

happyReduce_42 = happySpecReduce_1  16 happyReduction_42
happyReduction_42 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn16
		 (syn happy_var_1
	)
happyReduction_42 _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_3  16 happyReduction_43
happyReduction_43 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn16
		 (array bit (read happy_var_2)
	)
happyReduction_43 _ _ _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_3  16 happyReduction_44
happyReduction_44 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn16
		 (array bit (read happy_var_2)
	)
happyReduction_44 _ _ _  = notHappyAtAll 

happyReduce_45 = happySpecReduce_0  17 happyReduction_45
happyReduction_45  =  HappyAbsSyn17
		 (Nothing
	)

happyReduce_46 = happySpecReduce_2  17 happyReduction_46
happyReduction_46 (HappyAbsSyn16  happy_var_2)
	_
	 =  HappyAbsSyn17
		 (Just happy_var_2
	)
happyReduction_46 _ _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_1  18 happyReduction_47
happyReduction_47 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn18
		 ([happy_var_1]
	)
happyReduction_47 _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_3  18 happyReduction_48
happyReduction_48 (HappyAbsSyn18  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1:happy_var_3
	)
happyReduction_48 _ _ _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_0  19 happyReduction_49
happyReduction_49  =  HappyAbsSyn19
		 ([]
	)

happyReduce_50 = happySpecReduce_1  19 happyReduction_50
happyReduction_50 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn19
		 (happy_var_1
	)
happyReduction_50 _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_1  20 happyReduction_51
happyReduction_51 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn19
		 ([happy_var_1]
	)
happyReduction_51 _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_2  20 happyReduction_52
happyReduction_52 (HappyAbsSyn19  happy_var_2)
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn19
		 (happy_var_1:happy_var_2
	)
happyReduction_52 _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_0  21 happyReduction_53
happyReduction_53  =  HappyAbsSyn21
		 ([]
	)

happyReduce_54 = happySpecReduce_3  21 happyReduction_54
happyReduction_54 (HappyAbsSyn21  happy_var_3)
	_
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn21
		 (happy_var_1:happy_var_3
	)
happyReduction_54 _ _ _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_0  22 happyReduction_55
happyReduction_55  =  HappyAbsSyn22
		 ([]
	)

happyReduce_56 = happySpecReduce_3  22 happyReduction_56
happyReduction_56 (HappyAbsSyn22  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1:happy_var_3
	)
happyReduction_56 _ _ _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_0  23 happyReduction_57
happyReduction_57  =  HappyAbsSyn23
		 ([]
	)

happyReduce_58 = happySpecReduce_1  23 happyReduction_58
happyReduction_58 (HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn23
		 (happy_var_1
	)
happyReduction_58 _  = notHappyAtAll 

happyReduce_59 = happySpecReduce_1  24 happyReduction_59
happyReduction_59 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn23
		 ([happy_var_1]
	)
happyReduction_59 _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_3  24 happyReduction_60
happyReduction_60 (HappyAbsSyn23  happy_var_3)
	_
	(HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn23
		 (happy_var_1:happy_var_3
	)
happyReduction_60 _ _ _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_0  25 happyReduction_61
happyReduction_61  =  HappyAbsSyn18
		 ([]
	)

happyReduce_62 = happySpecReduce_1  25 happyReduction_62
happyReduction_62 (HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1
	)
happyReduction_62 _  = notHappyAtAll 

happyReduce_63 = happySpecReduce_1  26 happyReduction_63
happyReduction_63 (HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn18
		 ([happy_var_1]
	)
happyReduction_63 _  = notHappyAtAll 

happyReduce_64 = happySpecReduce_3  26 happyReduction_64
happyReduction_64 (HappyAbsSyn18  happy_var_3)
	_
	(HappyAbsSyn6  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1:happy_var_3
	)
happyReduction_64 _ _ _  = notHappyAtAll 

happyReduce_65 = happySpecReduce_0  27 happyReduction_65
happyReduction_65  =  HappyAbsSyn27
		 ([]
	)

happyReduce_66 = happySpecReduce_1  27 happyReduction_66
happyReduction_66 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn27
		 (happy_var_1
	)
happyReduction_66 _  = notHappyAtAll 

happyReduce_67 = happySpecReduce_1  28 happyReduction_67
happyReduction_67 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn27
		 ([happy_var_1]
	)
happyReduction_67 _  = notHappyAtAll 

happyReduce_68 = happySpecReduce_3  28 happyReduction_68
happyReduction_68 (HappyAbsSyn27  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn27
		 (happy_var_1:happy_var_3
	)
happyReduction_68 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 57 57 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	T.Keyword    _ "import" -> cont 29;
	T.Keyword    _ "as" -> cont 30;
	T.Keyword    _ "let" -> cont 31;
	T.Keyword    _ "and" -> cont 32;
	T.Keyword    _ "fun" -> cont 33;
	T.Keyword    _ "in" -> cont 34;
	T.Keyword    _ "type" -> cont 35;
	T.Keyword    _ "do" -> cont 36;
	T.Keyword    _ "integer" -> cont 37;
	T.Infix      _ "=" -> cont 38;
	T.Infix      _ "->" -> cont 39;
	T.Infix      _ ";" -> cont 40;
	T.Infix      _ "," -> cont 41;
	T.Infix      _ ":" -> cont 42;
	T.Infix      _ "::" -> cont 43;
	T.OutfixL    _ "(" -> cont 44;
	T.OutfixR    _ ")" -> cont 45;
	T.OutfixL    _ "[" -> cont 46;
	T.OutfixR    _ "]" -> cont 47;
	T.OutfixL    _ "{" -> cont 48;
	T.OutfixR    _ "}" -> cont 49;
	T.Postfix    _ "[" -> cont 50;
	T.Postfix    _ "." -> cont 51;
	T.Infix      _ happy_dollar_dollar -> cont 52;
	T.Bitfield   _ happy_dollar_dollar -> cont 53;
	T.String     _ happy_dollar_dollar -> cont 54;
	T.Integer    _ happy_dollar_dollar -> cont 55;
	T.Identifier _ happy_dollar_dollar -> cont 56;
	_ -> happyError' (tk:tks)
	}

happyError_ 57 tk tks = happyError' tks
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

bitsOfString :: String -> [Expr MPType]
bitsOfString = (map (\b -> Bit b (Just bit))) . (map (/='0'))

-- 'FIXME: Insert the mt argument correctly
uncurryFunction :: [(Name, MPType)] -> MPType -> Expr MPType -> Expr MPType
uncurryFunction [(name, annot)] mt e    = 
  Function name annot e Nothing
uncurryFunction ((name, annot):as) mt e = 
  Function name annot (uncurryFunction as mt e) Nothing
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
