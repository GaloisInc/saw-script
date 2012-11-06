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
 happyReduce_58,
 happyReduce_59,
 happyReduce_60 :: () => ({-HappyReduction (HappyIdentity) = -}
	   Int 
	-> (T.Token AlexPosn)
	-> HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)
	-> [HappyState (T.Token AlexPosn) (HappyStk HappyAbsSyn -> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(T.Token AlexPosn)] -> (HappyIdentity) HappyAbsSyn)

action_0 (26) = happyShift action_4
action_0 (28) = happyShift action_2
action_0 (32) = happyShift action_5
action_0 (52) = happyShift action_6
action_0 (4) = happyGoto action_3
action_0 _ = happyFail

action_1 (28) = happyShift action_2
action_1 _ = happyFail

action_2 (52) = happyShift action_28
action_2 (5) = happyGoto action_26
action_2 (14) = happyGoto action_27
action_2 _ = happyFail

action_3 (53) = happyAccept
action_3 _ = happyFail

action_4 (52) = happyShift action_25
action_4 (6) = happyGoto action_24
action_4 _ = happyFail

action_5 (52) = happyShift action_23
action_5 _ = happyFail

action_6 (28) = happyShift action_12
action_6 (30) = happyShift action_13
action_6 (33) = happyShift action_14
action_6 (40) = happyShift action_15
action_6 (41) = happyShift action_16
action_6 (43) = happyShift action_17
action_6 (45) = happyShift action_18
action_6 (49) = happyShift action_19
action_6 (50) = happyShift action_20
action_6 (51) = happyShift action_21
action_6 (52) = happyShift action_22
action_6 (8) = happyGoto action_7
action_6 (9) = happyGoto action_8
action_6 (10) = happyGoto action_9
action_6 (18) = happyGoto action_10
action_6 (19) = happyGoto action_11
action_6 _ = happyReduce_45

action_7 _ = happyReduce_47

action_8 _ = happyReduce_13

action_9 (28) = happyShift action_12
action_9 (30) = happyShift action_13
action_9 (33) = happyShift action_14
action_9 (41) = happyShift action_16
action_9 (43) = happyShift action_17
action_9 (45) = happyShift action_18
action_9 (47) = happyShift action_62
action_9 (48) = happyShift action_63
action_9 (49) = happyShift action_19
action_9 (50) = happyShift action_20
action_9 (51) = happyShift action_21
action_9 (52) = happyShift action_22
action_9 (8) = happyGoto action_7
action_9 (9) = happyGoto action_8
action_9 (10) = happyGoto action_9
action_9 (19) = happyGoto action_61
action_9 _ = happyReduce_14

action_10 _ = happyReduce_3

action_11 _ = happyReduce_46

action_12 (52) = happyShift action_28
action_12 (5) = happyGoto action_26
action_12 (14) = happyGoto action_60
action_12 _ = happyFail

action_13 (41) = happyShift action_32
action_13 (52) = happyShift action_33
action_13 (7) = happyGoto action_29
action_13 (15) = happyGoto action_59
action_13 (16) = happyGoto action_31
action_13 _ = happyReduce_39

action_14 (45) = happyShift action_58
action_14 _ = happyFail

action_15 (34) = happyShift action_54
action_15 (43) = happyShift action_55
action_15 (47) = happyShift action_56
action_15 (52) = happyShift action_57
action_15 (12) = happyGoto action_53
action_15 _ = happyFail

action_16 (28) = happyShift action_12
action_16 (30) = happyShift action_13
action_16 (33) = happyShift action_14
action_16 (41) = happyShift action_16
action_16 (43) = happyShift action_17
action_16 (45) = happyShift action_18
action_16 (49) = happyShift action_19
action_16 (50) = happyShift action_20
action_16 (51) = happyShift action_21
action_16 (52) = happyShift action_22
action_16 (8) = happyGoto action_52
action_16 (9) = happyGoto action_8
action_16 (10) = happyGoto action_49
action_16 _ = happyFail

action_17 (28) = happyShift action_12
action_17 (30) = happyShift action_13
action_17 (33) = happyShift action_14
action_17 (41) = happyShift action_16
action_17 (43) = happyShift action_17
action_17 (45) = happyShift action_18
action_17 (49) = happyShift action_19
action_17 (50) = happyShift action_20
action_17 (51) = happyShift action_21
action_17 (52) = happyShift action_22
action_17 (8) = happyGoto action_48
action_17 (9) = happyGoto action_8
action_17 (10) = happyGoto action_49
action_17 (20) = happyGoto action_50
action_17 (21) = happyGoto action_51
action_17 _ = happyReduce_49

action_18 (50) = happyShift action_46
action_18 (52) = happyShift action_47
action_18 (11) = happyGoto action_43
action_18 (22) = happyGoto action_44
action_18 (23) = happyGoto action_45
action_18 _ = happyReduce_53

action_19 (39) = happyShift action_39
action_19 (13) = happyGoto action_42
action_19 _ = happyReduce_35

action_20 (39) = happyShift action_39
action_20 (13) = happyGoto action_41
action_20 _ = happyReduce_35

action_21 (39) = happyShift action_39
action_21 (13) = happyGoto action_40
action_21 _ = happyReduce_35

action_22 (39) = happyShift action_39
action_22 (13) = happyGoto action_38
action_22 _ = happyReduce_35

action_23 (35) = happyShift action_37
action_23 _ = happyFail

action_24 _ = happyReduce_5

action_25 (27) = happyShift action_35
action_25 (41) = happyShift action_36
action_25 _ = happyReduce_7

action_26 (29) = happyShift action_34
action_26 _ = happyReduce_37

action_27 _ = happyReduce_1

action_28 (41) = happyShift action_32
action_28 (52) = happyShift action_33
action_28 (7) = happyGoto action_29
action_28 (15) = happyGoto action_30
action_28 (16) = happyGoto action_31
action_28 _ = happyReduce_39

action_29 (41) = happyShift action_32
action_29 (52) = happyShift action_33
action_29 (7) = happyGoto action_29
action_29 (16) = happyGoto action_90
action_29 _ = happyReduce_41

action_30 (39) = happyShift action_39
action_30 (13) = happyGoto action_89
action_30 _ = happyReduce_35

action_31 _ = happyReduce_40

action_32 (52) = happyShift action_88
action_32 _ = happyFail

action_33 _ = happyReduce_11

action_34 (52) = happyShift action_28
action_34 (5) = happyGoto action_26
action_34 (14) = happyGoto action_87
action_34 _ = happyFail

action_35 (52) = happyShift action_86
action_35 _ = happyFail

action_36 (52) = happyShift action_85
action_36 (24) = happyGoto action_83
action_36 (25) = happyGoto action_84
action_36 _ = happyReduce_57

action_37 (34) = happyShift action_54
action_37 (43) = happyShift action_55
action_37 (47) = happyShift action_56
action_37 (52) = happyShift action_57
action_37 (12) = happyGoto action_82
action_37 _ = happyFail

action_38 _ = happyReduce_20

action_39 (34) = happyShift action_54
action_39 (43) = happyShift action_55
action_39 (47) = happyShift action_56
action_39 (52) = happyShift action_57
action_39 (12) = happyGoto action_81
action_39 _ = happyFail

action_40 _ = happyReduce_19

action_41 _ = happyReduce_18

action_42 _ = happyReduce_17

action_43 (38) = happyShift action_80
action_43 _ = happyReduce_55

action_44 (46) = happyShift action_79
action_44 _ = happyFail

action_45 _ = happyReduce_54

action_46 (39) = happyShift action_78
action_46 _ = happyFail

action_47 (39) = happyShift action_77
action_47 _ = happyFail

action_48 (38) = happyShift action_76
action_48 _ = happyReduce_51

action_49 (47) = happyShift action_62
action_49 (48) = happyShift action_63
action_49 _ = happyReduce_14

action_50 (44) = happyShift action_75
action_50 _ = happyFail

action_51 _ = happyReduce_50

action_52 (42) = happyShift action_74
action_52 _ = happyFail

action_53 _ = happyReduce_2

action_54 _ = happyReduce_29

action_55 (34) = happyShift action_54
action_55 (43) = happyShift action_55
action_55 (47) = happyShift action_56
action_55 (51) = happyShift action_73
action_55 (52) = happyShift action_57
action_55 (12) = happyGoto action_72
action_55 _ = happyFail

action_56 (34) = happyShift action_54
action_56 (43) = happyShift action_55
action_56 (47) = happyShift action_56
action_56 (51) = happyShift action_71
action_56 (52) = happyShift action_57
action_56 (12) = happyGoto action_70
action_56 _ = happyFail

action_57 _ = happyReduce_30

action_58 (26) = happyShift action_4
action_58 (28) = happyShift action_2
action_58 (32) = happyShift action_5
action_58 (52) = happyShift action_6
action_58 (4) = happyGoto action_68
action_58 (17) = happyGoto action_69
action_58 _ = happyReduce_43

action_59 (39) = happyShift action_39
action_59 (13) = happyGoto action_67
action_59 _ = happyReduce_35

action_60 (31) = happyShift action_66
action_60 _ = happyFail

action_61 _ = happyReduce_48

action_62 (28) = happyShift action_12
action_62 (30) = happyShift action_13
action_62 (33) = happyShift action_14
action_62 (41) = happyShift action_16
action_62 (43) = happyShift action_17
action_62 (45) = happyShift action_18
action_62 (49) = happyShift action_19
action_62 (50) = happyShift action_20
action_62 (51) = happyShift action_21
action_62 (52) = happyShift action_22
action_62 (8) = happyGoto action_65
action_62 (9) = happyGoto action_8
action_62 (10) = happyGoto action_49
action_62 _ = happyFail

action_63 (52) = happyShift action_64
action_63 _ = happyFail

action_64 (39) = happyShift action_39
action_64 (13) = happyGoto action_111
action_64 _ = happyReduce_35

action_65 (44) = happyShift action_110
action_65 _ = happyFail

action_66 (28) = happyShift action_12
action_66 (30) = happyShift action_13
action_66 (33) = happyShift action_14
action_66 (41) = happyShift action_16
action_66 (43) = happyShift action_17
action_66 (45) = happyShift action_18
action_66 (49) = happyShift action_19
action_66 (50) = happyShift action_20
action_66 (51) = happyShift action_21
action_66 (52) = happyShift action_22
action_66 (8) = happyGoto action_109
action_66 (9) = happyGoto action_8
action_66 (10) = happyGoto action_49
action_66 _ = happyFail

action_67 (36) = happyShift action_108
action_67 _ = happyFail

action_68 (37) = happyShift action_107
action_68 _ = happyFail

action_69 (46) = happyShift action_106
action_69 _ = happyFail

action_70 (44) = happyShift action_105
action_70 _ = happyFail

action_71 (44) = happyShift action_104
action_71 _ = happyFail

action_72 (44) = happyShift action_103
action_72 _ = happyFail

action_73 (44) = happyShift action_102
action_73 _ = happyFail

action_74 (39) = happyShift action_39
action_74 (13) = happyGoto action_101
action_74 _ = happyReduce_35

action_75 (39) = happyShift action_39
action_75 (13) = happyGoto action_100
action_75 _ = happyReduce_35

action_76 (28) = happyShift action_12
action_76 (30) = happyShift action_13
action_76 (33) = happyShift action_14
action_76 (41) = happyShift action_16
action_76 (43) = happyShift action_17
action_76 (45) = happyShift action_18
action_76 (49) = happyShift action_19
action_76 (50) = happyShift action_20
action_76 (51) = happyShift action_21
action_76 (52) = happyShift action_22
action_76 (8) = happyGoto action_48
action_76 (9) = happyGoto action_8
action_76 (10) = happyGoto action_49
action_76 (21) = happyGoto action_99
action_76 _ = happyFail

action_77 (28) = happyShift action_12
action_77 (30) = happyShift action_13
action_77 (33) = happyShift action_14
action_77 (41) = happyShift action_16
action_77 (43) = happyShift action_17
action_77 (45) = happyShift action_18
action_77 (49) = happyShift action_19
action_77 (50) = happyShift action_20
action_77 (51) = happyShift action_21
action_77 (52) = happyShift action_22
action_77 (8) = happyGoto action_98
action_77 (9) = happyGoto action_8
action_77 (10) = happyGoto action_49
action_77 _ = happyFail

action_78 (28) = happyShift action_12
action_78 (30) = happyShift action_13
action_78 (33) = happyShift action_14
action_78 (41) = happyShift action_16
action_78 (43) = happyShift action_17
action_78 (45) = happyShift action_18
action_78 (49) = happyShift action_19
action_78 (50) = happyShift action_20
action_78 (51) = happyShift action_21
action_78 (52) = happyShift action_22
action_78 (8) = happyGoto action_97
action_78 (9) = happyGoto action_8
action_78 (10) = happyGoto action_49
action_78 _ = happyFail

action_79 (39) = happyShift action_39
action_79 (13) = happyGoto action_96
action_79 _ = happyReduce_35

action_80 (50) = happyShift action_46
action_80 (52) = happyShift action_47
action_80 (11) = happyGoto action_43
action_80 (23) = happyGoto action_95
action_80 _ = happyFail

action_81 _ = happyReduce_36

action_82 _ = happyReduce_4

action_83 (42) = happyShift action_94
action_83 _ = happyFail

action_84 _ = happyReduce_58

action_85 (38) = happyShift action_93
action_85 _ = happyReduce_59

action_86 _ = happyReduce_9

action_87 _ = happyReduce_38

action_88 (39) = happyShift action_92
action_88 _ = happyFail

action_89 (35) = happyShift action_91
action_89 _ = happyFail

action_90 _ = happyReduce_42

action_91 (28) = happyShift action_12
action_91 (30) = happyShift action_13
action_91 (33) = happyShift action_14
action_91 (41) = happyShift action_16
action_91 (43) = happyShift action_17
action_91 (45) = happyShift action_18
action_91 (49) = happyShift action_19
action_91 (50) = happyShift action_20
action_91 (51) = happyShift action_21
action_91 (52) = happyShift action_22
action_91 (8) = happyGoto action_118
action_91 (9) = happyGoto action_8
action_91 (10) = happyGoto action_49
action_91 _ = happyFail

action_92 (34) = happyShift action_54
action_92 (43) = happyShift action_55
action_92 (47) = happyShift action_56
action_92 (52) = happyShift action_57
action_92 (12) = happyGoto action_117
action_92 _ = happyFail

action_93 (52) = happyShift action_85
action_93 (25) = happyGoto action_116
action_93 _ = happyFail

action_94 (27) = happyShift action_115
action_94 _ = happyReduce_8

action_95 _ = happyReduce_56

action_96 _ = happyReduce_21

action_97 _ = happyReduce_28

action_98 _ = happyReduce_27

action_99 _ = happyReduce_52

action_100 _ = happyReduce_23

action_101 _ = happyReduce_22

action_102 _ = happyReduce_32

action_103 _ = happyReduce_34

action_104 _ = happyReduce_31

action_105 _ = happyReduce_33

action_106 _ = happyReduce_24

action_107 (26) = happyShift action_4
action_107 (28) = happyShift action_2
action_107 (32) = happyShift action_5
action_107 (52) = happyShift action_6
action_107 (4) = happyGoto action_68
action_107 (17) = happyGoto action_114
action_107 _ = happyReduce_43

action_108 (28) = happyShift action_12
action_108 (30) = happyShift action_13
action_108 (33) = happyShift action_14
action_108 (41) = happyShift action_16
action_108 (43) = happyShift action_17
action_108 (45) = happyShift action_18
action_108 (49) = happyShift action_19
action_108 (50) = happyShift action_20
action_108 (51) = happyShift action_21
action_108 (52) = happyShift action_22
action_108 (8) = happyGoto action_113
action_108 (9) = happyGoto action_8
action_108 (10) = happyGoto action_49
action_108 _ = happyFail

action_109 _ = happyReduce_16

action_110 (39) = happyShift action_39
action_110 (13) = happyGoto action_112
action_110 _ = happyReduce_35

action_111 _ = happyReduce_25

action_112 _ = happyReduce_26

action_113 _ = happyReduce_15

action_114 _ = happyReduce_44

action_115 (52) = happyShift action_120
action_115 _ = happyFail

action_116 _ = happyReduce_60

action_117 (42) = happyShift action_119
action_117 _ = happyFail

action_118 _ = happyReduce_6

action_119 _ = happyReduce_12

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

happyReduce_3 = happySpecReduce_2  4 happyReduction_3
happyReduction_3 (HappyAbsSyn18  happy_var_2)
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn4
		 (Command happy_var_1 happy_var_2
	)
happyReduction_3 _ _  = notHappyAtAll 

happyReduce_4 = happyReduce 4 4 happyReduction_4
happyReduction_4 ((HappyAbsSyn12  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_2)) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Typedef happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_5 = happySpecReduce_2  4 happyReduction_5
happyReduction_5 (HappyAbsSyn4  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (happy_var_2
	)
happyReduction_5 _ _  = notHappyAtAll 

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

happyReduce_15 = happyReduce 5 9 happyReduction_15
happyReduction_15 ((HappyAbsSyn8  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn13  happy_var_3) `HappyStk`
	(HappyAbsSyn15  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Function happy_var_2 happy_var_5 happy_var_3
	) `HappyStk` happyRest

happyReduce_16 = happyReduce 4 9 happyReduction_16
happyReduction_16 ((HappyAbsSyn8  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn14  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (LetBlock happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_17 = happySpecReduce_2  10 happyReduction_17
happyReduction_17 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (T.Bitfield   _ happy_var_1))
	 =  HappyAbsSyn8
		 (Bitfield (bitsOfString happy_var_1) happy_var_2
	)
happyReduction_17 _ _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_2  10 happyReduction_18
happyReduction_18 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (T.String     _ happy_var_1))
	 =  HappyAbsSyn8
		 (Quote happy_var_1 happy_var_2
	)
happyReduction_18 _ _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_2  10 happyReduction_19
happyReduction_19 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (T.Integer    _ happy_var_1))
	 =  HappyAbsSyn8
		 (Z (read happy_var_1) happy_var_2
	)
happyReduction_19 _ _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_2  10 happyReduction_20
happyReduction_20 (HappyAbsSyn13  happy_var_2)
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn8
		 (Var happy_var_1 happy_var_2
	)
happyReduction_20 _ _  = notHappyAtAll 

happyReduce_21 = happyReduce 4 10 happyReduction_21
happyReduction_21 ((HappyAbsSyn13  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn22  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Record happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_22 = happyReduce 4 10 happyReduction_22
happyReduction_22 (_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (happy_var_2
	) `HappyStk` happyRest

happyReduce_23 = happyReduce 4 10 happyReduction_23
happyReduction_23 ((HappyAbsSyn13  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn18  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Array happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_24 = happyReduce 4 10 happyReduction_24
happyReduction_24 (_ `HappyStk`
	(HappyAbsSyn17  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Procedure happy_var_3 Nothing
	) `HappyStk` happyRest

happyReduce_25 = happyReduce 4 10 happyReduction_25
happyReduction_25 ((HappyAbsSyn13  happy_var_4) `HappyStk`
	(HappyTerminal (T.Identifier _ happy_var_3)) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Lookup happy_var_1 happy_var_3 happy_var_4
	) `HappyStk` happyRest

happyReduce_26 = happyReduce 5 10 happyReduction_26
happyReduction_26 ((HappyAbsSyn13  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn8  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn8
		 (Index happy_var_1 happy_var_3 happy_var_5
	) `HappyStk` happyRest

happyReduce_27 = happySpecReduce_3  11 happyReduction_27
happyReduction_27 (HappyAbsSyn8  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn11
		 ((happy_var_1, happy_var_3)
	)
happyReduction_27 _ _ _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_3  11 happyReduction_28
happyReduction_28 (HappyAbsSyn8  happy_var_3)
	_
	(HappyTerminal (T.String     _ happy_var_1))
	 =  HappyAbsSyn11
		 ((happy_var_1, happy_var_3)
	)
happyReduction_28 _ _ _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_1  12 happyReduction_29
happyReduction_29 _
	 =  HappyAbsSyn12
		 (Z'
	)

happyReduce_30 = happySpecReduce_1  12 happyReduction_30
happyReduction_30 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn12
		 (Var' happy_var_1
	)
happyReduction_30 _  = notHappyAtAll 

happyReduce_31 = happySpecReduce_3  12 happyReduction_31
happyReduction_31 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn12
		 (Bitfield' (read happy_var_2)
	)
happyReduction_31 _ _ _  = notHappyAtAll 

happyReduce_32 = happySpecReduce_3  12 happyReduction_32
happyReduction_32 _
	(HappyTerminal (T.Integer    _ happy_var_2))
	_
	 =  HappyAbsSyn12
		 (Bitfield' (read happy_var_2)
	)
happyReduction_32 _ _ _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_3  12 happyReduction_33
happyReduction_33 _
	(HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (Array' happy_var_2 Nothing
	)
happyReduction_33 _ _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_3  12 happyReduction_34
happyReduction_34 _
	(HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn12
		 (Array' happy_var_2 Nothing
	)
happyReduction_34 _ _ _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_0  13 happyReduction_35
happyReduction_35  =  HappyAbsSyn13
		 (Nothing
	)

happyReduce_36 = happySpecReduce_2  13 happyReduction_36
happyReduction_36 (HappyAbsSyn12  happy_var_2)
	_
	 =  HappyAbsSyn13
		 (Just happy_var_2
	)
happyReduction_36 _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_1  14 happyReduction_37
happyReduction_37 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn14
		 ([happy_var_1]
	)
happyReduction_37 _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_3  14 happyReduction_38
happyReduction_38 (HappyAbsSyn14  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_1:happy_var_3
	)
happyReduction_38 _ _ _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_0  15 happyReduction_39
happyReduction_39  =  HappyAbsSyn15
		 ([]
	)

happyReduce_40 = happySpecReduce_1  15 happyReduction_40
happyReduction_40 (HappyAbsSyn15  happy_var_1)
	 =  HappyAbsSyn15
		 (happy_var_1
	)
happyReduction_40 _  = notHappyAtAll 

happyReduce_41 = happySpecReduce_1  16 happyReduction_41
happyReduction_41 (HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn15
		 ([happy_var_1]
	)
happyReduction_41 _  = notHappyAtAll 

happyReduce_42 = happySpecReduce_2  16 happyReduction_42
happyReduction_42 (HappyAbsSyn15  happy_var_2)
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn15
		 (happy_var_1:happy_var_2
	)
happyReduction_42 _ _  = notHappyAtAll 

happyReduce_43 = happySpecReduce_0  17 happyReduction_43
happyReduction_43  =  HappyAbsSyn17
		 ([]
	)

happyReduce_44 = happySpecReduce_3  17 happyReduction_44
happyReduction_44 (HappyAbsSyn17  happy_var_3)
	_
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn17
		 (happy_var_1:happy_var_3
	)
happyReduction_44 _ _ _  = notHappyAtAll 

happyReduce_45 = happySpecReduce_0  18 happyReduction_45
happyReduction_45  =  HappyAbsSyn18
		 ([]
	)

happyReduce_46 = happySpecReduce_1  18 happyReduction_46
happyReduction_46 (HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1
	)
happyReduction_46 _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_1  19 happyReduction_47
happyReduction_47 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn18
		 ([happy_var_1]
	)
happyReduction_47 _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_2  19 happyReduction_48
happyReduction_48 (HappyAbsSyn18  happy_var_2)
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1:happy_var_2
	)
happyReduction_48 _ _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_0  20 happyReduction_49
happyReduction_49  =  HappyAbsSyn18
		 ([]
	)

happyReduce_50 = happySpecReduce_1  20 happyReduction_50
happyReduction_50 (HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1
	)
happyReduction_50 _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_1  21 happyReduction_51
happyReduction_51 (HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn18
		 ([happy_var_1]
	)
happyReduction_51 _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_3  21 happyReduction_52
happyReduction_52 (HappyAbsSyn18  happy_var_3)
	_
	(HappyAbsSyn8  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1:happy_var_3
	)
happyReduction_52 _ _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_0  22 happyReduction_53
happyReduction_53  =  HappyAbsSyn22
		 ([]
	)

happyReduce_54 = happySpecReduce_1  22 happyReduction_54
happyReduction_54 (HappyAbsSyn22  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1
	)
happyReduction_54 _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_1  23 happyReduction_55
happyReduction_55 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn22
		 ([happy_var_1]
	)
happyReduction_55 _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_3  23 happyReduction_56
happyReduction_56 (HappyAbsSyn22  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn22
		 (happy_var_1:happy_var_3
	)
happyReduction_56 _ _ _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_0  24 happyReduction_57
happyReduction_57  =  HappyAbsSyn24
		 ([]
	)

happyReduce_58 = happySpecReduce_1  24 happyReduction_58
happyReduction_58 (HappyAbsSyn24  happy_var_1)
	 =  HappyAbsSyn24
		 (happy_var_1
	)
happyReduction_58 _  = notHappyAtAll 

happyReduce_59 = happySpecReduce_1  25 happyReduction_59
happyReduction_59 (HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn24
		 ([happy_var_1]
	)
happyReduction_59 _  = notHappyAtAll 

happyReduce_60 = happySpecReduce_3  25 happyReduction_60
happyReduction_60 (HappyAbsSyn24  happy_var_3)
	_
	(HappyTerminal (T.Identifier _ happy_var_1))
	 =  HappyAbsSyn24
		 (happy_var_1:happy_var_3
	)
happyReduction_60 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 53 53 notHappyAtAll (HappyState action) sts stk []

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
	T.Bitfield   _ happy_dollar_dollar -> cont 49;
	T.String     _ happy_dollar_dollar -> cont 50;
	T.Integer    _ happy_dollar_dollar -> cont 51;
	T.Identifier _ happy_dollar_dollar -> cont 52;
	_ -> happyError' (tk:tks)
	}

happyError_ 53 tk tks = happyError' tks
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
