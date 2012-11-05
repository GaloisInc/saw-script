{-# OPTIONS_GHC -w #-}
module SAWScript.Parser where

import qualified SAWScript.Token as T
import SAWScript.Lexer
import SAWScript.AST

-- parser produced by Happy Version 1.18.9

data HappyAbsSyn t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20 t21 t22 t23 t24 t25 t26
	= HappyTerminal (T.Token AlexPosn)
	| HappyErrorToken Int
	| HappyAbsSyn4 t4
	| HappyAbsSyn5 t5
	| HappyAbsSyn6 t6
	| HappyAbsSyn7 t7
	| HappyAbsSyn8 t8
	| HappyAbsSyn9 t9
	| HappyAbsSyn10 t10
	| HappyAbsSyn11 t11
	| HappyAbsSyn12 t12
	| HappyAbsSyn13 t13
	| HappyAbsSyn14 t14
	| HappyAbsSyn15 t15
	| HappyAbsSyn16 t16
	| HappyAbsSyn17 t17
	| HappyAbsSyn18 t18
	| HappyAbsSyn19 t19
	| HappyAbsSyn20 t20
	| HappyAbsSyn21 t21
	| HappyAbsSyn22 t22
	| HappyAbsSyn23 t23
	| HappyAbsSyn24 t24
	| HappyAbsSyn25 t25
	| HappyAbsSyn26 t26

action_0 (27) = happyShift action_4
action_0 (29) = happyShift action_2
action_0 (33) = happyShift action_5
action_0 (53) = happyShift action_6
action_0 (4) = happyGoto action_3
action_0 _ = happyFail

action_1 (29) = happyShift action_2
action_1 _ = happyFail

action_2 (53) = happyShift action_26
action_2 (5) = happyGoto action_24
action_2 (6) = happyGoto action_25
action_2 _ = happyFail

action_3 (54) = happyAccept
action_3 _ = happyFail

action_4 (53) = happyShift action_23
action_4 (10) = happyGoto action_22
action_4 _ = happyFail

action_5 (53) = happyShift action_21
action_5 _ = happyFail

action_6 (29) = happyShift action_11
action_6 (34) = happyShift action_12
action_6 (41) = happyShift action_13
action_6 (42) = happyShift action_14
action_6 (44) = happyShift action_15
action_6 (46) = happyShift action_16
action_6 (50) = happyShift action_17
action_6 (51) = happyShift action_18
action_6 (52) = happyShift action_19
action_6 (53) = happyShift action_20
action_6 (13) = happyGoto action_7
action_6 (17) = happyGoto action_8
action_6 (18) = happyGoto action_9
action_6 (21) = happyGoto action_10
action_6 _ = happyReduce_44

action_7 (29) = happyShift action_11
action_7 (34) = happyShift action_12
action_7 (42) = happyShift action_14
action_7 (44) = happyShift action_15
action_7 (46) = happyShift action_16
action_7 (48) = happyShift action_63
action_7 (49) = happyShift action_64
action_7 (50) = happyShift action_17
action_7 (51) = happyShift action_18
action_7 (52) = happyShift action_19
action_7 (53) = happyShift action_20
action_7 (13) = happyGoto action_7
action_7 (18) = happyGoto action_62
action_7 (21) = happyGoto action_10
action_7 _ = happyFail

action_8 _ = happyReduce_3

action_9 _ = happyReduce_45

action_10 (40) = happyShift action_37
action_10 (16) = happyGoto action_61
action_10 _ = happyReduce_42

action_11 (42) = happyShift action_30
action_11 (53) = happyShift action_31
action_11 (7) = happyGoto action_27
action_11 (8) = happyGoto action_60
action_11 (9) = happyGoto action_29
action_11 _ = happyReduce_11

action_12 (46) = happyShift action_59
action_12 _ = happyFail

action_13 (35) = happyShift action_55
action_13 (44) = happyShift action_56
action_13 (48) = happyShift action_57
action_13 (53) = happyShift action_58
action_13 (15) = happyGoto action_54
action_13 _ = happyFail

action_14 (29) = happyShift action_51
action_14 (31) = happyShift action_52
action_14 (34) = happyShift action_12
action_14 (42) = happyShift action_14
action_14 (44) = happyShift action_15
action_14 (46) = happyShift action_16
action_14 (50) = happyShift action_17
action_14 (51) = happyShift action_18
action_14 (52) = happyShift action_19
action_14 (53) = happyShift action_20
action_14 (11) = happyGoto action_53
action_14 (12) = happyGoto action_47
action_14 (13) = happyGoto action_48
action_14 (21) = happyGoto action_10
action_14 _ = happyFail

action_15 (29) = happyShift action_51
action_15 (31) = happyShift action_52
action_15 (34) = happyShift action_12
action_15 (42) = happyShift action_14
action_15 (44) = happyShift action_15
action_15 (46) = happyShift action_16
action_15 (50) = happyShift action_17
action_15 (51) = happyShift action_18
action_15 (52) = happyShift action_19
action_15 (53) = happyShift action_20
action_15 (11) = happyGoto action_46
action_15 (12) = happyGoto action_47
action_15 (13) = happyGoto action_48
action_15 (19) = happyGoto action_49
action_15 (20) = happyGoto action_50
action_15 (21) = happyGoto action_10
action_15 _ = happyReduce_48

action_16 (51) = happyShift action_44
action_16 (53) = happyShift action_45
action_16 (22) = happyGoto action_41
action_16 (23) = happyGoto action_42
action_16 (24) = happyGoto action_43
action_16 _ = happyReduce_55

action_17 (40) = happyShift action_37
action_17 (16) = happyGoto action_40
action_17 _ = happyReduce_42

action_18 (40) = happyShift action_37
action_18 (16) = happyGoto action_39
action_18 _ = happyReduce_42

action_19 (40) = happyShift action_37
action_19 (16) = happyGoto action_38
action_19 _ = happyReduce_42

action_20 (40) = happyShift action_37
action_20 (16) = happyGoto action_36
action_20 _ = happyReduce_42

action_21 (36) = happyShift action_35
action_21 _ = happyFail

action_22 _ = happyReduce_5

action_23 (28) = happyShift action_33
action_23 (42) = happyShift action_34
action_23 _ = happyReduce_15

action_24 (30) = happyShift action_32
action_24 _ = happyReduce_7

action_25 _ = happyReduce_1

action_26 (42) = happyShift action_30
action_26 (53) = happyShift action_31
action_26 (7) = happyGoto action_27
action_26 (8) = happyGoto action_28
action_26 (9) = happyGoto action_29
action_26 _ = happyReduce_11

action_27 (42) = happyShift action_30
action_27 (53) = happyShift action_31
action_27 (7) = happyGoto action_27
action_27 (9) = happyGoto action_93
action_27 _ = happyReduce_13

action_28 (40) = happyShift action_37
action_28 (16) = happyGoto action_92
action_28 _ = happyReduce_42

action_29 _ = happyReduce_12

action_30 (53) = happyShift action_91
action_30 _ = happyFail

action_31 _ = happyReduce_9

action_32 (53) = happyShift action_26
action_32 (5) = happyGoto action_24
action_32 (6) = happyGoto action_90
action_32 _ = happyFail

action_33 (53) = happyShift action_89
action_33 _ = happyFail

action_34 (53) = happyShift action_88
action_34 (25) = happyGoto action_86
action_34 (26) = happyGoto action_87
action_34 _ = happyReduce_59

action_35 (35) = happyShift action_55
action_35 (44) = happyShift action_56
action_35 (48) = happyShift action_57
action_35 (53) = happyShift action_58
action_35 (15) = happyGoto action_85
action_35 _ = happyFail

action_36 _ = happyReduce_27

action_37 (35) = happyShift action_55
action_37 (44) = happyShift action_56
action_37 (48) = happyShift action_57
action_37 (53) = happyShift action_58
action_37 (15) = happyGoto action_84
action_37 _ = happyFail

action_38 _ = happyReduce_26

action_39 _ = happyReduce_25

action_40 _ = happyReduce_24

action_41 (39) = happyShift action_83
action_41 _ = happyReduce_57

action_42 (47) = happyShift action_82
action_42 _ = happyFail

action_43 _ = happyReduce_56

action_44 (40) = happyShift action_81
action_44 _ = happyFail

action_45 (40) = happyShift action_80
action_45 _ = happyFail

action_46 (39) = happyShift action_79
action_46 _ = happyReduce_50

action_47 _ = happyReduce_19

action_48 (29) = happyShift action_11
action_48 (34) = happyShift action_12
action_48 (42) = happyShift action_14
action_48 (44) = happyShift action_15
action_48 (46) = happyShift action_16
action_48 (48) = happyShift action_63
action_48 (49) = happyShift action_64
action_48 (50) = happyShift action_17
action_48 (51) = happyShift action_18
action_48 (52) = happyShift action_19
action_48 (53) = happyShift action_20
action_48 (13) = happyGoto action_7
action_48 (18) = happyGoto action_78
action_48 (21) = happyGoto action_10
action_48 _ = happyReduce_20

action_49 (45) = happyShift action_77
action_49 _ = happyFail

action_50 _ = happyReduce_49

action_51 (53) = happyShift action_26
action_51 (5) = happyGoto action_24
action_51 (6) = happyGoto action_76
action_51 _ = happyFail

action_52 (42) = happyShift action_30
action_52 (53) = happyShift action_31
action_52 (7) = happyGoto action_27
action_52 (8) = happyGoto action_75
action_52 (9) = happyGoto action_29
action_52 _ = happyReduce_11

action_53 (43) = happyShift action_74
action_53 _ = happyFail

action_54 _ = happyReduce_2

action_55 _ = happyReduce_36

action_56 (35) = happyShift action_55
action_56 (44) = happyShift action_56
action_56 (48) = happyShift action_57
action_56 (52) = happyShift action_73
action_56 (53) = happyShift action_58
action_56 (15) = happyGoto action_72
action_56 _ = happyFail

action_57 (35) = happyShift action_55
action_57 (44) = happyShift action_56
action_57 (48) = happyShift action_57
action_57 (52) = happyShift action_71
action_57 (53) = happyShift action_58
action_57 (15) = happyGoto action_70
action_57 _ = happyFail

action_58 _ = happyReduce_37

action_59 (27) = happyShift action_4
action_59 (29) = happyShift action_2
action_59 (33) = happyShift action_5
action_59 (53) = happyShift action_6
action_59 (4) = happyGoto action_68
action_59 (14) = happyGoto action_69
action_59 _ = happyReduce_34

action_60 (40) = happyShift action_37
action_60 (16) = happyGoto action_67
action_60 _ = happyReduce_42

action_61 _ = happyReduce_28

action_62 _ = happyReduce_47

action_63 (29) = happyShift action_51
action_63 (31) = happyShift action_52
action_63 (34) = happyShift action_12
action_63 (42) = happyShift action_14
action_63 (44) = happyShift action_15
action_63 (46) = happyShift action_16
action_63 (50) = happyShift action_17
action_63 (51) = happyShift action_18
action_63 (52) = happyShift action_19
action_63 (53) = happyShift action_20
action_63 (11) = happyGoto action_66
action_63 (12) = happyGoto action_47
action_63 (13) = happyGoto action_48
action_63 (21) = happyGoto action_10
action_63 _ = happyFail

action_64 (53) = happyShift action_65
action_64 _ = happyFail

action_65 _ = happyReduce_32

action_66 (45) = happyShift action_112
action_66 _ = happyFail

action_67 (37) = happyShift action_111
action_67 _ = happyFail

action_68 (38) = happyShift action_110
action_68 _ = happyFail

action_69 (47) = happyShift action_109
action_69 _ = happyFail

action_70 (45) = happyShift action_108
action_70 _ = happyFail

action_71 (45) = happyShift action_107
action_71 _ = happyFail

action_72 (45) = happyShift action_106
action_72 _ = happyFail

action_73 (45) = happyShift action_105
action_73 _ = happyFail

action_74 (40) = happyShift action_37
action_74 (16) = happyGoto action_104
action_74 _ = happyReduce_42

action_75 (40) = happyShift action_37
action_75 (16) = happyGoto action_103
action_75 _ = happyReduce_42

action_76 (32) = happyShift action_102
action_76 _ = happyFail

action_77 _ = happyReduce_30

action_78 _ = happyReduce_22

action_79 (29) = happyShift action_51
action_79 (31) = happyShift action_52
action_79 (34) = happyShift action_12
action_79 (42) = happyShift action_14
action_79 (44) = happyShift action_15
action_79 (46) = happyShift action_16
action_79 (50) = happyShift action_17
action_79 (51) = happyShift action_18
action_79 (52) = happyShift action_19
action_79 (53) = happyShift action_20
action_79 (11) = happyGoto action_46
action_79 (12) = happyGoto action_47
action_79 (13) = happyGoto action_48
action_79 (20) = happyGoto action_101
action_79 (21) = happyGoto action_10
action_79 _ = happyFail

action_80 (29) = happyShift action_51
action_80 (31) = happyShift action_52
action_80 (34) = happyShift action_12
action_80 (42) = happyShift action_14
action_80 (44) = happyShift action_15
action_80 (46) = happyShift action_16
action_80 (50) = happyShift action_17
action_80 (51) = happyShift action_18
action_80 (52) = happyShift action_19
action_80 (53) = happyShift action_20
action_80 (11) = happyGoto action_100
action_80 (12) = happyGoto action_47
action_80 (13) = happyGoto action_48
action_80 (21) = happyGoto action_10
action_80 _ = happyFail

action_81 (29) = happyShift action_51
action_81 (31) = happyShift action_52
action_81 (34) = happyShift action_12
action_81 (42) = happyShift action_14
action_81 (44) = happyShift action_15
action_81 (46) = happyShift action_16
action_81 (50) = happyShift action_17
action_81 (51) = happyShift action_18
action_81 (52) = happyShift action_19
action_81 (53) = happyShift action_20
action_81 (11) = happyGoto action_99
action_81 (12) = happyGoto action_47
action_81 (13) = happyGoto action_48
action_81 (21) = happyGoto action_10
action_81 _ = happyFail

action_82 _ = happyReduce_52

action_83 (51) = happyShift action_44
action_83 (53) = happyShift action_45
action_83 (22) = happyGoto action_41
action_83 (24) = happyGoto action_98
action_83 _ = happyFail

action_84 _ = happyReduce_43

action_85 _ = happyReduce_4

action_86 (43) = happyShift action_97
action_86 _ = happyFail

action_87 _ = happyReduce_60

action_88 (39) = happyShift action_96
action_88 _ = happyReduce_61

action_89 _ = happyReduce_17

action_90 _ = happyReduce_8

action_91 (40) = happyShift action_95
action_91 _ = happyFail

action_92 (36) = happyShift action_94
action_92 _ = happyFail

action_93 _ = happyReduce_14

action_94 (29) = happyShift action_51
action_94 (31) = happyShift action_52
action_94 (34) = happyShift action_12
action_94 (42) = happyShift action_14
action_94 (44) = happyShift action_15
action_94 (46) = happyShift action_16
action_94 (50) = happyShift action_17
action_94 (51) = happyShift action_18
action_94 (52) = happyShift action_19
action_94 (53) = happyShift action_20
action_94 (11) = happyGoto action_120
action_94 (12) = happyGoto action_47
action_94 (13) = happyGoto action_48
action_94 (21) = happyGoto action_10
action_94 _ = happyFail

action_95 (35) = happyShift action_55
action_95 (44) = happyShift action_56
action_95 (48) = happyShift action_57
action_95 (53) = happyShift action_58
action_95 (15) = happyGoto action_119
action_95 _ = happyFail

action_96 (53) = happyShift action_88
action_96 (26) = happyGoto action_118
action_96 _ = happyFail

action_97 (28) = happyShift action_117
action_97 _ = happyReduce_16

action_98 _ = happyReduce_58

action_99 _ = happyReduce_54

action_100 _ = happyReduce_53

action_101 _ = happyReduce_51

action_102 (29) = happyShift action_51
action_102 (31) = happyShift action_52
action_102 (34) = happyShift action_12
action_102 (42) = happyShift action_14
action_102 (44) = happyShift action_15
action_102 (46) = happyShift action_16
action_102 (50) = happyShift action_17
action_102 (51) = happyShift action_18
action_102 (52) = happyShift action_19
action_102 (53) = happyShift action_20
action_102 (11) = happyGoto action_116
action_102 (12) = happyGoto action_47
action_102 (13) = happyGoto action_48
action_102 (21) = happyGoto action_10
action_102 _ = happyFail

action_103 (37) = happyShift action_115
action_103 _ = happyFail

action_104 _ = happyReduce_29

action_105 _ = happyReduce_39

action_106 _ = happyReduce_41

action_107 _ = happyReduce_38

action_108 _ = happyReduce_40

action_109 _ = happyReduce_31

action_110 (27) = happyShift action_4
action_110 (29) = happyShift action_2
action_110 (33) = happyShift action_5
action_110 (53) = happyShift action_6
action_110 (4) = happyGoto action_68
action_110 (14) = happyGoto action_114
action_110 _ = happyReduce_34

action_111 (29) = happyShift action_51
action_111 (31) = happyShift action_52
action_111 (34) = happyShift action_12
action_111 (42) = happyShift action_14
action_111 (44) = happyShift action_15
action_111 (46) = happyShift action_16
action_111 (50) = happyShift action_17
action_111 (51) = happyShift action_18
action_111 (52) = happyShift action_19
action_111 (53) = happyShift action_20
action_111 (11) = happyGoto action_113
action_111 (12) = happyGoto action_47
action_111 (13) = happyGoto action_48
action_111 (21) = happyGoto action_10
action_111 _ = happyFail

action_112 _ = happyReduce_33

action_113 _ = happyReduce_46

action_114 _ = happyReduce_35

action_115 (29) = happyShift action_51
action_115 (31) = happyShift action_52
action_115 (34) = happyShift action_12
action_115 (42) = happyShift action_14
action_115 (44) = happyShift action_15
action_115 (46) = happyShift action_16
action_115 (50) = happyShift action_17
action_115 (51) = happyShift action_18
action_115 (52) = happyShift action_19
action_115 (53) = happyShift action_20
action_115 (11) = happyGoto action_123
action_115 (12) = happyGoto action_47
action_115 (13) = happyGoto action_48
action_115 (21) = happyGoto action_10
action_115 _ = happyFail

action_116 _ = happyReduce_23

action_117 (53) = happyShift action_122
action_117 _ = happyFail

action_118 _ = happyReduce_62

action_119 (43) = happyShift action_121
action_119 _ = happyFail

action_120 _ = happyReduce_6

action_121 _ = happyReduce_10

action_122 _ = happyReduce_18

action_123 _ = happyReduce_21

happyReduce_1 = happySpecReduce_2  4 happyReduction_1
happyReduction_1 (HappyAbsSyn6  happy_var_2)
	_
	 =  HappyAbsSyn4
		 (Declarations happy_var_2
	)
happyReduction_1 _ _  = notHappyAtAll 

happyReduce_2 = happySpecReduce_3  4 happyReduction_2
happyReduction_2 (HappyAbsSyn15  happy_var_3)
	_
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn4
		 (ForwardDecl happy_var_1 happy_var_3
	)
happyReduction_2 _ _ _  = notHappyAtAll 

happyReduce_3 = happySpecReduce_2  4 happyReduction_3
happyReduction_3 (HappyAbsSyn17  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn4
		 (Command happy_var_1 happy_var_2
	)
happyReduction_3 _ _  = notHappyAtAll 

happyReduce_4 = happyReduce 4 4 happyReduction_4
happyReduction_4 ((HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn4
		 (Typedef happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_5 = happySpecReduce_2  4 happyReduction_5
happyReduction_5 _
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn4
		 (happy_var_1
	)
happyReduction_5 _ _  = notHappyAtAll 

happyReduce_6 = happyReduce 5 5 happyReduction_6
happyReduction_6 ((HappyAbsSyn11  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn16  happy_var_3) `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn5
		 (Declaration happy_var_1 happy_var_2 happy_var_5 happy_var_3
	) `HappyStk` happyRest

happyReduce_7 = happySpecReduce_1  6 happyReduction_7
happyReduction_7 (HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn6
		 ([happy_var_1]
	)
happyReduction_7 _  = notHappyAtAll 

happyReduce_8 = happySpecReduce_3  6 happyReduction_8
happyReduction_8 (HappyAbsSyn6  happy_var_3)
	_
	(HappyAbsSyn5  happy_var_1)
	 =  HappyAbsSyn6
		 (happy_var_1:happy_var_3
	)
happyReduction_8 _ _ _  = notHappyAtAll 

happyReduce_9 = happySpecReduce_1  7 happyReduction_9
happyReduction_9 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn7
		 ((happy_var_1, Nothing)
	)
happyReduction_9 _  = notHappyAtAll 

happyReduce_10 = happyReduce 5 7 happyReduction_10
happyReduction_10 (_ `HappyStk`
	(HappyAbsSyn15  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn7
		 ((happy_var_2, Just happy_var_4)
	) `HappyStk` happyRest

happyReduce_11 = happySpecReduce_0  8 happyReduction_11
happyReduction_11  =  HappyAbsSyn8
		 ([]
	)

happyReduce_12 = happySpecReduce_1  8 happyReduction_12
happyReduction_12 (HappyAbsSyn9  happy_var_1)
	 =  HappyAbsSyn8
		 (happy_var_1
	)
happyReduction_12 _  = notHappyAtAll 

happyReduce_13 = happySpecReduce_1  9 happyReduction_13
happyReduction_13 (HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn9
		 ([happy_var_1]
	)
happyReduction_13 _  = notHappyAtAll 

happyReduce_14 = happySpecReduce_2  9 happyReduction_14
happyReduction_14 (HappyAbsSyn9  happy_var_2)
	(HappyAbsSyn7  happy_var_1)
	 =  HappyAbsSyn9
		 (happy_var_1:happy_var_2
	)
happyReduction_14 _ _  = notHappyAtAll 

happyReduce_15 = happySpecReduce_1  10 happyReduction_15
happyReduction_15 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn10
		 (Import happy_var_1 Nothing Nothing
	)
happyReduction_15 _  = notHappyAtAll 

happyReduce_16 = happyReduce 4 10 happyReduction_16
happyReduction_16 (_ `HappyStk`
	(HappyAbsSyn25  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Import happy_var_1 (Just happy_var_3) Nothing
	) `HappyStk` happyRest

happyReduce_17 = happySpecReduce_3  10 happyReduction_17
happyReduction_17 (HappyTerminal happy_var_3)
	_
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn10
		 (Import happy_var_1 Nothing (Just happy_var_3)
	)
happyReduction_17 _ _ _  = notHappyAtAll 

happyReduce_18 = happyReduce 6 10 happyReduction_18
happyReduction_18 (_ `HappyStk`
	(HappyTerminal happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn25  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn10
		 (Import happy_var_1 (Just happy_var_3) (Just happy_var_5)
	) `HappyStk` happyRest

happyReduce_19 = happySpecReduce_1  11 happyReduction_19
happyReduction_19 (HappyAbsSyn12  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_19 _  = notHappyAtAll 

happyReduce_20 = happySpecReduce_1  11 happyReduction_20
happyReduction_20 (HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn11
		 (happy_var_1
	)
happyReduction_20 _  = notHappyAtAll 

happyReduce_21 = happyReduce 5 12 happyReduction_21
happyReduction_21 ((HappyAbsSyn11  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn16  happy_var_3) `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 (Function happy_var_2 happy_var_5 happy_var_3
	) `HappyStk` happyRest

happyReduce_22 = happySpecReduce_2  12 happyReduction_22
happyReduction_22 (HappyAbsSyn18  happy_var_2)
	(HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn12
		 (Application happy_var_1 happy_var_2 Nothing
	)
happyReduction_22 _ _  = notHappyAtAll 

happyReduce_23 = happyReduce 4 12 happyReduction_23
happyReduction_23 ((HappyAbsSyn11  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn6  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn12
		 (LetBlock happy_var_2 happy_var_4
	) `HappyStk` happyRest

happyReduce_24 = happySpecReduce_2  13 happyReduction_24
happyReduction_24 (HappyAbsSyn16  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn13
		 (Bitfield happy_var_1 happy_var_2
	)
happyReduction_24 _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_2  13 happyReduction_25
happyReduction_25 (HappyAbsSyn16  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn13
		 (Quote happy_var_1 happy_var_2
	)
happyReduction_25 _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_2  13 happyReduction_26
happyReduction_26 (HappyAbsSyn16  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn13
		 (Z (read happy_var_1) happy_var_2
	)
happyReduction_26 _ _  = notHappyAtAll 

happyReduce_27 = happySpecReduce_2  13 happyReduction_27
happyReduction_27 (HappyAbsSyn16  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn13
		 (Var happy_var_1 happy_var_2
	)
happyReduction_27 _ _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_2  13 happyReduction_28
happyReduction_28 (HappyAbsSyn16  happy_var_2)
	(HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn13
		 (Record happy_var_1 happy_var_2
	)
happyReduction_28 _ _  = notHappyAtAll 

happyReduce_29 = happyReduce 4 13 happyReduction_29
happyReduction_29 (_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn11  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn13
		 (happy_var_2
	) `HappyStk` happyRest

happyReduce_30 = happySpecReduce_3  13 happyReduction_30
happyReduction_30 _
	(HappyAbsSyn19  happy_var_2)
	_
	 =  HappyAbsSyn13
		 (Array happy_var_2
	)
happyReduction_30 _ _ _  = notHappyAtAll 

happyReduce_31 = happyReduce 4 13 happyReduction_31
happyReduction_31 (_ `HappyStk`
	(HappyAbsSyn14  happy_var_3) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn13
		 (Procedure happy_var_3 Nothing
	) `HappyStk` happyRest

happyReduce_32 = happySpecReduce_3  13 happyReduction_32
happyReduction_32 (HappyTerminal happy_var_3)
	_
	(HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn13
		 (Lookup happy_var_1 happy_var_3
	)
happyReduction_32 _ _ _  = notHappyAtAll 

happyReduce_33 = happyReduce 4 13 happyReduction_33
happyReduction_33 (_ `HappyStk`
	(HappyAbsSyn11  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn13  happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn13
		 (Index happy_var_1 happy_var_3
	) `HappyStk` happyRest

happyReduce_34 = happySpecReduce_0  14 happyReduction_34
happyReduction_34  =  HappyAbsSyn14
		 ([]
	)

happyReduce_35 = happySpecReduce_3  14 happyReduction_35
happyReduction_35 (HappyAbsSyn14  happy_var_3)
	_
	(HappyAbsSyn4  happy_var_1)
	 =  HappyAbsSyn14
		 (happy_var_1:happy_var_3
	)
happyReduction_35 _ _ _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_1  15 happyReduction_36
happyReduction_36 _
	 =  HappyAbsSyn15
		 (Z'
	)

happyReduce_37 = happySpecReduce_1  15 happyReduction_37
happyReduction_37 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn15
		 (Var' happy_var_1
	)
happyReduction_37 _  = notHappyAtAll 

happyReduce_38 = happySpecReduce_3  15 happyReduction_38
happyReduction_38 _
	(HappyTerminal happy_var_2)
	_
	 =  HappyAbsSyn15
		 (Bitfield' happy_var_2
	)
happyReduction_38 _ _ _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_3  15 happyReduction_39
happyReduction_39 _
	(HappyTerminal happy_var_2)
	_
	 =  HappyAbsSyn15
		 (Bitfield' happy_var_2
	)
happyReduction_39 _ _ _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_3  15 happyReduction_40
happyReduction_40 _
	(HappyAbsSyn15  happy_var_2)
	_
	 =  HappyAbsSyn15
		 (Array' happy_var_2 Nothing
	)
happyReduction_40 _ _ _  = notHappyAtAll 

happyReduce_41 = happySpecReduce_3  15 happyReduction_41
happyReduction_41 _
	(HappyAbsSyn15  happy_var_2)
	_
	 =  HappyAbsSyn15
		 (Bitfield' happy_var_2 Nothing
	)
happyReduction_41 _ _ _  = notHappyAtAll 

happyReduce_42 = happySpecReduce_0  16 happyReduction_42
happyReduction_42  =  HappyAbsSyn16
		 (Nothing
	)

happyReduce_43 = happySpecReduce_2  16 happyReduction_43
happyReduction_43 (HappyAbsSyn15  happy_var_2)
	_
	 =  HappyAbsSyn16
		 (Just happy_var_2
	)
happyReduction_43 _ _  = notHappyAtAll 

happyReduce_44 = happySpecReduce_0  17 happyReduction_44
happyReduction_44  =  HappyAbsSyn17
		 ([]
	)

happyReduce_45 = happySpecReduce_1  17 happyReduction_45
happyReduction_45 (HappyAbsSyn18  happy_var_1)
	 =  HappyAbsSyn17
		 (happy_var_1
	)
happyReduction_45 _  = notHappyAtAll 

happyReduce_46 = happyReduce 5 18 happyReduction_46
happyReduction_46 ((HappyAbsSyn11  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn16  happy_var_3) `HappyStk`
	(HappyAbsSyn8  happy_var_2) `HappyStk`
	_ `HappyStk`
	happyRest)
	 = HappyAbsSyn18
		 (Function happy_var_2 happy_var_5 happy_var_3
	) `HappyStk` happyRest

happyReduce_47 = happySpecReduce_2  18 happyReduction_47
happyReduction_47 (HappyAbsSyn18  happy_var_2)
	(HappyAbsSyn13  happy_var_1)
	 =  HappyAbsSyn18
		 (happy_var_1:[happy_var_2]
	)
happyReduction_47 _ _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_0  19 happyReduction_48
happyReduction_48  =  HappyAbsSyn19
		 ([]
	)

happyReduce_49 = happySpecReduce_1  19 happyReduction_49
happyReduction_49 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn19
		 (happy_var_1
	)
happyReduction_49 _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_1  20 happyReduction_50
happyReduction_50 (HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn20
		 ([happy_var_1]
	)
happyReduction_50 _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_3  20 happyReduction_51
happyReduction_51 (HappyAbsSyn20  happy_var_3)
	_
	(HappyAbsSyn11  happy_var_1)
	 =  HappyAbsSyn20
		 (happy_var_1:happy_var_3
	)
happyReduction_51 _ _ _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_3  21 happyReduction_52
happyReduction_52 _
	(HappyAbsSyn23  happy_var_2)
	_
	 =  HappyAbsSyn21
		 (Record happy_var_2
	)
happyReduction_52 _ _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_3  22 happyReduction_53
happyReduction_53 (HappyAbsSyn11  happy_var_3)
	_
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn22
		 ((happy_var_1, happy_var_3)
	)
happyReduction_53 _ _ _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_3  22 happyReduction_54
happyReduction_54 (HappyAbsSyn11  happy_var_3)
	_
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn22
		 ((happy_var_1, happy_var_3)
	)
happyReduction_54 _ _ _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_0  23 happyReduction_55
happyReduction_55  =  HappyAbsSyn23
		 ([]
	)

happyReduce_56 = happySpecReduce_1  23 happyReduction_56
happyReduction_56 (HappyAbsSyn24  happy_var_1)
	 =  HappyAbsSyn23
		 (happy_var_1
	)
happyReduction_56 _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_1  24 happyReduction_57
happyReduction_57 (HappyAbsSyn22  happy_var_1)
	 =  HappyAbsSyn24
		 ([happy_var_1]
	)
happyReduction_57 _  = notHappyAtAll 

happyReduce_58 = happySpecReduce_3  24 happyReduction_58
happyReduction_58 (HappyAbsSyn24  happy_var_3)
	_
	(HappyAbsSyn22  happy_var_1)
	 =  HappyAbsSyn24
		 (happy_var_1:happy_var_3
	)
happyReduction_58 _ _ _  = notHappyAtAll 

happyReduce_59 = happySpecReduce_0  25 happyReduction_59
happyReduction_59  =  HappyAbsSyn25
		 ([]
	)

happyReduce_60 = happySpecReduce_1  25 happyReduction_60
happyReduction_60 (HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn25
		 (happy_var_1
	)
happyReduction_60 _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_1  26 happyReduction_61
happyReduction_61 _
	 =  HappyAbsSyn26
		 ([name]
	)

happyReduce_62 = happySpecReduce_3  26 happyReduction_62
happyReduction_62 (HappyAbsSyn26  happy_var_3)
	_
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn26
		 (happy_var_1:happy_var_3
	)
happyReduction_62 _ _ _  = notHappyAtAll 

happyNewToken action sts stk [] =
	action 54 54 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	T.Keyword _ "import" -> cont 27;
	T.Keyword _ "as" -> cont 28;
	T.Keyword _ "let" -> cont 29;
	T.Keyword _ "and" -> cont 30;
	T.Keyword _ "fun" -> cont 31;
	T.Keyword _ "in" -> cont 32;
	T.Keyword _ "type" -> cont 33;
	T.Keyword _ "do" -> cont 34;
	T.Keyword _ "integer" -> cont 35;
	T.Infix _ "=" -> cont 36;
	T.Infix _ "->" -> cont 37;
	T.Infix _ ";" -> cont 38;
	T.Infix _ "," -> cont 39;
	T.Infix _ ":" -> cont 40;
	T.Infix _ "::" -> cont 41;
	T.OutfixL _ "(" -> cont 42;
	T.OutfixR _ ")" -> cont 43;
	T.OutfixL _ "[" -> cont 44;
	T.OutfixR _ "]" -> cont 45;
	T.OutfixL _ "{" -> cont 46;
	T.OutfixR _ "}" -> cont 47;
	T.Postfix _ '[' -> cont 48;
	T.Postfix _ '.' -> cont 49;
	T.Bitfield _ _ -> cont 50;
	T.String _ _ -> cont 51;
	T.Integer _ _ -> cont 52;
	T.Identifier _ _ -> cont 53;
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
happyError' = HappyIdentity . happyError

happyParse tks = happyRunIdentity happySomeParser where
  happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn4 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq



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
