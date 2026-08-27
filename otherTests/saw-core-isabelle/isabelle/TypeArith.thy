theory "TypeArith"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition lg2_concrete_test :: "Bit" where
"lg2_concrete_test  \<equiv> (map`{14,[64],[64]} (lg2`{64}) (list_to_seq [0x0 :: [64],0x1 :: [64],0x2 :: [64],0x1e :: [64],0x1f :: [64],0x20 :: [64],0x21 :: [64],0x22 :: [64],0x23 :: [64],0x24 :: [64],0x3e :: [64],0x3f :: [64],0x40 :: [64],0x41 :: [64]] :: [14][64])) ==`{[14][64]} (list_to_seq [0x0 :: [64],0x0 :: [64],0x1 :: [64],0x5 :: [64],0x5 :: [64],0x5 :: [64],0x6 :: [64],0x6 :: [64],0x6 :: [64],0x6 :: [64],0x6 :: [64],0x6 :: [64],0x6 :: [64],0x7 :: [64]] :: [14][64])"

cryptol_definition lg2_validlba_gteq_2rb :: "{'a} ((fin 'a,'a \<ge> 2) =?> ((['a]) \<Rightarrow> Bit))" where
"lg2_validlba_gteq_2rb x \<equiv> ((lg2`{1 + 'a} ((0x2 :: [1 + 'a]) ^^`{[1 + 'a],[1 + 'a]} (lg2`{1 + 'a} (zext`{1 + 'a,'a} x)))) ==`{[1 + 'a]} (lg2`{1 + 'a} (zext`{1 + 'a,'a} x))) \<and> (((lg2`{1 + 'a} ((zext`{1 + 'a,'a} x) +`{[1 + 'a]} (0x1 :: [1 + 'a]))) ==`{[1 + 'a]} ((0x1 :: [1 + 'a]) +`{[1 + 'a]} (lg2`{1 + 'a} (zext`{1 + 'a,'a} x)))) \<longrightarrow> (((0x2 :: [1 + 'a]) ^^`{[1 + 'a],['a]} (lg2`{'a} x)) ==`{[1 + 'a]} (zext`{1 + 'a,'a} x)))"

cryptol_definition lg2_validlba_lt_2rb :: "{'a} ((fin 'a,'a < 2) =?> ((['a]) \<Rightarrow> Bit))" where
"lg2_validlba_lt_2rb x \<equiv> (lg2`{'a} x) ==`{['a]} (0x0 :: ['a])"

cryptol_definition lg2_valid :: "{'a} ((fin 'a) =?> ((['a]) \<Rightarrow> Bit))" where
"lg2_valid  \<equiv> if PRED('a < 2) then ((lg2_validlba_lt_2rb`{'a}) : ((['a]) \<Rightarrow> Bit)) else coerce (('a \<ge> 2) \<Rightarrow> ((lg2_validlba_gteq_2rb`{'a}) : ((['a]) \<Rightarrow> Bit)))"

cryptol_definition type_add :: "{'a,'b} ((fin 'a,fin 'b) =?> Bit)" where
"type_add  \<equiv> (number`{'a + 'b,Integer}) ==`{Integer} ((number`{'a,Integer}) +`{Integer} (number`{'b,Integer}))"

cryptol_definition type_div :: "{'a,'b} ((fin 'a,fin 'b,'b \<ge> 1) =?> Bit)" where
"type_div  \<equiv> (number`{'a / 'b,Integer}) ==`{Integer} ((number`{'a,Integer}) /`{Integer} (number`{'b,Integer}))"

cryptol_definition type_exp :: "{'a,'b} ((fin 'a,fin 'b) =?> Bit)" where
"type_exp  \<equiv> (number`{'a ^ 'b,Integer}) ==`{Integer} ((number`{'a,Integer}) ^^`{Integer,Integer} (number`{'b,Integer}))"

cryptol_definition type_lg2 :: "{'a} ((fin 'a) =?> Bit)" where
"type_lg2  \<equiv> (number`{('a) lg2,['a]}) ==`{['a]} (lg2`{'a} (number`{'a,['a]}))"

cryptol_definition type_lits :: "Bit" where
"type_lits  \<equiv> ((0 :: Integer) ==`{Integer} (0 :: Integer)) \<and> (((1 :: Integer) ==`{Integer} (1 :: Integer)) \<and> (((2 :: Integer) ==`{Integer} (2 :: Integer)) \<and> ((1234 :: Integer) ==`{Integer} (1234 :: Integer))))"

cryptol_definition type_max :: "{'a,'b} ((fin 'a,fin 'b) =?> Bit)" where
"type_max  \<equiv> (number`{('a,'b) Min,Integer}) ==`{Integer} (min`{Integer} (number`{'a,Integer}) (number`{'b,Integer}))"

cryptol_definition type_min :: "{'a,'b} ((fin 'a,fin 'b) =?> Bit)" where
"type_min  \<equiv> (number`{('a,'b) Min,Integer}) ==`{Integer} (min`{Integer} (number`{'a,Integer}) (number`{'b,Integer}))"

cryptol_definition type_mod :: "{'a,'b} ((fin 'a,fin 'b,'b \<ge> 1) =?> Bit)" where
"type_mod  \<equiv> (number`{'a % 'b,Integer}) ==`{Integer} ((number`{'a,Integer}) %`{Integer} (number`{'b,Integer}))"

cryptol_definition type_mul :: "{'a,'b} ((fin 'a,fin 'b) =?> Bit)" where
"type_mul  \<equiv> (number`{'a * 'b,Integer}) ==`{Integer} ((number`{'a,Integer}) *`{Integer} (number`{'b,Integer}))"

cryptol_definition type_sub :: "{'a,'b} ((fin 'a,fin 'b,'a \<ge> 'b) =?> Bit)" where
"type_sub  \<equiv> (number`{'a - 'b,Integer}) ==`{Integer} ((number`{'a,Integer}) -`{Integer} (number`{'b,Integer}))"

cryptol_definition width_vallba_gteq_2rb :: "{'a} ((fin 'a,'a \<ge> 2) =?> ((['a]) \<Rightarrow> (['a])))" where
"width_vallba_gteq_2rb x \<equiv> lg2`{'a} (x +`{['a]} (0x1 :: ['a]))"

cryptol_definition width_vallba_lt_2rb :: "{'a} ((fin 'a,'a < 2) =?> ((['a]) \<Rightarrow> (['a])))" where
"width_vallba_lt_2rb x \<equiv> x"

cryptol_definition width_val :: "{'a} ((fin 'a) =?> ((['a]) \<Rightarrow> (['a])))" where
"width_val  \<equiv> if PRED('a < 2) then ((width_vallba_lt_2rb`{'a}) : ((['a]) \<Rightarrow> (['a]))) else coerce (('a \<ge> 2) \<Rightarrow> ((width_vallba_gteq_2rb`{'a}) : ((['a]) \<Rightarrow> (['a]))))"

cryptol_definition type_width :: "{'a} ((fin 'a) =?> Bit)" where
"type_width  \<equiv> (number`{width 'a,['a]}) ==`{['a]} (width_val`{'a} (number`{'a,['a]}))"

end
end
