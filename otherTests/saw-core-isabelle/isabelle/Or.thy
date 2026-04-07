theory "Or"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition or_logic :: "{'a} ((Logic 'a,Eq 'a) =?> ('a \<Rightarrow> ('a \<Rightarrow> 'a)))" where
"or_logic x y \<equiv> x ||`{'a} y"

cryptol_definition or_truth_table :: "Bit" where
"or_truth_table  \<equiv> ((False ||`{Bit} False) ==`{Bit} False) &&`{Bit} (((True ||`{Bit} False) ==`{Bit} True) &&`{Bit} (((False ||`{Bit} True) ==`{Bit} True) &&`{Bit} ((True ||`{Bit} True) ==`{Bit} True)))"

cryptol_definition or_valid :: "{'a} ((Logic 'a,Eq 'a) =?> ('a \<Rightarrow> ('a \<Rightarrow> Bit)))" where
"or_valid x y \<equiv> (or_logic`{'a} x y) ==`{'a} (x ||`{'a} y)"

cryptol_definition or_valid_Bit :: "Bit \<Rightarrow> (Bit \<Rightarrow> Bit)" where
"or_valid_Bit  \<equiv> or_valid`{Bit}"

cryptol_definition or_valid_seq :: "{'a,'b} ((fin 'a,Logic 'b,Eq 'b) =?> ((['a]'b) \<Rightarrow> ((['a]'b) \<Rightarrow> Bit)))" where
"or_valid_seq  \<equiv> or_valid`{['a]'b}"

cryptol_definition or_valid_seq_seq_word :: "([32][16][8]) \<Rightarrow> (([32][16][8]) \<Rightarrow> Bit)" where
"or_valid_seq_seq_word  \<equiv> or_valid_seq`{32,[16][8]}"

cryptol_definition or_valid_word :: "{'a} ((fin 'a) =?> ((['a]) \<Rightarrow> ((['a]) \<Rightarrow> Bit)))" where
"or_valid_word  \<equiv> or_valid`{['a]}"

cryptol_definition or_word_lit :: "Bit" where
"or_word_lit  \<equiv> ((list_to_seq [True,True,False,True] :: [4]) ||`{[4]} (list_to_seq [False,True,False,True] :: [4])) ==`{[4]} (list_to_seq [True,True,False,True] :: [4])"

end
end
