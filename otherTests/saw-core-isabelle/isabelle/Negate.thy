theory "Negate"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition negate_logic :: "{'a} ((Logic 'a,Eq 'a) =?> ('a \<Rightarrow> 'a))" where
"negate_logic x \<equiv> complement`{'a} x"

cryptol_definition negate_true_is_false :: "Bit" where
"negate_true_is_false  \<equiv> (complement`{Bit} True) ==`{Bit} False"

cryptol_definition negate_valid :: "{'a} ((Logic 'a,Eq 'a) =?> ('a \<Rightarrow> Bit))" where
"negate_valid x \<equiv> (negate_logic`{'a} x) ==`{'a} (complement`{'a} x)"

cryptol_definition negate_valid_bit :: "Bit \<Rightarrow> Bit" where
"negate_valid_bit  \<equiv> negate_valid`{Bit}"

cryptol_definition negate_valid_seq :: "{'a,'b} ((fin 'a,Logic 'b,Eq 'b) =?> ((['a]'b) \<Rightarrow> Bit))" where
"negate_valid_seq  \<equiv> negate_valid`{['a]'b}"

cryptol_definition negate_valid_seq_seq_word :: "([32][16][8]) \<Rightarrow> Bit" where
"negate_valid_seq_seq_word  \<equiv> negate_valid_seq`{32,[16][8]}"

cryptol_definition negate_valid_word :: "{'a} ((fin 'a) =?> ((['a]) \<Rightarrow> Bit))" where
"negate_valid_word  \<equiv> negate_valid`{['a]}"

cryptol_definition negate_word_lit :: "Bit" where
"negate_word_lit  \<equiv> (complement`{[4]} (list_to_seq [True,True,False,True] :: [4])) ==`{[4]} (list_to_seq [False,False,True,False] :: [4])"

end
end
