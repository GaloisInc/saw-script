theory "Inf"
imports "Cryptol.Cryptol" "Cryptol.Unsupported"
begin

context includes cryptol_translation_syntax begin
typedecl Inf'

type_synonym Inf = "(Inf') unsupportedT"

cryptol_definition any_seq_refl :: "{'a} ((fin 'a) =?> ((['a]) \<Rightarrow> Bit))" where
"any_seq_refl x \<equiv> (x @`{'a,Bit,Integer} (0 :: Integer)) ==`{Bit} (x @`{'a,Bit,Integer} (0 :: Integer))"

cryptol_definition bounded_seq_refl :: "{'a} (('a < 3) =?> ((['a]) \<Rightarrow> Bit))" where
"bounded_seq_refl x \<equiv> any_seq_refl`{'a} x"

cryptol_definition inf_seq_refl :: "([Inf]) \<Rightarrow> Bit" where
"inf_seq_refl x \<equiv> any_seq_refl`{Inf} x"

end
end
