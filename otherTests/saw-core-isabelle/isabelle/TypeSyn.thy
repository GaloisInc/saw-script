theory "TypeSyn"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
type_synonym ('k) Div2T = "'k / 2"

cryptol_definition seq_noop :: "{'n} ((fin 'n) =?> (([('n) Div2T]) \<Rightarrow> ([('n) Div2T])))" where
"seq_noop x \<equiv> x"

end
end
