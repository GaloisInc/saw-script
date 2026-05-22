theory "tac_prove0"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition goal :: "{'a} ((Eq 'a,Ring 'a) =?> ('a \<Rightarrow> ('a \<Rightarrow> Bit)))" where
"goal x y \<equiv> (x +`{'a} y) ==`{'a} (y +`{'a} x)"

end
end
