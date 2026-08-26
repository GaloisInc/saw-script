theory "tac_prove0"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition goal :: "{'u} ((Eq 'u,Ring 'u) =?> ('u \<Rightarrow> ('u \<Rightarrow> Bit)))" where
"goal x y \<equiv> (x +`{'u} y) ==`{'u} (y +`{'u} x)"

end
end
