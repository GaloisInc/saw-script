theory "Foreign"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition my_add :: "([32]) \<Rightarrow> (([32]) \<Rightarrow> ([32]))"

cryptol_definition my_mul :: "([32]) \<Rightarrow> (([32]) \<Rightarrow> ([32]))"

cryptol_definition my_test :: "([32]) \<Rightarrow> (([32]) \<Rightarrow> ([32]))" where
"my_test x y \<equiv> my_mul`{} (my_add`{} x y) y"

end
end
