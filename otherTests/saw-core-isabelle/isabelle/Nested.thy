theory "Nested"
imports "Cryptol.Cryptol" Qualifier1_Qualified Qualifier2_Qualified
begin

context includes cryptol_translation_syntax begin
type_synonym ('n) Q2R = "('n) Qualifier2_Qualified.R"
term \<open>\<forall>\<close>
cryptol_definition toIntegral :: "{'n,'a} ((fin 'n,Integral 'a,Literal 2 'a) =?> ((['n]) \<Rightarrow> 'a))" where
"toIntegral x \<equiv> foldr`{'n,Bit,'a} (\<lambda>(y :: Bit) (b :: 'a). ((if y then (1 :: 'a) else coerce (0 :: 'a)) +`{'a} ((2 :: 'a) *`{'a} b))) (0 :: 'a) (reverse`{'n,Bit} x)"

cryptol_definition toIntegral_valid :: "{'n} ((fin 'n) =?> ((['n]) \<Rightarrow> Bit))" where
"toIntegral_valid x \<equiv> (toIntegral`{'n,Integer} x) ==`{Integer} (toInteger`{['n]} x)"

declare [[show_sorts]]
term toIntegral

end
context includes cryptol_syntax begin
declare [[show_types]]
thm toIntegral_def


end
