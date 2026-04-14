theory "Names"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition f :: "{'a,'b,'c} ((fin 'a,fin 'b,Eq 'c) =?> ((['a + 'b]'c) \<Rightarrow> (['a]'c)))" where
"f x \<equiv> take`{'a,'b,'c} x"

cryptol_definition g :: "{'b} ((3 \<ge> 'b,fin 'b) =?> (['b]))" where
"g  \<equiv> f`{'b,3 - 'b,Bit} (0x0 :: [3])"

end
end
