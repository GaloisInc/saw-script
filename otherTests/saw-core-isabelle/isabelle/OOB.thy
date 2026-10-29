theory "OOB"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition at_oob :: "{'n,'a,'ix} ((fin 'n,Eq 'a,Integral 'ix,Cmp 'ix,Literal 'n 'ix) =?> ((['n]'a) \<Rightarrow> ('ix \<Rightarrow> Bit)))" where
"at_oob a i \<equiv> ((length`{'n,'a,'ix} a) <=`{'ix} i) \<longrightarrow> ((a @`{'n,'a,'ix} i) ==`{'a} (a !`{'n,'a,Integer} (0 :: Integer)))"

cryptol_definition bang_oob :: "{'n,'a,'ix} ((fin 'n,Eq 'a,Integral 'ix,Cmp 'ix,Literal 'n 'ix) =?> ((['n]'a) \<Rightarrow> ('ix \<Rightarrow> Bit)))" where
"bang_oob a i \<equiv> ((length`{'n,'a,'ix} a) <=`{'ix} i) \<longrightarrow> ((a !`{'n,'a,'ix} i) ==`{'a} (a @`{'n,'a,'ix} (0 :: 'ix)))"

end
end
