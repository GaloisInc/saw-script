theory "ArithMap"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition map2 :: "{'n,'a,'b} ((fin 'n,Eq 'a,Eq 'b) =?> (('a \<Rightarrow> ('a \<Rightarrow> 'b)) \<Rightarrow> ((['n]'a) \<Rightarrow> ((['n]'a) \<Rightarrow> (['n]'b)))))" where
"map2 f x y \<equiv> map`{'n,('a) \<times> ('a),'b} (\<lambda>(i__p0 :: ('a) \<times> ('a)). (
  let
    b = ((\<lambda>(_,x). x) i__p0 :: 'a);
    a = ((\<lambda>(x,_). x) i__p0 :: 'a)
  in (f`{} a b))) (zip`{'n,'a,'a} x y)"

cryptol_definition map2_minus :: "{'n} ((fin 'n) =?> ((['n]['n]) \<Rightarrow> ((['n]['n]) \<Rightarrow> Bit)))" where
"map2_minus x y \<equiv> (map2`{'n,['n],['n]} (\<lblot>-`{['n]}\<rblot>) x y) ==`{['n]['n]} (x -`{['n]['n]} y)"

cryptol_definition map2_plus :: "{'n} ((fin 'n) =?> ((['n]['n]) \<Rightarrow> ((['n]['n]) \<Rightarrow> Bit)))" where
"map2_plus x y \<equiv> (map2`{'n,['n],['n]} (\<lblot>+`{['n]}\<rblot>) x y) ==`{['n]['n]} (x +`{['n]['n]} y)"

cryptol_definition map2_times :: "{'n} ((fin 'n) =?> ((['n]['n]) \<Rightarrow> ((['n]['n]) \<Rightarrow> Bit)))" where
"map2_times x y \<equiv> (map2`{'n,['n],['n]} (\<lblot>*`{['n]}\<rblot>) x y) ==`{['n]['n]} (x *`{['n]['n]} y)"

cryptol_definition map_uminus :: "{'n} ((fin 'n) =?> ((['n]['n]) \<Rightarrow> Bit))" where
"map_uminus x \<equiv> (map`{'n,['n],['n]} (\<lambda>(a :: ['n]). (negate`{['n]} a)) x) ==`{['n]['n]} (negate`{['n]['n]} x)"

end
end
