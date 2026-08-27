theory Cryptol_Quickcheck
  imports Alt_Type_Length ZInt_Code
begin

text \<open>Missing attribute for adding default types to quickcheck. 
Corresponds to quickcheck_params [default_type = [..]], but works within local contexts and bundles.\<close> 

attribute_setup quickcheck_set_default_types = 
  \<open>Parse.and_list1' Args.typ >> (fn tps => 
     (Thm.declaration_attribute (fn _ => Quickcheck.map_test_params (fn (_,ys) => (tps,ys)))))\<close>


text \<open>We setup mod_ring with a length so it can serve the dual purpose of a type argument for
 sequence indexes as well as an actual value-carrier for the purposes of generating counter-examples.\<close>

instantiation mod_ring :: (_) len0 begin
definition "len_of_mod_ring \<equiv> (\<lambda>(_ :: 'a mod_ring itself). CARD('a))"
instance ..
end

declare len_of_mod_ring_def[simp]

lemma len_of_mod_ring_code[code]:
  "len_of = (\<lambda>(_ :: ('a :: finite) mod_ring itself). CARD('a))"
  by simp

instance mod_ring :: (finite) len
  apply standard
  unfolding len_of_mod_ring_def len_of_alt_def2
  by simp

(* this stops quickcheck from complaining when trying to use int
   as a default instance for a type parameter that is used as a length*)
instantiation int :: len begin
definition "len_of_int \<equiv> \<lambda>(_ :: int itself). (1 :: nat)"
instance
  apply standard
  by (simp add: len_of_int_def len_of_alt_def2)

end

instantiation mod_ring :: (finite) card_UNIV begin
definition "card_UNIV_mod_ring == Phantom ('a mod_ring) (CARD('a))"
definition "finite_UNIV_mod_ring == Phantom ('a mod_ring) True"
instance
  apply standard
  unfolding card_UNIV_mod_ring_def finite_UNIV_mod_ring_def
  by (auto)
end

end
