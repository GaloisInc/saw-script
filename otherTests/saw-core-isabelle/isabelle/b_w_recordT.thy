theory "b_w_recordT"
imports "Cryptol.Cryptol"
begin

record ('a,'b) b_w_recordT =
  b :: 'a
  w :: 'b

free_constructors b_w_recordT_ext for b_w_recordT.b_w_recordT_ext
  by (erule b_w_recordT.cases_scheme) (rule b_w_recordT.ext_inject)

translations
  (type) "\<lparr>b :: 'a, w :: 'b\<rparr>" \<leftharpoondown> (type) "('a,'b) b_w_recordT"
  (type) "\<lparr>b :: 'a, w :: 'b, \<dots> :: 'ext\<rparr>" \<leftharpoondown> (type) "('a,'b,'ext) b_w_recordT_scheme"

instantiation b_w_recordT_ext :: (strip_type,strip_type,strip_type) strip_type begin
definition "strip_type_b_w_recordT_ext \<equiv> strip_type_from_Rep (STR ''b_w_recordT_ext'') Rep_b_w_recordT_ext"
instance ..
end

instantiation b_w_recordT_ext:: (zero,zero,zero) zero begin
definition "zero_b_w_recordT_ext \<equiv> \<lparr>b = 0,w = 0,\<dots> = 0\<rparr>"
instance ..
end

context includes cryptol_translation_syntax begin
lemma b_w_recordT_ext_same_type[simp]: 
  "same_type (TYPE((('a::coercible_atom),('b::coercible_atom),('c::coercible_atom)) b_w_recordT_ext)) (TYPE((('d::coercible_atom),('e::coercible_atom),('f::coercible_atom)) b_w_recordT_ext)) = same_type TYPE({('a::coercible_atom),('b::coercible_atom),('c::coercible_atom)} unit) TYPE({('d::coercible_atom),('e::coercible_atom),('f::coercible_atom)} unit)"
  apply simp
  by (simp add: same_type_def strip_type_b_w_recordT_ext_def strip_type_prod_def)
end

instantiation b_w_recordT_ext :: (coercible_atom,coercible_atom,coercible_atom) coercible
begin
definition strip_b_w_recordT_ext :: "(('a::coercible_atom),('b::coercible_atom),('c::coercible_atom)) b_w_recordT_ext \<Rightarrow> stripped" where
  "strip_b_w_recordT_ext \<equiv> (\<lambda> r. strip (Record.iso_tuple_fst b_w_recordT_ext_Tuple_Iso r, Record.iso_tuple_snd b_w_recordT_ext_Tuple_Iso r))"

definition unstrip_b_w_recordT_ext :: "stripped \<Rightarrow> (('a::coercible_atom),('b::coercible_atom),('c::coercible_atom)) b_w_recordT_ext" where
  "unstrip_b_w_recordT_ext \<equiv> (\<lambda> r. let (a, b) = unstrip r in Record.iso_tuple_cons b_w_recordT_ext_Tuple_Iso a b)"

instance
  apply standard
  apply (simp add: strip_b_w_recordT_ext_def unstrip_b_w_recordT_ext_def Rep_b_w_recordT_ext_inverse b_w_recordT_ext_Tuple_Iso_def)
  apply (rule abs_rep_to_record)
  apply (rule Rep_b_w_recordT_ext_inverse)
  done
end

instantiation b_w_recordT_ext :: (coercible_atom,coercible_atom,coercible_atom) coercible_atom begin
instance
  apply standard
  by (simp add: strip_b_w_recordT_ext_def)
end

lemmas b_w_recordT_all_defs =
  b_w_recordT_ext_Tuple_Iso_def
  strip_b_w_recordT_ext_def 
  unstrip_b_w_recordT_ext_def
  b_w_recordT.select_defs 
  b_w_recordT.defs
  b_w_recordT.b_w_recordT.b_w_recordT_ext_def
  Rep_b_w_recordT_ext_inverse 
  Abs_b_w_recordT_ext_inverse


interpretation b_w_recordT: coercion "(\<lambda>x. (case x of \<lparr>b = a__b_w_recordT,w = b__b_w_recordT,\<dots> = c__b_w_recordT\<rparr> \<Rightarrow> \<lparr>b = (coerce a__b_w_recordT),w = (coerce b__b_w_recordT),\<dots> = (coerce c__b_w_recordT)\<rparr>))"
  apply standard
  subgoal for x
    apply (cases x;simp)
    by (simp add: record_raw_defs b_w_recordT_all_defs case_prod_unfold coerce_to_def)
  done

instantiation b_w_recordT_ext :: (_,_,_) not_bool begin
definition "is_bool0_b_w_recordT_ext (_ :: ('a,'b,'c) b_w_recordT_ext itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_b_w_recordT_ext_def])
end
interpretation not_bool_code "TYPE(('a,'b,'c) b_w_recordT_ext)" .

end
