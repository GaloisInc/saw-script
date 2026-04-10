theory "s_s_recordT"
imports "Cryptol.Cryptol"
begin

record ('a) s_s_recordT =
  s :: 'a

free_constructors s_s_recordT_ext for s_s_recordT.s_s_recordT_ext
  by (erule s_s_recordT.cases_scheme) (rule s_s_recordT.ext_inject)

translations
  (type) "\<lparr>s :: 'a\<rparr>" \<leftharpoondown> (type) "('a) s_s_recordT"
  (type) "\<lparr>s :: 'a, \<dots> :: 'ext\<rparr>" \<leftharpoondown> (type) "('a,'ext) s_s_recordT_scheme"

instantiation s_s_recordT_ext :: (strip_type,strip_type) strip_type begin
definition "strip_type_s_s_recordT_ext \<equiv> strip_type_from_Rep (STR ''s_s_recordT_ext'') Rep_s_s_recordT_ext"
instance ..
end

instantiation s_s_recordT_ext:: (zero,zero) zero begin
definition "zero_s_s_recordT_ext \<equiv> \<lparr>s = 0,\<dots> = 0\<rparr>"
instance ..
end

context includes cryptol_translation_syntax begin
lemma s_s_recordT_ext_same_type[simp]: 
  "same_type (TYPE((('a::coercible_atom),('b::coercible_atom)) s_s_recordT_ext)) (TYPE((('c::coercible_atom),('d::coercible_atom)) s_s_recordT_ext)) = same_type TYPE({('a::coercible_atom),('b::coercible_atom)} unit) TYPE({('c::coercible_atom),('d::coercible_atom)} unit)"
  apply simp
  by (simp add: same_type_def strip_type_s_s_recordT_ext_def strip_type_prod_def)
end

instantiation s_s_recordT_ext :: (coercible_atom,coercible_atom) coercible
begin
definition strip_s_s_recordT_ext :: "(('a::coercible_atom),('b::coercible_atom)) s_s_recordT_ext \<Rightarrow> stripped" where
  "strip_s_s_recordT_ext \<equiv> (\<lambda> r. strip (Record.iso_tuple_fst s_s_recordT_ext_Tuple_Iso r, Record.iso_tuple_snd s_s_recordT_ext_Tuple_Iso r))"

definition unstrip_s_s_recordT_ext :: "stripped \<Rightarrow> (('a::coercible_atom),('b::coercible_atom)) s_s_recordT_ext" where
  "unstrip_s_s_recordT_ext \<equiv> (\<lambda> r. let (a, b) = unstrip r in Record.iso_tuple_cons s_s_recordT_ext_Tuple_Iso a b)"

instance
  apply standard
  apply (simp add: strip_s_s_recordT_ext_def unstrip_s_s_recordT_ext_def Rep_s_s_recordT_ext_inverse s_s_recordT_ext_Tuple_Iso_def)
  apply (rule abs_rep_to_record)
  apply (rule Rep_s_s_recordT_ext_inverse)
  done
end

instantiation s_s_recordT_ext :: (coercible_atom,coercible_atom) coercible_atom begin
instance
  apply standard
  by (simp add: strip_s_s_recordT_ext_def)
end

lemmas s_s_recordT_all_defs =
  s_s_recordT_ext_Tuple_Iso_def
  strip_s_s_recordT_ext_def 
  unstrip_s_s_recordT_ext_def
  s_s_recordT.select_defs 
  s_s_recordT.defs
  s_s_recordT.s_s_recordT.s_s_recordT_ext_def
  Rep_s_s_recordT_ext_inverse 
  Abs_s_s_recordT_ext_inverse


interpretation s_s_recordT: coercion "(\<lambda>x. (case x of \<lparr>s = a__s_s_recordT,\<dots> = b__s_s_recordT\<rparr> \<Rightarrow> \<lparr>s = (coerce a__s_s_recordT),\<dots> = (coerce b__s_s_recordT)\<rparr>))"
  apply standard
  subgoal for x
    apply (cases x;simp)
    by (simp add: record_raw_defs s_s_recordT_all_defs case_prod_unfold coerce_to_def)
  done

instantiation s_s_recordT_ext :: (_,_) not_bool begin
definition "is_bool0_s_s_recordT_ext (_ :: ('a,'b) s_s_recordT_ext itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_s_s_recordT_ext_def])
end
interpretation not_bool_code "TYPE(('a,'b) s_s_recordT_ext)" .

end
