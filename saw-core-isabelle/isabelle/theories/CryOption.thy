theory "CryOption"
imports "Coercible_Insts" Bool_Class Name_Qualifier
begin

(* Cryptol datatype constructors need to take the type arguments explicitly, thus we
   require a variant of option *)

qualifier "Cryptol"

datatype ('a) Option = None "('a) tyarg" | Some "('a) tyarg" "'a"

instantiation Cryptol.Option :: (strip_type) strip_type begin
definition "strip_type_Option \<equiv> (\<lambda>(_ :: ('a) Cryptol.Option itself). T [strip_type TYPE('a)] (STR ''Option''))"
instance ..
end

lemma Option_same_type[simp]:
  "same_type TYPE((('a::coercible_atom)) Cryptol.Option) TYPE((('a1::coercible_atom)) Cryptol.Option) = ((same_type TYPE('a) TYPE('a1)))"
  by (simp add: same_type_def Cryptol.strip_type_Option_def)

instantiation Cryptol.Option :: (coercible_atom) coercible
begin
definition strip_Option :: "('a) Cryptol.Option => stripped" where
  "strip_Option \<equiv> Cryptol.case_Option (curry strip (0::nat)) ((curry)(curry strip (1::nat)))"

definition unstrip_Option :: "stripped => ('a) Cryptol.Option" where
  "unstrip_Option \<equiv> (\<lambda> r. let (a :: nat, b :: stripped) = unstrip r in
     (case a of 0 \<Rightarrow> Cryptol.None o unstrip | Suc (0) \<Rightarrow> (\<lambda>(a,b). Cryptol.Some a b) o unstrip) b)"

instance
  apply standard
  apply (simp add: strip_Option_def unstrip_Option_def)
  by (auto split: Cryptol.Option.splits)
end

instance Cryptol.Option :: (coercible_atom) coercible_atom
  apply standard
  by (auto simp add: Cryptol.strip_Option_def split: Cryptol.Option.splits)

interpretation Option: coercion "Cryptol.case_Option (\<lambda>_. (Cryptol.None tyargCtr)) (\<lambda>_. (Cryptol.Some tyargCtr) o coerce)"
  apply standard
  supply [simp] = Cryptol.unstrip_Option_def Cryptol.strip_Option_def coerce_to_def
  by (auto split: Cryptol.Option.splits)

instantiation Cryptol.Option :: (_) not_bool begin
definition "is_bool0_Option (_ :: ('a) Cryptol.Option itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_Option_def])
end
interpretation not_bool_code "TYPE(('a) Cryptol.Option)" .

end
