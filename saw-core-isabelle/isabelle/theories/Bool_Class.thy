theory Bool_Class
imports Coercible_Insts Integral ListOOB Fin
begin

class maybe_bool0 = 
  fixes is_bool0 :: "'a itself \<Rightarrow> bool"
    and of_bool_list0 :: "bool list \<Rightarrow> 'a list"
    and bool_list_of0 :: "'a list \<Rightarrow> bool list"
begin
definition "of_bool_list x \<equiv> of_bool_list0 x"
definition "bool_list_of x \<equiv> bool_list_of0 x"
end
declare maybe_bool0.intro_of_class[unconstrain_intro]

unconstrain_const of_bool_list :: "bool list \<Rightarrow> 'a list"
unconstrain_const bool_list_of :: "'a list \<Rightarrow> bool list"

definition bool_of :: "'a \<Rightarrow> bool" where
  "bool_of x \<equiv> hd (bool_list_of [x])"

class bool0 = strip + unstrip + ord + one + zero + strip_type + maybe_bool0
declare bool0.intro_of_class[unconstrain_intro]

instantiation bool :: bool0 begin
definition "is_bool0_bool (_::bool itself) \<equiv> True"
definition "of_bool_list0_bool (x :: bool list) \<equiv> x"
definition "bool_list_of0_bool (x :: bool list) \<equiv> x"
instance ..
end

instantiation Enum.finite_2 :: bool0 begin
definition "is_bool0_finite_2 (_::Enum.finite_2 itself) \<equiv> True"
definition "of_bool_list0_finite_2 (xs :: bool list) \<equiv> (map (\<lambda>x. if x then (1 :: Enum.finite_2) else 0) xs)"
definition "bool_list_of0_finite_2 (xs :: Enum.finite_2 list) \<equiv> (map (\<lambda>x. x = 1) xs)"
instance ..
end

lemma of_bool_list_bool[simp,code_unfold]: "of_bool_list = (\<lambda>x. x)"
  apply (rule ext)
  by (simp add: of_bool_list0_bool_def of_bool_list_def)

lemma bool_list_of_bool[simp,code_unfold]: "bool_list_of = (\<lambda>x. x)"
  apply (rule ext)
  by (simp add: bool_list_of_def bool_list_of0_bool_def)

lemma bool_of_bool[simp,code_unfold]: "bool_of = (\<lambda>x. x)"
  apply (rule ext)
  by (simp add: bool_list_of_def bool_list_of0_bool_def bool_of_def)

lemma of_bool_bool[simp,code_unfold]: "of_bool = (\<lambda>x. x)"
  by (auto simp add: of_bool_def[abs_def] one_bool_def zero_bool_def)

class bool = bool0 + zero_neq_one + linorder + coercible_atom +
  assumes zero_or_one: "\<And>x. x = 0 \<or> x = 1"
      and zero_lt_one: "(0 :: 'a) < 1"
      and strips_bool: "\<And>(x::'a). strip x = strip (bool_of x)"
      and unstrips_bool: "\<And>x. unstrip x = of_bool (unstrip x)"
      and is_bool_type: "strip_type TYPE('a) = strip_type TYPE(bool)"
      and is_bool0: "is_bool0 TYPE('a)"
      and of_bool_list_eq_map: "of_bool_list = map of_bool"
      and bool_list_of_eq_map: "bool_list_of = map bool_of"
      and bool_of_eq_0: "bool_of = (\<lambda>x. x \<noteq> 0)"
      and of_bool_list_len: "\<And>(x :: bool list) n. map of_bool (list_len n x) = list_len n (map of_bool x)"
      and bool_of_list_len: "\<And>(x :: 'a list) n. map bool_of (list_len n x) = list_len n (map bool_of x)"

instance bool :: bool
  apply standard
  by (simp add: zero_bool_def one_bool_def is_bool0_bool_def
                of_bool_def[abs_def])+


definition (in bool0)
  "is_bool (x :: 'a itself) \<equiv> 
    class.bool is_bool0  of_bool_list0 bool_list_of0 strip strip_type unstrip (1 :: 'a) 0 (\<le>) (<)"
unconstrain_const is_bool :: "'a itself \<Rightarrow> bool"
lemmas is_bool_def = is_bool_def[unconstrain]

class maybe_bool = maybe_bool0 +
  assumes maybe_bool[code]: "is_bool TYPE('a) = is_bool0 TYPE('a)"

class not_bool = maybe_bool +
  assumes not_bool0: "\<not> is_bool0 TYPE('a)"

lemma is_bool_of_class[unconstrain_intro]: 
  "is_bool TYPE('a) \<Longrightarrow> OFCLASS('a,bool_class)"
  apply (simp add: is_bool_def)
  apply (rule bool.intro_of_class)
  by assumption

lemmas of_bool_list_def2[simp] = of_bool_list_eq_map[unconstrain]
lemmas bool_list_of_def2[simp] = bool_list_of_eq_map[unconstrain]

lemma is_bool[simp,code_unfold]: 
  "is_bool TYPE('a::bool)"
  unfolding is_bool_def
  apply (rule bool_class.bool_axioms)
  done

instance bool < maybe_bool
  apply standard
  apply (simp add: is_bool_def is_bool0)
  apply (rule bool_axioms)
  done

lemmas is_bool0 = is_bool0[unconstrain]

lemma not_is_bool0[unconstrain]: 
  "\<not> is_bool0 TYPE('a::bool0) \<Longrightarrow> \<not> is_bool TYPE('a)"
  using is_bool0
  by blast

lemma not_bool[simp]: "\<not>is_bool TYPE('a::not_bool)"
  apply (rule not_is_bool0)
  by (rule not_bool0)

lemma maybe_bool_bool_class[unconstrain]:
  "class.maybe_bool (is_bool0 :: 'a :: bool itself \<Rightarrow> bool)"
  by (rule maybe_bool_class.axioms)

lemma not_maybe_not_bool:
  "(\<not> class.maybe_bool (is_bool0 :: 'a :: maybe_bool0 itself \<Rightarrow> bool)) \<Longrightarrow>
         (\<not> is_bool TYPE('a))"
  using maybe_bool_bool_class
  by blast

lemma not_bool_class[unconstrain]:
 "(is_bool0 TYPE('a) \<equiv> False) \<Longrightarrow> OFCLASS('a::maybe_bool0, not_bool_class)"
  apply atomize
  apply (rule not_bool.intro_of_class)
  apply (constrain 'a="'aa :: maybe_bool")
  subgoal H[unconstrain_cases]
    apply (standard)
    by (simp add: maybe_bool[symmetric])
  apply (rule H)
  apply (drule not_maybe_not_bool)
   apply simp
  subgoal premises prems
    apply standard
    by (simp add: prems)+
  by simp


locale not_bool_code = fixes a :: "'a::not_bool itself" begin
declare [[code abort: "of_bool_list0 :: bool list \<Rightarrow> 'a list"]]
declare [[code abort: "bool_list_of0 ::  'a list \<Rightarrow> bool list"]]
end
  

instantiation unit :: not_bool begin
definition "is_bool0_unit (_ :: unit itself) \<equiv> False"
instance
  by (rule not_bool_class[OF is_bool0_unit_def])
end
interpretation not_bool_code "TYPE(unit)" .

instantiation int :: not_bool begin
definition "is_bool0_int (_ :: int itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_int_def])
end
interpretation not_bool_code "TYPE(int)" .

instantiation nat :: not_bool begin
definition "is_bool0_nat (_ :: nat itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_nat_def])
end
interpretation not_bool_code "TYPE(nat)" .

instantiation list :: (_) not_bool begin
definition "is_bool0_list (_ :: 'a list itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_list_def])
end
interpretation not_bool_code "TYPE('a list)" .

instantiation option :: (_) not_bool begin
definition "is_bool0_option (_ :: 'a option itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_option_def])
end
interpretation not_bool_code "TYPE('a option)" .

instantiation word :: (_) not_bool begin
definition "is_bool0_word (_ :: 'a word itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_word_def])
end
interpretation not_bool_code "TYPE('a word)" .

instantiation sum :: (_,_) not_bool begin
definition "is_bool0_sum (_ :: ('a+'b) itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_sum_def])
end
interpretation not_bool_code "TYPE('a + 'b)" .

instantiation prod :: (_,_) not_bool begin
definition "is_bool0_prod (_ :: ('a\<times>'b) itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_prod_def])
end
interpretation not_bool_code "TYPE('a \<times> 'b)" .

instantiation Enum.finite_1 :: not_bool begin
definition "is_bool0_finite_1 (_ :: Enum.finite_1 itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_finite_1_def])
end
interpretation not_bool_code "TYPE(Enum.finite_1)" .

instantiation Enum.finite_3 :: not_bool begin
definition "is_bool0_finite_3 (_ :: Enum.finite_3 itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_finite_3_def])
end
interpretation not_bool_code "TYPE(Enum.finite_3)" .

instantiation Enum.finite_4 :: not_bool begin
definition "is_bool0_finite_4 (_ :: Enum.finite_4 itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_finite_4_def])
end
interpretation not_bool_code "TYPE(Enum.finite_4)" .

instantiation Enum.finite_5 :: not_bool begin
definition "is_bool0_finite_5 (_ :: Enum.finite_5 itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_finite_5_def])
end
interpretation not_bool_code "TYPE(Enum.finite_5)" .

instantiation bit0 :: (_) not_bool begin
definition "is_bool0_bit0(_ :: 'a bit0 itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_bit0_def])
end
interpretation not_bool_code "TYPE('a bit0)" .

instantiation bit1 :: (_) not_bool begin
definition "is_bool0_bit1(_ :: 'a bit1 itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_bit1_def])
end
interpretation not_bool_code "TYPE('a bit1)" .

instantiation num1 :: not_bool begin
definition "is_bool0_num1(_ :: num1 itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_num1_def])
end
interpretation not_bool_code "TYPE(num1)" .

instantiation mod_ring :: (_) not_bool begin
definition "is_bool0_mod_ring (_ :: 'a mod_ring itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_mod_ring_def])
end
interpretation not_bool_code "TYPE('a mod_ring)" .

definition (in maybe_bool0) of_bool' :: "bool \<Rightarrow> 'a" where "of_bool' x \<equiv> hd (of_bool_list [x])"
definition (in maybe_bool0) bool_of' :: "'a \<Rightarrow> bool" where "bool_of' x \<equiv> hd (bool_list_of [x])"

unconstrain_const of_bool' :: "bool \<Rightarrow> 'a"
unconstrain_const bool_of' :: "'a \<Rightarrow> bool"

lemma (in bool) of_bool': "of_bool' = of_bool"
  apply (rule ext)
  by (simp add: of_bool'_def of_bool_list_eq_map)

lemma (in bool) bool_of'[simp]: "bool_of' = bool_of"
  apply (rule ext)
  by (simp add: bool_of'_def bool_list_of_eq_map)

lemmas [unconstrain,simp] = of_bool' bool_of'

unconstrain_const (unchecked) bool_of :: "'a :: bool \<Rightarrow> bool"

lemma bool_of_def2: "bool_of = (unstrip_atom o strip_atom)"
  apply (rule ext)
  apply (simp add: comp_def)
  by (metis (full_types) strip_unstrip strips_bool)

lemma of_bool_def2: "(of_bool :: bool \<Rightarrow> 'a :: bool) = (unstrip_atom o strip_atom)"
  apply (rule ext)
  apply (simp add: comp_def)
  by (metis of_bool_eq strip_unstrip unstrips_bool)

lemma bool_of_le[simp]: "(bool_of x \<le> bool_of y) = (x \<le> y)"
  apply (simp add: bool_of_eq_0)
  by (metis (full_types) le_boolI
      linorder_not_less nle_le zero_lt_one
      zero_or_one)

lemma bool_of_lt[simp]: "(bool_of x < bool_of y) = (x < y)"
  apply (simp add: bool_of_eq_0)
  by (metis (full_types) le_boolI
      linorder_not_less nle_le zero_lt_one
      zero_or_one)

declare zero_bool_def[simp]
declare one_bool_def[simp]

lemma of_bool_id[simp]: "of_bool = id"
  apply (rule ext)
  by (simp add: of_bool_def)

lemma bool_of_id[simp]: "bool_of = id"
  apply (rule ext)
  by (simp add: bool_of_def)

lemma of_bool_of_id: "of_bool (bool_of x) = x"
  apply (simp add: of_bool_def bool_of_eq_0)
  using zero_or_one by auto  
  
lemma bool_of_bool_id: "bool_of (of_bool x) = x"
  by (simp add: of_bool_def bool_of_eq_0)

lemma of_bool_of_comp: "of_bool o bool_of = id"
  apply (rule ext)
  by (simp add: of_bool_of_id)

lemma bool_of_bool_comp: "bool_of o of_bool = id"
  apply (rule ext)
  by (simp add: bool_of_bool_id)


lemma bool_of_inj: "inj (bool_of :: 'a :: bool \<Rightarrow> bool)"
  apply (simp add: bool_of_eq_0)
  by (metis (mono_tags, lifting)
      injI zero_or_one)

lemma bool_of_surj: "surj bool_of"
  apply (rule surjI[where f="of_bool"])
  apply (simp add: bool_of_bool_id)
  done

lemma bool_of_bij: "bij bool_of"
  apply (rule bijI)
  by (auto simp add: bool_of_inj bool_of_surj)


lemma of_bool_inj: "inj (of_bool :: bool \<Rightarrow> 'a :: bool)"
  apply (simp add: of_bool_def[abs_def])
  by (simp add: inj_on_def)

lemma of_bool_surj: "surj (of_bool :: bool \<Rightarrow> 'a :: bool)"
  apply (rule surjI[where f="bool_of"])
  apply (simp add: bool_of_bool_id bool_of_eq_0)       
  by (metis zero_or_one)

lemma of_bool_bij: "bij (of_bool :: bool \<Rightarrow> 'a :: bool)"
  by (simp add: bijI of_bool_inj of_bool_surj)


lemmas of_bool_idents[unconstrain, simp] =
 of_bool_of_comp bool_of_bool_comp bool_of_bool_id
 of_bool_of_id  bool_of_inj bool_of_surj bool_of_bij
 of_bool_inj of_bool_surj of_bool_bij


lemma of_bool_simps[unconstrain, simp]: 
  "of_bool False = (0 :: 'a :: bool)"
  "of_bool True = (1 :: 'a :: bool)"
  by auto


context begin
private lemma the_the: "THE x. x"
  apply (rule HOL.theI')
  by auto

private lemma the_not_the: "\<not> (THE x. \<not> x)"
  apply (rule HOL.theI')
  by auto

private lemma undefined_list_elem_fin2: 
 "(undefined_list_elem :: Enum.finite_2) = of_bool undefined_list_elem"
  unfolding undefined_list_elem_def of_bool_def
  apply (cases "undefined_bool :: bool"; rule the_equality; 
    simp add: UNIV_bool the_the the_not_the split del: if_splits; rule UNIV_eq_I)
  subgoal for x
    by (cases x;auto)
  subgoal for x
    by (cases x;auto)
  done

lemma undefined_list_elem_bool_class_def: 
 "(undefined_list_elem :: 'a :: bool) = of_bool undefined_list_elem"
  unfolding undefined_list_elem_def of_bool_def
  apply (cases "undefined_bool :: bool"; rule the_equality; 
    simp add: UNIV_bool the_the the_not_the split del: if_splits; rule UNIV_eq_I)
  by (auto simp add: zero_or_one)

lemma oob_list_elem_bool_class_def: 
  "oob_list_elem bs = of_bool (oob_list_elem (map bool_of bs))"
  unfolding oob_list_elem_def
  by (simp add: undefined_list_elem_bool_class_def[where 'a='a])


lemma finite_2_bool_class: "OFCLASS(Enum.finite_2, bool_class)"
  apply (standard; ((rule ext)+)?)
  subgoal for x
    by (cases x;simp)
  by (auto simp: 
    less_finite_2_def strip_finite_2_def bool_of_def strip_type_bool_def strip_type_finite_2_def
    bool_list_of0_finite_2_def unstrip_finite_2_def is_bool0_finite_2_def of_bool_list0_finite_2_def
    list_len_def nth_list_def oob_list_elem_def undefined_list_elem_fin2 bool_list_of_def
    of_bool_list_def)

end

lemma bool_of_1[simp]: "bool_of (1 :: 'a :: bool) = 1"
  by (simp add: bool_of_eq_0)

lemma bool_of_0[simp]: "bool_of (0 :: 'a :: bool) = 0"
  by (simp add: bool_of_eq_0)

instance Enum.finite_2 :: bool
  by (rule finite_2_bool_class)

lemma of_bool_induct: "(\<And>y. P (of_bool y)) \<Longrightarrow> P (x :: 'a :: bool)"
  by (metis of_bool_of_id)

definition test :: "'a \<Rightarrow> bool" where
  "test x \<equiv> if is_bool TYPE('a) then bool_of' x  else False"

definition test1 :: bool where
  "test1 \<equiv> (test (1::int) \<or> test True) \<and> \<not> test False"

lemma "test1" by eval

hide_const test
hide_const test1

end