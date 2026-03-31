theory ZInt_Code
imports ZIntSeq "HOL-Library.Code_Cardinality"
begin

instantiation fin :: (_) card_UNIV begin
definition "card_UNIV_fin == Phantom ('a fin) (max 1 LEN('a))"
definition "finite_UNIV_fin == Phantom ('a fin) True"
instance
  supply [simp] = type_definition.card [OF type_definition_fin]
                  card_UNIV_fin_def finite_UNIV_fin_def
  apply standard
  by auto
end

instantiation fin :: (_) len0 begin
definition "len_of_fin \<equiv> \<lambda>(_:: 'a fin itself). LEN('a)"
instance ..
end

instance fin :: (len) len
  apply standard
  by (simp add: len_of_fin_def)

(* same trick as len type wrapper. Lifts any type to be a prime-length type, but
   has (effectively) undefined length if the source is not actually prime *)
datatype 'a prime = PrimeCtr

instantiation prime :: (_) prime_len begin

definition some_prime :: "unit \<Rightarrow> nat" where
  "some_prime _ \<equiv> (SOME n. prime n)"

lemma some_prime_prime: "prime (some_prime ())"
  apply (simp add: some_prime_def)
  apply (rule someI[of _ 2])
  by simp

definition "len_of_prime \<equiv> (\<lambda>(_ :: 'a prime itself). if prime LEN('a) then LEN('a) else some_prime ())"
instance
  apply standard
    apply (simp_all add: len_of_prime_def)
  using prime_gt_0_nat prime_gt_Suc_0_nat some_prime_prime
  by auto
end

declare [[code abort: some_prime]]

lemma prime_len[simp]: "prime LEN('a) \<Longrightarrow> LENGTH('a prime) = LEN('a)"
  by (simp add: len_of_prime_def)

hide_fact len_of_prime_def
hide_fact some_prime_def

lemma UNIV_card: "CARD('a::card_UNIV) = of_phantom (card_UNIV :: ('a,nat) phantom)"
  by (simp add: card_UNIV)

instance Enum.finite_2 :: prime_card
  apply standard
  by (simp add: UNIV_card card_UNIV_finite_2_def)

instance Enum.finite_3 :: prime_card
  apply standard
  by (simp add: UNIV_card card_UNIV_finite_3_def)

instance Enum.finite_5 :: prime_card
  apply standard
  by (simp add: UNIV_card card_UNIV_finite_5_def)


lift_definition
  to_mr :: "int \<Rightarrow> 'a :: finite mod_ring" is "\<lambda>x. x mod int (CARD('a))"
  by simp

abbreviation from_mr :: "'a :: finite mod_ring \<Rightarrow> int" where
  "from_mr \<equiv> Rep_mod_ring"

lemma to_mr_inverse[code abstype]: "to_mr (from_mr x) = x"
  apply transfer
  by simp

lemma zero_mod_ring_code[code abstract]:
  "from_mr (0 :: 'a :: finite mod_ring) = 0"
  apply transfer
  by simp

lemma one_mod_ring_code[code abstract]:
  "from_mr (1 :: 'a :: finite mod_ring) = (if CARD('a) = 1 then 0 else 1)"
  apply transfer
  by simp


abbreviation (input)
  mr_size :: "'a mod_ring \<Rightarrow> int" where
  "mr_size _ \<equiv> int (CARD ('a))"

lemma plus_mod_ring_code[code abstract]:
  "from_mr (x + y) = (from_mr x + from_mr y) mod mr_size x"
  by transfer simp

lemma minus_mod_ring_code[code abstract]:
  "from_mr (x - y) = (from_mr x - from_mr y) mod mr_size x"
  by transfer simp

lemma uminus_mod_ring_code[code abstract]:
  "from_mr (uminus x) = (uminus (from_mr x)) mod mr_size x"
  apply transfer
  by (simp add: zmod_zminus1_eq_if)

lemma times_mod_ring_code[code abstract]:
  "from_mr (x * y) = (from_mr x * from_mr y) mod mr_size x"
  by transfer simp

lemma power_mod_ring_code[code_unfold]: "x ^ n = to_mr ((from_mr x) ^ n)"
  apply transfer
  apply simp
  done

lemma equal_mod_ring_code[code]:
  "HOL.equal x y = HOL.equal (from_mr x) (from_mr y)"
  by transfer (simp add: equal_eq)

lemma divide_mod_ring_code[code abstract]:
  "from_mr (x div y) = (from_mr x * (if y = 0 then 0 else from_mr y ^ nat (mr_size x - 2))) mod mr_size x"
  apply (simp add: divide_mod_ring_def)
  apply transfer
  by (simp add: mod_mult_right_eq nat_minus_as_int)

lemma card_fin_prime: "prime LEN('a) \<Longrightarrow> CARD(('a prime) fin) = LEN('a)"
  by simp

lemma to_mr_numeral_post[code_post]: "to_mr (numeral x) = numeral x"
  apply (constrain 'a="'aa::nontriv")
  subgoal H[unconstrain_cases]
    apply transfer
    using zmod_int by force
  apply (rule H;simp add: class_axioms)
  apply (rule CARD_1_singleton)
  apply simp
  done

lemma to_mr_one_post[code_post]: "to_mr 1 = 1"
  apply transfer
  apply simp
  by (metis One_nat_def mod_0 mod_Suc of_nat_1
      zmod_int)

lemma to_mr_zero_post[code_post]: "to_mr 0 = 0"
  apply transfer
  by simp

value "(4 :: ((5 prime) fin) mod_ring) div 2"

lift_definition of_nat_mod_ring :: "nat \<Rightarrow> 'a::finite mod_ring" is
  "\<lambda>x. int (x mod (CARD('a)))" by simp


lift_definition to_nat_mod_ring :: "'a::finite mod_ring \<Rightarrow> nat" is
  "nat" .

lemma of_nat_mod_ring_code[code]:
  "from_mr (of_nat_mod_ring x :: ('a :: finite mod_ring)) = (int x) mod (CARD('a))"
  apply transfer
  using zmod_int by blast

lemma to_nat_mod_ring_code[code]:
  "to_nat_mod_ring x = nat (from_mr x)"
  apply transfer
  by simp

instantiation mod_ring :: (finite) enum begin
definition "enum_mod_ring == (map of_nat_mod_ring [0..<CARD('a)]) :: 'a mod_ring list"
definition "enum_all_mod_ring == (\<lambda>f. list_all (f o of_nat_mod_ring) [0..<CARD('a)]) :: ('a mod_ring \<Rightarrow> bool) \<Rightarrow> bool"
definition "enum_ex_mod_ring == (\<lambda>f. list_ex (f o of_nat_mod_ring) [0..<CARD('a)]) :: ('a mod_ring \<Rightarrow> bool) \<Rightarrow> bool"
instance
  apply standard
  subgoal H
     apply (simp add: enum_mod_ring_def )
     apply (rule UNIV_eq_I)
     apply transfer
     by (simp add: image_int_atLeastLessThan)
   
   subgoal
     apply (rule card_distinct)
     apply (simp add: H[symmetric])
     by (simp add: enum_mod_ring_def)
    apply (simp add: H)
    apply (simp add: enum_mod_ring_def enum_all_mod_ring_def)
   subgoal
     by (metis (full_types) Ball_set set_upt)
    apply (simp add: H)
   apply (simp add: enum_mod_ring_def enum_ex_mod_ring_def)
   by (metis (full_types) Bex_set comp_apply set_upt)
end

lift_definition 
  "SucZ" :: "'a::finite mod_ring \<Rightarrow> 'a::finite mod_ring" is
  "\<lambda>x. (x + 1) mod int (CARD('a))" by auto


lift_definition 
  "MaxZ" :: "'a::finite mod_ring" is
  "int (CARD('a)-1)" by auto

lemma SucZ_def2: "SucZ (x :: 'a ::finite mod_ring) = (if x = MaxZ then 0 else x + 1)"
  apply transfer
  by auto

lemma SucZ_code[code abstract]: "from_mr (SucZ (x :: 'a ::finite mod_ring))=
  (let i = from_mr x in if nat i = CARD('a)-1 then 0 else i + 1)"
  apply transfer
  apply clarsimp
  by (metis One_nat_def Suc_diff_1 add.commute int_nat_eq
      mod_self of_nat_Suc zero_less_card_finite)

instantiation mod_ring :: ("{finite,typerep}") full_exhaustive begin

function exhaustive_zint' ::
    "('a mod_ring \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option) \<Rightarrow> natural \<Rightarrow> 'a mod_ring  \<Rightarrow> (bool \<times> term list) option"
    where "exhaustive_zint' f d i = (if d < natural_of_nat (to_nat_mod_ring i) then None else 
    let j = SucZ i in if j = 0 then f (i, \<lambda>_. Code_Evaluation.term_of i)
    else (Quickcheck_Exhaustive.orelse (f (i, \<lambda>_. Code_Evaluation.term_of i)) (exhaustive_zint' f d j)))"
  by pat_completeness auto

termination
  apply (relation "measure (\<lambda>(_, d, i). nat_of_natural (d + 1 - natural_of_nat (to_nat_mod_ring i)))")
  apply clarsimp
   apply (clarsimp simp add: less_natural_def SucZ_def2)
  apply transfer
  by auto

definition full_exhaustive_mod_ring ::  
   "('a mod_ring \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
    \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option" where
  "full_exhaustive_mod_ring f d \<equiv> exhaustive_zint' f d 0"
instance ..
end

export_code "Quickcheck_Exhaustive.full_exhaustive :: ('a :: {typerep,finite} mod_ring \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
    \<Rightarrow> natural \<Rightarrow> (bool \<times> term list) option" in SML module_name ex

instantiation mod_ring :: ("{finite,typerep}") check_all begin
definition
  check_all_mod_ring :: "('a mod_ring \<times> (unit \<Rightarrow> term) \<Rightarrow> (bool \<times> term list) option)
    \<Rightarrow> (bool \<times> term list) option" where
  "check_all_mod_ring f \<equiv> Quickcheck_Exhaustive.full_exhaustive f (natural_of_nat (CARD('a)-1))"
definition enum_term_of_mod_ring :: "('a mod_ring) itself \<Rightarrow> unit \<Rightarrow> term list"
where
  "enum_term_of_mod_ring = (\<lambda>_ _. map Code_Evaluation.term_of (Enum.enum :: 'a mod_ring list))"
instance ..
end

instantiation mod_ring :: ("{finite,typerep}") random begin

context
  includes state_combinator_syntax
begin

definition random_mod_ring ::
  "natural \<Rightarrow> Random.seed \<Rightarrow> ('a mod_ring \<times> (unit \<Rightarrow> term)) \<times> Random.seed" where
  "random_mod_ring i \<equiv> Random.range (natural_of_nat (LEN('a))) \<circ>\<rightarrow> 
    (\<lambda>x. let j = of_nat_mod_ring (nat_of_natural x) in Pair (j,\<lambda>_. Code_Evaluation.term_of j))"

instance ..
end
end

experiment begin
lemma "x > 1 \<Longrightarrow> (x :: (3 fin) mod_ring) = y"
  quickcheck
  quickcheck [ random ]
  oops
end

end