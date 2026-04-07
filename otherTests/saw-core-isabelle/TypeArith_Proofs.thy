theory TypeArith_Proofs
imports "./isabelle/TypeArith"
begin

context includes cryptol_syntax begin

lemma "lg2_concrete_test"
  unfolding lg2_concrete_test_def
  by simp

lemma log2_nat_seq_less_inc_max[simp]: "log2_nat (to_nat (y :: ('a,bool) seq)) < 2 ^ LEN(1 + 'a)"
  apply (rule order.strict_trans2)
   apply (rule log2_nat_seq_less_max)
  by simp

lemma "lg2_valid`{'a} x"
  unfolding lg2_valid_def lg2_validlba_lt_2rb_def
            lg2_validlba_gteq_2rb_def
  supply [simp] = from_to_nat_seq[OF log2_nat_pow2_bound_strict, OF to_nat_seq_bound]
                  to_nat_seq_pow2[OF log2_nat_less_zext_inc]
  apply (constrain 'a="'b::len")
    subgoal H[unconstrain_cases] for y
    apply (simp add: cryptol_prim_defs)
    apply (intro impI conjI)
        apply (drule degenerate_bitseq[where 'a='b,simplified, of y])
        apply fastforce
       apply (rule to_nat_seq_inj)
       apply (simp del: len_of_sum_def len_of_alt_def)
      apply (rule to_nat_seq_inj)
      apply simp
      apply (rule log2_nat_pow2_exact[THEN iffD1])
      using log2_nat_pow2_suc_case
      by force
  by (rule H;simp)

lemma "type_width`{'a}"
  unfolding type_width_def width_val_def
            width_vallba_lt_2rb_def width_vallba_gteq_2rb_def
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases]
    apply (simp add: cryptol_prim_defs )
    apply (intro conjI impI)
     apply (cases "LENGTH('b) = 0"; cases "LENGTH('b) = 1";simp)
    apply (simp add: seq_len_suc[simplified len_of_alt_def2])
    by (simp add: from_nat_def)
  by (rule H;simp)

lemma "type_add`{'a,'b}"
  unfolding type_add_def
  by (simp add: cryptol_prim_defs)

lemma "type_mul`{'a,'b}"
  unfolding type_mul_def
  by (simp add: cryptol_prim_defs)

lemma "type_exp`{'a,'b}"
  unfolding type_exp_def
  by (simp add: cryptol_prim_defs)

lemma "PRED ('b \<le> 'a) \<Longrightarrow> type_sub`{'a,'b}"
  unfolding type_sub_def
  by (simp add: cryptol_prim_defs)

lemma "PRED('b \<ge> 1) \<Longrightarrow> type_div`{'a,'b}"
  unfolding type_div_def
  apply (simp add: cryptol_prim_defs)
  using zdiv_int by blast

lemma "PRED('b \<ge> 1) \<Longrightarrow> type_mod`{'a,'b}"
  unfolding type_mod_def
  apply (simp add: cryptol_prim_defs)
  using zmod_int by blast

lemma "type_min`{'a,'b}"
  unfolding type_min_def
  by (simp add: cryptol_prim_defs)

lemma "type_max`{'a,'b}"
  unfolding type_max_def
  by (simp add: cryptol_prim_defs)

lemma "type_lg2`{'a}"
  unfolding type_lg2_def
  apply (simp add: cryptol_prim_defs)
  by (metis from_int_seq_def from_nat_def
      from_to_nat_seq n_less_equal_power_2)

lemma "type_lits"
  unfolding type_lits_def
  by simp

end

end