theory ZIntSeq
imports Bool_Class Fin Seq
begin

instantiation Exp :: (len2,len) len2 begin
instance
  apply standard
  apply (insert nontriv[where 'a='a])
  apply (insert len_gt_0[where 'a='b])
  unfolding len_of_Exp_def
  apply (rule one_less_power)
   apply simp+
  done
end

lemma pcr_mod_ring_def2: "pcr_mod_ring x y = (x = to_int_mod_ring y)"
  apply (simp add: pcr_mod_ring_def cr_mod_ring_def eq_OO)
  apply transfer
  by simp

lemma mod_ring_less_eq_transfer[transfer_rule]:
  "(pcr_mod_ring ===> pcr_mod_ring ===> (=)) (\<le>) (\<le>)"
  apply (rule rel_funI)+
  apply (simp add: pcr_mod_ring_def2)
  by (simp add: less_eq_mod_ring_def)

lemma mod_ring_less_transfer[transfer_rule]:
  "(pcr_mod_ring ===> pcr_mod_ring ===> (=)) (<) (<)"
  apply (rule rel_funI)+
  apply (simp add: pcr_mod_ring_def2)
  by (simp add: less_mod_ring_def)

lemma pcr_mod_ring_transfer: 
  "(pcr_mod_ring ===> (=) ===> (=)) pcr_mod_ring (=)"
  apply (rule rel_funI)+
  apply (simp add: pcr_mod_ring_def cr_mod_ring_def eq_OO)
  by (simp add: Rep_mod_ring_inject)

lemma nontriv_ofclass: "CARD('a) > 1 \<Longrightarrow> OFCLASS('a,nontriv_class)"
  apply standard
  apply simp
  done

lemma pcr_mod_ring_trivial:
  "\<not> Suc 0 < CARD('a) \<Longrightarrow> (CARD('a) = 1 \<Longrightarrow> x = 0) \<Longrightarrow> pcr_mod_ring x (y :: 'a :: finite mod_ring)"
  apply (simp add: pcr_mod_ring_def2)
  apply (subgoal_tac "CARD('a) = 1 \<or> CARD('a) = 0")
   apply (erule disjE)
  apply simp
    apply (simp add: CARD_1_singleton)+
  by (simp add: le_antisym)

lemma nontriv'[simp]: "Suc 0 < CARD('a::nontriv)"
  using nontriv_class.nontriv by auto


lemma numeral_mod_ring_transfer[transfer_rule]: 
  "((=) ===> pcr_mod_ring) (\<lambda>x. int (numeral x mod CARD('a))) (numeral :: num \<Rightarrow> 'a :: finite mod_ring)"
  apply (constrain 'a="'c::nontriv")
  subgoal H[unconstrain_cases]
      apply (rule rel_funI)+
  apply (simp add: pcr_mod_ring_def2)
  subgoal for x
    apply (induct x)
      apply simp
      apply (metis Suc_0_mod_card mod_by_Suc_0 zero_neq_one)
     apply (simp add: numeral.simps)
     apply (subst numeral_plus_numeral[symmetric])+
    apply (metis (no_types, opaque_lifting) int_ops(5)
          mod_add_eq to_int_mod_ring_add zmod_int)
    apply (simp add: numeral.simps)
    apply (subst numeral_plus_numeral[symmetric])+
    by (smt (verit, del_insts) One_nat_def add.commute
        add.right_neutral add_Suc_right mod_add_left_eq
        numeral_One of_nat_Suc of_nat_add of_nat_mod
        to_int_mod_ring_add
        to_int_mod_ring_hom.hom_one)
  done
  apply (rule H)
  apply (rule rel_funI)+
  by (rule pcr_mod_ring_trivial;simp)

lemma mod_ring_power_transfer[transfer_rule]:
  "(pcr_mod_ring ===> (=) ===> pcr_mod_ring) (\<lambda>x y. (x ^ y) mod int CARD('a::finite)) ((^):: 'a mod_ring \<Rightarrow> nat \<Rightarrow> 'a mod_ring)"
  apply (rule pow_mod_ring_transfer[unconstrain_cases])
  apply (rule rel_funI)+
  by (rule pcr_mod_ring_trivial;simp)


lemma mod_ring_transfer_1[transfer_rule]:
  "(pcr_mod_ring) (1 mod CARD('a)) (1:: 'a :: finite mod_ring)"
  apply (cases "CARD('a) > 1")
    apply simp
   apply (rule one_mod_ring.transfer[unconstrain_cases])
   apply simp
  by (rule pcr_mod_ring_trivial;simp)

lemma of_bool_seq_induct: "(\<And>y. P (map_seq of_bool y)) \<Longrightarrow> P (x :: ('a,'b :: bool) seq)"
  by (metis of_bool_of_comp
      seq.map_comp seq.map_id)
declare CARD_fin[simp]


type_synonym 'n Zpow2 = "(2^'n) Z"
type_notation Zpow2 (\<open>(\<open>notation=\<open>postfix\<close>\<close>_ Z\<^sup>2)\<close> [100]) 
translations
  (type) "'n Z\<^sup>2" \<leftharpoondown> (type) "(2^'n) fin mod_ring"

definition zint_to_list :: "'n Z\<^sup>2 \<Rightarrow> ('b::bool) list" where
  "zint_to_list \<equiv> \<lambda>(w :: 'n Z\<^sup>2). map of_bool (bin_to_bl LEN('n) (to_int_mod_ring w))"

definition list_to_zint :: "('b::bool) list \<Rightarrow> 'n Z\<^sup>2" where
  "list_to_zint \<equiv> \<lambda>(bs :: 'b list). (of_int_mod_ring (bl_to_bin (map bool_of bs)) :: 'n Z\<^sup>2)"

definition eq_zint_list :: "'n Z\<^sup>2 \<Rightarrow> ('b::bool) list \<Rightarrow> bool" where
  "eq_zint_list zi s \<equiv> zint_to_list zi = s"

lift_definition zint_to_seq :: "'n Z\<^sup>2 \<Rightarrow> ('n,'b::bool) seq" is
  "zint_to_list"
  unfolding zint_to_list_def
  using size_bin_to_bl by auto

lift_definition seq_to_zint :: "('n,'b::bool) seq \<Rightarrow> 'n Z\<^sup>2" is
  "list_to_zint"
  .

definition eq_zint_seq :: "'n Z\<^sup>2 \<Rightarrow> ('n,'b::bool) seq \<Rightarrow> bool" where
  "eq_zint_seq zi s \<equiv> zint_to_seq zi = s"

lemma eq_zint_def2: "eq_zint_seq zi s = (zint_to_list zi = seq_to_list s)"
  apply (simp add: eq_zint_seq_def)
  apply transfer
  by simp

lemma zint_take_bit_eqI:
  "take_bit LEN('n) (to_int_mod_ring r) = take_bit LEN('n) (to_int_mod_ring s) \<Longrightarrow>  ((r :: 'n Z\<^sup>2) = s)"
  apply transfer
  apply simp
  by (metis take_bit_int_eq_self_iff)

lemma zint_take_bit_less_eqI:
  "take_bit LEN('n) (to_int_mod_ring r) \<le> take_bit LEN('n) (to_int_mod_ring s) \<Longrightarrow>  ((r :: 'n Z\<^sup>2) \<le> s)"
  apply transfer
  apply simp
  by (metis take_bit_int_eq_self_iff)

lemma zint_take_bit_lessI:
  "take_bit LEN('n) (to_int_mod_ring r) < take_bit LEN('n) (to_int_mod_ring s) \<Longrightarrow>  ((r :: 'n Z\<^sup>2) < s)"
  apply transfer
  apply simp
  by (metis take_bit_int_eq_self_iff)

lemma seq_zint_quot: "Quotient (=)  zint_to_seq (seq_to_zint :: ('n,'a::bool) seq \<Rightarrow>'n Z\<^sup>2) eq_zint_seq"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule QuotientI;simp?)
    apply transfer
    apply (simp del: bin_to_bl_def)
     apply (subst to_int_mod_ring_of_int_mod_ring)
  
       apply (simp add: bl_to_bin_ge0)
      apply (simp del: bin_to_bl_def)
      apply (metis bl_to_bin_lt2p length_map)
  
  apply (metis bl_bin_bl length_map list.map_comp
      list.map_id of_bool_of_comp)
  subgoal
    apply transfer
    apply (rule iffI)
     apply simp
    apply (simp del: bin_to_bl_def)
    apply (rule zint_take_bit_eqI)
    by (metis bin_bl_bin)
  apply (simp add: eq_zint_seq_def[abs_def])
  done

lifting_update Seq.seq.lifting
locale seq_zint begin
context begin
qualified setup_lifting seq_zint_quot
end
end

lifting_forget seq_zint.seq.lifting

lemmas [transfer_domain_rule] = seq_zint.seq.domain
lemmas [simp] = seq_zint.seq.domain

lemmas [transfer_rule] = seq_zint.seq.rel_eq_transfer
                         seq_zint.seq.right_total
                         seq_zint.seq.right_unique
  
lemma take_bit_lex_order: "length x = length y \<Longrightarrow>
            lex_list_order x y =
           (take_bit (length x) (bl_to_bin x)
            \<le> take_bit (length y) (bl_to_bin y))"
  apply (induct x y rule: list_induct2)
   apply simp
  subgoal for x xs y ys
    apply (cases x; cases y;simp add: bl_to_bin_def)
    by (smt (verit, best) bl_to_bin_aux_alt
        bl_to_bin_def bl_to_bin_ge2p_aux
        bl_to_bin_lt2p_aux concat_bit_eq
        power.simps(2) ring_class.ring_distribs(2)
        take_bit_Suc take_bit_int_eq_self_iff
        trunc_bl2bin_len)+
  done

lemma take_bit_lex_order_lt: "length x = length y \<Longrightarrow>
           lex_list_order_strict x y =
           (take_bit (length x) (bl_to_bin x)
            < take_bit (length y) (bl_to_bin y))"
  unfolding lex_list_order_strict_def
  by (metis bl_bin_bl less_le_not_le
      order_le_imp_less_or_eq take_bit_lex_order
      trunc_bl2bin_len)

lemma lex_of_bool_order: "length a = length b \<Longrightarrow> lex_list_order  (map bool_of a) (map bool_of b) = (lex_list_order a b)"
  apply (induct a b rule: list_induct2)
   apply simp
  using bool_of_le nle_le by auto


lemma less_eq_as_int: "x \<le> y = (seq_to_zint (x :: ('a,'b::bool) seq) \<le> seq_to_zint y)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply transfer
  apply simp
  apply transfer
  apply simp
  by (metis length_map lex_of_bool_order take_bit_eq_mod
      take_bit_lex_order)

lemma lex_of_bool_order_strict: "length a = length b \<Longrightarrow> lex_list_order_strict (map bool_of a) (map bool_of b) = (lex_list_order_strict a b)"
  unfolding lex_list_order_strict_def
  apply (induct a b rule: list_induct2)
   apply simp
  by (metis length_Cons lex_list_order.nle_le
      lex_of_bool_order)


lemma less_as_int: "x < y = (seq_to_zint (x :: ('a,'b::bool) seq) < seq_to_zint y)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply transfer
  apply simp
  apply transfer
  apply simp
  by (metis length_map lex_of_bool_order_strict
      take_bit_lex_order_lt take_bit_eq_mod)



lemma zint_to_bs_transfer[transfer_rule]:                                                 
  "(pcr_mod_ring ===> pcr_seq (=)) (\<lambda>i. map of_bool (bin_to_bl LEN('a) i)) (zint_to_seq :: 'a Z\<^sup>2 \<Rightarrow> ('a, 'b::bool) seq)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply transfer
  by (simp add: pcr_mod_ring_def2 list.rel_eq)
  
lemma less_eq_seq_transfer[transfer_rule]: 
  "(eq_zint_seq ===> eq_zint_seq ===> (=)) (\<le>) (\<le>)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_zint_seq_def)
  apply (simp add: less_eq_as_int)
  apply transfer
  apply simp
  apply transfer
  apply (simp add: word_eqI_folds del: bin_to_bl_def)
  using bin_bl_bin take_bit_int_eq_self 
  by force

lemma less_seq_transfer[transfer_rule]: 
  "(eq_zint_seq ===> eq_zint_seq ===> (=)) (<) (<)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_zint_seq_def)
  apply (simp add: less_as_int)
  apply transfer
  apply simp
  apply transfer
  apply (simp add: word_eqI_folds del: bin_to_bl_def)
  using bin_bl_bin take_bit_int_eq_self 
  by force

lemma bs_to_zint_inj: "seq_to_zint y = seq_to_zint x \<Longrightarrow> x = y"
  by (simp add: dual_order.eq_iff less_eq_as_int)

lemma bs_to_zint_inj'[simp]: "inj seq_to_zint"
  by (simp add: bs_to_zint_inj injI)

lemma zero_transfer_seq[transfer_rule]: 
  "eq_zint_seq 0 (0 :: ('a,'b::bool) seq)"
  apply (simp add: eq_zint_seq_def)
  apply transfer
  using bin_to_bl_zero by force


instantiation seq :: (_, bool) comm_ring begin
interpretation seq_zint .

lift_definition plus_seq :: 
  "('a,'b::bool) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq" is "(+)" .

lift_definition minus_seq :: 
  "('a,'b::bool) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq" is "(-)" .

lift_definition times_seq :: 
  "('a,'b::bool) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'b) seq" is "(*)" .

lift_definition uminus_seq :: "('a,'b::bool) seq \<Rightarrow> ('a,'b) seq" is "\<lambda>x. -x" .

instance
  apply (standard;transfer;simp?)
    apply (simp add: mult.assoc)
   apply (simp add: mult.commute)
  by (simp add: distrib_left mult.commute)
end




instantiation seq :: (_, bool) one begin
context includes  seq_zint.seq.lifting begin
lift_definition one_seq :: "('a,'b::bool) seq" is "1 :: 'a Z\<^sup>2" .
end
instance ..
end

instantiation seq :: (_, bool) comm_monoid_mult begin
context includes  seq_zint.seq.lifting begin
instance
  apply standard
  apply transfer
  apply transfer
  by force
end
end

instantiation seq :: (_, bool) numeral begin
instance
  by (standard;transfer;simp)
end

lemma zint_to_bs_distrib[simp]: "zint_to_seq (x + y) = (zint_to_seq x) + (zint_to_seq y)"
  by (simp add: plus_seq.abs_eq)

lemma zint_to_bs_1[simp]: "zint_to_seq 1 = 1"
  by (simp add: one_seq.abs_eq)


instantiation seq :: (len, bool) comm_ring_1 begin
instance
  by (standard;transfer;simp)
end

lemma bool_ofclass_triv: "OFCLASS('b::bool, bool_class)"
  by standard

(* Same trick as before, we can drop the nontriv constraint from the transfer
   rule, despite the "numeral" constant having a "nontriv" constraint for mod_ring. 
   This follows because eq_zint_seq is trivially satisfied for 0-length sequences. *)
lemma numeral_seq_int_transfer[transfer_rule]: 
  "((=) ===> eq_zint_seq) (numeral :: num \<Rightarrow> 'a Z\<^sup>2) numeral"
  apply (constrain 'a="'g::len")
  subgoal H[unconstrain_cases]
    apply (rule rel_funI)
    apply (simp add: eq_zint_seq_def )
    subgoal for x
      apply (induct x)
        apply simp

      apply (simp add: numeral.simps)
      apply (subst numeral_plus_numeral[symmetric])+
      apply (subst zint_to_bs_distrib)
      apply simp

      apply (simp add: numeral.simps)
      apply (subst numeral_plus_numeral[symmetric])+
      apply (subst zint_to_bs_distrib)+
      apply simp
      done
    done
  apply (rule H)
  apply (rule rel_funI)+
  apply (simp add: eq_zint_seq_def)
  done

experiment  begin
lemma "(19 :: (4,bool) seq) = 3"
  apply transfer (* to Zint *)
  apply transfer (* to int *)
  by simp
end

lemma 
  bs_to_from_zint[simp]:
  "seq_to_zint ((zint_to_seq y) :: ('n,'b::bool) seq) = y"
  using Quotient_rep_abs seq_zint_quot
  by fastforce

lemma zint_to_from_bs[simp]:
  "zint_to_seq (seq_to_zint x) = x"
  by (simp add: bs_to_zint_inj)

lemma seq_one_neq_zero: "LEN('n) > 0 \<Longrightarrow> (1 :: ('n,bool) seq) \<noteq> 0"
  apply (constrain 'n="'c::len")
  subgoal H[unconstrain_cases] by simp
  by (rule H;simp)

lemma zint_power_transfer[transfer_rule]: "(eq_zint_seq ===> (=) ===> eq_zint_seq) (^) (^)"
  apply (constrain 'a="'g::len")
  subgoal H[unconstrain_cases]
    by transfer_prover
  apply (rule H)
  apply (rule rel_funI)+
  by (simp add: eq_zint_seq_def)

lemma to_int_zint_trivial[simp]:
  "LEN('a) = 0 \<Longrightarrow> to_int (x :: 'a Z\<^sup>2) = 0"
  by (simp add:
      Integral.to_int_mod_ring_def
      zint_take_bit_eqI)

lemma zint_bound_minus_one[simp]: "(x :: 'a Z\<^sup>2) \<le> - 1"
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases]
    by (transfer;simp)
  apply (rule H)
  by (simp add: zint_take_bit_less_eqI)

lemma zint_pos[simp]: "0 \<le> (x :: 'a Z\<^sup>2)"
  by (transfer;simp)

context includes Seq.seq.lifting begin
lift_definition
  zth_seq :: "('a,'b) seq \<Rightarrow> 'a Z \<Rightarrow> 'b" is
  "\<lambda>(xs :: 'b list) i. nth_list xs (nat i)" .
end

lemma zth_seq_transfer[transfer_rule]: 
  assumes A:"(LEN('a) = 0 \<Longrightarrow> A (oob_list_elem []) (oob_list_elem []))"
  shows "(pcr_seq A ===> pcr_mod_ring ===> A) (\<lambda>xs i. nth_list xs (nat i)) (zth_seq :: ('a,'b) seq \<Rightarrow> 'a Z \<Rightarrow> 'b)"
  apply (rule rel_funI)+
  apply (simp add: pcr_seq_def pcr_mod_ring_def relcompp_apply cr_mod_ring_def cr_seq_def)
  apply (insert A)
  apply transfer
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] by (fastforce simp add: list_all2_lengthD list_all2_nthD2 nat_less_iff)
  apply (rule H;assumption?)
  by simp

lemma zth_seq_transfer_len[transfer_rule]: 
  "(pcr_seq A ===> pcr_mod_ring ===> A) (\<lambda>xs i. nth_list xs (nat i)) (zth_seq :: ('a::len,'b) seq \<Rightarrow> 'a Z \<Rightarrow> 'b)"
  apply (rule zth_seq_transfer)
  by simp

instantiation seq :: (_,_) not_bool begin
definition "is_bool0_seq (_ :: ('a,'b) seq itself) \<equiv> False"
instance by (rule not_bool_class[OF is_bool0_seq_def])
end
interpretation not_bool_code "TYPE(('a,'b) seq)" .

end