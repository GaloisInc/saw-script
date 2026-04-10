theory Sequences_Proofs
  imports "./isabelle/Sequences"
begin

context includes cryptol_syntax begin

lemmas test_defs =
  drop_append_def
  groupBy_map_def
  join_append_def
  join_split_def
  split_groupBy_def
  split_join_def
  take_append_def
  take_drop_append_def
  join_map_def

lemma "drop_append`{'front,'back,'a::coercible_atom} x y"
  unfolding test_defs
  by (simp add: cryptol_prim_defs)

lemma "groupBy_map`{'parts,'each,'a::cryptol_ring} x"
  unfolding test_defs
  apply (simp add: cryptol_prim_defs)
  apply (simp add: group_seq_def2)
  by (simp add: nat_plus_as_int)

lemma "join_append`{'parts,'each,'a::cryptol_ring} x y"
  unfolding test_defs
  by (simp add: cryptol_prim_defs append_seq_def)

lemma "join_split`{'parts,'each,'a::cryptol_ring} x"
  unfolding test_defs
  by (simp add: cryptol_prim_defs)

lemma "split_join`{'parts,'each,'a::cryptol_ring} x"
  unfolding test_defs
  by (simp add: cryptol_prim_defs)

lemma "take_append`{'front,'back,'a::coercible_atom} x y"
  unfolding test_defs
  by (simp add: cryptol_prim_defs)

lemma "LEN('m) \<le> LEN('n) \<Longrightarrow> take_drop_append`{'n,'m,'a::coercible_atom} x"
  unfolding test_defs
  by (simp add: cryptol_prim_defs)

lemma "join_map`{'n,'m,'a::cryptol_ring} x"
  unfolding test_defs
  apply (simp add: cryptol_prim_defs)
  apply (simp add: concat_seq_as_map)
  by (metis (no_types, opaque_lifting) minus_mod_eq_div_mult
      of_nat_mult pos_nat_simps(2) zdiv_int zmod_int)

lemma "transpose_rectangle`{'n,'m,'a::coercible_atom} x"
  unfolding transpose_rectangle_def
  apply (simp add: cryptol_prim_defs)
  by (simp add: transpose_seq_def)

lemma "reverse_nth`{'n,'a::coercible_atom} x i"
  unfolding reverse_nth_def
  apply (simp add: cryptol_prim_defs)
  apply (clarsimp simp: rev_seq_nth)
  by (simp add: nat_minus_as_int)

lemma "LEN('n) > 0 \<Longrightarrow> head_0th`{'n,'a::coercible_atom} x"
  unfolding head_0th_def
  by (simp add: cryptol_prim_defs)

lemma "LEN('n) > 0 \<Longrightarrow> tail_is_drop`{'n,'a::coercible_atom} x"
  unfolding tail_is_drop_def
  by (simp add: cryptol_prim_defs)

lemma "LEN('n) > 0 \<Longrightarrow> last_nth`{'n,'a::coercible_atom} x"
  unfolding last_nth_def
  apply (simp add: cryptol_prim_defs)
  by (simp add: nat_minus_as_int)

lemma "map_upto`{'n,'a::coercible_atom} x"
  unfolding map_upto_def
  by (simp add: cryptol_prim_defs)

lemma "append_upto`{'n,'m,'a::coercible_atom} x y"
  unfolding append_upto_def
  apply (simp add: cryptol_prim_defs cong: if_cong)
  apply (simp add: append_seq_as_map)
  using nat_minus_as_int 
  by presburger


lemma "bang_is_end`{'n,'a::coercible_atom} x y"
  unfolding bang_is_end_def
  apply (clarsimp simp: nth_end_seq_def2)
  apply (simp add: cryptol_prim_defs)
  using nat_diff_distrib' by force

lemma "selects_as_map`{'n,'k,'a::coercible_atom} x y"
  unfolding selects_as_map_def
  by (clarsimp simp: selects_seq_def2)

lemma "selects_end_as_map`{'n,'k,'a::coercible_atom} x y"
  unfolding selects_end_as_map_def
  by (clarsimp simp: selects_end_seq_def2)

lemma "update_as_map`{'n,'a::coercible_atom} xs x ix"
  unfolding update_as_map_def
  apply (clarsimp simp: cryptol_prim_defs seq_update_def2)
  by (fastforce intro: upto_seq_cong)

lemma "update_end_as_map`{'n,'a::coercible_atom} xs x ix"
  unfolding update_end_as_map_def
  apply (clarsimp simp: cryptol_prim_defs seq_update_end_def seq_update_def2)
  by (fastforce intro: upto_seq_cong)

lemma "updates_as_foldl`{'n,'k,'a::coercible_atom} x y ixs"
  unfolding updates_as_foldl_def
  apply (clarsimp simp: cryptol_prim_defs seq_updates_def2 foldl_seq_map)
  by (fastforce intro: foldl_seq_cong)

lemma "updatesEnd_as_foldl`{'n,'k,'a::coercible_atom} x y ixs"
  unfolding updatesEnd_as_foldl_def
  apply (clarsimp simp: cryptol_prim_defs seq_updates_def2 
                        seq_updates_end_def seq_update_end_def foldl_seq_map)
  by (fastforce intro: foldl_seq_cong)

lemma "rotater_as_map`{'n,'a::coercible_atom} x i"
  unfolding rotater_as_map_def
  apply (simp add: cryptol_prim_defs)
  apply (rule seq_eq_nthI)
  by (simp)

lemma "rotatel_as_map`{'n,'a::coercible_atom} x i"
  unfolding rotatel_as_map_def
  apply (simp add: cryptol_prim_defs)
  apply (rule seq_eq_nthI)
  by (simp add: add.commute)

lemma "shiftl_as_map`{'n,'a::{zero,coercible_atom}} x i"
  unfolding shiftl_as_map_def
  apply (clarsimp simp add: cryptol_prim_defs)
  apply (rule seq_eq_nthI)
  by (auto simp add: left_shift_seq_nth add.commute nat_plus_as_int)

lemma "shiftr_as_map`{'n,'a::{zero,coercible_atom}} x i"
  unfolding shiftr_as_map_def
  apply (clarsimp simp add: cryptol_prim_defs)
  apply (rule seq_eq_nthI)
  by (auto simp add: right_shift_seq_nth nat_minus_as_int)

lemma "shift_r_l_neg`{'n,'a::{zero,coercible_atom}} x i"
  unfolding shift_r_l_neg_def
  apply (clarsimp simp add: cryptol_prim_defs)
  by (simp add: left_shift_neg)


lemma 
  "LEN('k) < LEN('n) \<Longrightarrow> foldl_valid`{'n,'k,'a::coercible_atom, 'b::coercible_atom} f a bs"
  unfolding foldl_valid_def
  apply (clarsimp simp add: cryptol_prim_defs)
  apply transfer
  apply simp
  by (metis append_take_drop_id foldl_append)

lemma "LEN('k) < LEN('n) \<Longrightarrow> foldr_valid`{'n,'k,'a::coercible_atom, 'b::coercible_atom} f a bs"
  unfolding foldr_valid_def
  apply (clarsimp simp add: cryptol_prim_defs)
  apply transfer
  apply simp
  by (metis append_take_drop_id foldr_append)

lemma len_plus_one[transfer_rule]: "LEN(1 + 'k) = Suc (LEN('k))"
  by simp

lemma len_append:
  "LEN('k) < LEN('n) \<Longrightarrow> LEN(1 + 'n) = LEN('k) + LEN(1 + 'n - 'k)"
  by simp

lemma butlast_seq_transfer[transfer_rule]: "(pcr_seq R ===> pcr_seq R) List.butlast (Sequences.butlast`{'k,'b::coercible_atom})"
  unfolding Sequences.butlast_def
  apply (clarsimp simp add: cryptol_prim_defs)
  apply (rule rel_funI)+
  apply (simp add: pcr_seq_def cr_seq_def relcompp_apply)
  apply transfer
  by (simp add: butlast_conv_take list_all2_lengthD)

lemma last_list_nth: "length xs = k + 1 \<Longrightarrow> last xs = xs ! k"
  by (metis add_diff_cancel_right' add_is_0 last_conv_nth
      list.size(3) zero_neq_one)

lemma 
  assumes k_lt_n: "LEN('k) < LEN('n)"
  shows "scanl_valid`{'n,'k,'a::coercible_atom, 'b::coercible_atom} f a bs"
  unfolding scanl_valid_def
  supply [transfer_rule] = len_append[OF k_lt_n]
  apply (insert k_lt_n)
  apply (clarsimp simp add: cryptol_prim_defs Let_def)
  apply transfer
  apply simp
  subgoal for f a bs
    apply (subst append_take_drop_id[where xs=bs and n="LEN('k)", symmetric])
    apply (simp only: scanl_list_append)
    by (auto simp: last_list_nth)
  done


lemma 
  assumes k_lt_n: "LEN('k) < LEN('n)"
  shows "scanr_valid`{'n,'k,'a::coercible_atom, 'b::coercible_atom} f a bs"
  unfolding scanr_valid_def
  supply [transfer_rule] = len_append[OF k_lt_n]
  apply (insert k_lt_n)
  apply (simp add: cryptol_prim_defs Let_def)
  apply transfer
  apply simp
  subgoal for f a bs
    apply (subst append_take_drop_id[where xs="bs" and n="LEN('k)", symmetric])
    apply (simp only: scanr_list_append)
    by (auto simp: last_list_nth rev_drop hd_conv)
  done

lemma "sum_as_fold`{'n,'a::cryptol_ring} x"
  unfolding sum_as_fold_def
  apply simp
   apply transfer
  by (simp add: foldl_eq_foldr sum_list.eq_foldr)

lemma "product_as_fold`{'n,'a::cryptol_ring} x"
  unfolding product_as_fold_def
  apply simp
   apply transfer
  by (simp add: product_list_def)

lemma foldl_as_list_all: "foldl (\<lambda>a b. a \<and> f b) b x = (list_all f x \<and> b)"
  apply (induct x arbitrary: b;auto)
  done

lemma foldr_as_list_all: "foldr (\<lambda>b a. a \<and> f b) x b = (list_all f x \<and> b)"
  by (induct x arbitrary: b rule: rev_induct; auto)

lemma "all_as_fold`{'n,'a::coercible_atom} f x"
  unfolding all_as_fold_def
  apply simp
  apply (rule conjI)
   apply transfer
   apply (simp add: foldl_as_list_all)
  apply transfer
  apply (simp add: foldr_as_list_all)
  done

lemma "zipWith_as_map`{'n,'a::coercible_atom,'b::coercible_atom,'c::coercible_atom} f xs ys"
  unfolding zipWith_as_map_def fromToLessThan_def
  apply clarsimp
  apply (simp add: zipWith_seq_def)
  apply (rule seq_eq_nthI)
  by simp

end

end