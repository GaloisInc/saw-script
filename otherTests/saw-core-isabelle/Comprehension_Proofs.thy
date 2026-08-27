theory Comprehension_Proofs
imports "./isabelle/Comprehension"
begin

lemma le_div_helper: "0 \<le> i \<Longrightarrow>
    (i::int) < int (a :: nat) * int (b::nat) \<Longrightarrow> nat i mod b < b"
  by (metis leD mod_less_divisor mult_eq_0_iff
      of_nat_gt_0)


context includes cryptol_syntax begin

lemma n_m_product_def2: "n_m_product`{'a,'b} = product_seq (map_seq int upto_seq) (map_seq int upto_seq)"
  unfolding n_m_product_def
  apply simp
  apply (simp add: cryptol_prim_defs)
  apply (simp add: product_seq_def2)
  by (auto intro!: seq_all2_nthI)

lemma "product_valid`{'a,'b} i"
  unfolding product_valid_def n_m_product_def2
  apply (simp add: cryptol_prim_defs)
  apply (simp add: nat_less_iff)
  apply (clarsimp simp add: less_mult_imp_div_less nat_less_iff le_div_helper)
   using int_nat_eq zdiv_int zmod_int by presburger

lemma n_m_zip_def2: "n_m_zip`{'a,'b} = zip_seq (map_seq int upto_seq) (map_seq (\<lambda>x. x + 5) (map_seq int upto_seq))"
  unfolding n_m_zip_def
  by (simp add: cryptol_prim_defs)

lemma "zip_valid`{'a,'b} i"
  unfolding zip_valid_def n_m_zip_def2
  apply (clarsimp simp add: cryptol_prim_defs)
  apply (simp add: nat_less_iff)
  done

lemma "par_is_zip`{'a,'b::coercible_atom} x y"
  unfolding par_is_zip_def
  by simp

lemma n_m_combined_def2: "n_m_combined`{'a,'b} = zipWith_seq (\<lambda>(x,y) z. (x,y,int z)) (n_m_product`{'a,'b}) upto_seq"
  unfolding n_m_combined_def zipWith_seq_def n_m_product_def
  apply simp
  apply (simp add: cryptol_prim_defs)
  apply (simp add: coerce_seq[symmetric] del: coerce_seq)
  by (auto intro: seq.map_cong)

lemma "combined_valid`{'a,'b} i"
  unfolding combined_valid_def n_m_combined_def2 n_m_product_def2
  apply (simp add: cryptol_prim_defs)
  apply clarsimp
  apply (subst zipWith_seq_nth)
   apply (simp add: nat_less_iff)
  apply (simp add: product_seq_def2 concat_seq_nth nat_less_iff)
  apply (subst upto_seq_nth_f)
  apply (metis less_imp_diff_less less_mult_imp_div_less
      nat_less_iff of_nat_mult)
  apply (subst upto_seq_nth_f)
  using le_div_helper apply blast
  apply clarsimp
  by (simp add: minus_mod_eq_mult_div zdiv_int
      zmod_int)

lemma "seq_is_map_join`{'a,'b,'c::coercible_atom} x y"
  unfolding seq_is_map_join_def
  by (simp add: cryptol_prim_defs)


end

end