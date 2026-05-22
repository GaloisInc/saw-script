theory WordSeq
  imports ZIntSeq Word_Lib.Reversed_Bit_Lists Log2
begin

lift_definition zint_to_word :: "'n Z\<^sup>2 \<Rightarrow> ('n::len) word" is
  "\<lambda>(zi :: 'n Z\<^sup>2). (to_int_mod_ring zi)" .

lift_definition word_to_zint :: "('n::len) word \<Rightarrow> 'n Z\<^sup>2" is
  "\<lambda>(w :: int). ((of_int_mod_ring w) :: 'n Z\<^sup>2)"
  apply transfer
  apply simp
  using no_bintr_alt1 by auto

context includes seq_zint.seq.lifting begin
lift_definition word_to_seq :: "'n word \<Rightarrow> ('n::len,'b::bool) seq" is
  "word_to_zint" .

lift_definition seq_to_word :: "('n::len,'b::bool) seq \<Rightarrow> 'n word" is
  "zint_to_word" .
end

definition eq_word_seq :: "'n word \<Rightarrow> ('n::len,'b::bool) seq  \<Rightarrow> bool" where
  "eq_word_seq x y \<equiv> word_to_seq x = y"

lemma take_bit_of_to_mod_ring:
  "to_int_mod_ring ((of_int_mod_ring x) :: 'a Z\<^sup>2) = (take_bit LEN('a) x)"
  apply transfer
  apply simp
  using take_bit_int_def by presburger

lemma eq_word_seq_def2: "eq_word_seq x y = ((uint x) = (to_int_mod_ring (seq_to_zint y)))"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (simp add: eq_word_seq_def word_to_seq.abs_eq)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: bin_to_bl_def)
  by (metis bin_bl_bin bl_bin_bl bool_of_bool_comp
      length_map list.map_comp list.map_id of_bool_of_comp
      size_bin_to_bl)

lemma map_of_to_bool: "(map bool_of (seq_to_list (map_seq of_bool y))) = seq_to_list y"
  apply transfer
  apply simp
  done

lemma eq_word_seq_of_bool[simp]: "eq_word_seq x (map_seq of_bool y) = eq_word_seq x y"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (simp add: eq_word_seq_def2)
  by (simp add: seq_to_zint.rep_eq map_of_to_bool)

lemma eq_word_seq_bool_of[simp]: "eq_word_seq x (map_seq bool_of y) = eq_word_seq x y"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (simp add: eq_word_seq_def2)
  by (simp add: seq_to_zint.rep_eq map_seq_def)

lemma eq_word_seq_def3: "eq_word_seq x y = ((seq_to_word y) = x)"
  apply (simp add: eq_word_seq_def)
  apply transfer
  apply transfer
  apply transfer
  apply simp
  by (metis no_bintr_alt1 take_bit_int_eq_self)

lemma eq_word_seq_rt[transfer_rule]: "right_total eq_word_seq"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule right_totalI)
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring)
  by fastforce


lemma word_to_from_zint[simp]:
  "zint_to_word (word_to_zint x) = x"
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring)
  done

lemma zint_to_from_word[simp]:
  "word_to_zint (zint_to_word x) = x"
  apply transfer
  apply simp
  done

lemma word_to_from_seq[simp]: "seq_to_word (word_to_seq (x :: 'n word) :: ('n::len,'b :: bool) seq) = x"
  apply transfer
  by auto

lemma word_to_zint_def2: "word_to_zint x = of_int_mod_ring (uint x)"
  by (metis Word_eq_word_of_int word_of_int_uint
      word_to_zint.abs_eq)

lemma bl_bin_bl': "n = length bs \<Longrightarrow> bin_to_bl n (bl_to_bin bs) = bs"
  using bl_bin_bl by auto

lemma seq_to_from_word[simp]: "word_to_seq (seq_to_word (x :: ('n::len,'b :: bool) seq)) = (map_seq (\<lambda>i. of_bool (bool_of i)) x)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (simp add: seq_to_word.rep_eq seq_to_zint.rep_eq zint_to_word.abs_eq
                   word_to_zint_def2
                   word_to_seq.abs_eq zint_to_seq.abs_eq del: bin_to_bl_def)
  apply (simp add: take_bit_of_to_mod_ring del: bin_to_bl_def)
  apply transfer
  apply (simp del: bin_to_bl_def)
  apply (subst bl_bin_bl')
   apply simp+
  done

lemma of_bool_ident[simp]: "(\<lambda>i. of_bool (bool_of i)) = (\<lambda>i. i)"
  apply simp
  done

lemmas seq_to_from_word' = seq_to_from_word[where 'a="'a::bool" and 'b="'a::bool",simplified of_bool_ident seq.map_ident ]

lemma eq_word_seq_lt: "left_total (eq_word_seq :: 'n word \<Rightarrow> ('n::len,'b::bool) seq => bool)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule left_totalI)
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply simp
  subgoal for y
    apply (rule exI[of _ "map of_bool (bin_to_bl LENGTH('n) y)"])
    by (simp del: bin_to_bl_def)
  done


lemma eq_word_seq_ru: "right_unique (eq_word_seq :: 'n word \<Rightarrow> ('n::len, 'b::bool) seq \<Rightarrow> bool)"
  apply (rule right_uniqueI)
  apply (simp add: eq_word_seq_def3)
  apply transfer
  by (metis zint_to_from_word)

lemma eq_word_seq_lu: "left_unique (eq_word_seq :: 'n word \<Rightarrow> ('n::len,'b::bool) seq \<Rightarrow> bool)"
  apply (rule left_uniqueI)
  by (simp add: eq_word_seq_def3)

lemma eq_word_seq_bu: "bi_unique (eq_word_seq :: 'n word \<Rightarrow> ('n::len,'b::bool) seq \<Rightarrow> bool)"
  by (simp add: bi_unique_alt_def
      eq_word_seq_lu eq_word_seq_ru)

lemma eq_word_seq_bt: "bi_total (eq_word_seq :: 'n word \<Rightarrow> ('n::len,'b::bool) seq \<Rightarrow> bool)"
  by (simp add: bi_total_alt_def eq_word_seq_lt
      eq_word_seq_rt)

lemma map_to_from_word_seq:
  "map_seq seq_to_word (map_seq (word_to_seq :: ('n word \<Rightarrow> ('n::len,'b::bool) seq)) x) = x"
  by simp

lemma map_from_to_word_seq:
  "map_seq (word_to_seq :: ('n word \<Rightarrow> ('n::len,'b::bool) seq)) (map_seq seq_to_word x) = x"
  by simp

lemma eq_word_seq_rel_transfer[transfer_rule]: "(eq_word_seq ===> eq_word_seq ===> (=)) (=) (=)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def3)
  by (metis seq_to_from_word')

lemma bs_to_zint_transfer[transfer_rule]:
  "(eq_zint_seq ===> pcr_mod_ring) to_int_mod_ring seq_to_zint"
  apply (rule rel_funI)+
  by (simp add: pcr_mod_ring_def2 eq_zint_seq_def)

lemma 
  numeral_seq_word_transfer[transfer_rule]:
  "((=) ===> eq_word_seq) numeral (numeral :: num \<Rightarrow> ('a::len, 'b::bool) seq)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply transfer
  apply simp
  by (metis take_bit_eq_mod uint_bintrunc
      unsigned_numeral)

lemma plus_seq_word_transfer[transfer_rule]: 
  "(eq_word_seq ===> eq_word_seq ===> eq_word_seq) (+) (+)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply transfer
  apply simp
  by (metis take_bit_add take_bit_eq_mod)

lemma minus_seq_word_transfer[transfer_rule]: 
  "(eq_word_seq ===> eq_word_seq ===> eq_word_seq) (-) (-)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply transfer
  apply simp
  by (metis take_bit_diff take_bit_eq_mod)

lemma times_seq_word_transfer[transfer_rule]: 
  "(eq_word_seq ===> eq_word_seq ===> eq_word_seq) (*) (*)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply transfer
  apply simp
  by (metis take_bit_mult take_bit_eq_mod)

lemma uminus_seq_word_transfer[transfer_rule]: 
  "(eq_word_seq ===> eq_word_seq) uminus uminus"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply transfer
  apply simp
  by (metis add.inverse_neutral bintrunc_bintrunc
      less_le_not_le take_bit_minus take_bit_minus_small_eq
      verit_la_disequality)

context includes seq_zint.seq.lifting begin
lift_definition ucast_seq :: "('n,'b::bool) seq \<Rightarrow> ('m,'b::bool) seq" 
  is "\<lambda>x. of_int_mod_ring (to_int_mod_ring x)" .
end

lemma ucast_seq_word_transfer[transfer_rule]: 
  "(eq_word_seq ===> eq_word_seq) ucast ucast_seq"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  by (simp add: take_bit_of_to_mod_ring)



lemma seq_as_word_induct:
  "(\<And>(x :: 'n :: len word). P (word_to_seq x)) \<Longrightarrow> P (w :: ('n,'b::bool) seq)"
  by (metis seq_to_from_word')

lemma word_as_seq_induct:
  "(\<And>(x :: ('n::len,'b::bool) seq). P (seq_to_word x)) \<Longrightarrow> P (w :: 'n word)"
  by (metis word_to_from_seq)

named_theorems word_seq_convs \<open>Rewrite rules for converting seq primitives into word primitives\<close>

lemmas [word_seq_convs] = map_from_to_word_seq map_to_from_word_seq

definition word_compr :: "('e_in \<Rightarrow> bool) \<Rightarrow> ('len, 'e_in) seq \<Rightarrow> ('len::len) word" where
  "word_compr f s \<equiv> seq_to_word (map_seq f s)"

lemma map_seq_word_compr: "map_seq f w = word_to_seq ((word_compr f w) :: 'n :: len word)"
  by (simp add: word_compr_def)

context includes rotate_shift_syntax begin

lemma shiftl_is_push: 
  "shiftl_list 0 (bin_to_bl a w) n = bin_to_bl a (push_bit n w)"
  apply (rule nth_equalityI)
   apply (simp add: size_bin_to_bl_aux)
  subgoal for i
    apply (subgoal_tac "i < a")
    prefer 2
     apply (simp add: size_bin_to_bl_aux)
    apply (simp add: shiftl_list_nth del: zero_bool_def)
    by (simp add: Nat.le_diff_conv2
        bit_push_bit_iff_int
        nth_bin_to_bl_aux
        size_bin_to_bl_aux)
  done

lemma list_as_int: 
  "(\<And>(y :: int). P (bin_to_bl (length xs) y)) \<Longrightarrow>  P (xs :: bool list)"
  apply (induct xs)
   apply simp
  apply simp
  by (metis bin_to_bl_aux.Suc bin_to_bl_def bl_bin_bl
      length_Suc_conv)

lemma 
  push_is_shiftl:
  "length x = a \<Longrightarrow> take_bit a (bl_to_bin (shiftl_list 0 x ya)) = take_bit a (push_bit ya (bl_to_bin x))"
  apply (induct x rule:list_as_int)
  by (metis bin_bl_bin bl_bin_bl shiftl_is_push size_bin_to_bl)

lemmas bool_of_zero = bool_of_0

lemma map_shiftl_list[simp]: "map f (shiftl_list pad y ya) = shiftl_list (f pad) (map f y) ya"
  by (simp add: shiftl_list_def drop_map)

lemma map_shiftr_list[simp]: "map f (shiftr_list pad y ya) = shiftr_list (f pad) (map f y) ya"
  by (simp add: shiftr_list_def take_map)

lemmas [simp] = rotate_map rotater_map


lemma shiftl_word_list_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) shiftl (shiftl_seq 0)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: zero_bool_def)
  apply (subst push_is_shiftl)
   apply simp
  by (metis push_bit_of_int word_ubin.norm_eq_iff)


lemma shiftr_is_drop_take: 
  "shiftr_list 0 (bin_to_bl a w) n = bin_to_bl a (drop_bit n (take_bit a w))"
  apply (rule nth_equalityI)
   apply (simp add: size_bin_to_bl_aux)
  subgoal for i
    apply (subgoal_tac "i < a")
    prefer 2
     apply (simp add: size_bin_to_bl_aux)
    apply (simp add: shiftr_list_nth del: zero_bool_def)
    apply (rule conjI)
    by (auto simp: nth_bin_to_bl_aux bin_nth_shiftr bit_take_bit_iff size_bin_to_bl_aux add.commute)
  done

lemma drop_take_is_shiftr:
  "length x = a \<Longrightarrow> 
    take_bit a (bl_to_bin (shiftr_list 0 x ya)) = 
      take_bit a (drop_bit ya (take_bit a (bl_to_bin x)))"
  apply (induct x rule:list_as_int)
  by (metis bin_bl_bin bl_bin_bl shiftr_is_drop_take size_bin_to_bl)

lemma shiftl_word_seq_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) shiftr (shiftr_seq 0)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: zero_bool_def)
  apply (subst drop_take_is_shiftr;simp)
  done

lemma right_shift_word_list_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) right_shift right_shift"
  apply (simp add: right_shift_def[abs_def] cong: if_cong del: zero_bool_def)
  by transfer_prover

lemma left_shift_word_list_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) (<<) (<<)"
  apply (simp add: left_shift_def[abs_def])
  by transfer_prover

lemma word_to_seq_transfer[transfer_rule]: "((=) ===> eq_word_seq) (\<lambda>x. x) word_to_seq"
  apply (rule rel_funI)+
  by (simp add: eq_word_seq_def)

lemma seq_to_word_transfer[transfer_rule]: "(eq_word_seq ===> (=)) (\<lambda>x. x) seq_to_word"
  apply (rule rel_funI)
  by (simp add: eq_word_seq_def)

lemma word_left_shift_seq[word_seq_convs]: "w << n = word_to_seq ((seq_to_word w) << n)"
  apply transfer
  by (transfer;simp)

lemma word_right_shift_seq[word_seq_convs]: "w >> n = word_to_seq ((seq_to_word w) >> n)"
  by (transfer;simp)

lemma rotate_word_list_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) (\<lambda>x y. word_rotl y x) rotatel_seq"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: word_rotl_eq eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring  del: bin_to_bl_def)
  by (metis bin_bl_bin bl_bin_bl length_map rotate_map
      size_bin_to_bl)

lemma rotater_word_list_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) (\<lambda>x y. word_rotr y x) rotater_seq"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: word_rotr_eq eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: bin_to_bl_def)
  by (metis bin_bl_bin bl_bin_bl length_map rotater_map
      size_bin_to_bl)

lemma right_rotate_word_list_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) (>>>) (>>>)"
  apply (simp add: right_rotate_def[abs_def] cong: if_cong)
  by transfer_prover

lemma left_rotate_word_list_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) (<<<) (<<<)"
  apply (simp add: left_rotate_def[abs_def])
  by transfer_prover

lemma word_left_rotate_seq[word_seq_convs]: "w <<< n = word_to_seq (seq_to_word w <<< n)"
  by (transfer;simp)

lemma word_right_rotate_seq[word_seq_convs]: "w >>> n = word_to_seq (seq_to_word w >>> n)"
  by (transfer;simp)

end (* rotate_shift_syntax *)

context includes Seq.seq.lifting begin

lift_definition word_split_seq :: "(('parts::len) * ('each::len)) word \<Rightarrow> ('parts, ('each word)) seq" is
  "word_rsplit" 
  apply (subst length_word_rsplit_exp_size')
  apply (simp add: word_size)
  using given_quot_alt by blast

end

lemma take_bit_idx: "length s = n \<Longrightarrow> n > 0 \<Longrightarrow>
           (\<And>i. i < n \<Longrightarrow>
                 (rev s) ! i = w !! i) \<Longrightarrow>
           take_bit n (bl_to_bin s) =
           take_bit n w"
  by (meson bin_eqI bin_nth_of_bl
      nth_bintr)

lemma nth_mod_seq_word_transfer:
  "(eq_word_seq ===> (=) ===> (=)) (\<lambda>(w :: 'n :: len word) i. of_bool ((to_bl w) ! (i mod LEN('n)))) nth_mod_seq"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring nth_mod_list_def  del: bin_to_bl_def)
  apply (intro conjI impI)
  apply (metis (mono_tags, opaque_lifting) bl_bin_bl
      bool_of_zero len_gt_0 length_map mod_less_divisor
      nth_map to_bl_eq to_bl_of_bin uint_word_of_int_eq
      zero_bool_def zero_or_one)
  by (metis bin_bl_bin bl_bin_bl bool_of_eq_0 len_gt_0
      length_map mod_less_divisor nth_map
      size_bin_to_bl)


lemma eq_word_seq_domain[simp]: "Domainp eq_word_seq s"
  apply (rule DomainPI[of _ _ "word_to_seq s"])
  apply (simp add: eq_word_seq_def)
  done

lemma nth_equality_mod_eqI:
  "(\<And>i. x ! (i mod n) = y ! (i mod n)) \<Longrightarrow> length x = n \<Longrightarrow> length y = n \<Longrightarrow> x = y"
  by (metis mod_less nth_equalityI)

lemma eq_word_seq_nth_modI: 
  "(\<And>i. bool_of (nth_mod_seq s (i mod LENGTH('n))) =  ((to_bl w) ! (i mod LENGTH('n)))) \<Longrightarrow> eq_word_seq (w :: 'n :: len word) s"
  apply (simp add: eq_word_seq_def)
  supply [transfer_rule] = nth_mod_seq_word_transfer
  apply transfer
  apply simp
  apply (drule nth_equality_mod_eqI)
    apply simp+
  done


lemma eq_word_seq_nthI: 
  "(\<And>i. i < LENGTH('n) \<Longrightarrow> bool_of (nth_seq s i) =  ((to_bl w) ! i)) \<Longrightarrow> eq_word_seq (w :: 'n :: len word) s"
  apply (rule eq_word_seq_nth_modI)
  by (simp add: nth_seq_def2)

context begin

private lemma mul_helper1: "a > 0 \<Longrightarrow> x < a \<Longrightarrow> (((a - x) * (b ::nat)) + (b * x)) = a * b"
  by (metis add.commute distrib_left
      le_add_diff_inverse le_eq_less_or_eq
      mult.commute)
  
private lemma mul_helper2: "a > 0 \<Longrightarrow> x < a \<Longrightarrow> a * b - ((a - x) * (b ::nat)) = (b * x)"
  by (metis add_diff_cancel_left' mul_helper1)


private lemma mul_helper3:
  "y < a \<Longrightarrow> (a * b - (a - (Suc y)) * (b::nat)) = (b * (Suc y))"
  apply (simp)
  apply (cases "y + 1 = a")
  apply clarsimp
  apply (subst mul_helper2)
    apply simp+
  done

private lemma mul_helper4: "y < a \<Longrightarrow>
    ya < b \<Longrightarrow>
    \<not> a * b + ya - b < a * b - (b + b * (y::nat)) \<Longrightarrow>
    b * y + ya =
    a * b + ya - (b + (a * b - (b + b * y)))"
  apply (induct y rule: nat_less_induct)
  by (simp add: less_le_mult_nat
      mult.commute)


private lemma group_list_helper: "length x = a * b \<Longrightarrow>
    y < a \<Longrightarrow>
    ya < b \<Longrightarrow>
    (x ! (y * b + ya)) =
    (replicate
      ((a - (Suc y)) * b)
      pad @
     take
      (a * b -
       (a - (Suc y)) * b)
      (x)) !
    ((a - Suc 0) * b + ya)"
  apply (simp add: mul_helper3)
  apply (subst nth_append)
  apply clarsimp
  apply (intro impI conjI)
  
  apply (metis (no_types, lifting) One_nat_def
      add_diff_inverse_nat add_lessD1
      diff_Suc_less mult.commute
      nat_mult_less_cancel_disj not_less_eq
      plus_1_eq_Suc)
  by (simp add:  mult.commute right_diff_distrib' mul_helper4)
  
private lemma of_bl_to_bl_helper: "length x = LENGTH('a) \<Longrightarrow> of_bl x = (i :: 'a::len word) \<Longrightarrow> to_bl i = x"
  by (simp add: to_bl_use_of_bl)

private lemma word_split_seq_as_group': 
  "((eq_word_seq :: ('a::len \<times> 'b::len) word \<Rightarrow> ('a\<times>'b,bool) seq \<Rightarrow> bool) ===> seq_all2 eq_word_seq) word_split_seq group_seq"
  supply [simp del] = zero_bool_def 
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: group_seq_def2)
  apply (rule seq_all2_nthI;simp?)
  apply (rule eq_word_seq_nthI)
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring  del: bin_to_bl_def)
  apply (clarsimp split: nth_list_splits)
  apply (intro impI conjI)
  subgoal for x i y ia
    supply [simp] = source_size_def target_size_def word_size nth_rev
    apply (subst word_rsplit_upt[where n="LENGTH('a)"];simp)
    apply (subst ucast_down_drop[where n="(LENGTH('a)-1) * (LENGTH('b))"];simp)
    subgoal by (simp add: mult_eq_if)
    apply (subst bl_shiftr;simp)
    apply (fold zero_bool_def)
    apply (subst group_list_helper[where pad=0];assumption?)
    by (metis (no_types, opaque_lifting) bin_bl_bin bl_bin_bl
        len_of_alt_def len_of_prod_def to_bl_to_bin
        word_bl_Rep')
  (* out of bounds cases *)
    apply (meson leD parts_each_bound)
   apply (simp add: length_word_rsplit_size size_word.rep_eq)
  apply (metis linorder_not_le parts_each_bound)
  done


private lemma group_seq_of_bool_of: "group_seq = (\<lambda>xs. (map_seq (map_seq of_bool)) (group_seq (map_seq bool_of xs)))"
  apply (rule ext)
  by (simp add: group_seq_map)



lemma word_split_seq_as_group[transfer_rule]: 
  "((eq_word_seq :: ('a::len \<times> 'b::len) word \<Rightarrow> ('a\<times>'b,'c::bool) seq \<Rightarrow> bool) ===> seq_all2 eq_word_seq) word_split_seq group_seq"
  apply (subst group_seq_of_bool_of)
  apply (rule rel_funI)+
  apply (subst (asm) eq_word_seq_bool_of[symmetric])
  apply (insert word_split_seq_as_group'[where 'a='a and 'b='b])
  apply (drule(1) rel_funD)
  apply (simp add: seq_all2_map2)
  done

end

lemma pcr_seq_eq_rev:
  "(seq_all2 (=) ===> pcr_seq (=) ===> (=)) (\<lambda>x y. pcr_seq (=) y x) (=)"
  apply (rule rel_funI)+
  apply transfer
  apply transfer
  by (auto simp add: list.rel_eq)

lemma seq_split_word[word_seq_convs]: "map_seq seq_to_word (group_seq (w :: ('a::len \<times> 'b::len, 'c::bool) seq)) = word_split_seq (seq_to_word w)"
  supply [transfer_rule] = pcr_seq_eq_rev map_seq_weaken
  apply transfer
  apply simp
  apply (simp add: pcr_seq_def3)
  apply transfer
  apply (simp add: nth_mod_list_def)
  apply (rule context_conjI)
   apply (simp add: length_word_rsplit_exp_size' word_size given_quot_alt)
  by simp


lemma word_split_seq[word_seq_convs]: 
  "group_seq (word_to_seq w :: ('a::len \<times> 'b ::len,'c::bool) seq) = map_seq word_to_seq (word_split_seq w)"
  apply (induct w rule: word_as_seq_induct)
  by (simp add: seq_split_word[symmetric] group_seq_map)

context includes Seq.seq.lifting begin
lift_definition join_words_seq :: "('parts, ('each word)) seq \<Rightarrow> (('parts::len) * ('each::len)) word" is
  "word_rcat" .
end

lemma word_split_join[simp]: "(word_split_seq (join_words_seq ws)) = ws"
  apply transfer
  by (simp add: word_rsplit_rcat_size word_size)

lemma join_words_seq[word_seq_convs]: 
   "concat_seq ws = word_to_seq (join_words_seq (map_seq seq_to_word ws))"
  apply (rule seqs_eqI;simp?)
  by (simp add: word_seq_convs)

lemma eq_word_seqI: "word_to_seq w = s \<Longrightarrow> eq_word_seq w s"
  by (simp add: eq_word_seq_def)  

lemma seq_all2_eq_word[simp]: "seq_all2 eq_word_seq y x \<Longrightarrow> map_seq word_to_seq y = x"
  apply (simp add: eq_word_seq_def[abs_def])
  apply (rule seq_eq_nthI)
  using seq_all2_nthD by fastforce

lemma seq_all2_eq_seq[simp]: "seq_all2 eq_word_seq y x \<Longrightarrow> map_seq seq_to_word x = y"
  apply (simp add: eq_word_seq_def[abs_def])
  apply (rule seq_eq_nthI)
  apply (drule(1) seq_all2_nthD)
  apply simp
  by (metis word_to_from_seq)

lemma join_words_seq_as_concat[transfer_rule]: 
    "(seq_all2 (eq_word_seq :: 'a :: len word \<Rightarrow> ('a,bool) seq \<Rightarrow> bool) ===> eq_word_seq) 
         join_words_seq (concat_seq :: ('b::len, ('a, bool) seq) seq \<Rightarrow> ('b \<times> 'a, bool) seq)"
  apply (rule rel_funI)+
  apply (rule eq_word_seqI)
  by (simp add: word_seq_convs)

context includes seq_zint.seq.lifting begin
lift_definition signed_shift_nat :: "('a,'b::bool) seq \<Rightarrow> nat \<Rightarrow> ('a,'b::bool) seq" is
  "\<lambda>(w :: 'a Z\<^sup>2) n. of_int_mod_ring (drop_bit n (signed_take_bit (LEN('a) - Suc 0) (to_int_mod_ring w)))"
  .
end

lemma signed_shift_nat_word_transfer[transfer_rule]:
  "(eq_word_seq ===> (=) ===> eq_word_seq) sshiftr signed_shift_nat"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring bin_sbin_eq_iff')
  apply transfer
  by force

(* negative signed right shift is just left shift (which is negative unsigned right shift) *)
definition signed_shift :: "('a,'b::bool) seq \<Rightarrow> int \<Rightarrow> ('a,'b::bool) seq" (infixl \<open>>>$\<close> 55) where
  "signed_shift w idx \<equiv> if idx \<ge> 0 then signed_shift_nat w (nat idx) else right_shift w idx"


lemma signed_shift_transfer[transfer_rule]:
 "(eq_word_seq ===> (=) ===> eq_word_seq) 
   (\<lambda>w i. if i \<ge> 0 then sshiftr w (abs_nat i) else shiftl w (abs_nat i))  
   signed_shift"
  apply (simp add: signed_shift_def[abs_def] right_shift_def[abs_def] del: zero_bool_def cong:if_cong)
  by transfer_prover


lemma signed_shift_conv1[word_seq_convs]: 
  "seq_to_word (s >>$ i) = (if i \<ge> 0 then sshiftr (seq_to_word s) (abs_nat i) else shiftl (seq_to_word s) (abs_nat i))"
  unfolding signed_shift_def
  apply transfer
  by (simp add: right_shift_def)

lemma signed_shift_conv2[word_seq_convs]: 
  "(word_to_seq s) >>$ i = word_to_seq (if i \<ge> 0 then sshiftr s (abs_nat i) else shiftl s (abs_nat i))"
  apply (induct s rule: word_as_seq_induct[where 'b='b])
  apply (subst signed_shift_conv1[symmetric])
  by simp


(* Using native mod_ring division is only defined if the cardinality is prime, which
   is more restrictive than word division, so we need to perform the division
   as integers. *)
instantiation seq :: (_,bool) divide begin
context includes seq_zint.seq.lifting begin
lift_definition divide_seq :: "('a, 'b::bool) seq \<Rightarrow> ('a, 'b) seq \<Rightarrow> ('a, 'b) seq" is 
  "\<lambda>x y. of_int_mod_ring (to_int_mod_ring x div to_int_mod_ring y)" .
end
instance ..
end

lemma div_seq_transfer[transfer_rule]:
 "(eq_word_seq ===> eq_word_seq ===> eq_word_seq) (div) (div)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  by (simp add: take_bit_of_to_mod_ring)

lemma seq_to_word_div[word_seq_convs]: 
  "seq_to_word (x div y) = (seq_to_word x) div (seq_to_word y)"
  by (transfer;simp)

lemma word_to_seq_div[word_seq_convs]: 
  "(word_to_seq x) div y = word_to_seq (x div (seq_to_word y))"
  apply (induct x rule: word_as_seq_induct[where 'b='b])
  apply (subst seq_to_word_div[symmetric])
  by simp

instantiation seq :: (_,bool) modulo begin
context includes seq_zint.seq.lifting begin
lift_definition modulo_seq :: "('a, 'b) seq \<Rightarrow> ('a, 'b) seq \<Rightarrow> ('a, 'b) seq" is 
  "\<lambda>x y. of_int_mod_ring (to_int_mod_ring x mod to_int_mod_ring y)" .
end
instance ..
end

lemma mod_seq_transfer[transfer_rule]:
 "(eq_word_seq ===> eq_word_seq ===> eq_word_seq) (mod) (mod)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  by (simp add: take_bit_of_to_mod_ring bin_sbin_eq_iff')

lemma seq_to_word_mod[word_seq_convs]: 
  "(x mod y) = word_to_seq ((seq_to_word x) mod (seq_to_word y))"
  by (transfer;simp)

definition msb_int :: "nat \<Rightarrow> int \<Rightarrow> bool" where
  "msb_int n x \<equiv> (take_bit n x) !! (n - 1)"

lift_definition msb_zint :: "'a Z\<^sup>2 \<Rightarrow> bool" is
  "msb_int (LEN('a))" .

instantiation seq :: (_,bool) msb begin
context includes seq_zint.seq.lifting begin
lift_definition msb_seq :: "('a, 'b) seq \<Rightarrow> bool" is
  "msb_zint" .
end
instance ..
end

lemma msb_is_bit_zero: "take_bit a (x::int) =
           take_bit a (y::int) \<Longrightarrow>
           a > 0 \<Longrightarrow>
           bin_to_bl a x ! 0 =
           msb_int a y"
  unfolding msb_int_def
  apply (subst nth_bin_to_bl)
   apply simp+
  apply (subst nth_bintr)
  apply simp
  by (metis sbintrunc_bintruncS0
      signed_take_bit_negative_iff)

lemma hd_conv:"length x \<noteq> 0 \<Longrightarrow> hd x = x ! 0"
  by (cases x;simp)
  

lemma msb_seq_transfer[transfer_rule]:
 "(eq_word_seq ===> (=)) (msb) (msb)"
  apply (simp add: word_msb_alt[abs_def])
  apply (rule rel_funI)
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: len_of_alt_def2 del: bin_to_bl_def)
  apply (subst hd_conv)
   apply (subst size_bin_to_bl)
   apply simp
  apply transfer
  subgoal for x y
    by (auto simp add: msb_is_bit_zero[where y=y] simp del:bin_to_bl_def)
  done

lemma msb_int_resp: "take_bit a x = take_bit a y \<Longrightarrow> msb_int a x = msb_int a y"
  by (simp add: msb_int_def)


instantiation seq :: (_,bool) abs begin
context includes seq_zint.seq.lifting begin
lift_definition abs_seq :: "('a, 'b) seq \<Rightarrow> ('a, 'b) seq" is
  "\<lambda>x. if msb_zint x then (-x) else  x" .
end
instance ..
end

lemma abs_seq_def2: "abs (s :: ('a,'b::bool) seq) = (if msb s then (-s) else s)"
  apply transfer
  by (auto simp add: msb_int_def)

lemma abs_seq_transfer[transfer_rule]:
 "(eq_word_seq ===> eq_word_seq) (abs) (abs)"
  apply (simp add:  word_abs_msb[abs_def] abs_seq_def2[abs_def])
  by transfer_prover

lemma seq_to_word_abs[word_seq_convs]: 
  "seq_to_word (abs x) = abs (seq_to_word x)"
  by (transfer;simp)

lemma word_to_seq_abs[word_seq_convs]: 
  "abs (word_to_seq x) = word_to_seq (abs x)"
  apply (induct x rule: word_as_seq_induct[where 'b='b])
  apply (subst seq_to_word_abs[symmetric])
  by simp

lemma bit_agree: "take_bit a (x :: int) = take_bit a (y :: int) \<Longrightarrow> n < a \<Longrightarrow> x !! n = y !! n"
  by (metis bit_take_bit_iff)

lemma signed_take_bit_rsp: "a > 0 \<Longrightarrow>
  take_bit a x =
       take_bit (a::nat) y \<Longrightarrow>
       signed_take_bit (a - Suc 0) (x::int) =
       signed_take_bit (a - Suc 0) y"
    apply (cases "msb_int a x")
     apply (subst signed_take_bit_eq_if_negative)
      apply (simp add: msb_int_def) 
    
      apply (metis nth_bintr)
     apply (subst signed_take_bit_eq_if_negative)
        apply (simp add: msb_int_def)
      apply (metis nth_bintr)
    apply (metis bintrunc_bintrunc_ge
        diff_le_self)
    apply (simp add: msb_int_def)
    apply (subst signed_take_bit_eq_if_positive)
      apply (simp add: nth_bintr)
      apply (simp add: bit_agree)

    apply (subst signed_take_bit_eq_if_positive)
      apply (simp add: nth_bintr)
     apply (simp add: bit_take_bit_iff)
    using diff_le_self take_bit_tightened
    apply blast
    done

definition sint_int :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "sint_int n x \<equiv> if n > 0 then signed_take_bit (n - 1) x else 0"

lift_definition sint_zint :: "'n Z\<^sup>2 \<Rightarrow> int" is
  "sint_int LEN('n)" .

context includes seq_zint.seq.lifting begin
lift_definition sint_seq :: "('a,'b::bool) seq \<Rightarrow> int" is "sint_zint" .
lift_definition uint_seq :: "('a,'b::bool) seq \<Rightarrow> int" is to_int_mod_ring .
lift_definition of_int_seq :: "int \<Rightarrow> ('a,'b::bool) seq" is of_int_mod_ring .
end



lemma sint_seq_transfer[transfer_rule]:
 "(eq_word_seq ===> (=)) (sint) (sint_seq)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply transfer
  apply (simp add: sint_int_def)
  apply (rule signed_take_bit_rsp)
   apply simp
  apply transfer
  apply simp
  by fastforce

instantiation seq :: (_,bool) integral begin
definition "to_int_seq == uint_seq :: ('a, 'b) seq \<Rightarrow> int"
definition "to_sint_seq == sint_seq :: ('a, 'b) seq \<Rightarrow> int"
definition "from_int_seq == of_int_seq :: int \<Rightarrow> ('a, 'b) seq"
instance
  supply [simp] = to_int_mod_ring_bound
  apply standard
  apply (simp_all add: to_int_seq_def from_int_seq_def)
  by (transfer;simp)+
end
lemmas [simp] = to_int_seq_def to_sint_seq_def from_int_seq_def


instantiation seq :: (_,bool) signed_modulo begin
definition signed_modulo_seq :: "('a,'b::bool) seq \<Rightarrow> ('a,'b::bool) seq \<Rightarrow> ('a,'b::bool) seq"  where
  "signed_modulo_seq x y \<equiv> of_int_seq ((sint_seq x) smod (sint_seq y))"
instance ..
end

lemma of_int_seq_transfer_word[transfer_rule]: "((=) ===> eq_word_seq) of_int of_int_seq"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  by (simp add: take_bit_of_to_mod_ring)

lemma signed_mod_transfer[transfer_rule]:
 "(eq_word_seq ===> eq_word_seq ===> eq_word_seq) (smod) (smod)"
  unfolding signed_modulo_seq_def smod_word_def
  by transfer_prover

lemma seq_to_zint_uint_transfer[transfer_rule]: "(eq_word_seq ===> pcr_mod_ring) uint seq_to_zint"
  apply (rule rel_funI)+
  by (simp add: pcr_mod_ring_def2 eq_word_seq_def2)

lemma eq_word_seq_of_int[simp]: "eq_word_seq (word_of_int x) (of_int_seq x)"
  apply (simp add: eq_word_seq_def2)
  apply transfer
  by (simp add: uint_word_of_int_eq)

lemma signed_mod_conv[word_seq_convs]: 
  "x smod y = word_to_seq ((seq_to_word x) smod (seq_to_word y))"
  apply transfer
  apply simp
  done

instantiation seq :: (_,bool) signed_divide begin
definition signed_divide_seq :: "('a,'b::bool) seq \<Rightarrow> ('a,'b::bool) seq \<Rightarrow> ('a,'b::bool) seq"  where
  "signed_divide_seq x y \<equiv> of_int_seq ((sint_seq x) sdiv (sint_seq y))"
instance ..
end

lemma signed_div_transfer[transfer_rule]:
 "(eq_word_seq ===> eq_word_seq ===> eq_word_seq) (sdiv) (sdiv)"
  unfolding signed_divide_seq_def sdiv_word_def
  by transfer_prover

lemma signed_div_conv[word_seq_convs]: 
  "x sdiv y = word_to_seq ((seq_to_word x) sdiv (seq_to_word y))"
  apply transfer
  apply simp
  done

instantiation seq :: (_,bool) signedCmp begin
definition signed_lt_seq :: "('a, 'b) seq \<Rightarrow> ('a, 'b) seq \<Rightarrow> bool" where
  "signed_lt_seq x y \<equiv> sint_seq x < sint_seq y"
definition signed_le_seq :: "('a, 'b) seq \<Rightarrow> ('a, 'b) seq \<Rightarrow> bool" where
  "signed_le_seq x y \<equiv> sint_seq x \<le> sint_seq y"
instance ..
end

interpretation signed: linorder "\<lambda>(x :: ('a,'b::bool) seq) y. x <=$ y" "\<lambda>x y. x <$ y"
  apply (simp add: signed_lt_seq_def signed_le_seq_def)
  apply (standard;transfer;simp)
  subgoal by auto
  subgoal
    apply transfer
    apply (clarsimp simp add: bin_sbin_eq_iff' sint_int_def split: if_splits)
    by (metis bintrunc_sbintruncS0
        take_bit_int_eq_self)
  by auto

lemma signed_lt_transfer[transfer_rule]:
 "(eq_word_seq ===> eq_word_seq ===> (=)) (<s) signed_lt"
  unfolding signed_lt_seq_def word_sless_alt
  by transfer_prover

lemma signed_le_transfer[transfer_rule]:
 "(eq_word_seq ===> eq_word_seq ===> (=)) (\<le>s) signed_le"
  unfolding signed_le_seq_def word_sle_eq
  by transfer_prover

lemma signed_lt_conv[word_seq_convs]: 
  "x <$ y = ((seq_to_word x) <s (seq_to_word y))"
  apply (simp add: word_sless_alt)
  apply transfer
  apply (simp add: word_sless_alt)
  done

lemma signed_le_conv[word_seq_convs]: 
  "x <=$ y = ((seq_to_word x) \<le>s (seq_to_word y))"
  apply (simp add: word_sle_eq)
  apply transfer
  apply (simp add: word_sle_eq)
  done

lemma uint_seq_transfer[transfer_rule]: "(eq_word_seq ===> (=)) uint uint_seq"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  by simp


lemma word_to_seq_of_int_transfer: "(pcr_word ===> eq_word_seq) of_int word_to_seq"
  apply (rule rel_funI)+
  by (simp add: eq_word_seq_def3 pcr_word_def cr_word_def eq_OO)

lemma plus_seq_conv[word_seq_convs]: "(x + y) = word_to_seq (seq_to_word x + seq_to_word y)"
  apply transfer
  apply simp
  done

lemma minus_seq_conv[word_seq_convs]: "(x - y) = word_to_seq (seq_to_word x - seq_to_word y)"
  apply transfer
  apply simp
  done

lemma div_seq_conv[word_seq_convs]: "(x div y) = word_to_seq (seq_to_word x div seq_to_word y)"
  apply transfer
  apply simp
  done


lemma uint_seq_conv[word_seq_convs]: "uint_seq x = uint (seq_to_word x)"
  apply transfer
  apply simp
  done

lemma eq_seq_conv[word_seq_convs]: "(x = y) =  (seq_to_word x = seq_to_word y)"
  apply transfer
  apply simp
  done


lemma nth_end_seq_as_bl[transfer_rule]: 
  "(eq_word_seq ===> (=) ===> (=)) (\<lambda>w i. nth_end_list (to_bl w) i) (nth_end_seq :: ('n::len,bool) seq \<Rightarrow> nat \<Rightarrow> bool)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: bin_to_bl_def)
  by (metis bin_bl_bin bl_bin_bl size_bin_to_bl)

lemma nth_end_list_to_bit_word:
  "nth_end_list (to_bl w) i = (if i < LENGTH('a) then (w :: 'a :: len word) !! (LENGTH('a) - Suc (LENGTH('a) - Suc i)) else oob_list_elem (rev (to_bl w)))"
  apply (simp add: word_size nth_end_list_def)
  apply (subst to_bl_nth)
  apply (simp add: word_size)
  apply (simp add: word_size)
  done

lemma nth_end_seq_to_bit_word[word_seq_convs]:
  "nth_end_seq (s :: ('a::len,bool) seq) i = (if i < LENGTH('a) then (seq_to_word s) !! (LENGTH('a) - Suc (LENGTH('a)- Suc i)) else oob_seq_elem (rev_seq s))"
  supply [transfer_rule] = nth_end_seq_as_bl
  apply (clarsimp)
  apply (intro conjI impI)
  apply transfer
   apply (subst nth_end_list_to_bit_word)
   apply simp
  by (simp add: nth_end_seq_def2)

lemma takefill_same': "length xs = n \<Longrightarrow> takefill fill n xs = xs"
  by force

lemma word_of_bl: "(word_of_int (bl_to_bin xs) :: 'a::len word) = of_bl xs"
  apply transfer
  apply simp
  done

lemma list_to_seq_to_word[abs_def, word_seq_convs]:
  "(list_to_seq bs :: ('n::len ,bool) seq)= word_to_seq (of_bl (list_len (LENGTH('n)) bs))"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (simp add: word_to_seq.abs_eq)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: bin_to_bl_def)
  by (metis bl_bin_bl list_len_length)

lemma uint_seq_pos[simp]:"uint_seq w \<ge> 0"
  apply transfer
  apply transfer
  by simp

lemma pos_nat_seq[simp]: "pos_nat (s :: ('a,bool) seq) = to_nat s"
  by (simp add: pos_nat_def to_nat_def)

lemma pos_nat_word[simp]: "pos_nat (s :: 'a::len word) = to_nat s"
  by (simp add: pos_nat_def to_nat_def)

lemma to_nat_seq_to_word[abs_def, word_seq_convs]:"to_nat w = to_nat (seq_to_word w)"
  apply (simp add: pos_nat_def to_nat_def)
   apply transfer
  by simp

lemma to_nat_unat[simp]: "to_nat (w :: 'a::len word) = unat w"
  by (simp add: to_nat_def)

lemma power_word_transfer[transfer_rule]:
 "(eq_word_seq ===> (=) ===> eq_word_seq) power power"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply transfer
  apply simp
  by (metis no_bintr_alt1 power_mod)

lemma power_word_conv[abs_def, word_seq_convs]:
  "x ^ y = word_to_seq ((seq_to_word x) ^ y)"
  by (transfer;simp)
  

lemma numeral_seq_word_conv[abs_def, word_seq_convs]:
  "numeral x = word_to_seq (numeral x)"
  supply [transfer_rule] = word_to_seq_of_int_transfer
  apply transfer
  apply transfer
  apply simp
  done


lemma times_seq_conv[word_seq_convs]: "(x * y) = word_to_seq (seq_to_word x * seq_to_word y)"
  by (transfer;simp)

lemma  seq_to_word_int_list_transfer:
  "(pcr_seq (=) ===> pcr_word) (\<lambda>l. take_bit (LENGTH('a::len)) (bl_to_bin (map bool_of l))) 
   (seq_to_word :: ('a,'b::bool) seq \<Rightarrow> 'a word)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: seq_to_word.rep_eq)
  apply (simp add: pcr_word_def cr_word_def eq_OO pcr_seq_def cr_seq_def relcompp_apply list.rel_eq)
  apply (simp add: zint_to_word.abs_eq seq_to_zint.rep_eq)
  apply transfer
  apply simp
  by (simp add: no_bintr_alt1)

lemma word_int_to_seq_list_transfer:
  "(pcr_word ===> pcr_seq (=)) (\<lambda>i. map of_bool (bin_to_bl LENGTH('a) i))
   (word_to_seq :: 'a word \<Rightarrow> ('a::len,'b::bool) seq)"
  supply [simp] = zint_to_list_def list_to_zint_def
  supply [simp del] = bin_to_bl_def
  apply (rule rel_funI)+
  apply (simp add: word_to_seq.abs_eq)
  apply (simp add: pcr_word_def cr_word_def eq_OO pcr_seq_def cr_seq_def relcompp_apply list.rel_eq)
  apply (simp add: word_to_zint_def2 zint_to_seq.abs_eq)
  by (simp add: uint_word_of_int_eq)

lemma word_to_seq_list_transfer:
  "((=) ===> pcr_seq (=)) (\<lambda>w. map of_bool (to_bl w))
   (word_to_seq :: 'a word \<Rightarrow> ('a::len,'b::bool) seq)"
  supply [simp] = zint_to_list_def list_to_zint_def
  supply [simp del] = bin_to_bl_def
  apply (rule rel_funI)+
  apply (simp add: word_to_seq.abs_eq)
  apply (simp add: pcr_word_def cr_word_def eq_OO pcr_seq_def cr_seq_def relcompp_apply list.rel_eq)
  by (simp add: word_to_zint_def2 zint_to_seq.abs_eq to_bl_def)

lemma seq_to_word_list_transfer:
  "(pcr_seq (=) ===> (=)) (\<lambda>bl. (of_bl (map bool_of bl)))
   (seq_to_word :: ('a::len,'b::bool) seq \<Rightarrow> 'a word)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: seq_to_word.rep_eq)
  apply (simp add: pcr_word_def cr_word_def eq_OO pcr_seq_def cr_seq_def relcompp_apply list.rel_eq)
  apply (simp add: zint_to_word.abs_eq seq_to_zint.rep_eq)
  apply transfer
  apply simp
  by (simp add: no_bintr_alt1)

context notes seq_to_word_list_transfer[transfer_rule] and word_to_seq_list_transfer[transfer_rule] begin

lemma zip_seq_as_bl_zip:
  "zip_seq x y = list_to_seq (zip (map of_bool (to_bl (seq_to_word x))) (map of_bool (to_bl (seq_to_word y))))"
  supply [transfer_rule] = seq_to_word_list_transfer
  apply transfer
  apply simp
  by (metis length_map list.map_comp list.map_id
      of_bool_of_comp size_bin_to_bl to_bl_eq
      to_bl_use_of_bl)

lemma and_seq_conv[word_seq_convs]:
 "(\<lambda>x y. map2_seq ((\<and>) :: bool \<Rightarrow> bool \<Rightarrow> bool) x y) = (\<lambda>x y. word_to_seq (seq_to_word x AND seq_to_word y))"
  apply (rule ext)+
  apply (simp add: zip_seq_as_bl_zip)
  apply transfer
  by (simp add: word_rotate.blwl_syms)

lemma or_seq_conv[word_seq_convs]:
 "(\<lambda>x y. map2_seq ((\<or>) :: bool \<Rightarrow> bool \<Rightarrow> bool) x y) = (\<lambda>x y. word_to_seq (seq_to_word x OR seq_to_word y))"
  apply (rule ext)+
  apply (simp add: zip_seq_as_bl_zip)
  apply transfer
  apply simp
  by (simp add: word_rotate.blwl_syms)

lemma xor_seq_conv[word_seq_convs]:
 "(\<lambda>x y. map2_seq ((\<noteq>) :: bool \<Rightarrow> bool \<Rightarrow> bool) x y) = (\<lambda>x y. word_to_seq (seq_to_word x XOR seq_to_word y))"
  supply [simp del] = not_iff
  apply (rule ext)+
  apply (simp add: zip_seq_as_bl_zip)
  apply transfer
  by (simp add: word_rotate.blwl_syms)


end


lemma ucast_seq_down_is_drop:
  assumes A:"LEN('m) \<le> LEN('n)"
  shows "(ucast_seq :: ('n::len,'b::bool) seq \<Rightarrow> ('m::len,'b::bool) seq) xs = drop_seq xs"
  apply (induct xs rule: seq_zint.seq.abs_induct)
  apply (simp add: ucast_seq.abs_eq )
  apply transfer
  apply (simp add: drop_map drop_bin2bl del: bin_to_bl_def)
  using A
  apply (clarsimp simp del: bin_to_bl_def)
  by (metis int_word_uint to_bl_of_bin word_of_int_uint)


lemma append_seq_word_transfer[transfer_rule]:
  assumes nm: "LEN('nm) = LEN('n) + LEN('m)"
  shows
  "(eq_word_seq ===> eq_word_seq ===> eq_word_seq) (word_cat) 
        (append_seq :: ('n::len,bool) seq \<Rightarrow> ('m::len,bool) seq \<Rightarrow> ('nm::len,bool) seq)"
  supply [transfer_rule] = word_int_to_seq_list_transfer 
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def)
  apply transfer
  apply (simp del: bin_to_bl_def)
  using bin_to_bl_cat_app bin_to_bl_trunc nm by auto


lemma append_seq_conv[word_seq_convs]:
  assumes nm: "LEN('nm) = LEN('n) + LEN('m)"
  shows "((append_seq :: ('n::len,bool) seq \<Rightarrow> ('m::len,bool) seq \<Rightarrow> ('nm::len,bool) seq) xs ys)
       = word_to_seq (word_cat (seq_to_word xs) (seq_to_word ys))"
  supply [transfer_rule] = nm
  apply transfer
  by simp

lemma take_seq_drop_bit_transfer[transfer_rule]:
  "(eq_word_seq ===> eq_word_seq) (\<lambda>xs. ucast (drop_bit LEN('back::len) xs))
          (take_seq :: ('front + 'back, bool) seq \<Rightarrow> ('front::len,bool) seq)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: bin_to_bl_def)
  by (metis bin_bl_bin bin_to_bl_drop_bit bl_bin_bl
      take_bit_drop_bit)

lemma coerce_seq_len_drop_bit_transfer[transfer_rule]:
  "LEN ('m) \<ge> LEN ('n) \<Longrightarrow> (eq_word_seq ===> eq_word_seq) (\<lambda>xs. ucast (drop_bit (LEN ('m) - LEN('n)) xs))
          (coerce_seq_len :: ('m::len, bool) seq \<Rightarrow> ('n::len,bool) seq)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: bin_to_bl_def)
  by (metis bin_bl_bin bin_to_bl_drop_bit bl_bin_bl
      le_add_diff_inverse take_bit_drop_bit)


lemma coerce_seq_len_to_ucast_drop[word_seq_convs]: 
  assumes le: "LEN('n::len) \<le> LEN('m::len)"
  shows "(coerce_seq_len :: ('m,bool) seq \<Rightarrow> ('n,bool) seq) xs = 
          word_to_seq (ucast ((drop_bit (LEN('m::len)-LEN('n)) (seq_to_word xs))))"
  supply [transfer_rule] = coerce_seq_len_drop_bit_transfer[OF le]
  apply transfer
  apply simp
  done

lemmas [word_seq_convs] = coerce_seq_len_to_ucast_drop[simplified len_of_alt_def]

lemmas [transfer_rule] = coerce_seq_len_drop_bit_transfer[simplified len_of_alt_def, OF order_eq_refl]

lemma drop_seq_take_bit_transfer[transfer_rule]:
  "(eq_word_seq ===> eq_word_seq) (\<lambda>xs. ucast (take_bit LEN('back::len) xs))
          (drop_seq :: ('front::len + 'back, bool) seq \<Rightarrow> ('back::len,bool) seq)"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  apply (simp add: take_bit_of_to_mod_ring del: bin_to_bl_def)
  by (metis add.commute add_diff_cancel_right' bin_bl_bin
      bl_bin_bl drop_bin2bl size_bin_to_bl)


lemma left_shift_seq_conv[word_seq_convs]:
 "(\<lambda>x y. left_shift x y) = (\<lambda>x y. word_to_seq (left_shift (seq_to_word x) y))"
  apply (rule ext)+
  apply transfer
  apply simp
  done

lemma right_shift_seq_conv[word_seq_convs]:
 "(\<lambda>x y. right_shift x y) = (\<lambda>x y. word_to_seq (right_shift (seq_to_word x) y))"
  apply (rule ext)+
  apply transfer
  apply simp
  done

lemma right_rotate_seq_conv[word_seq_convs]:
 "(\<lambda>x y. right_rotate x y) = (\<lambda>x y. word_to_seq (right_rotate (seq_to_word x) y))"
  apply (rule ext)+
  apply transfer
  apply simp
  done

lemma take_seq_is_drop_bit[word_seq_convs]:
  "(take_seq (xs :: (('front::len) + 'back,bool) seq) :: ('front::len,bool) seq) =
      word_to_seq (ucast ((drop_bit LEN('back::len) (seq_to_word xs))))"
  apply transfer
  apply simp
  done

lemma drop_seq_is_take_bit[word_seq_convs]:
  "(drop_seq (xs :: (('front::len) + 'back,bool) seq) :: ('back::len,bool) seq) =
      word_to_seq (ucast ((take_bit LEN('back::len) (seq_to_word xs))))"
  apply transfer
  apply simp
  done

lemma seq_to_zint0: "(seq_to_zint 0) = 0"
  apply transfer
  apply simp
  done

lemma word_to_zint0: "(word_to_zint 0) = 0"
  by (simp add: word_to_zint_def2)

lemma zero_seq_conv[word_seq_convs]: "0 = word_to_seq 0"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (simp add: word_to_seq.abs_eq zint_to_seq.abs_eq zero_seq.abs_eq word_to_zint0 del: bin_to_bl_def)
  using bin_to_bl_zero by fastforce
  
lemmas [word_seq_convs] = zero_seq_conv[where 'b=bool, simplified zero_seq_def2 zero_bool_def]

lemma ucast_seq_to_ucast[word_seq_convs]:
  "ucast_seq xs = word_to_seq (ucast (seq_to_word xs))"
  apply transfer
  apply simp
  done

lemma zext_is_ucast: "(zext_seq (xs :: ('n::len,bool) seq) :: ('m::len,bool) seq) = ucast_seq xs"
  apply (cases "LEN('n) < LEN('m)")
   apply (simp add: zext_seq_defs right_shift_def word_seq_convs word_cat_eq)
  by (simp add: zext_seq_defs ucast_seq_down_is_drop)

lemma zext_seq_word_transfer[transfer_rule]: 
  "(eq_word_seq ===> eq_word_seq) ucast (zext_seq :: ('n::len,bool) seq \<Rightarrow> ('m::len,bool) seq)"
  unfolding zext_is_ucast
  by transfer_prover

lemma zext_ucast_conv[word_seq_convs]: "zext_seq (xs :: ('n::len,bool) seq) = word_to_seq (ucast (seq_to_word xs))"
  unfolding zext_is_ucast
  by (simp add: word_seq_convs)

definition scast_seq :: "('n,'b::bool) seq \<Rightarrow> ('m,'b::bool) seq" where
  "scast_seq xs \<equiv> of_int_seq (sint_seq xs)"

lemma scast_seq_word_transfer[transfer_rule]: 
  "(eq_word_seq ===> eq_word_seq) scast scast_seq"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2 scast_seq_def)
  apply transfer
  apply simp
  by (metis signed_of_int
      word_ubin.inverse_norm)

lemma scast_seq_to_scast[word_seq_convs]:
  "scast_seq xs = word_to_seq (scast (seq_to_word xs))"
  apply transfer
  apply simp
  done

lemma sign_is_msb: "(sign_seq (xs :: ('n,bool) seq)) = msb xs"
  supply [simp] = zint_to_list_def list_to_zint_def
  apply (simp add: msb_seq_def sign_seq_def msb_zint.rep_eq msb_int_def seq_to_zint.rep_eq)
  apply transfer
  apply (clarsimp simp add: sign_list_def)
  by (metis bl_bin_bl no_bintr_alt1 nth_bin_to_bl
      trunc_bl2bin_len)


lemma seq_as_zint_eq_transfer: "(pcr_seq (=) ===> eq_zint_seq ===> (=)) (\<lambda>x y. eq_zint_list y x) (=)"
  supply [simp del] = bin_to_bl_def
  apply (rule rel_funI)+
  apply (simp add: pcr_seq_def cr_seq_def relcompp_apply list.rel_eq eq_zint_def2 eq_zint_list_def zint_to_list_def)
  by (metis seq_preserved)


lemma to_int_mod_ring_numeral: "to_int_mod_ring (numeral x :: ('a::finite) mod_ring) = (numeral x mod CARD('a))"
  apply (constrain 'a="'b::nontriv")
  subgoal H[unconstrain_cases]
    by (transfer;simp)
  apply (rule H)
  by (simp add: CARD_1_singleton)

lemma to_int_mod_ring_uminus:
  "to_int_mod_ring ((- x) :: ('a::finite) mod_ring) = (if x \<noteq> 0 then CARD('a) - (to_int_mod_ring x) else 0)"
  apply transfer
  by simp

lemma to_int_mod_ring_max: "to_int_mod_ring ((- 1) :: ('a::finite) mod_ring) = (CARD('a)-1)"
  apply (constrain 'a="'b::nontriv")
  subgoal H[unconstrain_cases] by (simp add: to_int_mod_ring_uminus)
  apply (rule H)
  by (simp add: CARD_1_singleton)

lemma max_seq_eq_neg_one: "replicate_seq (1::'a::bool) = - 1"
  supply [transfer_rule] = seq_as_zint_eq_transfer
  supply [simp del] = bin_to_bl_def
  apply transfer
  apply (simp add: eq_zint_list_def zint_to_list_def to_int_mod_ring_max)
  by (metis bin_bl_bin bin_to_bl_minus1 bintr_Min
      bl_bin_bl length_replicate map_replicate
      of_bool_eq(2))

lemma replicate_seq_msb: "(replicate_seq (msb xs)) = (if msb xs then (-1) else 0)"
  apply (cases "msb xs")
   apply simp
   apply (simp add: max_seq_eq_neg_one[where 'a=bool, simplified one_bool_def])
  by (simp add: zero_seq_def2)


lemma replicate_seq_conv:
  "((replicate_seq b) :: ('n::len,'b::bool) seq) = word_to_seq (of_bl (replicate LEN('n) (bool_of b)))"
  supply [transfer_rule] = word_to_seq_list_transfer word_int_to_seq_list_transfer
  apply transfer
  by (metis bl_bin_bl len_of_alt_def3
      length_replicate map_replicate
      of_bool_of_id)

lemma uminus_num_conv[word_seq_convs]: "(- (numeral x)) = word_to_seq (-(numeral x))"
  supply [transfer_rule] = word_to_seq_of_int_transfer
  apply transfer
  apply transfer
  apply simp
  done

lemma uminus_neg_one_conv[word_seq_convs]: "(- 1) = word_to_seq (-1)"
  by (metis numeral_One uminus_num_conv)

lemma msb_conv[word_seq_convs]: "msb x = msb (seq_to_word x)"
  apply transfer
  by simp

lemma msb_transfer[transfer_rule]:
  "(pcr_word ===> (=)) (msb_int LENGTH('a)) (msb :: 'a::len word \<Rightarrow> bool)"
  apply (rule rel_funI)+
  apply (simp add: msb_int_def msb_word_def pcr_word_def cr_word_def eq_OO)
  apply transfer
  using bin_sign_lem by blast

lemma bin_to_bl_inj: 
  "bin_to_bl n x = bin_to_bl n y \<Longrightarrow> take_bit n x = take_bit n y"
  by (metis bin_bl_bin)

lemma plus_lessE: "(n::nat) < m \<Longrightarrow> (\<And>i. 0 < i \<Longrightarrow> m = i + n \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (metis add.commute less_imp_add_positive)

lemma bin_to_bl_cat':
  "nvnw = nv + nw \<Longrightarrow> bin_to_bl nvnw (concat_bit nw w v) =
    bin_to_bl_aux nv v (bin_to_bl nw w)"
  by (simp add: bin_to_bl_cat del: bin_to_bl_def)

lemma msb_int_def2: "n > 0 \<Longrightarrow> msb_int n x = hd (bin_to_bl n x)"
  apply (simp add: msb_int_def del: bin_to_bl_def)
  by (metis Suc_pred bin_sign_lem bl_sbin_sign
      sbintrunc_bintruncS0)

lemma bin_to_bl_plus_append: "bin_to_bl (n + m) x = xs @ ys \<Longrightarrow>
       xs = bin_to_bl n (drop_bit m x) \<Longrightarrow>
       ys = bin_to_bl m x"
  apply (induct xs arbitrary: n m x ys)
   apply simp
  apply (metis add_0 bin_to_bl_def list.size(3)
      size_bin_to_bl)
  by (metis add_diff_cancel_left' append_eq_conv_conj drop_bin2bl
      size_bin_to_bl)

lemma last_append: "length ys = n \<Longrightarrow> b = (ys @ [b]) ! n"
  by fastforce

lemma bin_to_bl_plus_Cons: "bin_to_bl (Suc n) x = b # ys \<Longrightarrow>
       bin_to_bl n x = ys"
  apply (rule sym)
  apply (rule bin_to_bl_plus_append[where n=1 and xs="[b]"])
   apply simp
  apply simp
  apply (simp add: bin_last_shiftr)
  apply (subst bin_nth_bl[where m="Suc n"])
   apply simp
  apply simp
  apply (rule last_append)
  by (metis add_right_cancel length_Cons length_rev list.size(3,4)
      size_bin_to_bl_aux)

lemma bin_to_bl_mask_neg1:
  "bin_to_bl i (mask i) @ [True] = bin_to_bl (Suc i) (- 1)"
  apply (induct i)
   apply simp
  apply simp
  by (simp add: bin_to_bl_aux_append mask_half
      semiring_bit_operations_class.even_mask_iff)
  
lemma scast_is_cat:
  "LENGTH('n::len) < LENGTH('m::len) \<Longrightarrow>
         msb x \<Longrightarrow>
         SCAST('n \<rightarrow> 'm) x = word_cat ((- 1) :: ('m - 'n) len word) x"
  supply [simp del] = bin_to_bl_def
  supply [split del] = split_of_bool
  apply (rule sym)
  apply transfer
  apply (simp add: msb_int_def2)
  apply (erule plus_lessE)
  apply (rule bin_to_bl_inj)
  apply (simp)
  apply (subst bin_to_bl_cat)
  apply (subst signed_take_bit_eq_concat_bit)
  subgoal for x i
    apply (subst bin_to_bl_cat'[where nv="i+1"])
     apply simp
    apply (rotate_tac)
    apply (cases "bin_to_bl LENGTH('n) x")
     apply simp
     apply (metis len_not_eq_0 list.size(3) size_bin_to_bl)
    apply (subgoal_tac "(x !! (LENGTH('n) - Suc 0))")
    apply (simp add: bin_to_bl_aux_alt)
    apply (cases "LENGTH('n)"; simp)
    apply (drule bin_to_bl_plus_Cons)
    apply (simp)
     apply (rule bin_to_bl_mask_neg1)
    using nth_bin_to_bl apply fastforce
    done
  done
  
  
lemma sext_is_scast: "(sext_seq (xs :: ('n::len,bool) seq) :: ('m::len,bool) seq) = scast_seq xs"
  apply (cases "LEN('n) < LEN('m)")
   apply (simp add: sext_seq_defs right_shift_def word_seq_convs sign_is_msb replicate_seq_msb)
   apply (intro impI conjI)
    apply (simp add: scast_is_cat)
   apply (simp add: scast_eq_ucast)
   apply (simp add: word_cat_eq')
  apply (simp add: sext_seq_defs word_seq_convs scast_ucast_down_same)
  by (metis len_of_alt_def3 linorder_not_le ucast_seq_down_is_drop
      ucast_seq_to_ucast word_to_from_seq)

lemma sext_seq_word_transfer[transfer_rule]: 
  "(eq_word_seq ===> eq_word_seq) scast (sext_seq :: ('n::len,bool) seq \<Rightarrow> ('m::len,bool) seq)"
  unfolding sext_is_scast
  by transfer_prover

lemma sext_scast_conv[word_seq_convs]: "sext_seq (xs :: ('n::len,bool) seq) = word_to_seq (scast (seq_to_word xs))"
  unfolding sext_is_scast
  by (simp add: word_seq_convs)

definition carry_int :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "carry_int n x y \<equiv> (take_bit n x + take_bit n y) \<noteq> take_bit n (x + y)"

lift_definition carry_zint :: "'n Z\<^sup>2 \<Rightarrow> 'n Z\<^sup>2 \<Rightarrow> bool" is "carry_int LEN('n)" .

definition scarry_int :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "scarry_int n x y \<equiv> (sint_int n x + sint_int n y) \<noteq> sint_int n (x + y)"

lift_definition scarry_zint :: "'n Z\<^sup>2 \<Rightarrow> 'n Z\<^sup>2 \<Rightarrow> bool" is "scarry_int LEN('n)" .

definition sborrow_int :: "nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "sborrow_int n x y \<equiv> (sint_int n x - sint_int n y) \<noteq> sint_int n (x - y)"

lift_definition sborrow_zint :: "'n Z\<^sup>2 \<Rightarrow> 'n Z\<^sup>2 \<Rightarrow> bool" is "sborrow_int LEN('n)" .

lift_definition carry_word :: "'n::len word \<Rightarrow> 'n::len word \<Rightarrow> bool" is "carry_int LENGTH('n)"
  apply (simp add: carry_int_def)
  by (metis take_bit_add)

lemma carry_word_def2: "carry_word x y = ((uint x + uint y) \<noteq> uint (x + y))"
  apply transfer
  by (simp add: carry_int_def)

lift_definition scarry_word :: "'n::len word \<Rightarrow> 'n::len word \<Rightarrow> bool" is "scarry_int LENGTH('n)"
  apply (simp add: scarry_int_def sint_int_def)
  by (metis (no_types, opaque_lifting) One_nat_def
      take_bit_add word_sbin.eq_norm
      word_ubin.Abs_norm)

lemma scarry_word_def2: "scarry_word x y = ((sint x + sint y) \<noteq> sint (x + y))"
  apply transfer
  by (simp add: scarry_int_def sint_int_def)

lift_definition sborrow_word :: "'n::len word \<Rightarrow> 'n::len word \<Rightarrow> bool" is "sborrow_int LENGTH('n)"
  apply (simp add: sborrow_int_def sint_int_def)
  by (metis signed_take_bit_decr_length_iff
      take_bit_diff)

lemma sborrow_word_def2: "sborrow_word x y = ((sint x - sint y) \<noteq> sint (x - y))"
  apply transfer
  by (simp add: sborrow_int_def sint_int_def)

lemma carry_word_code[code]: "carry_word (x :: 'a :: len word) y = carry_int LEN('a) (Word.the_int x) (Word.the_int y)"
  apply transfer
  apply (simp add: carry_int_def)
  by (simp add: take_bit_add)

lemma scarry_word_code[code]: "scarry_word (x :: 'a :: len word) y = scarry_int LEN('a) (Word.the_int x) (Word.the_int y)"
  apply transfer
  apply (simp add: scarry_int_def sint_int_def)
  by (metis signed_take_bit_decr_length_iff
        take_bit_add)

lemma sborrow_word_code[code]: "sborrow_word (x :: 'a :: len word) y = sborrow_int LEN('a) (Word.the_int x) (Word.the_int y)"
  apply transfer
  apply (simp add: sborrow_int_def sint_int_def)
  by (metis signed_take_bit_decr_length_iff
      take_bit_diff)

context includes seq_zint.seq.lifting begin
lift_definition carry_seq :: "('n,'b::bool) seq \<Rightarrow> ('n,'b::bool) seq \<Rightarrow> bool" is "carry_zint" .
lift_definition scarry_seq :: "('n,'b::bool) seq \<Rightarrow> ('n,'b::bool) seq \<Rightarrow> bool" is "scarry_zint" .
lift_definition sborrow_seq :: "('n,'b::bool) seq \<Rightarrow> ('n,'b::bool) seq \<Rightarrow> bool" is "sborrow_zint" .
end

lemma carry_seq_def2: "carry_seq x y = ((uint_seq x + uint_seq y) \<noteq> uint_seq (x + y))"
  apply transfer
  apply transfer
  by (simp add: carry_int_def take_bit_eq_mod)

lemma scarry_seq_def2: "scarry_seq x y = ((sint_seq x + sint_seq y) \<noteq> sint_seq (x + y))"
  apply transfer
  apply transfer
  apply (simp add: scarry_int_def sint_int_def)
  by (metis sbintrunc_bintruncS0 take_bit_eq_mod)

lemma sborrow_seq_def2: "sborrow_seq x y = ((sint_seq x - sint_seq y) \<noteq> sint_seq (x - y))"
  apply transfer
  apply transfer
  apply (simp add: sborrow_int_def sint_int_def)
  by (metis sbintrunc_bintruncS0 take_bit_eq_mod)

lemma sint_seq_conv[word_seq_convs]: "sint_seq x = sint (seq_to_word x)"
  apply transfer
  by simp

lemma carry_seq_conv[word_seq_convs]: "carry_seq x y = carry_word (seq_to_word x) (seq_to_word y)"
  by (simp add: carry_seq_def2 carry_word_def2 word_seq_convs)

lemma scarry_seq_conv[word_seq_convs]: "scarry_seq x y = scarry_word (seq_to_word x) (seq_to_word y)"
  by (simp add: scarry_seq_def2 scarry_word_def2 word_seq_convs)

lemma sborrow_seq_conv[word_seq_convs]: "sborrow_seq x y = sborrow_word (seq_to_word x) (seq_to_word y)"
  by (simp add: sborrow_seq_def2 sborrow_word_def2 word_seq_convs)


lemma of_int_seq_conv[word_seq_convs]: "of_int_seq i = word_to_seq (of_int i)"
  supply [transfer_rule] = word_to_seq_of_int_transfer
  apply transfer
  by simp

lemma one_seq_conv[word_seq_convs]: "1 = word_to_seq (1 :: 'a :: len word)"
  supply [transfer_rule] = word_to_seq_of_int_transfer
  apply (simp only: word_seq_convs)
  apply transfer
  by (simp add: zint_to_word.abs_eq)

lemma uminus_seq_conv[word_seq_convs]: "(-x) = word_to_seq (-(seq_to_word x))"
  apply transfer
  by simp

lemma le_seq_word_transfer[transfer_rule]: "(eq_word_seq ===> eq_word_seq ===> (=)) (\<le>) (\<le>)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  by (simp add: less_eq_mod_ring_def)

lemma lt_seq_word_transfer[transfer_rule]: "(eq_word_seq ===> eq_word_seq ===> (=)) (<) (<)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def2)
  apply transfer
  by (simp add: less_mod_ring_def)

lemma le_seq_conv[word_seq_convs]: "x \<le> y = (seq_to_word x \<le> seq_to_word y)"
  by (transfer;simp)

lemma lt_seq_conv[word_seq_convs]: "x < y = (seq_to_word x < seq_to_word y)"
  by (transfer;simp)

lemma shift_rotate_word_defs:
  "left_shift (x :: 'a ::len word) y = (if y \<ge> 0 then x << (nat y) else x >> nat (- y))"
  "right_shift (x :: 'a ::len word) y = (if y \<ge> 0 then x >> (nat y) else x << nat (- y))"
  "left_rotate (x :: 'a ::len word) y = (word_roti (-y) x)"
  "right_rotate (x :: 'a ::len word) y = (word_roti y x)"
  by (simp add: left_shift_def2 right_shift_def left_rotate_word_def2 right_rotate_word_def2)+


lemma seq_to_list_conv[word_seq_convs]: "(seq_to_list xs) = to_bl (seq_to_word xs)"
  apply (simp add: seq_to_word.rep_eq
                   zint_to_word.abs_eq
                   list_to_zint_def
                   seq_to_zint.rep_eq)
  apply transfer
  by (metis (no_types, opaque_lifting)
      Rep_mod_ring_mod bl_bin_bl
      len_of_alt_def of_int_mod_ring.abs_eq
      of_int_mod_ring.rep_eq
      take_bit_of_to_mod_ring to_bl_of_bin
      word_ubin.Abs_norm)

lemma seq_to_list_of_bl:
  "LENGTH('a::len) = LENGTH('b::len) \<Longrightarrow>
         of_bl (seq_to_list (x :: ('a,bool) seq)) = (seq_to_word (coerce_seq_len x) :: 'b word)"
  apply (simp add: word_seq_convs)
  by (simp add: ucast_bl)

lemma seq_to_word_bool_of: "seq_to_word xs = seq_to_word (map_seq bool_of xs)"
  by (meson eq_word_seq_bool_of
      eq_word_seq_def3)

lemma seq_to_list_of_bl':
  "LENGTH('a::len) = LENGTH('b::len) \<Longrightarrow>
         of_bl (map bool_of (seq_to_list (x :: ('a,'c::bool) seq))) = (seq_to_word (coerce_seq_len x) :: 'b word)"
  apply (subst seq_to_word_bool_of)
  apply (simp add: seq_to_list_of_bl[symmetric])
  by (transfer;simp)

lemma same_type_seq_word[simp]: "same_type TYPE(('a, 'c::bool) seq) TYPE('b word) = (LEN('a) = LEN('b))"
  by (simp add: same_type_def strip_type_seq_def strip_type_word_def is_bool_type[where 'a='c])

lemma same_type_word_seq[simp]: "same_type TYPE('a word) TYPE(('b, 'c::bool) seq) = (LEN('a) = LEN('b))"
  by (simp add: same_type_def strip_type_seq_def strip_type_word_def is_bool_type[where 'a='c])

interpretation seq_to_word: coercion 
  "\<lambda>(x :: ('a,'c::bool) seq). (seq_to_word (coerce_seq_len x))"
      apply standard
      apply (simp add: strip_seq_def unstrip_seq_def strip_word_def
                       unstrip_word_def)
  apply (constrain 'a="'d::len")
  subgoal H[unconstrain_cases] for x
    by (simp add: seq_to_list_of_bl'[symmetric] bool_of_def2)
  by (rule H;simp)

lemma list_to_seq_to_bl:
  "LENGTH('a::len) = LENGTH('b::len) \<Longrightarrow>
         list_to_seq (to_bl (x :: 'a word)) = (coerce_seq_len (word_to_seq x :: ('a, bool) seq) :: ('b, bool) seq)"
  apply (simp add: word_seq_convs)
  by (simp add: ucast_bl)

lemma word_to_seq_of_bool: "word_to_seq xs = map_seq of_bool (word_to_seq xs)"
  by (meson eq_word_seq_def eq_word_seq_of_bool)

lemma list_to_seq_to_bl':
  "LENGTH('a::len) = LENGTH('b::len) \<Longrightarrow>
         list_to_seq (map of_bool (to_bl (x :: 'a word))) = 
              (coerce_seq_len (word_to_seq x :: ('a, 'c::bool) seq) :: ('b, 'c::bool) seq)"
  apply (subst word_to_seq_of_bool)
  by (simp del: map_seq_coerce add: map_seq_coerce[symmetric] list_to_seq_to_bl[symmetric])


interpretation word_to_seq: coercion
  "\<lambda>(x :: ('a::len) word). coerce_seq_len ((word_to_seq x) :: ('a,'c::bool) seq)"
  apply standard
  apply (simp add: strip_seq_def unstrip_seq_def strip_word_def
                   unstrip_word_def)
  apply (constrain 'b="'d::len")
  subgoal H[unconstrain_cases]
    apply (simp add: of_bool_def2[symmetric])
    by (rule list_to_seq_to_bl'; simp)
  by (rule H;simp)

lemma log2_seq_conv[word_seq_convs]:
  "log2_nat (to_nat (xs :: ('a::len,bool) seq)) = 
         (if seq_to_word xs > 1 then (word_log2 (seq_to_word xs - 1) + 1) else 0)"
  apply clarsimp
  apply (intro impI conjI)
   apply (subst word_log2_to_lg2_nat)
    apply (simp add: less_diff_gt0)
   apply simp
  apply (metis Suc_pred Suc_unat_minus_one log2_nat.elims
      order_less_irrefl to_nat_seq_to_word to_nat_unat
      unat_eq_1 word_gt_a_gt_0 zero_less_Suc)
  by (metis log2_nat.simps(2,3) linorder_neq_iff to_nat_0
      to_nat_seq_to_word to_nat_unat unat_eq_1
      word_less_1)

lemma to_nat_seq_num[simp]:
  "to_nat ((numeral x) :: ('n,bool) seq) = (numeral x) mod (2 ^ LEN('n) :: nat)"
  apply (simp add: to_nat_def)
  apply transfer
  apply transfer
  by simp

lemma to_int_seq_num[simp]:
  "to_int ((numeral x) :: ('n,bool) seq) = (numeral x) mod (2 ^ LEN('n) :: int)"
  apply (simp add: to_nat_def)
  apply transfer
  apply transfer
  apply simp
  by (simp add: zmod_int)

lemma from_nat_seq_suc[simp]:
  "(from_nat (Suc n) :: ('n,bool) seq) = from_nat n + 1"
  apply (simp add: from_nat_def)
  apply transfer
  apply transfer
  by (auto;presburger)


lemma to_int_seq_trivial[simp]:
  "LEN('a) = 0 \<Longrightarrow> to_int (x :: ('a,bool) seq) = 0"
  apply (simp add: to_nat_def)
  apply (simp add: uint_seq.rep_eq)
  using to_int_not_zero to_int_zint_trivial
  by blast

lemma to_nat_seq_trivial[simp]:
  "LEN('a) = 0 \<Longrightarrow> to_nat (x :: ('a,bool) seq) = 0"
  by (metis to_int_seq_trivial to_nat_0
      to_nat_def)

lemma degenerate_bitseq: "LEN('a) < 2 \<Longrightarrow> (x :: ('a,bool) seq) = 0 \<or> x = 1"
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases] for x'
    apply (simp add: word_seq_convs)
    by (simp add: degenerate_word less_le_not_le)
  by (rule H;simp)

lemma from_to_nat_seq[simp]: "n < 2 ^ LEN('a) \<Longrightarrow> to_nat ((from_nat n) :: ('a,bool) seq) = n"
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_convs from_nat_def)
    by (simp add: unat_of_nat_len)
  by (rule H;simp)

lemma to_nat_seq_bound[simp]: 
  "(to_nat (x :: ('a,bool) seq)) < (2 ^ LEN('a))"
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases] for x'
    by (simp add: word_seq_convs)
  by (rule H;simp)

lemma to_nat_seq_pow2[simp]:
  "n < LEN('a) \<Longrightarrow> to_nat ((2 :: ('a,bool) seq) ^ n) = (2 :: nat) ^ n"
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs)
  by (rule H; simp)

lemma to_nat_seq_zext[simp]:
  "LEN('b) \<ge> LEN('a) \<Longrightarrow> (to_nat ((zext_seq x) :: ('b,bool) seq)) = to_nat (x :: ('a,bool) seq)"
  apply (constrain 'a="'c::len" and 'b="'d::len")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_convs)
    by (simp add: unat_ucast_up_simp)
  apply (rule H;clarsimp)
  by (elim disjE;simp add: zero_len_trivial[of x 0])

lemma to_nat_seq_inj: "to_nat x = to_nat y \<Longrightarrow> x = (y :: ('a,bool) seq)"
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs)
  by (rule H;simp)

lemma take_bit_nat_inc: "a < b \<Longrightarrow> take_bit b (take_bit a x + 1) = Suc (take_bit a (x::nat))"
  by (metis Suc_1 add.commute less_add_one less_trans_Suc
      plus_1_eq_Suc power_strict_increasing_iff
      take_bit_nat_eq_self_iff
      take_bit_nat_less_exp)

lemma 
  word_pos_induct: "(\<And>(y :: int). y \<ge> 0 \<Longrightarrow> P (of_int y)) \<Longrightarrow> P (x :: 'a :: len word)"  
  by (metis word_int_cases)

lemma unat_inc_zext:
  "LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> unat (UCAST('a \<rightarrow> 'b) x + 1) = Suc (unat x)"
  apply (induct x rule: word_pos_induct)
  apply transfer
  apply simp
  subgoal for y
    apply (induct y;simp)
    apply (simp add: take_bit_of_nat)
    by (metis Suc_eq_plus1 add.commute nat_int.Rep_inverse
        of_nat_Suc take_bit_nat_inc take_bit_of_nat)
  done

lemma to_nat_zext_inc[simp]:
  "LEN('b) > LEN('a) \<Longrightarrow> 
        to_nat ((zext_seq (x :: ('a,bool) seq) :: ('b,bool) seq) + 1) = Suc (to_nat x)"
  apply (constrain 'a="'c::len" and 'b="'d::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs unat_inc_zext)
  apply (rule H;simp)
  by (metis (full_types) One_nat_def add_0
      seq_one_neq_zero to_nat_1
      to_nat_seq_inj to_nat_seq_trivial
      zext_seq_0)

lemma seq_not_max_inc_int[simp]: "(x :: ('a,bool) seq) < (2 ^ LEN('a)-1) \<Longrightarrow> to_int (x + 1) = to_int x + 1"
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_convs)
    by (simp add: no_plus_overflow_neg
        uint_plus_simple)
  by (rule H;simp)

lemmas [simp] = seq_not_max_inc_int[simplified to_int_seq_def]
  
lemma seq_not_max_inc_nat[simp]: "(x :: ('a,bool) seq) < (2 ^ LEN('a)-1) \<Longrightarrow> to_nat (x + 1) = Suc (to_nat x)"
  by (simp add: to_nat_def Suc_as_int)

lemma to_nat_zext_inc_leq[simp]:
  "LEN('b) \<ge> LEN('a) \<Longrightarrow> (x :: ('a,bool) seq) < (2 ^ LEN('b)-1) \<Longrightarrow>
        to_nat ((zext_seq (x :: ('a,bool) seq) :: ('b,bool) seq) + 1) = Suc (to_nat x)"
  apply (cases "LEN('b) = LEN('a)";simp)
  by (metis dual_order.refl from_nat_seq_suc
      from_to_nat_seq seq_not_max_inc_nat
      to_nat_seq_bound to_nat_seq_inj
      to_nat_seq_zext)


lemma from_nat_seq_conv[word_seq_convs]: "(from_nat n :: ('a::len,bool) seq) = word_to_seq (from_nat n)"
  by (simp add: from_nat_def word_seq_convs)

lemma log2_nat_less_zext_inc[simp]: "log2_nat (to_nat (x :: ('a,bool) seq)) < LEN(1 + 'a)"
  apply simp
  apply (rule le_imp_less_Suc)
  apply (rule log2_nat_pow2_bound)
  by (simp add: dual_order.order_iff_strict)

lemma of_int_to_nat_seq:
  "x \<ge> 0 \<Longrightarrow> x < 2 ^ LEN('a) \<Longrightarrow> to_nat ((of_int_seq x)::('a,bool) seq) = to_nat x"
  apply (simp add: to_nat_def)
  apply transfer
  apply transfer
  apply simp
  done

lemma take_bit_less_mask: "n > 1 \<Longrightarrow> take_bit n (int n) < mask n"
  by (metis One_nat_def Suc_1 lessI less_mask
      nat_mask_eq of_nat_take_bit power_gt_expt
      take_bit_nat_eq_self
      zless_nat_eq_int_zless)

lemma seq_len_less_max: "LEN('a) > 1 \<Longrightarrow> (of_int_seq (int LEN('a)) :: ('a,bool) seq) < 2 ^ LEN('a) -1"
  apply (constrain 'a="'b::len")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_convs)
    apply transfer
    by (simp add: take_bit_less_mask)
  by (rule H;simp)

lemma seq_len_suc:
  "LEN('a) > 1 \<Longrightarrow> to_nat ((of_int_seq (int LEN('a)) :: ('a,bool) seq) + 1) = Suc (LEN('a))"
    apply (subst seq_not_max_inc_nat)
     apply (simp add: seq_len_less_max)
  by (simp add: of_int_to_nat_seq)

lemma log2_nat_seq_less_max[simp]: "log2_nat (to_nat (y :: ('a,bool) seq)) < 2 ^ LEN('a)"
  using log2_nat_pow2_bound_strict to_nat_seq_bound
  by blast

lemma uint_seq_coerce[simp]: 
  "LEN('a) = LEN('b) \<Longrightarrow> uint_seq ((coerce_seq_len (y :: ('a,bool) seq)) :: ('b,bool) seq) = uint_seq y"
  apply (constrain 'a="'aa::len" and 'b="'bb::len")
  subgoal H[unconstrain_cases] for x
    by (auto simp add: word_seq_convs is_up.rep_eq intro!: uint_up_ucast)
  apply (rule H;simp)
  by (metis to_int_seq_def to_int_seq_trivial)

lemma coerce_to_nat[simp]: 
  "LEN('a) = LEN('b) \<Longrightarrow> to_nat (coerce_seq_len (y :: ('a,bool) seq) :: ('b,bool) seq) = to_nat y"
  by (simp add: to_nat_def)

context
  fixes x :: "'a::len word" 
    and y :: "'b::len word"
  assumes A: "LENGTH('c::len) \<ge> LENGTH('a) + LENGTH('b)"
begin

lemma uint_append_word[simp]:
  shows "uint (word_cat x y :: 'c word) = 2 ^ LENGTH('b) * uint x + uint y"
  apply transfer
  apply (insert A)
  by (metis bin_cat_num bintr_cat1 bintrunc_bintrunc_l
      mult.commute)

lemma unat_append_word[simp]:
  shows "unat (word_cat x y :: 'c word) = 2 ^ LENGTH('b) * unat x + unat y"
  apply (simp only: unat_def uint_append_word)
  apply transfer
  by (simp add: nat_plus_as_int)
end

text\<open>
   Note that we need to strengthen the condition (compared to the above lemmas) 
   to assume that the resulting seq length is exactly the sum of the argument seq lengths.
   This is because @{const append_seq} is not completely defined in cases when the sequence
   length is extended (the additional elements are undefined, rather than zero).
\<close>

lemma to_nat_append_seq[simp]:
  assumes A: "LEN('c) = LEN('a) + LEN('b)"
  shows "to_nat ((append_seq (x :: ('a,bool) seq) (y :: ('b,bool) seq)) :: ('c,bool) seq) = (2 ^ LEN('b)) * to_nat x + to_nat y"
  apply (constrain 'a="'aa::len" and 'b="'bb::len" and 'c="'cc::len" notes A)
  subgoal H[unconstrain_cases] for x y
    by (simp add: word_seq_convs)
  apply (rule H[OF _ A];clarsimp)
  by (elim disjE;simp)

lemma to_nat_list_to_seq_singleton[simp]:
  assumes A:"LEN('a) = 1"
  shows "to_nat ((list_to_seq [b]) :: ('a,bool) seq) = of_bool b"
  apply (constrain 'a="'aa::len" notes A)
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs)
  apply (rule H[OF _ A])
  by simp

thm word_reverse_def

lemma word_reverse_transfer[transfer_rule]: "(pcr_word ===> pcr_word) 
    (\<lambda>x. bl_to_bin (rev (bin_to_bl LENGTH('n)  x))) 
    (word_reverse :: 'n :: len word \<Rightarrow> 'n word)"
  unfolding word_reverse_def
  by transfer_prover

lemma rev_seq_word_transfer[transfer_rule]: "(eq_word_seq ===> eq_word_seq) word_reverse rev_seq"
  supply [transfer_rule] = word_int_to_seq_list_transfer
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def)
  apply transfer
  by (metis bl_bin_bl length_rev rev_map
      size_bin_to_bl)

lemma rev_seq_word_conv[word_seq_convs]: "rev_seq xs = word_to_seq (word_reverse (seq_to_word xs))"
  by transfer simp

lemma concat_seq_map[word_seq_convs]:
  "((concat_seq (s :: ('a,('b,'c) seq) seq)) :: ('a::len \<times> 'b::len,'c::bool) seq) = word_to_seq (word_rcat (map seq_to_word (seq_to_list s)))"
  apply (simp add: join_words_seq join_words_seq.rep_eq)
  by (simp add: Seq.map_seq_code)


lemma bin_to_bl_mod_2n: "(bin_to_bl n (x mod 2 ^ n)) = bin_to_bl n x"
  
  using bin_to_bl_trunc no_bintr_alt1 by auto

lemma map_seq_word_transfer[transfer_rule]:
  "((=) ===> eq_word_seq ===> eq_word_seq) (\<lambda>f x. of_bl (map (bool_of o f o of_bool) (to_bl x))) map_seq"
  apply (rule rel_funI)+
  unfolding eq_word_seq_def seq_to_word_def seq_to_zint_def list_to_zint_def zint_to_word_def
            word_to_seq_def
  apply simp
  apply transfer
  unfolding zint_to_list_def
  apply (simp del: bin_to_bl_def)
  apply transfer
  apply (simp add: bin_to_bl_mod_2n bl_bin_bl' comp_def del: bin_to_bl_def)
  by force

lemma map_seq_conv[word_seq_convs]:
  "map_seq f s = word_to_seq (of_bl (map f (to_bl (seq_to_word s))))"
  supply [transfer_rule] = word_to_seq_of_int_transfer
  apply transfer
  by (simp add: word_of_bl comp_def)

lemma word_compr_transfer[transfer_rule]:
  "((=) ===> eq_word_seq ===> (=)) (\<lambda>f x. of_bl (map (bool_of o f o of_bool) (to_bl x))) word_compr"
  unfolding word_compr_def
  by transfer_prover

lemma not_seq_conv[simplified, word_seq_convs]:
  "(map_seq Not (x :: ('a::len,bool) seq)) = word_to_seq (~~ (seq_to_word x))"
  apply transfer
  by (simp add: word_rotate.blwl_syms comp_def)

lemma word_to_seq_inj: "word_to_seq x = word_to_seq y \<Longrightarrow> x = y"
  by (metis word_to_from_seq)
             
lemmas not_seq_conv'[word_seq_convs] = not_seq_conv[simplified map_seq_conv, THEN word_to_seq_inj]

lemmas [simplified map_seq_conv, THEN fun_cong, THEN fun_cong, word_seq_convs] =
  and_seq_conv or_seq_conv xor_seq_conv[simplified]

lemma nth_mod_seq_word_bit_transfer[transfer_rule]: 
  "(eq_word_seq ===> (=) ===> (=)) (\<lambda>x i. x !! (LEN('n::len) - (Suc (i mod LEN('n))))) (nth_mod_seq :: ('n,bool) seq \<Rightarrow> nat \<Rightarrow> bool)"
  supply [transfer_rule] = nth_mod_seq_word_transfer
  apply (rule rel_funI)+
  apply (erule rel_funE[OF nth_mod_seq_word_transfer])
  apply (simp add: fun.rel_eq)
  by (metis len_gt_0 mod_less_divisor nth_to_bl)

lemma nth_mod_seq_conv[word_seq_convs]: 
  "nth_mod_seq (x :: ('n::len,bool) seq) i = (seq_to_word x) !! (LEN('n) - (Suc (i mod LEN('n))))"
  apply transfer
  apply simp
  done

lemma not_bits_take_bit: "\<forall>i<n. \<not> (x !! (n - Suc i)) \<Longrightarrow> take_bit n (x :: int) = 0"
  apply (rule bin_eqI)
  apply (simp add: bit_take_bit_iff)
  by (metis Suc_diff_Suc diff_diff_cancel diff_le_self
      less_eq_Suc_le nat_less_le)

lemma nonzero_ex_bit: "0 < take_bit n (x :: int) \<Longrightarrow> \<exists>i. x !! (n - Suc (i mod n))"
  by (metis dual_order.refl linorder_not_le mod_less
      not_bits_take_bit)

lemma nth_seq_conv[word_seq_convs]: 
  "i < LEN('n::len) \<Longrightarrow> nth_seq (x :: ('n,bool) seq) i = (seq_to_word x) !! (LEN('n) - (Suc i))"
  by (simp add: nth_seq_def2 word_seq_convs)

lemma of_bool_swapI:
  "bool_of x = y \<Longrightarrow> x = of_bool y"
  by force

lemma nth_seq_conv'[word_seq_convs]: 
  "i < LEN('n::len) \<Longrightarrow> nth_seq (x :: ('n,'b::bool) seq) i = of_bool ((seq_to_word x) !! (LEN('n) - (Suc i)))"
  apply (rule of_bool_swapI)
  apply (subst seq_to_word_bool_of)
  apply (subst nth_seq_conv[symmetric])
  by auto

lemma nth_end_seq_conv[word_seq_convs]:
  "i < LEN('n::len) \<Longrightarrow> nth_end_seq (x :: ('n,bool) seq) i = (seq_to_word x) !! i"
  by (simp add: word_seq_convs)

lemma seq_to_word_neg1_iff_all_ones: "(seq_to_word xs = (-1)) = (xs = replicate_seq 1)"
  by (simp add: word_seq_convs max_seq_eq_neg_one)

lemma seq_to_word_zero_iff_all_zeros: "(seq_to_word xs = 0) = (xs = replicate_seq 0)"
  apply (subst zero_seq_def2[symmetric])
  by (simp add: word_seq_convs)

lemma list_all_id_as_replicate: "length xs = n \<Longrightarrow> list_all (\<lambda>x. x) xs = (xs = replicate n True)"
  by (metis (full_types) Ball_set in_set_replicate
      replicate_length_same)

lemma list_all_not_as_replicate: "length xs = n \<Longrightarrow> list_all Not xs = (xs = replicate n False)"
  by (metis (full_types) Ball_set in_set_replicate
      replicate_length_same)

lemma all_seq_id_conv[word_seq_convs]:
  "all_seq (\<lambda>x. x) (xs :: ('n::len,bool) seq) = (seq_to_word xs = (-1))"
  apply (simp add: seq_to_word_neg1_iff_all_ones)
  apply transfer
  by (simp add: list_all_id_as_replicate)

lemma all_seq_not_conv[word_seq_convs]:
  "all_seq Not (xs :: ('n::len,bool) seq) = (seq_to_word xs = 0)"
  apply (simp add: seq_to_word_zero_iff_all_zeros)
  apply transfer
  by (simp add: list_all_not_as_replicate)

lemma any_seq_word_id_conv[word_seq_convs]:
  "any_seq (\<lambda>x. x) (xs :: ('n::len,bool) seq) = (seq_to_word xs > 0)"
  by (simp add: any_seq_not_not_all word_seq_convs word_neq_0_conv)

lemma any_seq_word_not_conv[word_seq_convs]:
  "any_seq Not (xs :: ('n::len,bool) seq) = (seq_to_word xs \<noteq> (-1))"
  by (simp add: any_seq_not_not_all word_seq_convs)


lemma seq_to_word_swap: "seq_to_word a = b \<Longrightarrow> a = word_to_seq b"
  by force


lemma bin_to_bl_rev_map: "bin_to_bl n i = rev (map (bit i) [0..<n])"
  using bin_nth_bl size_bin_to_bl by (auto cong: map_upto_cong)

lemma bin_to_bl_map_rev[code]: "bin_to_bl n i = map (bit i) (rev [0..<n])"
  apply (simp only: bin_to_bl_rev_map)
  apply (simp cong: map_upto_cong)
  by (meson rev_map)

lemma set_bit_is_bl_update:
  "n < m \<Longrightarrow> bin_to_bl m (Generic_set_bit.set_bit x n a) = ((bin_to_bl m x)[(m - Suc n) := a])"
  apply (simp add: set_bit_eq del: bin_to_bl_def)
   apply (simp add: bin_to_bl_map_rev map_rev_upto_update del: bin_to_bl_def)
  apply (rule conjI)
  apply (metis possible_bit_int semiring_bit_operations_class.bit_set_bit_iff)
  using bit_unset_bit_iff by blast


lemma bin_to_bl_swap: "bin_to_bl n x = y \<Longrightarrow> take_bit n x = x \<Longrightarrow> x = bl_to_bin y"
  by (metis bin_bl_bin)

lemma set_bit_is_bl_update_take:
  "n < m \<Longrightarrow> take_bit m (Generic_set_bit.set_bit x n a) = bl_to_bin ((bin_to_bl m x)[(m - Suc n) := a])"
  apply (rule bin_to_bl_swap[where n=m])
  apply (subst set_bit_is_bl_update[symmetric];simp del: bin_to_bl_def)
  apply simp
  done

lemma seq_update_word_conv[word_seq_convs]:
  "n < length_seq x \<Longrightarrow> seq_update x n a = word_to_seq (set_bit (seq_to_word x) (length_seq x - Suc n) a)"
  apply (rule seq_to_word_swap)
  supply [transfer_rule] = seq_to_word_list_transfer
  apply transfer
  unfolding set_bit_eq
  apply transfer
  apply (subst set_bit_eq[symmetric])
  apply (simp add: set_bit_is_bl_update_take del: bin_to_bl_def)
  by (metis bl_bin_bl length_list_update
      trunc_bl2bin_len)

lemma seq_update_end_word_conv[word_seq_convs]:
  "n < length_seq x \<Longrightarrow> seq_update_end x n a = word_to_seq (set_bit (seq_to_word x) n a)"
  unfolding seq_update_end_def
  by (simp add: seq_update_word_conv)

lemma inj_seq_to_word[simp]: "inj seq_to_word"
  apply (rule injI)
  by (simp add: eq_seq_conv)

lemma surj_seq_to_word[simp]:"surj seq_to_word"
  apply (rule surjI[of _ word_to_seq])
  by simp

lemma bij_seq_to_word[simp]: "bij seq_to_word"
  by (rule bijI[OF inj_seq_to_word surj_seq_to_word])

lemma inj_word_to_seq[simp]: "inj word_to_seq"
  apply (rule injI)
  by (simp add: eq_seq_conv)

lemma surj_word_to_seq[simp]:"surj word_to_seq"
  apply (rule surjI[of _ seq_to_word])
  by simp

lemma bij_word_to_seq[simp]: "bij word_to_seq"
  by (rule bijI[OF inj_word_to_seq surj_word_to_seq])

lemma the_inv_seq_to_word: "the_inv (seq_to_word :: ('a::len,'b::bool) seq \<Rightarrow> 'a word) = word_to_seq"
  apply (rule ext)+
  subgoal for x
    apply (induct x rule: word_as_seq_induct[where 'b='b])
      apply (subst the_inv_f_f)
      apply (rule inj_seq_to_word)
      by simp
    done

lemma the_inv_word_to_seq: "the_inv (word_to_seq :: 'a word \<Rightarrow> ('a::len,'b::bool) seq) = seq_to_word"
  apply (rule ext)+
  subgoal for x
    apply (induct x rule: seq_as_word_induct[where 'b='b])
      apply (subst the_inv_f_f)
      apply (rule inj_word_to_seq)
      by simp
    done

lemma seq_to_word_def2: "seq_to_word x = of_bl (seq_to_list x)"
  by (simp add: seq_to_list_conv)

lemma pos_nat_nat[simp]: "pos_nat (x :: ('a,'b::bool) seq) = to_nat x"
  unfolding pos_nat_def
  by simp

lemma seq_to_list_word[word_seq_convs]: "seq_to_list (word_to_seq x) = map of_bool (to_bl x)"
  by (metis Seq.map_seq_code seq_to_list_conv
      word_to_from_seq word_to_seq_of_bool)

lemma len_eq: "LEN(('a::len) len) = LEN('a)"
  by simp

lemmas coerce_seq_len_ucast_len_transfer[transfer_rule] = 
  coerce_seq_len_drop_bit_transfer[OF order_eq_refl, OF len_eq, simplified]
  coerce_seq_len_drop_bit_transfer[OF order_eq_refl, OF len_eq[symmetric], simplified]

lemma coerce_seq_len_to_len_transfer[transfer_rule]:
  "(eq_word_seq ===> eq_word_seq) UCAST('m \<rightarrow> 'm len) (coerce_seq_len :: ('m::len,'b::bool) seq \<Rightarrow> ('m len,'b) seq)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def)
  apply (simp add: word_to_seq_of_bool[where 'b='b] )
  apply (subst map_seq_coerce[symmetric])
  apply simp
  apply transfer
  by simp

lemma coerce_seq_len_of_len_transfer[transfer_rule]:
  "(eq_word_seq ===> eq_word_seq) UCAST('m len \<rightarrow> 'm ) (coerce_seq_len :: ('m::len len,'b::bool) seq \<Rightarrow> ('m,'b) seq)"
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def)
  apply (simp add: word_to_seq_of_bool[where 'b='b] )
  apply (subst map_seq_coerce[symmetric])
  apply simp
  apply transfer
  by simp

lemma coerce_seq_len_ucast[word_seq_convs]:
    "LEN('a::len) = LEN('c::len) \<Longrightarrow> coerce_seq_len (x :: ('a,'b::bool) seq) = word_to_seq (UCAST('a \<rightarrow> 'c) (seq_to_word x))"
  supply [transfer_rule] = word_to_seq_of_int_transfer
  apply (induct x rule: seq_as_word_induct)
  apply simp
  apply (simp add: word_to_seq_of_bool[where 'b='b])
  apply (subst map_seq_coerce[symmetric])
   apply simp
  by (simp add: word_seq_convs)

lemma uint_seq_zero_length[simp]: "LEN('a) = 0 \<Longrightarrow> uint_seq (x :: ('a,'b::bool) seq) = 0"
  apply transfer
  apply transfer
  by simp

lemma ucast_seq_zero_length[simp]: "LEN('a) = 0 \<Longrightarrow> ucast_seq (x :: ('a,'b::bool) seq) = 0"
  apply transfer
  apply transfer
  apply simp
  by (metis mod_0 mod_by_1 mod_pos_pos_trivial)

lemma scast_seq_zero_length[simp]: "LEN('a) = 0 \<Longrightarrow> scast_seq (x :: ('a,'b::bool) seq) = 0"
  apply (simp add: scast_seq_def)
  apply transfer
  apply transfer
  by (simp add: sint_int_def)

lemma bool_of_sign_seq: "bool_of (sign_seq x) = sign_seq (map_seq bool_of x)"
  apply transfer
  by (simp add: sign_list_def)

lemma of_bool_0_0[simp]: "(map_seq of_bool 0 :: ('a,'b::bool) seq) = 0"
  by (simp add: zero_seq_def)

lemma seq_to_word_of_bool: "seq_to_word (map_seq of_bool xs) = seq_to_word xs"
  by (meson eq_word_seq_def3 eq_word_seq_of_bool)

lemma sint_seq_trivial[simp]: "LEN('a) = 0 \<Longrightarrow> sint_seq (x :: ('a,'b::bool) seq) = 0"
  apply transfer
  apply simp
  apply transfer
  by (simp add: sint_int_def)

lemma seq_to_list_to_word: "seq_to_word x = of_bl (map bool_of (seq_to_list x :: 'c :: bool list))"
  apply (simp add: seq_to_word_def)
  apply transfer
  apply (simp add: list_to_zint_def)
  by (simp add:
      take_bit_of_to_mod_ring)

lemma list_to_seq_to_word'[abs_def, word_seq_convs]:
  "(list_to_seq bs :: ('n::len, 'b :: bool) seq)= word_to_seq (of_bl (list_len (LENGTH('n)) (map bool_of bs)))"
  supply [simp] = oob_list_elem_bool_class_def[where 'a='b]
  apply (subst list_to_seq_map_map[where f=bool_of and g=of_bool];simp)
  by (simp add: word_seq_convs seq_to_list_to_word)


(* NOTE: This subsumes all other word coerce_seq_len transfer rules *)
lemma coerce_seq_len_word_transfer: 
    "(eq_word_seq ===> eq_word_seq) (\<lambda>x. if LEN('a) = LEN('c) then ucast x else 
         if LEN('c) < LEN('a) then ucast (drop_bit (LEN('a) - LEN('c)) x)
         else of_bl (map bool_of ((list_len LEN('c) (map of_bool (to_bl x) :: 'b list)))))
          (coerce_seq_len :: ('a::len,'b::bool) seq \<Rightarrow> ('c::len,'b) seq)"
  apply (simp add: coerce_seq_len_def)
  apply (rule rel_funI)+
  apply (simp add: eq_word_seq_def word_seq_convs )
  apply (clarsimp simp add:  seq_to_list_to_word )
  apply transfer
  apply (subst take_map[symmetric])
  apply (simp del: bin_to_bl_def)
  apply (intro conjI impI)
  subgoal by (metis bin_bl_bin bin_to_bl_drop_bit
    bl_bin_bl le_add_diff_inverse
    le_eq_less_or_eq length_map
    take_bit_drop_bit)
  by (metis bl_bin_bl length_map
      list.map_comp list.map_id
      of_bool_of_comp)


lemma coerce_seq_len_numeral[simp]:
  "LEN('a) = LEN('c) \<Longrightarrow> (coerce_seq_len (numeral x :: ('a,'b::bool) seq) :: ('c,'b) seq) = numeral x"
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs )
  by (rule H;simp)

context includes seq_syntax and rotate_shift_syntax begin

private lemma shiftr_seq_to_word: "shiftr (seq_to_word xs) n = seq_to_word (xs >> n)"
  by (simp add: shift_rotate_word_defs(2)
      word_right_shift_seq)

lemma slice_end_seq_word[word_seq_convs]:
  "LENGTH('m) + n \<le> LENGTH('n) \<Longrightarrow> 
  (slice_end_seq n (xs :: ['n::len]) :: ['m::len]) = word_to_seq (slice n (seq_to_word xs))"
  apply (simp add: slice_shiftr shiftr_seq_to_word slice_end_seq_def ucast_seq_to_ucast[symmetric]
                   ucast_seq_down_is_drop right_shift_pos)
  by (rule shiftr_drop_as_rotatel_take[symmetric, simplified len_of_alt_def2];simp)


lemma times2_is_shift: "(xs :: ['n]) + xs = xs << 1"
  apply (constrain 'n="'nn::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs shift_rotate_word_defs)
  by (rule H;simp)

end

abbreviation (input) replicate_word :: "bool \<Rightarrow> 'n :: len word" where
  "replicate_word b \<equiv> of_bl (replicate LEN('n) b)"

lemma replicate_word_def2: "(replicate_word b :: 'a :: len word) = (if b then -1 else 0)"
  by (simp add: word_bl.Rep_inverse')

lemma and_replicate: "2 ^ n && replicate_word (x !! n) = ucast (2 ^ n && (x :: 'a :: len word))"
  unfolding replicate_word_def2
  supply [simp] = bit_and_iff bit_exp_iff bit_unsigned_iff
  apply (rule word_eqI)
  using bit_imp_le_length 
  by auto


primrec num_to_bl :: "num \<Rightarrow> bool list" where
  "num_to_bl (num.Bit0 n) = num_to_bl n @ [False]"
| "num_to_bl (num.Bit1 n) = num_to_bl n @ [True]"
| "num_to_bl num.One = [True]"


lemma numeral_bit1_def2: "(numeral (num.Bit1 n) ) = (numeral (num.Bit0 n)) + 1"
  by simp

lemma numeral_word_unpack: "(numeral n :: 'n :: len word) = of_bl (num_to_bl n)"
  apply (induct n;simp)
  subgoal H for x
    by (metis shiftl1_numeral
      shiftl1_of_bl)
  apply (simp only: numeral_bit1_def2)
  by (metis (no_types, lifting) ext H
      add.right_neutral list.size(4) of_bl_False
      of_bl_append word_0_bl word_1_bl)

lemma seq_update_end_is_plus: 
  "n < LEN('n) \<Longrightarrow> seq_update_end (xs :: ('n,'a::bool) seq) n 1 = (if bool_of (nth_end_seq xs n) then xs else (2 ^ n) + xs)"
  apply (constrain 'n="'nn::len")
  subgoal H[unconstrain_cases]
    unfolding seq_update_end_def nth_end_seq_def2
    apply (subst seq_update_map_map[where f=bool_of and g=of_bool];simp)
    apply (simp add: word_seq_convs set_bit_eq semiring_bit_operations_class.set_bit_eq seq_to_word_of_bool)
    by (simp add: seq_to_word_bool_of[where 'b='a])
  by (rule H;simp)

lemma list_to_seq_pad_1_Cons: 
  "(list_to_seq_pad (1 # xs) :: ('n,'a::bool) seq) = 2 ^ length xs + list_to_seq_pad xs"
  apply (constrain 'n="'nn::len")
  subgoal H[unconstrain_cases]
    apply (cases "length xs < LEN('nn)")
     apply (simp add: list_to_seq_pad_Cons seq_update_end_is_plus)
      subgoal
      unfolding nth_end_seq_def list_to_seq_pad_def
      apply simp
      by (metis Suc_diff_Suc bool_of_zero
          length_replicate lessI nth_append
          nth_replicate zero_bool_def)
    apply (simp add: list_to_seq_pad_Cons)
    by (simp add: word_seq_convs)
  by (rule H;simp)


lemma list_to_seq_pad_conv[word_seq_convs]: 
  "list_to_seq_pad xs = word_to_seq (of_bl (map bool_of xs))"
  apply (induct xs)
   apply (simp add: list_to_seq_pad_Nil word_seq_convs)
  subgoal for y ys
    apply (rule disjE[OF zero_or_one[of y]])
    by (auto simp: list_to_seq_pad_0_absorb list_to_seq_pad_1_Cons word_seq_convs)
  done
  

lemmas list_to_seq_pack' = list_to_seq_pad_none list_to_seq_pad_1_Cons list_to_seq_pad_0_absorb list_to_seq_pad_Nil
lemmas list_to_seq_pack = list_to_seq_pack'[where 'a=bool,simplified]

lemma assumes A: "x = 7"
  shows "(x :: (8,bool) seq) = list_to_seq [False, False, False, False, False, True, True, True]"
  apply (simp add: list_to_seq_pack)
  by (rule A)


lemma numeral_seq_unpack_pad: "(numeral n :: ('n,bool) seq) = list_to_seq_pad (num_to_bl n)"
  apply (constrain 'n="'nn::len")
  subgoal H[unconstrain_cases]
    by (simp add: word_seq_convs numeral_word_unpack)
  by (rule H;simp)

lemma list_to_seq_pad_expand: 
  "length xs \<le> LEN('n) \<Longrightarrow> 
    (list_to_seq_pad xs :: ('n,'a::zero) seq) = list_to_seq (replicate (LEN('n) - length xs) 0 @ xs)"
  unfolding list_to_seq_pad_def
  by simp

lemmas numeral_seq_unpack = numeral_seq_unpack_pad list_to_seq_pad_expand

lemma
  assumes A: "list_to_seq [False, False, False, False, False, True, True, True] = x"
  shows "(7 :: (8,bool) seq) = x"
  apply (simp add: numeral_seq_unpack)
  by (rule A)

lemma
  assumes A: "of_bl [True, True, True] = x"
  shows "(7 :: 8 word) = x"
  apply (simp add: numeral_word_unpack del: of_bl_True of_bl_False)
  by (rule A)

end