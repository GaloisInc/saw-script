theory Seq_Lib
imports Cryptol_Syntax Fin Seq_Code
begin

lemma inj_foldl:
  assumes inj: "inj g"
  shows "foldl f x ys = the_inv g (foldl (\<lambda>x y. g (f (the_inv g x) y)) (g x) ys)"
  apply (induct ys arbitrary: x)
  by (simp add: inj the_inv_f_f)+

lemma transpose_nth_length:
  "x \<in> set (transpose xs) \<Longrightarrow> (\<forall>x\<in>set xs. length x = n) \<Longrightarrow> (xs = [] \<Longrightarrow> n = 0) \<Longrightarrow> length x = length xs"
  apply (subst (asm) transpose_rectangle[where n=n];simp)
  using map_nth' by fastforce

lemma drop_bit0[unconstrain,simp]: "drop_bit 0 (x :: 'a :: len word) = x"
  by simp

lemma map_prodL: "(map_prod f g x = y) \<Longrightarrow> f (fst x) = fst y"
  by (cases x;cases y;simp)

lemma map_prodR: "(map_prod f g x = y) \<Longrightarrow> g (snd x) = snd y"
  by (cases x;cases y; simp)

context includes cryptol_syntax begin

lemma splitAt_word_conv[word_seq_convs]:
  "splitAt`{'n::len,'m::len,bool} k = map_prod word_to_seq word_to_seq (word_split (seq_to_word k))"
  unfolding cryptol_prim_defs
  apply (induct k rule: seq_as_word_induct)
  apply (simp add: word_seq_convs word_split_def)
  by (simp add: unsigned_take_bit_eq)

end


named_theorems seq_to_word
named_theorems seq_to_list

setup \<open>Sign.qualified_path true @{binding seq_to_word}\<close>

context includes cryptol_syntax begin

lemma coerce_seq_len[seq_to_word]:
  assumes AB: "LEN('a) = LEN('b)"
  shows "seq_to_word (coerce_seq_len (w :: ('a::len,bool) seq)) = (ucast (seq_to_word w) :: 'b :: len word)"
  supply [transfer_rule] = coerce_seq_len_drop_bit_transfer[OF eq_refl, OF AB[symmetric]]
  apply transfer
  using AB
  by simp

context assumes AB: "LEN('a) = LEN('b)" and A_pos: "LEN('a) > 0" begin
private lemma B_pos: "LEN('b) > 0" using AB A_pos by simp

lemmas coerce_seq_len0[seq_to_word] = 
  coerce_seq_len[unconstrain, OF A_pos B_pos AB]

end

context fixes each_it :: "'each::len itself" and parts_it :: "'parts::len itself" begin

lemma groupBy[seq_to_word]:
  "seq_to_list (groupBy`{'each,'parts,bool} xs) = map word_to_seq (word_rsplit (seq_to_word xs))"
  unfolding cryptol_prim_defs
  apply (induct xs rule: seq_as_word_induct)
  by (simp add: word_seq_convs map_seq_code word_split_seq.rep_eq[symmetric])

lemma join[seq_to_word]:
  "seq_to_word (join'`{'parts,'each,bool} xs) = word_rcat (map seq_to_word (seq_to_list xs))"
  unfolding cryptol_prim_defs
  by (simp add: concat_seq_map)

end

context fixes front_it :: "'front itself" and back_it :: "'back::len itself" begin

lemma drop[seq_to_word]: 
  fixes x :: "['fb::len]" 
  assumes fb: "LEN('fb) = LEN('front) + LEN('back)"
  shows "seq_to_word ((drop_seq x) :: ['back]) = ucast (take_bit LEN('back) (seq_to_word x))"
  by (metis fb le_add2 len_of_alt_def
      take_bit_length_eq
      ucast_seq_down_is_drop ucast_seq_to_ucast
      unsigned_take_bit_eq word_to_from_seq)

lemma drop'[seq_to_word]: "seq_to_word (drop'`{'front,'back,bool} w) = ucast (take_bit LEN('back) (seq_to_word w))"
  unfolding cryptol_prim_defs
  by (simp add: drop)

end

lemma take_len: 
  fixes x :: "['fb::len]" 
  assumes fb: "LEN('fb) = LEN('front::len) + LEN('back)"
  shows "seq_to_word ((take_seq x) :: ['front]) = ucast (drop_bit LEN('back) (seq_to_word x))"
  by (metis add.commute add_diff_cancel_right'
      coerce_seq_len_to_ucast_drop fb le_add1
      take_seq_def2 word_to_from_seq)

lemmas take[seq_to_word] = 
  take_len[unconstrain, where 'front="'front::len",simplified, simplified len_of_alt_def2[symmetric]]


(* Extra work needed because "'a::len + 'b" is not a "len" instance 
   (whereas "'a + 'b::len" is, which was arbitrarily chosen).

   Since this lemma is not type-correct with the existing constraints, it will only
   be applicable in a similarly unconstrained context.
*)

unconstraining 
 seq_to_word and
 unsigned and
 drop_bit
begin

lemma take'_len: "seq_to_word (take'`{'front::len,'back,bool} w) = unsigned (drop_bit LEN('back) (seq_to_word w))"
  unfolding cryptol_prim_defs
  apply (constrain 'back="'bak::len")
  subgoal H[unconstrain_cases]
    by (simp add: seq_to_word.take[where 'back='bak])
  apply (rule H)
  by (simp add: take'_def seq_to_word.coerce_seq_len0)

end

lemmas take'[seq_to_word] = seq_to_word.take'_len[unconstrain]

context fixes x z :: "['n::len]" and y :: "['m::len]" begin

lemma from_nat[seq_to_word]: "seq_to_word (from_nat n) = word_of_nat n"
  unfolding from_nat_def
  by (simp add: word_seq_convs)

lemma from_int[seq_to_word]: "seq_to_word (from_int n) = word_of_int n"
  by (simp add: word_seq_convs)

lemma of_int_seq[seq_to_word]: "seq_to_word (of_int_seq n) = word_of_int n"
  by (simp add: word_seq_convs)

lemma number[seq_to_word]: "seq_to_word (number`{'a,['m::len]}) = of_nat LEN('a)"
  unfolding number_def
  apply (subst from_nat_def[symmetric])
  by (simp add: from_nat)

lemma zext[seq_to_word]:
  "seq_to_word (zext`{'n,'m} y) = UCAST('m \<rightarrow> 'n) (seq_to_word y)"
  unfolding cryptol_prim_defs
  by transfer simp

lemma sext[seq_to_word]:
  "seq_to_word (sext`{'n,'m} y) = SCAST('m \<rightarrow> 'n) (seq_to_word y)"
  unfolding cryptol_prim_defs
  by transfer simp

lemma splitAt[seq_to_word]:
  "map_prod seq_to_word seq_to_word (splitAt`{'n,'m,bool} k) = word_split (seq_to_word k)"
  apply (simp add: word_seq_convs)
  by (simp add: word_split_bl_eq)

lemmas splitAtL[seq_to_word] = map_prodL[OF splitAt]
lemmas splitAtR[seq_to_word] = map_prodR[OF splitAt]

lemmas carry[seq_to_word] = carry_seq_conv
lemmas scarry[seq_to_word] = scarry_seq_conv
lemmas sborrow[seq_to_word] = sborrow_seq_conv               


lemma seq_update[seq_to_word]:
  "n < length_seq x \<Longrightarrow> seq_to_word (seq_update x n a) = set_bit (seq_to_word x) (length_seq x - Suc n) a"
  by (simp add: word_seq_convs)

lemma seq_updateEnd[seq_to_word]:
  "n < length_seq x \<Longrightarrow> seq_to_word (seq_update_end x n a) = set_bit (seq_to_word x) n a"
  by (simp add: word_seq_convs)

lemma seq_updates[seq_to_word]:
  "(\<And>ix. ix \<in> set_seq ixs \<longrightarrow> ix < LEN('n)) \<Longrightarrow> 
      seq_to_word (seq_updates x ixs (as :: ['n])) = 
       foldl (\<lambda>w (b,n). set_bit w (length_seq as - Suc n) b) (seq_to_word x) (zip  (seq_to_list as) (seq_to_list ixs))"
  unfolding seq_updates_def2 foldl_seq.rep_eq zip_seq.rep_eq set_seq_def
  apply simp
  apply (rule sym)
  apply (subst inj_foldl[OF inj_seq_to_word])
  apply (simp add: the_inv_seq_to_word)
  apply (rule foldl_cong;simp?)
  apply clarsimp
  apply (subst seq_update_word_conv)
   apply simp
   apply (metis in_set_zipE)
  apply simp
  done

lemma seq_updates_end[seq_to_word]:
  "(\<And>ix. ix \<in> set_seq ixs \<longrightarrow> ix < LEN('n)) \<Longrightarrow> 
      seq_to_word (seq_updates_end x ixs (as :: ['n])) = 
       foldl (\<lambda>w (b,n). set_bit w n b) (seq_to_word x) (zip  (seq_to_list as) (seq_to_list ixs))"
  unfolding seq_updates_end_def
  apply (subst seq_updates)
   apply force
  apply (simp add: map_seq_code zip_map2 foldl_map set_seq_def)
  apply (rule foldl_cong;simp?)
  by (fastforce elim: in_set_zipE)

lemma zero[seq_to_word]:
  "seq_to_word (0 :: ['n]) = 0"
  by (simp add: word_seq_convs)

lemma map_seq[seq_to_word]:
  "seq_to_word (map_seq f xs) = of_bl (map f (seq_to_list xs))"
  apply (simp add: map_seq_code[symmetric])
  by (simp add: word_seq_convs)

lemma rev_seq[seq_to_word]:
  "seq_to_word (rev_seq x :: ['n]) = word_reverse (seq_to_word x)"
  by (simp add: word_seq_convs)


lemma zipWith_seq[seq_to_word]:
  "seq_to_word (zipWith_seq f x z) = of_bl (map2 f (seq_to_list x) (seq_to_list z))"
  by (simp add: seq_to_word_def2 zipWith_seq_def zip_seq.rep_eq map_seq_code)


lemma concat_seq[seq_to_word]:
  "seq_to_word (concat_seq (s :: ('n,('m,bool) seq) seq) :: ('n \<times> 'm,bool) seq) = 
    word_rcat (map seq_to_word (seq_to_list s))"
  by (simp add: concat_seq_map)

lemma not[seq_to_word]:
  "seq_to_word (map_seq Not x) = NOT (seq_to_word x)"
  by (simp add: not_seq_conv)

lemmas sint_seq[seq_to_word] = sint_seq_conv
lemmas uint_seq[seq_to_word] = uint_seq_conv

lemmas all_seq[seq_to_word] = all_seq_id_conv
lemmas any_seq[seq_to_word] = any_seq_word_id_conv

lemma list_to_seq[seq_to_word]: "seq_to_word (list_to_seq bl) = (of_bl (list_len LEN('n) bl) :: 'n word)"
  by (simp add: seq_to_word_def2 list_to_seq.rep_eq)

lemma foldl_seq[seq_to_word]:
  "foldl_seq f a x = foldl f a (to_bl (seq_to_word x))"
  by (simp add: seq_to_word_def2 foldl_seq.rep_eq word_bl.Abs_inverse)

lemma foldr_seq[seq_to_word]:
  "foldr_seq f x a = foldr f (to_bl (seq_to_word x)) a"
  by (simp add: seq_to_word_def2 foldr_seq.rep_eq word_bl.Abs_inverse)

lemma min_seq[seq_to_word]:
  "seq_to_word (min x z) = min (seq_to_word x) (seq_to_word z)"
  unfolding min_def
  by (simp add: word_seq_convs)

lemma max_seq[seq_to_word]:
  "seq_to_word (max x z) = max (seq_to_word x) (seq_to_word z)"
  unfolding max_def
  by (simp add: word_seq_convs)

lemmas nth_seq[seq_to_word] = nth_seq_conv
lemmas nth_end_seq[seq_to_word] = nth_end_seq_conv

lemmas log2[seq_to_word] = log2_seq_conv

lemma power[seq_to_word]:
  "seq_to_word (power x n) = power (seq_to_word x) n"
  by (simp add: word_seq_convs)

lemma signed_shift[seq_to_word]: 
  "seq_to_word (signed_shift x n) = (if n \<ge> 0 then sshiftr (seq_to_word x) (nat n) else shiftl (seq_to_word x) (nat (-n)))"
  unfolding signed_shift_def
  apply transfer
  by (simp add: right_shift_def)

lemma right_rotate[seq_to_word]: 
  "seq_to_word (right_rotate x n) = word_roti n (seq_to_word x)"
  apply transfer
  by (simp add: right_rotate_word_def2)

lemma left_rotate[seq_to_word]: 
  "seq_to_word (left_rotate x n) = word_roti (-n) (seq_to_word x)"
  apply transfer
  by (simp add: left_rotate_word_def2)

lemma right_shift[seq_to_word]: 
  "seq_to_word (right_shift x n) = (if n \<ge> 0 then shiftr (seq_to_word x) (nat n) else shiftl (seq_to_word x) (nat (-n)))"
  apply transfer
  by (simp add: shift_rotate_word_defs)

lemma left_shift[seq_to_word]: 
  "seq_to_word (left_shift x n) = (if n \<ge> 0 then shiftl (seq_to_word x) (nat n) else shiftr (seq_to_word x) (nat (-n)))"
  apply transfer
  by (simp add: shift_rotate_word_defs)

lemma times[seq_to_word]: 
  "seq_to_word (x * z) = seq_to_word x * seq_to_word z"
  by (simp add: word_seq_convs)

lemma div[seq_to_word]: 
  "seq_to_word (x div z) = seq_to_word x div seq_to_word z"
  by (simp add: word_seq_convs)

lemma mod[seq_to_word]: 
  "seq_to_word (x mod z) = seq_to_word x mod seq_to_word z"
  by (simp add: word_seq_convs)

lemma plus[seq_to_word]: 
  "seq_to_word (x + z) = seq_to_word x + seq_to_word z"
  by (simp add: word_seq_convs)

lemma minus[seq_to_word]: 
  "seq_to_word (x - z) = seq_to_word x - seq_to_word z"
  by (simp add: word_seq_convs)


lemma "and"[seq_to_word]:
  "seq_to_word (map2_seq (\<and>) x z) =  (seq_to_word x) AND (seq_to_word z)"
  by (simp add: word_seq_convs)

lemma or[seq_to_word]:
  "seq_to_word (map2_seq (\<or>) x z) =  (seq_to_word x) OR (seq_to_word z)"
  by (simp add: word_seq_convs)

lemma xor[simplified, seq_to_word]:
  "seq_to_word (map2_seq (\<noteq>) x z) =  (seq_to_word x) xor (seq_to_word z)"
  by (simp add: word_seq_convs)

lemma signed_mod[seq_to_word]: 
  "seq_to_word (x smod z) = seq_to_word x smod seq_to_word z"
  by (simp add: word_seq_convs)

lemma signed_divide[seq_to_word]: 
  "seq_to_word (x sdiv z) = seq_to_word x sdiv seq_to_word z"
  by (simp add: word_seq_convs)

lemma signed_lt[seq_to_word]: 
  "(z <$ x) = (seq_to_word z <s seq_to_word x)"
  by (simp add: word_seq_convs)

lemma append_seq[seq_to_word]:
  "seq_to_word (append_seq x y :: ['nm]) = word_cat (seq_to_word x) (seq_to_word y)"
  if "LEN('nm::len) = LEN('n) + LEN('m)"
  supply [transfer_rule] = append_seq_word_transfer[OF that]
  by transfer simp

lemma lt[seq_to_word]: 
  "(z < x) = (seq_to_word z < seq_to_word x)"
  by (simp add: word_seq_convs)

lemma le[seq_to_word]: 
  "(z \<le> x) = (seq_to_word z \<le> seq_to_word x)"
  by (simp add: word_seq_convs)

lemma one[seq_to_word]:
  "seq_to_word (1 :: ['n]) = 1"
  by (simp add: word_seq_convs)

lemma numeral[seq_to_word]:
  "seq_to_word (numeral n) = (numeral n)"
  by (simp add: word_seq_convs)

lemmas abs[seq_to_word] = seq_to_word_abs


end
end

setup \<open>Sign.qualified_path true @{binding seq_to_list} o Sign.parent_path\<close>

context includes cryptol_syntax begin

lemma selects_seq[seq_to_list]:
  "seq_to_list (selects_seq x y) = map (nth_list (seq_to_list x)) (seq_to_list y)"
  by (simp add: selects_seq.rep_eq)

lemma selects_end_seq[seq_to_list]:
  "seq_to_list (selects_end_seq x y) = map (nth_end_list (seq_to_list x)) (seq_to_list y)"
  by (simp add: selects_end_seq.rep_eq)


lemma group_seq[seq_to_list]:
  "seq_to_list (group_seq (xs :: ('parts \<times> 'each,'b) seq)) =
   map list_to_seq (group_list LEN('parts) LEN('each) (seq_to_list xs))"
  unfolding cryptol_prim_defs
  by (simp add: Seq.group_seq_code)

lemma groupBy[seq_to_list]:
  "seq_to_list (groupBy`{'each,'parts,'a} xs) =
   map list_to_seq (group_list LEN('parts) LEN('each) (seq_to_list xs))"
  unfolding cryptol_prim_defs
  by (simp add: group_seq)


lemma concat_seq[seq_to_list]:
  assumes A: "LEN('nm) = LEN('n) * LEN('m)"
  shows "seq_to_list (concat_seq (xs :: ['n]['m]'e ) :: ['nm]'e) = concat (map seq_to_list (seq_to_list xs))"
  supply [transfer_rule] = concat_seq_transfer[OF A]
  by transfer simp

lemma join'[seq_to_list]:
  "seq_to_list (join'`{'parts,'each,'a} xs) = concat (map seq_to_list (seq_to_list xs))"
  unfolding cryptol_prim_defs
  by (simp add: concat_seq)

lemma drop_seq[seq_to_list]:
  assumes A: "LEN('m) \<le> LEN('n)"
  shows "seq_to_list (drop_seq (xs :: ['n]'e) :: ['m]'e) = drop (LEN('n) - LEN('m)) (seq_to_list xs)"
  apply transfer
  using A
  by simp

lemma drop'[seq_to_list]:
  "seq_to_list (drop'`{'front,'back,'a} xs) =  drop LEN('front) (seq_to_list xs)"
  unfolding cryptol_prim_defs
  by (simp add: drop_seq)

lemma take_seq[seq_to_list]:
  assumes A: "LEN('m) \<le> LEN('n)"
  shows "seq_to_list (take_seq (xs :: ['n]'e) :: ['m]'e) = take LEN('m) (seq_to_list xs)"
  apply transfer
  using A
  by simp

lemma take'[seq_to_list]:
  "seq_to_list (take'`{'front,'back,'a} xs) =  take LEN('front) (seq_to_list xs)"
  unfolding cryptol_prim_defs
  by (simp add: take_seq)

lemma fromToLessThan[seq_to_list]:
  "seq_to_list (fromToLessThan`{'lo,'hi,'a::integral}) = map from_nat [LEN('lo)..<LEN('hi)]"
  unfolding cryptol_prim_defs
  apply transfer
  apply (rule map_upt_eqI)
  by (simp add: add.commute)+

lemma fromTo[seq_to_list]:
  "LEN('lo) \<le> LEN('hi) \<Longrightarrow> 
    seq_to_list (fromTo`{'lo,'hi,'a::integral}) = map from_nat [LEN('lo)..<(Suc (LEN('hi)))]"
  unfolding cryptol_prim_defs
  apply transfer
  apply (rule map_upt_eqI;simp cong: map_upto_cong)
  by (metis add.commute less_diff_conv2 not_less_eq
      nth_upt upt_Suc)

lemma splitAt[seq_to_list]:
  "map_prod seq_to_list seq_to_list (splitAt`{'front,'back,'a} xs) = (take LEN('front) (seq_to_list xs), drop LEN('front) (seq_to_list xs))"
  unfolding cryptol_prim_defs
  by (simp add: take_seq drop_seq)

lemmas splitAtL[seq_to_list] = map_prodL[OF splitAt, simplified]
lemmas splitAtR[seq_to_list] = map_prodR[OF splitAt, simplified]


lemma fromThenTo[seq_to_list]:
  "seq_to_list (fromThenTo`{'first,'next,'last,'a::integral,'length}) = 
   map (\<lambda>i. from_int ((int LEN('next) - int LEN('first)) * int i + int LEN('first))) [0..<LEN('length)]"
  unfolding cryptol_prim_defs 
  apply transfer
  apply (rule map_upt_eqI;simp)
  done

lemma append_seq[seq_to_list]:
  "seq_to_list (append_seq (x::['n]'a) (y::['m]'a) :: ['nm]'a) = seq_to_list x @ seq_to_list y"
   if "LEN('nm) = LEN('n) + LEN('m)" 
  using that by (simp add: append_seq_def2)

lemmas scanl[seq_to_list] = scanl_seq_def
lemmas scanr[seq_to_list] = scanr_seq_def
lemmas all_seq[seq_to_list] = pred_seq_code
lemmas any_seq[seq_to_list] = any_seq.rep_eq
lemmas sum_seq[seq_to_list] = sum_seq.rep_eq
lemmas product_seq[seq_to_list] = prod_seq.rep_eq
lemmas update_seq[seq_to_list] = seq_update.rep_eq

lemma update_end_seq[seq_to_list]:
  "seq_to_list (seq_update_end xs n a) = list_update (seq_to_list xs) (length_seq xs - n - 1) a"
  by transfer simp

lemmas updates_seq[seq_to_list] = seq_updates.rep_eq

lemma updates_end_seq[seq_to_list]:
  "seq_to_list (seq_updates_end xs ixs as) = 
   list_updates (seq_to_list xs) (map (\<lambda>ix. length_seq xs - ix - 1) (seq_to_list ixs)) (seq_to_list as)"
  by transfer simp

lemmas zero_seq[seq_to_list] = zero_seq.rep_eq

lemmas map_seq[seq_to_list] = map_seq_code
lemmas rev_seq[seq_to_list] = rev_seq.rep_eq
lemmas zip_seq[seq_to_list] = zip_seq.rep_eq

lemma zip_seq_mismatched[seq_to_list]: 
  "seq_to_list (zip_seq_mismatched xs ys) = uncurry zip (truncate2 (seq_to_list xs) (seq_to_list ys))"
  apply transfer
  apply (simp add: truncate2_def)
  by (metis le_refl length_zip take_all_iff
      take_zip)

lemma zipWith_seq[seq_to_list]: "seq_to_list (zipWith_seq f xs ys) = map2 f (seq_to_list xs) (seq_to_list ys)"
  unfolding zipWith_seq_def
  by transfer simp

lemma not[seq_to_list]:
  "seq_to_list (logic_class.not x) = map logic_class.not (seq_to_list x)"
  apply simp
  by transfer simp

lemmas foldl_seq[seq_to_list] = foldl_seq.rep_eq
lemmas foldr_seq[seq_to_list] = foldr_seq.rep_eq

lemma transpose_seq[seq_to_list]:
  assumes A: "(LEN('rows) = 0 \<longrightarrow> LEN('cols) = 0)"
  shows "seq_to_list (transpose_seq (xs :: ('rows,('cols,'a) seq) seq)) = map list_to_seq (transpose (map seq_to_list (seq_to_list xs)))"
  supply [transfer_rule] = transpose_seq_transfer[OF A]
  apply transfer
  apply simp
  apply (rule sym)
  apply (rule map_idI)
  apply (rule list_len_noop)
  apply (clarsimp dest!: list_all2_pcrD)
  apply (drule(1) transpose_nth_length)
  by (auto simp: A)

lemmas transpose_seq'[seq_to_list] = transpose_seq[where 'rows="'rows::len",simplified]

lemma right_rotate[seq_to_list]:"seq_to_list (x >>> n) = seq_to_list x >>> n"
  by transfer simp

lemma left_rotate[seq_to_list]:"seq_to_list (x <<< n) = seq_to_list x <<< n"
  by transfer simp

lemma right_shift[seq_to_list]:"seq_to_list (x >> n) = seq_to_list x >> n"
  by transfer simp

lemma left_shift[seq_to_list]:"seq_to_list (x << n) = seq_to_list x << n"
  by transfer simp

lemma nth_seq[seq_to_list]:"nth_seq x n = nth_list (seq_to_list x) n"
  by transfer simp

lemma nth_end_seq[seq_to_list]:"nth_end_seq x n = nth_end_list (seq_to_list x) n"
  by transfer simp

lemma scanl_seq[seq_to_list]:
   "LEN('b) = Suc LEN('a) \<Longrightarrow> seq_to_list ((scanl_seq f x (ys :: ['a]'e)) :: ['b]'d) = scanl_list f x (seq_to_list ys)"
  by (simp add: scanl_seq_def)

lemma scanr_seq[seq_to_list]:
   "LEN('b) = Suc LEN('a) \<Longrightarrow> seq_to_list ((scanr_seq f x (ys :: ['a]'e)) :: ['b]'d) = scanr_list f x (seq_to_list ys)"
  by (simp add: scanr_seq_def)

lemma uint_seq[seq_to_list]:
  "uint_seq x = bl_to_bin (seq_to_list x)"
  apply (induct x rule: list_to_seq_raw_induct)
  apply (simp add: uint_seq_def seq_to_zint_def list_to_zint_def)
  by (metis take_bit_of_to_mod_ring trunc_bl2bin_len)

lemma sint_seq[seq_to_list]:
  "sint_seq (x :: ('a,bool) seq) = sint_int LEN('a) (bl_to_bin (seq_to_list x))"
  apply (induct x rule: list_to_seq_raw_induct)
  apply (simp add: sint_seq_def seq_to_zint_def list_to_zint_def  )
  apply transfer
  apply (clarsimp simp add: sint_int_def)
  by (metis no_bintr_alt1 trunc_bl2bin_len)

end

setup \<open>Sign.parent_path\<close>

end