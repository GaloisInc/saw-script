theory Seq 
imports Main Alt_Type_Length Coercible_Insts  Logic_Class Rotate_Shift ListOOB
begin

lemmas [simp] = list_update_beyond

lemma rel_fun_cong:
    "(\<And>x y. R1 x y \<Longrightarrow> R2 (f x) (g y) = R2 (f' x) (g' y)) \<Longrightarrow>
    ((R1 ===> R2) f g) = ((R1 ===> R2) f' g')"
  by (simp add: rel_fun_def)

typedef (overloaded) ('a, 'b) seq = "{xs :: 'b list. length xs = LEN('a)}"
  morphisms seq_to_list list_to_seq_raw
  by (auto intro!: exI[of _ "replicate _ _"])
setup_lifting type_definition_seq

abbreviation length_seq :: "('n,'a) seq \<Rightarrow> nat" where
  "length_seq _ \<equiv> LEN('n)"

(* some trickery to omit the length conversions in generated code, in the usual case where
   the given list has the expected length *)
definition list_len_checked :: "'b list \<Rightarrow> 'a itself \<Rightarrow> 'b list" where
  "list_len_checked xs _ \<equiv> (if length xs = LEN('a) then xs else seq_to_list ((list_to_seq_raw xs) :: ('a,'b) seq))"
declare [[code drop: list_len_checked]]

code_printing 
    constant list_len_checked \<rightharpoonup> (SML) "(fn '_ => _)"
  | constant list_len_checked \<rightharpoonup> (Eval) "(fn '_ => _)"


lift_definition list_to_seq :: "'b list \<Rightarrow> ('c,'b) seq" is 
  "list_len LEN('c)"
  by simp

lemma list_to_seq_transfer_strong[transfer_rule]:
  "list_all2 R xs ys \<Longrightarrow> length xs = LEN('c) \<Longrightarrow> (pcr_seq R) (list_len LEN('c) xs) ((list_to_seq ys) :: ('c,'b) seq)"
  by (simp add: cr_seq_def list_all2_lengthD
      list_to_seq.rep_eq pcr_seq_def
      relcompp_apply)


lemma list_to_seq_raw_def2[simp]: 
  "length xs = LEN('n) \<Longrightarrow> (list_to_seq_raw xs :: ('n,'a) seq) = list_to_seq xs"
  by (simp add: list_to_seq.abs_eq)

(* directional coercion rules that can be sensibly reversed if needed *)
named_theorems coerce_seq

lift_definition coerce_seq_len :: "('a,'b) seq \<Rightarrow> ('c,'b) seq" is 
  "list_len LEN('c)" by simp

lemma coerce_seq_len_leq_transfer[transfer_rule]: 
  "LEN('n) \<le> LEN('m) \<Longrightarrow> 
    (pcr_seq R ===> pcr_seq R) (\<lambda>x. take LEN('n) x) (coerce_seq_len :: ('m,'a) seq \<Rightarrow> ('n,'a) seq)"
  apply (rule rel_funI)+
  apply (simp add: pcr_seq_def cr_seq_def relcompp_apply)
  apply transfer
  by simp

lemma coerce_seq_len_transfer[transfer_rule]: 
  "LEN('n) = LEN('m) \<Longrightarrow> 
    (pcr_seq R ===> pcr_seq R) (\<lambda>x. x) (coerce_seq_len :: ('m,'a) seq \<Rightarrow> ('n,'a) seq)"
  apply (rule rel_funI)+
  apply (simp add: pcr_seq_def cr_seq_def relcompp_apply)
  apply transfer
  by simp



instantiation seq :: (_,_) len0 begin
definition "len_of_seq == (\<lambda>_. LEN('a)) :: ('a, 'b) seq itself \<Rightarrow> nat"
instance ..
end

lemma len_preserved[simp]: "length (seq_to_list (x :: ('a,'b) seq)) = LEN('a)"
  apply transfer
  apply simp
  done

lemma list_preserved[simp]: 
  "length xs = LEN('a) \<Longrightarrow> seq_to_list ((list_to_seq xs) :: ('a,'b) seq) = xs"
  by (transfer;simp)

lemma list_preserved_raw[simp]: 
  "length xs = LEN('a) \<Longrightarrow> seq_to_list ((list_to_seq_raw xs) :: ('a,'b) seq) = xs"
  by simp

lemma seq_preserved_raw[simp]: "list_to_seq_raw (seq_to_list (xs :: ('a,'b) seq)) = xs"
  by (simp add: seq_to_list_inverse)

lemma seq_preserved[simp]: "list_to_seq (seq_to_list (xs :: ('a,'b) seq)) = xs"
  by (transfer;simp)

lift_bnf (no_warn_wits) (dead 'a, 'b) seq 
  by auto
declare seq.set_map[simp]

lemma replicate_transfer [transfer_rule]:
  "(R ===> list_all2 R) (replicate n) (replicate n)"
  by transfer_prover

lift_definition replicate_seq :: "'a \<Rightarrow> ('n,'a) seq" is
  "replicate LEN('n)" parametric replicate_transfer 
  by simp

lift_definition seq_update :: "('n,'a) seq \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('n, 'a) seq" is
  "list_update" parametric list_update_transfer
  by simp

lemma map_seq_code[code abstract]: "seq_to_list (map_seq f xs) = map f (seq_to_list xs)"
  apply transfer
  by simp

lemma rel_seq_code[code]: "rel_seq f xs ys = list_all2 f (seq_to_list xs) (seq_to_list ys)"
  apply transfer
  apply simp                                                            
  done

lemma pred_seq_code[code]: "pred_seq f xs = list_all f (seq_to_list xs)"
  apply transfer
  by simp

definition list_to_seq_checked :: "'b list \<Rightarrow> ('a,'b) seq" where
  "list_to_seq_checked xs \<equiv> list_to_seq_raw xs"

definition list_to_seq_unchecked :: "'b list \<Rightarrow> ('a,'b) seq" where
  "list_to_seq_unchecked xs \<equiv> list_to_seq_raw xs"

lemma seq_to_list_roundtrip_checked: 
    "seq_to_list ((list_to_seq_checked x) :: ('a,'b) seq) = list_len_checked x TYPE('a)"
  unfolding list_to_seq_checked_def list_len_checked_def list_len_def
  by simp


lemma list_to_seq_check: 
  "LEN('a) = length xs \<Longrightarrow> ((list_to_seq xs) :: ('a,'b) seq) = ((list_to_seq_checked xs) :: ('a,'b) seq)"
  unfolding list_to_seq_checked_def
  by simp


instantiation seq :: (_,equal) equal begin
lift_definition equal_seq :: "('a,'b) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> bool" is equal_class.equal .
instance
  apply standard
  apply (simp add: equal_seq_def[abs_def] equal_eq)
  by (metis seq_preserved)
end

lift_definition seq_all2 :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('n,'a) seq \<Rightarrow> ('m, 'b) seq \<Rightarrow> bool" is
  "list_all2" parametric list.rel_transfer .

lemma rel_seq_def2: "rel_seq = seq_all2"
  apply (rule ext)+
  apply transfer
  apply simp
  done

lemma seq_all2_is_eq[relator_eq]: "seq_all2 (=) = (=)"
  by (metis rel_seq_def2 seq.rel_eq)

lemma seq_all2_map1: "seq_all2 P (map_seq f xs) ys = seq_all2 (\<lambda>x y. P (f x) y) xs ys"
  apply transfer
  by (simp add: list.rel_map(1))

lemma seq_all2_map2: "seq_all2 P xs (map_seq f ys) = seq_all2 (\<lambda>x y. P x (f y)) xs ys"
  apply transfer
  by (simp add: list.rel_map(2))

context 
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes same_len[simp]: "LEN('n) = LEN('m)" begin

lemma seq_all2_left_total[transfer_rule,simp]:
  "left_total R \<Longrightarrow> left_total ((seq_all2 R) :: ('n,'a) seq \<Rightarrow> ('m,'b) seq \<Rightarrow> bool)"
  apply (clarsimp simp add: left_total_def)
  apply transfer
  apply clarsimp
  by (metis (no_types, lifting) length_map
      list.rel_map(2) list_all2_same)
  
lemma seq_all2_right_total[transfer_rule,simp]:
  "right_total R \<Longrightarrow> right_total ((seq_all2 R) :: ('n,'a) seq \<Rightarrow> ('m,'b) seq \<Rightarrow> bool)"
  apply (clarsimp simp add: right_total_def)
  apply transfer
  apply clarsimp
  by (metis (no_types, lifting) length_map
    list.rel_map(1) list_all2_same)

lemma seq_all2_bi_total[transfer_rule,simp]:
  "bi_total R \<Longrightarrow> bi_total ((seq_all2 R) :: ('n,'a) seq \<Rightarrow> ('m,'b) seq \<Rightarrow> bool)"
  by (simp add: bi_total_alt_def)

end

lemma pcr_seq_len: "(pcr_seq R :: 'b list \<Rightarrow> ('n,'a) seq \<Rightarrow> bool) xs ys \<Longrightarrow> length xs = LEN('n)"
  by (simp add: pcr_seq_def cr_seq_def relcompp_apply list_all2_lengthD)


lemma seq_all2_left_unique[transfer_rule,simp]:
  "left_unique R \<Longrightarrow> left_unique (seq_all2 R)"
  apply (clarsimp simp add: left_unique_def)
  apply transfer
  by (metis (mono_tags, lifting)
      list_all2_conv_all_nth nth_equalityI)

lemma seq_all2_right_unique[transfer_rule,simp]:
  "right_unique R \<Longrightarrow> right_unique (seq_all2 R)"
  apply (clarsimp simp add: right_unique_def)
  apply transfer
  by (metis (mono_tags, lifting)
      list_all2_conv_all_nth nth_equalityI)

lemma seq_all2_bi_unique[transfer_rule,simp]:
  "bi_unique R \<Longrightarrow> bi_unique (seq_all2 R)"
  by (simp add: bi_unique_alt_def)

lemmas [transfer_rule,simp] =
  seq_all2_left_total[OF refl]
  seq_all2_right_total[OF refl]
  seq_all2_bi_total[OF refl]

lemma seq_eq_transfer[transfer_rule]: "(pcr_seq (=) ===> pcr_seq (=) ===> (=)) (=) (=)"
  apply (rule eq_transfer)
  by (simp add: bi_unique_eq seq.bi_unique)


instantiation seq :: (_,finite) finite begin
instance
  apply standard
  apply (rule finite_surj[where A="{x. length x = LEN('a)} :: 'b list set" and f=list_to_seq])
   apply (rule finite_list_length)
  apply safe
  apply (rule image_eqI)
   apply (rule seq_preserved[symmetric])
  apply simp
  done
end

lemma coerce_seq_len_same[simp]: "coerce_seq_len = (\<lambda>x. x)"
  apply (rule ext)
  apply transfer
  apply simp
  done

lemma seq_preserved2[simp]: 
  "LEN('n) = LEN ('m) \<Longrightarrow> list_to_seq (seq_to_list (xs :: ('n,'b) seq) ) = (coerce_seq_len xs :: ('m,'b) seq)"
  by (clarsimp simp add: coerce_seq_len_def)

lemma coerce_seq_len_absorb[simp]: 
  "LEN('n) = LEN ('m) \<Longrightarrow> 
    (coerce_seq_len ((coerce_seq_len (s :: ('n,'a) seq)) :: ('m,'a) seq) :: ('j,'a) seq) = coerce_seq_len s"
  by (transfer;simp)

lemma map_seq_coerce[simp, coerce_seq]:
 "LEN('n) = LEN('m) \<Longrightarrow> 
  map_seq f ((coerce_seq_len (s :: ('m,'a) seq)) :: ('n,'a) seq) = coerce_seq_len (map_seq f s)"
  by (transfer;simp)


lemma seq_rel_eq: "seq_all2 (=) s1 s2 = (s1 = s2)"
  apply transfer
  by (simp add: list.rel_eq)

lemma seq_all2_mono: "rel_seq P xs ys \<Longrightarrow>
(\<And>xs ys. P xs ys \<Longrightarrow> Q xs ys) \<Longrightarrow> seq_all2 Q xs ys"
  apply transfer
  using list_all2_mono by blast

lemma seq_all2_same: "seq_all2 (\<lambda>x y. x = f y) (map_seq f s) s"
  apply transfer'
  by (simp add: list_all2_map1 list_all2_same)

lift_definition nth_end_seq :: "('a,'b) seq \<Rightarrow> nat \<Rightarrow> 'b" is 
 "nth_end_list :: 'b list \<Rightarrow> nat \<Rightarrow> 'b" .

lift_definition nth_seq :: "('a,'b) seq \<Rightarrow> nat \<Rightarrow> 'b" is 
 "\<lambda>xs i. (nth_list (xs :: 'b list) i) :: 'b" .

lift_definition oob_seq_elem :: "('a,'b) seq \<Rightarrow> 'b" is oob_list_elem .

lift_definition rev_seq :: "('a,'e) seq \<Rightarrow> ('a,'e) seq" is
  "rev" parametric rev_transfer
  by simp

lemma rev_seq_nth_alt: "i < length_seq x \<Longrightarrow> nth_seq x i = nth_seq (rev_seq x) ((length_seq x  - i - 1))"
  apply transfer
  apply simp
  by (metis nth_rev_alt)

lemma rev_seq_nth: "i < length_seq x \<Longrightarrow> nth_seq (rev_seq x) i = nth_seq x (length_seq x - i - 1)" 
  apply transfer
  by (simp add: rev_nth)


lemma nth_end_seq_def2: "nth_end_seq xs i = (if i < length_seq xs then nth_seq xs (length_seq xs - i - 1) else oob_seq_elem (rev_seq xs))"
  by (transfer;auto)

lemma map_seq_nth[simp]: "i < LEN('n) \<Longrightarrow> nth_seq (map_seq f (s :: ('n,'a) seq)) i = f (nth_seq s i)"
  by (transfer;simp)

definition nth_mod_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "nth_mod_list l n \<equiv> nth_list l (n mod length l)"

lemma nth_mod_list_bound: "n < length l \<Longrightarrow> nth_mod_list l n = (l ! n)"
  by (simp add: nth_mod_list_def)

lemma 
  cr_seq_def2:
  "cr_seq l (s :: ('n,'a) seq) = (LEN('n) = length l \<and> (\<forall>i<LEN('n). l ! i = nth_seq s i))"
  apply (simp add: cr_seq_def)
  apply transfer
  by (auto simp add: list_eq_iff_nth_eq)

lemma 
  pcr_seq_def2:
  "pcr_seq = (\<lambda>R l (s :: ('n,'a) seq). (LEN('n) = length l \<and> (\<forall>i<LEN('n). R (l ! i) (nth_seq s i))))"
  apply (rule ext)+
  apply (simp add: pcr_seq_def[abs_def] cr_seq_def2[abs_def])
  apply (simp add: list_all2_conv_all_nth relcompp_apply
                   nth_seq.rep_eq)
  by (metis len_preserved)


lemma pcr_seq_eq[simp]:
  "length l2 = LEN('n) \<Longrightarrow> (pcr_seq (=) l1 ((list_to_seq l2) :: ('n,'a) seq)) = (l1 = l2)"
  apply (rule iffI)
  by (simp add: pcr_seq_def2 nth_seq.rep_eq nth_equalityI)+

lift_definition nth_mod_seq :: "('a,'e) seq \<Rightarrow> nat \<Rightarrow> 'e" is
  "nth_mod_list" .

lemma map_mod_nth: "(s = [] \<Longrightarrow> oob_list_elem [] = f (oob_list_elem [])) \<Longrightarrow> nth_mod_list (map f (s :: 'a list)) i = f (nth_mod_list s i)"
  apply (simp add: nth_mod_list_def)
  apply (induct s)
   apply simp
  apply simp
  by (metis length_Cons length_greater_0_conv
      less_Suc_eq list.simps(9) list.size(3)
      mod_less_divisor nth_map)

lemma map_mod_nth'[simp]: "s \<noteq> [] \<Longrightarrow> nth_mod_list (map f (s :: 'a list)) i = f (nth_mod_list s i)"
  by (simp add: map_mod_nth)

lemma map_seq_mod_nth: "(LEN('n) = 0 \<Longrightarrow> oob_list_elem [] = f (oob_list_elem [])) \<Longrightarrow> nth_mod_seq (map_seq f (s :: ('n,'a) seq)) i = f (nth_mod_seq s i)"
  apply transfer
  by (metis list.size(3) map_mod_nth)

lemma map_seq_mod_nth'[simp]: "LEN('n) > 0 \<Longrightarrow> nth_mod_seq (map_seq f (s :: ('n,'a) seq)) i = f (nth_mod_seq s i)"
  by (simp add: map_seq_mod_nth)

lemma nth_seq_def2: "n < length_seq s \<Longrightarrow> nth_seq s n = nth_mod_seq s n"
  apply transfer
  by (simp add: nth_mod_list_def)

lemma nth_mod_seq_transfer:
  "(LEN('n) = 0 \<Longrightarrow> R (oob_list_elem []) (oob_list_elem [])) \<Longrightarrow> (pcr_seq R ===> (=) ===> R) nth_mod_list (nth_mod_seq :: ('n,'a) seq \<Rightarrow> nat \<Rightarrow> 'a)"
  apply (rule rel_funI)+
  apply (cases "LEN('n) = 0")
  apply (metis len_preserved length_0_conv
      nth_list_oob(1) nth_mod_list_def nth_mod_seq.rep_eq
      pcr_seq_len)
  apply simp
  by (simp add: nth_mod_list_def
      nth_mod_seq.rep_eq nth_seq.rep_eq
      pcr_seq_def2)

lemma nth_mod_seq_mod_absorb: "nth_mod_seq xs (i mod length_seq xs) = nth_mod_seq xs i"
  apply transfer
  by (simp add: nth_mod_list_def)

definition nonzero :: "nat \<Rightarrow> bool" where
  "nonzero n \<equiv> n > 0"
declare nonzero_def[simp]

lemma nonzero_len[transfer_rule]: "nonzero (LEN('n::len))"
  by simp

lemma nonzero_length[transfer_rule]: "nonzero (LENGTH('n::len))"
  by simp

lemma nth_mod_seq_transfer'[transfer_rule]:
  "nonzero LEN('n) \<Longrightarrow> (pcr_seq R ===> (=) ===> R) nth_mod_list (nth_mod_seq :: ('n,'a) seq \<Rightarrow> nat \<Rightarrow> 'a)"
  by (simp add: nth_mod_seq_transfer)

lemmas nth_mod_seq_transfer_len[transfer_rule] = 
  nth_mod_seq_transfer'[where 'a="'a :: len",simplified len_of_alt_def2 nonzero_def,OF len_gt_0]

lemma nth_mod_seq_transfer_eq[transfer_rule]:
  "(pcr_seq (=) ===> (=) ===> (=)) nth_mod_list (nth_mod_seq :: ('n,'a) seq \<Rightarrow> nat \<Rightarrow> 'a)"
  by (simp add: nth_mod_seq_transfer)

  
lemma 
  pcr_seq_def3:
  "pcr_seq = (\<lambda>R l (s :: ('n,'a) seq). (length l = LEN('n) \<and> (LEN('n) > 0 \<longrightarrow>  (\<forall>i. R (l ! (i mod LEN('n))) (nth_mod_seq s i)))))"
  apply (rule ext)+
  apply (simp add: pcr_seq_def2 nth_seq_def2)
  apply (rule iffI)
  apply (simp add: nth_mod_list_def
      nth_mod_seq.rep_eq)
  apply clarsimp
  by (metis less_nat_zero_code list.size(3)
      mod_less)

lemma "oob_list_elem (seq_to_list y) = oob_seq_elem y"
  apply transfer
  by simp

definition oob_rel:: "'n itself \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "oob_rel _ R \<equiv> (\<forall>(xs :: 'a list) (ys :: ('n,'b) seq). pcr_seq R xs ys \<longrightarrow> R (oob_list_elem xs) (oob_seq_elem ys))"

lemma oob_rel_eq[simp]: "oob_rel n (=)"
  by (simp add: oob_rel_def pcr_seq_def cr_seq_def relcompp_apply oob_seq_elem.rep_eq list.rel_eq)

lemma oob_rel_eq_dr[transfer_domain_rule]: "oob_rel n (=) = True"
  by simp

lemma oob_relD: 
  "oob_rel TYPE('n) R \<Longrightarrow> (\<And>xs (ys :: ('n,'a) seq). pcr_seq R xs ys \<Longrightarrow> R (oob_list_elem xs) (oob_seq_elem ys))"
  by (simp add: oob_rel_def)

lemma oob_rev_relD: 
  "oob_rel TYPE('n) R \<Longrightarrow> (\<And>xs (ys :: ('n,'a) seq). pcr_seq R xs ys \<Longrightarrow> R (oob_list_elem (rev xs)) (oob_seq_elem (rev_seq ys)))"
  apply (rule oob_relD)
   apply simp
  by (metis apply_rsp' rev_seq.transfer)

lemma nth_end_seq_transfer[transfer_rule]:
  assumes R_oob:"oob_rel TYPE('n) R"
  shows "(pcr_seq R ===> (=) ===> R) nth_end_list (nth_end_seq :: ('n,'a) seq \<Rightarrow> nat \<Rightarrow> 'a)"
  apply (rule rel_funI)+
  apply (clarsimp simp add: pcr_seq_def2 nth_end_seq.rep_eq nth_seq.rep_eq 
                     split: nth_end_list_splits)+
  apply (rule oob_rev_relD[OF R_oob, simplified oob_seq_elem.rep_eq rev_seq.rep_eq])
  by (simp add: nth_seq.rep_eq pcr_seq_def2)

lemma nth_end_seq_transfer_eq[transfer_rule]:
  "(pcr_seq (=) ===> (=) ===> (=)) nth_end_list (nth_end_seq :: ('n,'a) seq \<Rightarrow> nat \<Rightarrow> 'a)"
  by (simp add: nth_end_seq_transfer)

lemmas nth_mod_seq_transfer_len1[transfer_rule] = 
  nth_mod_seq_transfer'[where 'n="'n :: len", simplified]


(* for non_equality relations this is a bit awkward, so we don't use it by default *)
lemma seq_nth_transfer:
  "(pcr_seq R ===> (\<lambda>n m. n = m \<and> n < LEN('a)) ===> R) (!) (nth_seq :: ('a,'e) seq \<Rightarrow> nat \<Rightarrow> 'e)"
  apply (rule rel_funI)+
  by (simp add: pcr_seq_def2 nth_seq.rep_eq)

lift_definition append_seq :: "(('a,'e) seq \<Rightarrow> ('b,'e) seq \<Rightarrow> ('c,'e) seq)" is
  "\<lambda>x y. list_len LEN('c) (x @ y)" by simp

lemma append_seq_def2: "append_seq x y = list_to_seq (seq_to_list x @ seq_to_list y)"
  apply transfer
  by simp

context assumes abc: "LEN('c) = LEN('a) + LEN('b)" begin
lift_definition append_seq2 :: "(('a,'e) seq \<Rightarrow> ('b,'e) seq \<Rightarrow> ('c,'e) seq)" is
  "\<lambda>a b. a @ b" parametric append_transfer
  by (simp add: abc)

lemma append_seq_def3: "append_seq = append_seq2"
  apply (rule ext)+
  apply transfer
  apply (simp add: abc)
  done

lemmas append_seq_transfer[transfer_rule] = append_seq2.transfer[simplified append_seq_def3[symmetric]]
end

lemma len_step[transfer_rule]: "LEN('c) > 0 \<Longrightarrow> LEN('c) = LEN(1) + (LEN('c-1))"
  by simp

lemma list_to_seq_cons:
  assumes A[transfer_rule]: "LEN('n) > 0"
  shows "LEN('n-1) = length bs \<Longrightarrow> (list_to_seq (b#bs) :: ('n,'a) seq) =
   append_seq (list_to_seq [b] :: (1,'a) seq) ((list_to_seq bs) :: ('n-1,'a) seq)"
  apply transfer
  apply simp
  using assms by linarith

lemma len_ab[transfer_rule]: "LEN('a + 'b) = LEN('a) + LEN('b)"
  by simp

context assumes n1: "LEN('n1) = LEN('n) + 1" begin
lift_definition cons_seq :: "'a \<Rightarrow> ('n,'a) seq \<Rightarrow> ('n1,'a) seq" is
  "\<lambda>a b. a # b" parametric List.list.ctr_transfer(2)
  by (simp add: n1)
end

lemma len_suc[transfer_rule]: "LEN('n + 1) = LEN('n) + 1"
  by simp


lift_definition selects_seq :: "('a,'e) seq \<Rightarrow> ('b,nat) seq \<Rightarrow> ('b,'e) seq" is
  "\<lambda>xs ids. map (\<lambda>i. nth_list xs i) ids" by simp

lemma selects_seq_def2: "selects_seq xs ids = map_seq (nth_seq xs) ids"
  apply transfer
  by simp

lemma seq_selects_transfer:
  "(pcr_seq R ===> pcr_seq (\<lambda>n m. n = m \<and> n < LEN('a))  ===> pcr_seq R) 
      (\<lambda>xs ids. map (\<lambda>i. xs ! i) ids) (selects_seq :: ('a,'e) seq \<Rightarrow> ('n,nat) seq \<Rightarrow> ('n,'e) seq)"
  apply (rule rel_funI)+
  apply (simp add: pcr_seq_def2)
  apply transfer
  by force

lift_definition selects_end_seq :: "('a,'e) seq \<Rightarrow> ('b,nat) seq \<Rightarrow> ('b,'e) seq" is
  "\<lambda>xs ids. map (\<lambda>i. nth_end_list xs i) ids" by simp

lemma selects_end_seq_def2: "selects_end_seq xs ids = map_seq (nth_end_seq xs) ids"
  apply transfer
  by simp





lift_definition zip_seq :: "('n,'a) seq \<Rightarrow> ('n,'b) seq \<Rightarrow> ('n, 'a \<times> 'b) seq" is
  "zip" parametric zip_transfer
  by simp

lemma zip_seq_nth[simp]: 
  "i < LEN('n) \<Longrightarrow> nth_seq (zip_seq s1 s2 :: ('n,'a \<times> 'b) seq) i = (nth_seq s1 i,nth_seq s2 i)"
  by (transfer;simp)

abbreviation (input) uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> (('a \<times> 'b) \<Rightarrow> 'c)" where
  "uncurry f \<equiv> (\<lambda>(a,b). f a b)"


definition zipWith_seq :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('n,'a) seq \<Rightarrow> ('n,'b) seq \<Rightarrow> ('n,'c) seq" where
  "zipWith_seq f a b \<equiv> map_seq (uncurry f) (zip_seq a b)"

lemma zipWith_seq_nth[simp]: 
  "i < LEN('n) \<Longrightarrow> nth_seq (zipWith_seq f s1 s2 :: ('n,'c) seq) i = f (nth_seq s1 i) (nth_seq s2 i)"
  by (simp add: zipWith_seq_def)

definition truncate2 :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a list \<times> 'b list)" where
  "truncate2 a b == (take (min (length a) (length b)) a, take (min (length a) (length b)) b)"

lemma truncate2_length1[simp]: "length (fst (truncate2 a b)) = min (length a) (length b)"
  by (simp add: truncate2_def)

lemma truncate2_nth1[simp]: "i < (length a) \<Longrightarrow> i < (length b) \<Longrightarrow> fst (truncate2 a b) ! i = a ! i"
  by (simp add: truncate2_def)

lemma truncate2_length2[simp]: "length (snd (truncate2 a b)) = min (length a) (length b)"
  by (simp add: truncate2_def)

lemma truncate2_nth2[simp]: "i < (length a) \<Longrightarrow> i < (length b) \<Longrightarrow> snd (truncate2 a b) ! i = b ! i"
  by (simp add: truncate2_def)

lemma truncate2_transfer [transfer_rule]: 
   "(list_all2 A ===> list_all2 B ===> rel_prod (list_all2 A) (list_all2 B))
     truncate2 truncate2"
  unfolding truncate2_def
  by transfer_prover

lift_definition truncate2_seq :: "('n,'a) seq \<Rightarrow> ('m,'b) seq \<Rightarrow> (('n,'m) Min, 'a) seq \<times> (('n,'m) Min, 'b) seq" 
  is "truncate2" parametric truncate2_transfer
  by (simp add: truncate2_def)

lemma truncate2_seq_nth1[simp]:
  "i < length_seq a \<Longrightarrow> i < length_seq b \<Longrightarrow> nth_seq (fst (truncate2_seq a b)) i = nth_seq a i"
  apply transfer
  by simp

lemma truncate2_seq_nth2[simp]:
  "i < length_seq a \<Longrightarrow> i < length_seq b \<Longrightarrow> nth_seq (snd (truncate2_seq a b)) i = nth_seq b i"
  apply transfer
  by simp



lemma seq_update_nth[simp]: 
  "i < LEN('n) \<Longrightarrow> nth_seq (seq_update s j a :: ('n,'a) seq) i 
      = (if i = j then a else nth_seq s i)"
  by (transfer;simp)

definition seq_update_end :: "('n,'a) seq \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('n, 'a) seq" where
  "seq_update_end xs ix x \<equiv> seq_update xs (LEN('n) - ix - 1) x"

lemma seq_update_end_transfer[transfer_rule]:
  "(pcr_seq A ===> (=) ===> A ===> pcr_seq A) (\<lambda>xs ix. list_update xs (length xs - ix - 1)) seq_update_end"
  unfolding seq_update_end_def
  apply (simp add: pcr_seq_len cong: rel_fun_cong)
  by transfer_prover

lift_definition upto_seq :: "('n,nat) seq" is "[0..<(LEN('n))]" by simp

lemma upto_seq_nth[simp]: "i < LEN('n) \<Longrightarrow> nth_seq (upto_seq :: ('n,nat) seq) i = i"
  apply transfer
  apply simp
  done

lemma upto_seq_nth_f[simp]: "i < LEN('n) \<Longrightarrow> nth_seq (map_seq f (upto_seq :: ('n,nat) seq)) i = f i"
  apply transfer
  apply simp
  done

lemma map_upto_nth[simp]: "map_seq (nth_seq x) upto_seq = x"
  apply transfer
  apply (simp cong: map_upto_cong)
  done

lift_definition map_index_seq :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> ('n,'a) seq \<Rightarrow> ('n, 'b) seq" is
  "map_index_list" parametric map_index_list_transfer by simp

lemma map_index_seq_nth[simp]: 
  "i < LEN('n) \<Longrightarrow> nth_seq (map_index_seq f s :: ('n,'b) seq) i = f i (nth_seq s i)"
  by (transfer;simp)

definition zip_seq_mismatched :: "('n,'a) seq \<Rightarrow> ('m,'b) seq \<Rightarrow> (('n,'m) Min, 'a \<times> 'b) seq" where
  "zip_seq_mismatched a b \<equiv> uncurry zip_seq (truncate2_seq a b)"

lemma zip_is_truncate: "zip = (\<lambda>a b. uncurry zip (truncate2 a b))"
  apply (rule ext)+
  subgoal for a b
    apply (induct a b rule: list_induct2')
    by (simp add: truncate2_def)+
  done

lemma zip_seq_mismatched_transfer[transfer_rule]: 
  "(pcr_seq P ===> pcr_seq Q ===> pcr_seq (rel_prod P Q)) zip zip_seq_mismatched "
  unfolding zip_seq_mismatched_def
  apply (subst zip_is_truncate)
  by transfer_prover

lemma zip_seq_mismatched_def2: "zip_seq_mismatched s l = zip_seq (coerce_seq_len s) (coerce_seq_len l)"
  apply transfer
  apply simp
  by (metis le_refl length_zip take_all_iff
      take_zip)

primrec group_list :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "group_list 0 each xs = []"
| "group_list (Suc parts) each xs =
      ((take each xs)) # group_list parts each (drop each xs)"

lemma group_list_length[simp]: "\<And>xs. length (group_list parts each xs) = parts"
  by (induct parts;simp)

lemma group_list_grouped:
  "\<And>xs. length xs = parts * each \<Longrightarrow> \<forall>x\<in>set (group_list parts each xs). length x = each"
  apply (induct parts;simp)
  by (metis diff_add_inverse length_drop)


lemma group_list_sub_elems:
  "\<And>xs. length xs = parts * each \<Longrightarrow> \<forall>x\<in>set (group_list parts each xs). set x \<subseteq> set xs"
  apply (induct parts;simp)
  by (metis add_diff_cancel_left' dual_order.trans
      length_drop set_drop_subset
      set_take_subset)

lemma group_list_sub_list:
  "\<And>xs. \<forall>x\<in>set (group_list parts each xs). (\<exists>j. x = take each (drop j xs))"
  apply (induct parts;simp)
  apply (rule conjI)
   apply (metis drop0)
  apply clarsimp
  by force

lemma group_list_each_length[simp]:
  "\<And>xs. length xs = parts * each \<Longrightarrow> n < parts \<Longrightarrow> length (group_list parts each xs ! n) = each"
  by (metis group_list_grouped
      group_list_length nth_mem)

lemma group_list_part: "\<And>xs p.
  length xs = parts * each \<Longrightarrow>
  p < parts \<Longrightarrow>
  group_list parts each xs ! p =  take each (drop (p * each) xs)"
  apply (induct parts;simp)
  by (metis add.commute add_diff_cancel_left' drop0
      drop_drop length_drop less_Suc_eq_0_disj
      nth_Cons' plus_1_eq_Suc
      times_nat.simps)



lemma group_list_elem: "\<And>xs p e.
  length xs = parts * each \<Longrightarrow>
  p < parts \<Longrightarrow>
  e < each \<Longrightarrow>
  group_list parts each xs ! p ! e = xs ! ((p * each) + e)"
  by (simp add: group_list_part)
  
  
lemma group_list_all_elems:
  "\<And>xs. length xs = parts * each \<Longrightarrow>  \<Union> (set (map set (group_list parts each xs))) = (set xs)"
  apply (induct parts;simp)
  by (metis atd_lem set_append)


fun unzip :: "('a \<times> 'b) list \<Rightarrow> ('a list \<times> 'b list)" where
  "unzip [] = ([],[])"
| "unzip ((a,b)#xs) = (let (as,bs) = unzip xs in (a#as,b#bs))"  

lemma unzip_zip[simp]:
  "length xs = length ys \<Longrightarrow> unzip (zip xs ys) = (xs,ys)"
  apply (induct rule: list_induct2;simp)
  done

lemma group_list_zip:
  "\<And>xs ys. length xs = length ys \<Longrightarrow> 
    (zip (group_list parts each xs) (group_list parts each ys)) =
    map unzip (group_list parts each (zip xs ys))"
  apply (induct parts;simp)
  apply (rule conjI)
   apply (simp add: take_zip)
  apply (simp add: drop_zip)
  done


lemma group_list_transfer[transfer_rule]:
  "(list_all2 A ===> list_all2 (list_all2 A)) (group_list parts each) (group_list parts each)"
  apply (rule rel_funI)+
  apply (rule list_all2I)
   apply (subst group_list_zip)
  using list_all2_lengthD apply blast
   apply clarsimp
   apply (drule group_list_sub_list[rule_format])
   apply (simp add: drop_zip take_zip)
  using list_all2_lengthD apply fastforce
  by force

lift_definition group_seq :: "((('parts * 'each),'a) seq \<Rightarrow> ('parts,('each, 'a) seq) seq)" is
  "group_list (LEN('parts)) (LEN('each))" parametric group_list_transfer
  apply simp
  apply (simp add: list_all2_conv_all_nth relcompp_apply
                   pcr_seq_def2
                   nth_seq.rep_eq)
  subgoal for xs
    apply (rule exI[of _ "map (list_to_seq) (group_list LEN('parts) LEN('each) xs)"])
    apply (intro impI conjI allI;simp?)
    done
  done

lemma group_seq_code[code abstract]: "seq_to_list (group_seq (xs :: ('parts \<times> 'each, 'a) seq )) = 
   map list_to_seq (group_list LEN('parts) LEN('each) (seq_to_list xs))"
  apply (simp add: group_seq_def)
  apply clarsimp
  by (metis group_list_grouped len_of_alt_def
      len_of_prod_def len_preserved
      list_to_seq_raw_def2)

lemma parts_each_bound:
    "p < (parts ::nat) \<Longrightarrow>
    e < each \<Longrightarrow>
    p * each + e < (parts * each)"
  using td_gal_lt by auto



lemma group_seq_nth_nth': 
  assumes p_parts[simp]: "p < LENGTH('parts::len)"
      and e_each[simp]: "e < LENGTH('each::len)"
    shows "nth_seq (nth_seq (group_seq (xs :: ((('parts * 'each),'a) seq))) p) e = nth_seq xs ((p * LENGTH('each)) + e)"
  apply (simp add: nth_seq_def2 parts_each_bound)
  apply (insert p_parts e_each)
  apply transfer
  apply (simp add: nth_mod_list_def)
  by (simp add: group_list_part parts_each_bound)

lemma group_seq_nth_nth: 
  "p < LEN('parts) \<Longrightarrow>
   e < LEN('each) \<Longrightarrow>
   nth_seq (nth_seq (group_seq (xs :: ((('parts * 'each),'a) seq))) p) e = nth_seq xs ((p * LEN('each)) + e)"
  apply (simp add: len_of_alt_def2)
  apply (rule group_seq_nth_nth'[unconstrain])
  by auto

lemma group_list_map: "map (map f) (group_list n m xs) = group_list n m (map f xs)"
  apply (induct n arbitrary: m xs)
   apply simp
  by (simp add: drop_map take_map)

lemma group_seq_map: "map_seq (map_seq f) (group_seq xs) = group_seq (map_seq f xs)"
  apply transfer
  apply (simp add: group_list_map)
  done


lemma take_transfer[transfer_rule]:
  "(list_all2 A ===> list_all2 A) (take n) (take n)"
  by transfer_prover

lemma drop_transfer[transfer_rule]:
  "(list_all2 A ===> list_all2 A) (drop n) (drop n)"
  by transfer_prover

lift_definition take_seq :: "(('frontback,'a) seq \<Rightarrow> ('front, 'a) seq)" is
  "list_len LEN('front)"
  by simp

lemma take_seq_def2: "take_seq xs = coerce_seq_len xs"
  apply transfer
  by simp

context assumes fb[simp]: " LEN('frontback) = LEN('front) + LEN('back)" begin

lift_definition take_seq2 :: "(('frontback,'a) seq \<Rightarrow> ('front, 'a) seq)" is
  "take LEN('front)" parametric take_transfer
  by simp

lemma take_seq2_def2: "take_seq2 s = take_seq s"
  apply (induct s rule: list_to_seq_raw_induct)
  apply (subst take_seq2.abs_eq)
   apply (simp add: eq_onp_def)
  by (simp add: take_seq_def)

lemmas take_seq_transfer[transfer_rule] = take_seq2.transfer[simplified take_seq2_def2[abs_def]]

lemma take_seq_0[simp]:
  "LEN('back) = 0 \<Longrightarrow> (take_seq (s :: ('frontback,'a) seq) :: ('front,'a) seq) = coerce_seq_len s"
  by (transfer;simp)

end

lemma take_seq_transfer_le[transfer_rule]:
  "(LEN('front) \<le> LEN('frontback)) \<Longrightarrow> 
    (pcr_seq A ===> pcr_seq A) (take (LEN('front))) (take_seq :: (('frontback,'a) seq \<Rightarrow> ('front, 'a) seq))"
  unfolding take_seq_def
  apply (rule rel_funI)+
  by (simp add: pcr_seq_def cr_seq_def relcompp_apply)

lift_definition drop_seq :: "(('frontback,'a) seq \<Rightarrow> ('back, 'a) seq)" is
  "\<lambda>xs. list_len LEN('back) (drop (LEN('frontback) - LEN('back)) xs)" by simp

lemma drop_seq_transfer[transfer_rule]: "LEN('back) \<le> LEN('frontback) \<Longrightarrow>
     (pcr_seq A ===> pcr_seq A) (drop (LEN('frontback) - LEN('back)))
     (drop_seq :: (('frontback,'a) seq \<Rightarrow> ('back, 'a) seq))"
  apply (rule rel_funI)+
  by (clarsimp simp add: pcr_seq_def cr_seq_def relcompp_apply drop_seq_def)

lemmas [transfer_rule] = 
          drop_seq_transfer[where 'back='back and 'frontback="'front + 'back" , simplified]

abbreviation (input) drop_seq' :: "(('front + 'back,'a) seq \<Rightarrow> ('back, 'a) seq)" where
  "drop_seq' \<equiv> drop_seq"

lemma split_seq_simp[simp]: 
  "group_seq (s :: (('parts + 1) \<times> ('each), 'a) seq) = 
    (let (s' :: ('each + ('parts * 'each),'a) seq) = coerce_seq_len s in
     (cons_seq (take_seq s')
       (group_seq (drop_seq' s'))))"
  by (transfer;simp)

lemma take_seq_list:
  assumes same_len[transfer_rule, simp]: "LEN ('n) = LEN('front) + LEN('back)"
  shows "(take_seq (s :: ('n,'a) seq) :: ('front, 'a) seq) = list_to_seq (take LEN('front) (seq_to_list s))"
  by (transfer;simp)

lemma append_take_drop_plus[simp]:
  "append_seq (take_seq (s :: ('front + 'back, 'a) seq) :: ('front,'a) seq) (drop_seq' s) = s"
  by (transfer;simp)

lemma concat_map_len:
  "(\<And>x. length (f x) = z) \<Longrightarrow>
       length (concat (map f xs)) = z * (length xs)"
  by (induct xs;simp)

lemma concat_fixed_len:
  "(\<And>x. x \<in> set xss \<Longrightarrow> length x = z) \<Longrightarrow>
       length (concat xss) = z * (length xss)"
  by (induct xss;simp)


lemma list_all2_2: 
    "list_all2 P xs zs \<Longrightarrow>
     list_all2 Q ys zs \<Longrightarrow>
    i < length xs \<Longrightarrow>
    P (xs ! i) (zs ! i) \<and> Q (ys ! i) (zs ! i)"
  by (simp add: list_all2_conv_all_nth)

definition concat_seq :: "('n, ('m, 'b) seq) seq \<Rightarrow> ('k, 'b) seq" where
  "concat_seq xss \<equiv> list_to_seq (concat (seq_to_list (map_seq seq_to_list xss)))"



context assumes asm[simp]: "LEN('k) = LEN('n) * LEN('m)" begin
lift_definition concat_seq2 :: 
  "('n, ('m, 'b) seq) seq \<Rightarrow> ('k, 'b) seq" is
  "concat" parametric concat_transfer
  apply simp
  apply (clarsimp simp:  relcompp_apply
                   pcr_seq_def2 
                   nth_seq.rep_eq)
  apply (rule context_conjI)
   apply (subst concat_fixed_len[where z="LEN('m)"])
  using list_all2_2 nth_the_index the_index_bounded
    apply fastforce
  apply (simp add: list_all2_conv_all_nth)
  apply (rule arg_cong[where f=concat])
  by (auto simp add: list_all2_conv_all_nth
           intro!: nth_equalityI)

lemma concat_seq_def2: "concat_seq = concat_seq2"
  apply (rule ext)+
  apply (simp add: concat_seq_def)
  apply transfer
  apply simp
  by (metis (no_types, lifting) ext asm concat_fixed_len
      cr_seq_def2 in_set_conv_nth list_all2_conv_all_nth
      list_preserved list_to_seq.rep_eq mult_commute_abs
      seq.pcr_cr_eq)

lemma concat_seq2_list_transfer: "(pcr_seq (seq_all2 R) ===> pcr_seq R) (\<lambda>xs. concat (map seq_to_list xs)) concat_seq2"
  apply (rule rel_funI)+
  apply (simp add: pcr_seq_def relcompp_apply cr_seq_def)
  apply transfer
  apply clarsimp
  by (metis apply_rsp' concat_transfer)

lemmas concat_seq_transfer[transfer_rule] = concat_seq2.transfer[simplified concat_seq_def2[symmetric]]
lemmas concat_seq_list_transfer = concat_seq2_list_transfer[simplified concat_seq_def2[symmetric]]
end

lemma 
  coerce_list_to_seq[simp]:
  "length s = LEN('n) \<Longrightarrow> coerce_seq_len ((list_to_seq s) :: ('n,'a) seq) = list_to_seq s"
  by (transfer;simp)

lemma coerce_seq_to_list[simp]:
  "LEN('n) = LEN('m) \<Longrightarrow> 
    (seq_to_list ((coerce_seq_len (s :: ('n,'a) seq)) :: ('m,'a) seq)) = seq_to_list s"
  by (transfer;simp)

abbreviation (input) concat_seq_map :: "('a \<Rightarrow> ('m, 'b) seq) \<Rightarrow> ('n, 'a) seq \<Rightarrow> ('k, 'b) seq" where
  "concat_seq_map f s \<equiv>  concat_seq (map_seq f s)"

instantiation seq :: (_, strip_type) strip_type begin
definition "strip_type_seq == (\<lambda>_. T [Tn (LEN('a)), strip_type (TYPE('b))] STR ''seq'') :: ('a,'b) seq itself \<Rightarrow> stripped_type"
instance ..
end

lemma seq_type_name[simp]: "type_name TYPE(('n,'a::strip_type) seq) = STR ''seq''"
  by (simp add: strip_type_seq_def type_name_def)

lemma not_same_type_seq[simp]: "\<not> same_type TYPE('a::strip_type) TYPE(('n,'a) seq)"
  apply (simp add: same_type_def strip_type_seq_def)
  apply (insert strip_type_nonrec[where 'a='a])
  apply (cases "strip_type TYPE('a)";simp)
  by (metis list.set_intros)

lemmas [THEN not_same_type_sym, simp] = not_same_type_seq

instantiation seq :: (_, strip) strip begin
definition "strip_seq (x :: ('a,'b) seq) \<equiv> strip (seq_to_list x)"
instance ..
end

instantiation seq :: (_, unstrip) unstrip begin
definition "unstrip_seq (x :: stripped) \<equiv> list_to_seq (unstrip x)"
instance ..
end

instantiation seq :: (_, coercible) coercible begin
instance
  supply [simp] = strip_seq_def unstrip_seq_def 
  by (standard;simp?)
end


instantiation seq :: (_, coercible_atom) coercible_atom begin
instance
  supply [simp] = strip_seq_def unstrip_seq_def 
  by (standard;simp?)
end

lemma unstrip_atom_seq_def: 
  "unstrip_atom x = 
     ((case x of S xs \<Rightarrow> list_to_seq (map unstrip_atom xs)) :: ('a,'b::coercible_atom) seq)"
  by (cases x;simp add: unstrip_atom_def unstrip_seq_def)


lemma unstrip_seq: "unstrip_atom (S xs) = (list_to_seq (map unstrip_atom xs) :: ('a,'b::coercible_atom) seq)"
  by (simp add: unstrip_atom_seq_def)

lemma seq_same_type[simp,code_unfold]: 
  "same_type (TYPE(('a,'d::strip_type) seq)) (TYPE(('b,'c::strip_type) seq)) = (LEN('a) = LEN('b) \<and> same_type TYPE('d) TYPE('c))"
  by (simp add: same_type_def strip_type_seq_def)

interpretation seq: coercion 
  "\<lambda>(x :: ('a,'d::coercible) seq).
   (map_seq coerce (coerce_seq_len x)) :: ('b,'c::coercible) seq"
  apply standard
  apply simp
  apply (simp add: strip_seq_def unstrip_seq_def)
  apply transfer
  apply simp
  done

declare seq.map_id[abs_def, simp, code_unfold]

definition coerce_seq_len_checked :: "('a,'b) seq \<Rightarrow> ('c,'b) seq" where
  "coerce_seq_len_checked x \<equiv> coerce_seq_len x" if "LEN('a) = LEN('c)"

code_printing 
    constant coerce_seq_len_checked \<rightharpoonup> (SML) "_"
  | constant coerce_seq_len_checked \<rightharpoonup> (Eval) "_"

lemma coerce_seq_len_check[code_unfold]: 
  "LEN('a) = LEN('b) \<Longrightarrow> coerce_seq_len (x :: ('a,'c) seq) = (coerce_seq_len_checked x :: ('b,'c) seq)"
  by (simp add: coerce_seq_len_checked_def)

value "(coerce :: ((2,bool) seq \<Rightarrow> (1+1,bool) seq)) (list_to_seq [True, False])"

lemma map_seq_id2[simp]:
  "map_seq (\<lambda>x. x) = (\<lambda>x. x)"
  using seq.map_ident by blast

lift_definition any_seq :: "('a \<Rightarrow> bool) \<Rightarrow> ('n,'a) seq \<Rightarrow> bool" is 
 "\<lambda>P xs. \<not> list_all (\<lambda>x. \<not> P x) xs" .

abbreviation "all_seq \<equiv> pred_seq"

lemma any_seq_not_not_all: "any_seq P xs = (\<not> all_seq (\<lambda>x. \<not> P x) xs)"
  by transfer simp
  
lemma all_seq_def2: "all_seq f xs = (\<forall>i<(length_seq xs). f (nth_seq xs i))"
  apply transfer
  by (fastforce simp add: list_all_length nth_list_def)

lemma all_seq_mod_nth: "all_seq f xs = (length_seq xs > 0 \<longrightarrow> (\<forall>i. f (nth_mod_seq xs i)))"
  apply transfer
  apply (simp add: list_all_length nth_mod_list_def nth_list_def)
  by (metis len_cases' mod_less_divisor nat_mod_lem
      not_less_zero)

lemma any_seq_def2: "any_seq f xs = (\<exists>i<(length_seq xs). f (nth_seq xs i))"
  by (simp add: any_seq_not_not_all all_seq_def2)

lemma any_seq_mod_nth: "any_seq f xs = (length_seq xs > 0 \<and> (\<exists>i. f (nth_mod_seq xs i)))"
  by (simp add: any_seq_not_not_all all_seq_mod_nth)

instantiation seq :: (_, zero) zero begin
lift_definition zero_seq :: "('a,'b::zero) seq" is "replicate LEN('a) 0" by simp
instance ..
end

lemma zero_seq_def2: "0 = replicate_seq 0"
  apply transfer
  apply simp
  done


lemma replicate_seq_nth[simp]: "i < LEN('n)  \<Longrightarrow> nth_seq (replicate_seq x :: ('n,'a) seq) i = x"
  by (transfer;simp)  

lemma replicate_seq_eq: "((replicate_seq x :: ('n,'a) seq) = s) = (\<forall>i. i < LEN('n) \<longrightarrow> nth_seq s i = x)"
  apply transfer
  apply (rule iffI)
   apply fastforce
  by (metis length_replicate nth_equalityI
      nth_replicate nth_list_nth)
  
abbreviation (input) map2_seq :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('n,'a) seq \<Rightarrow> ('n,'b) seq \<Rightarrow> ('n,'c) seq" where
  "map2_seq f a b \<equiv> map_seq (\<lambda>(a',b'). f a' b') (zip_seq a b)"

lemma map2_eqI: 
  "length a = length b \<Longrightarrow> 
   length b = length c \<Longrightarrow>
  list_all2 (\<lambda>(a',b') c'. f a' b' = c') (zip a b) c \<Longrightarrow> map2 f a b = c"
  by (induct a b c rule: list_induct3;simp)

lemma seq_all2_nthI: 
  "length_seq a = length_seq b \<Longrightarrow> 
   (\<And>i. i < length_seq a \<Longrightarrow> R (nth_seq a i) (nth_seq b i)) \<Longrightarrow> seq_all2 R a b"
  apply transfer
  apply (rule list_all2_all_nthI)
  by simp+

lemma seq_all2_nth_modI: 
  "length_seq a = length_seq b \<Longrightarrow> 
    0 < length_seq a \<Longrightarrow>
   (\<And>i. R (nth_mod_seq a i) (nth_mod_seq b i)) \<Longrightarrow> seq_all2 R a b"
  by (simp add: nth_seq_def2
      seq_all2_nthI)

lemma seq_all2_lengthD [intro?]: "seq_all2 R a b \<Longrightarrow> length_seq a = length_seq b"
  apply transfer
  by (simp add: list_all2_lengthD)

lemma seq_all2_nthD: 
  "seq_all2 R a b \<Longrightarrow> i < length_seq a \<Longrightarrow> R (nth_seq a i) (nth_seq b i)"
  apply transfer
  by (simp add: list_all2_conv_all_nth)

lemma seq_all2_nthD2: 
  "seq_all2 R a b \<Longrightarrow> i < length_seq b \<Longrightarrow> R (nth_seq a i) (nth_seq b i)"
  apply transfer
  by (simp add: list_all2_conv_all_nth)

lemma seq_all2_replicate1:
  "LEN('n) = length_seq b \<Longrightarrow> seq_all2 R (replicate_seq x :: ('n,'a) seq) b = all_seq (\<lambda>b'. R x b') b"
  apply transfer
  apply simp
  by (simp add: list_all2_conv_all_nth list_all_length)

lemma all_seqI[intro!]: "(\<And>i. i < LEN('n) \<Longrightarrow> P (nth_seq (s :: ('n,'a) seq) i)) \<Longrightarrow> all_seq P s"
  apply transfer
  by (simp add: list_all_length)

lemma all_seq_modI: "(\<And>i. LEN('n) > 0 \<Longrightarrow> P (nth_mod_seq (s :: ('n,'a) seq) i)) \<Longrightarrow> all_seq P s"
  apply (rule all_seqI)
  by (simp add: nth_seq_def2)

lemma all_seqD[dest!]: "all_seq P s \<Longrightarrow> (\<And>i. i < LEN('n) \<Longrightarrow> P (nth_seq (s :: ('n,'a) seq) i))"
  apply transfer
  by (simp add: list_all_length)

lemma all_seqE[elim!]: "all_seq P s \<Longrightarrow> ((\<And>i. i < LEN('n) \<Longrightarrow> P (nth_seq (s :: ('n,'a) seq) i)) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  apply transfer
  by (simp add: list_all_length)

lemma map2_seq_all2_eqI: 
  "seq_all2 (\<lambda>(a',b') c'. f a' b' = c') (zip_seq a b) c \<Longrightarrow> map2_seq f a b = c"
  apply transfer
  by (rule map2_eqI;simp)

lemma nth_seq_zip[simp]:
  "i < length_seq a \<Longrightarrow> nth_seq (zip_seq a b) i = (nth_seq a i, nth_seq b i)"
  apply transfer
  by auto

lemma zero_len_trivial[simp]:
  "LEN('n) = 0 \<Longrightarrow> (x :: ('n,'a) seq) = y"
  by (metis (full_types) len_preserved
      length_greater_0_conv less_not_refl
      seq_to_list_inject)

lemma map2_nth_eqI: 
  "(\<And>i. i < length_seq a \<Longrightarrow> f (nth_seq a i) (nth_seq b i) = nth_seq c i) \<Longrightarrow> 
    map2_seq f a b = c"
  apply (rule map2_seq_all2_eqI)
  apply (rule seq_all2_nthI)
  by auto

lemma map_nth_eqI: 
  "(\<And>i. i < length_seq a \<Longrightarrow> f (nth_seq a i) = nth_seq c i) \<Longrightarrow> 
    map_seq f a = c"
  apply transfer
  by (metis (mono_tags, lifting) length_map
      nth_equalityI nth_list_nth nth_map)

lemma nth_eq_map2[simp]:
  "i < length_seq a \<Longrightarrow> nth_seq (map2_seq f a b) i = f (nth_seq a i) (nth_seq b i)"
  apply transfer
  by simp

lemma nth_eq_map[simp]:
  "i < length_seq a \<Longrightarrow> nth_seq (map_seq f a) i = f (nth_seq a i)"
  apply transfer
  by auto

instantiation seq :: (_,logic) logic begin
definition "nand_seq \<equiv> map2_seq nand"
instance ..
end

lemma and_logic_seq[simp]: "logic_class.and = map2_seq logic_class.and"
  by (auto intro!: ext map2_nth_eqI simp add: logic_class.and_def[abs_def] nand_seq_def)

lemma or_logic_seq[simp]: "logic_class.or = map2_seq logic_class.or"
  by (auto intro!: ext map2_nth_eqI simp add: logic_class.or_def[abs_def] nand_seq_def)

lemma not_logic_seq[simp]: "logic_class.not = map_seq logic_class.not"
  by (auto intro!: ext map_nth_eqI simp add: logic_class.not_def[abs_def] nand_seq_def)
  
lemma xor_logic_seq[simp]: "logic_class.xor = map2_seq logic_class.xor"
  by (auto intro!: ext map2_nth_eqI simp add: logic_class.xor_def[abs_def] nand_seq_def)

primrec scanl_list :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b list" where
   "scanl_list f b (x#xs) = b # (scanl_list f (f b x) xs)"
 | "scanl_list _ b [] = [b]"

lemma scanl_list_length[simp]: "length (scanl_list f b xs) = length xs + 1"
  by (induct xs arbitrary: b;simp)
  
lemma scanl_list_nonempty[simp]: "scanl_list f b xs \<noteq> []"
  by (metis neq_Nil_conv scanl_list.simps)
  

lemma scanl_list_transfer[transfer_rule]:
  "((B ===> A ===> B) ===> B ===> list_all2 A ===> list_all2 B) scanl_list scanl_list"
  apply (rule rel_funI)+
  subgoal for f g a b xs ys
    apply (induct xs ys arbitrary: a b rule: list_induct2')
       apply simp+
    by (metis apply_rsp')
  done

lemma scanl_list_append[simplified Let_def]: "scanl_list f b (xs @ ys) = 
  (let 
    xs' = scanl_list f b xs
  in butlast xs' @ scanl_list f (last xs') ys)"
  apply (induct xs arbitrary: b ys)
   apply simp
  apply (simp add: Let_def)
  done

lemma rev_butlast[simp]: "rev (butlast xs) = tl (rev xs)"
  by (metis butlast_rev rev_rev_ident)

definition scanr_list :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "scanr_list f b xs \<equiv> rev (scanl_list (\<lambda>b a. f a b) b (rev xs))"

lemma scanl_list_hd[simp]: "hd (scanl_list f b xs) = b"
  by (induct xs;simp)

lemma scanr_list_last[simp]: "last (scanr_list f b xs) = b"
  by (simp add: scanr_list_def last_rev)

lemma scanr_list_Nil[simp]: "scanr_list f b [] = [b]"
  by (simp add: scanr_list_def)

lemma scanr_list_Cons[simp]:
    "scanr_list f b (x # xs) = f x (hd (scanr_list f b xs)) # (scanr_list f b xs)"
  apply (simp add: scanr_list_def scanl_list_append last_rev[symmetric])
  by (metis hd_rev list.collapse rev_is_Nil_conv scanl_list_nonempty)

lemma scanr_list_length[simp]: "length (scanr_list f b xs) = length xs + 1"
  by (simp add: scanr_list_def)
  
lemma scanr_list_nonempty[simp]: "scanr_list f b xs \<noteq> []"
  by (simp add: scanr_list_def)


lemma scanr_list_append[simplified Let_def]: "scanr_list f b (xs @ ys) = 
  (let 
    ys' = scanr_list f b ys
  in butlast (scanr_list f (hd ys') xs) @ ys')"
  apply (induct ys arbitrary: b xs rule: rev_induct)
   apply simp+
   apply (metis scanr_list_last scanr_list_nonempty snoc_eq_iff_butlast)
  apply (simp add: Let_def)
  by (simp add: scanr_list_def)


lemma scanr_list_transfer[transfer_rule]:
  "((A ===> B ===> B) ===> B ===> list_all2 A ===> list_all2 B) scanr_list scanr_list"
  unfolding scanr_list_def
  by transfer_prover

experiment begin
lemma 
  "scanl_list (+) 0 ([2,-3,4,5] :: int list) = 
    [0, 2, -1, 3, 8]"
  by simp
lemma 
  "scanr_list (+) 0 ([2,-3,4,5] :: int list) = 
    [8, 6, 9, 5, 0]"
  by (simp add: scanr_list_def)
end


definition scanl_seq :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('n,'a) seq \<Rightarrow> ('m,'b) seq" where
  "scanl_seq f b xs \<equiv> list_to_seq (scanl_list f b (seq_to_list xs))"

definition scanr_seq :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('n,'a) seq \<Rightarrow> ('m,'b) seq" where
  "scanr_seq f b xs \<equiv> list_to_seq (scanr_list f b (seq_to_list xs))"

context assumes A: "LEN('m) = Suc LEN('n)" begin

lift_definition scanl_seq2 :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('n,'a) seq \<Rightarrow> ('m,'b) seq"
  is "scanl_list" parametric scanl_list_transfer by (simp add: A)

lemma scanl_seq_def2: "scanl_seq = scanl_seq2"
  apply (rule ext)+
  apply (simp add: scanl_seq_def)
  apply transfer
  by (simp add: A)

lift_definition scanr_seq2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ('n,'a) seq \<Rightarrow> ('m,'b) seq"
  is "scanr_list" parametric scanr_list_transfer by (simp add: A)

lemma scanr_seq_def2: "scanr_seq = scanr_seq2"
  apply (rule ext)+
  apply (simp add: scanr_seq_def)
  apply transfer
  by (simp add: A)

lemmas scanl_seq_transfer[transfer_rule] = scanl_seq2.transfer[simplified scanl_seq_def2[symmetric]]
lemmas scanr_seq_transfer[transfer_rule] = scanr_seq2.transfer[simplified scanr_seq_def2[symmetric]]
end

lift_definition foldl_seq :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ('n,'b) seq \<Rightarrow> 'a" 
  is foldl parametric List.foldl_transfer .

lemma foldl_seq_cong[cong]: 
  "a = a' \<Longrightarrow> 
   xs = xs' \<Longrightarrow> 
  (\<And>a b. b \<in> set_seq xs \<Longrightarrow> f a b = f' a b) \<Longrightarrow> 
  foldl_seq f a xs = foldl_seq f' a' xs'"
  apply transfer
  by (rule foldl_cong;assumption)

lemma foldl_seq_map: "foldl_seq f x (map_seq g xs) = foldl_seq (\<lambda>a b. f a (g b)) x xs"
  apply transfer  
  by (simp add: foldl_map)

lift_definition foldr_seq :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('n,'a) seq  \<Rightarrow> 'b \<Rightarrow> 'b"
  is foldr parametric List.foldr_transfer .

lemma foldr_seq_cong[cong]: 
  "a = a' \<Longrightarrow> 
   xs = xs' \<Longrightarrow> 
  (\<And>a b. a \<in> set_seq xs \<Longrightarrow> f a b = f' a b) \<Longrightarrow> 
  foldr_seq f xs a = foldr_seq f' xs' a'"
  apply transfer
  by (rule foldr_cong;assumption)

lemma foldr_seq_map: "foldr_seq f (map_seq g xs) x = foldr_seq (\<lambda>a b. f (g a) b) xs x"
  apply transfer  
  by (simp add: foldr_map comp_def)

lemma rotate_transfer': 
  "(list_all2 A ===> (=) ===> list_all2 A) (\<lambda>n xs. rotate xs n) (\<lambda>n xs. rotate xs n)"
  by transfer_prover

lemma rotater_transfer':
  "(list_all2 A ===> (=) ===> list_all2 A) (\<lambda>n xs. rotater xs n) (\<lambda>n xs. rotater xs n)"
  by transfer_prover

lift_definition rotatel_seq :: "('n,'a) seq \<Rightarrow> nat \<Rightarrow> ('n,'a) seq"
  is "\<lambda>n xs. rotate xs n" parametric rotate_transfer' by simp

lift_definition rotater_seq :: "('n,'a) seq \<Rightarrow> nat \<Rightarrow> ('n,'a) seq"
  is "\<lambda>n xs. rotater xs n" parametric rotater_transfer' by simp

lemma rotate_seq_nth[simp]: "n < length_seq s \<Longrightarrow>
    nth_seq (rotatel_seq s m) n =
    nth_seq s ((m + n) mod length_seq s)"
  by (transfer; simp add: nth_rotate)

lift_definition shiftl_seq :: "'a \<Rightarrow> ('n,'a) seq \<Rightarrow> nat \<Rightarrow> ('n, 'a) seq" 
  is shiftl_list parametric shiftl_list_transfer by simp

lift_definition shiftr_seq :: "'a \<Rightarrow> ('n,'a) seq \<Rightarrow> nat \<Rightarrow> ('n, 'a) seq"
  is shiftr_list parametric shiftr_list_transfer by simp

lemma shiftl_seq0[simp]: "shiftl_seq x xs 0 = xs"
  by transfer simp

lemma shiftr_seq0[simp]: "shiftr_seq x xs 0 = xs"
  by transfer simp

instantiation seq :: (_, _) rotate_ops begin
definition "left_rotate_nat_seq (s :: ('a,'b) seq) n \<equiv> rotatel_seq s n"
definition "right_rotate_nat_seq (s :: ('a,'b) seq) n \<equiv> rotater_seq s n"
instance ..
end
lemmas [simp] = left_rotate_nat_seq_def right_rotate_nat_seq_def

instantiation seq :: (_,zero) shift_ops begin
definition "left_shift_nat_seq (s :: ('a,'b) seq) n \<equiv> shiftl_seq 0 s n"
definition "right_shift_nat_seq (s :: ('a,'b) seq) n \<equiv> shiftr_seq 0 s n"
instance ..
end
lemmas [simp] = left_shift_nat_seq_def right_shift_nat_seq_def

instantiation seq :: (_, _) zero_size begin
definition "size_seq (_ :: ('a,'b) seq) = LEN('a)"
instance by (standard; simp add: size_seq_def)
end
lemmas [simp] = size_seq_def[abs_def]

lemma size_seq_transfer[transfer_rule]: 
  shows "(pcr_seq R ===> (=)) size size"
  apply simp
  apply (rule rel_funI)
  by (simp add: pcr_seq_def2)
lemmas [simplified, transfer_rule] = size_seq_transfer


lemma right_shift_seq_transfer[transfer_rule]:
  assumes R0[transfer_rule]: "R 0 0"
  shows "(pcr_seq R ===> (=) ===> pcr_seq R) right_shift right_shift"
  apply (simp add: right_shift_def[abs_def] cong: if_cong)
  by transfer_prover

lemma right_rotate_seq_transfer[transfer_rule]:
  "(pcr_seq R ===> (=) ===> pcr_seq R) right_rotate right_rotate"
  apply (simp add: right_rotate_def[abs_def] cong: if_cong)
  by transfer_prover

instantiation seq :: (_,_) rotate_size begin
instance
  supply axs = right_rotate_mod right_rotate_0 right_rotate_add rotate_eqs rotater_eqs
  apply (standard; (simp add: right_shift_defs right_rotate_defs add.commute del:size_seq_def[abs_def])?; transfer; (rule axs)?)
  by (simp add: right_rotate_defs)
end


instantiation seq :: (_,zero) rotate_shift_size begin
instance
  supply axs = right_shift_0 right_shift_add
  apply (standard; (simp del:size_seq_def[abs_def])?; transfer; (rule axs)?)
  by simp+
end

context includes rotate_shift_syntax begin

lemma left_rotate_seq_transfer[transfer_rule]: 
  "(pcr_seq R ===> (=) ===> pcr_seq R) (<<<) (<<<)"
  unfolding left_rotate_def
  by transfer_prover

lemma left_shift_seq_transfer[transfer_rule]: 
  assumes R0[transfer_rule]: "R 0 0"
  shows "(pcr_seq R ===> (=) ===> pcr_seq R) (<<) (<<)"
  unfolding left_shift_def
  by transfer_prover


lemma left_shift_seq_nth:
  "n < length_seq l \<Longrightarrow> 
   nth_seq (l << i) n = (if i \<ge> 0 then 
        (if n + (nat i) < length_seq l then nth_seq l (n +nat i) else 0)
        else (if n \<ge> nat (-i) then nth_seq l (n - nat (-i)) else 0))"
  apply (simp only: nth_seq_def2 cong: if_cong)
  apply transfer
  apply (simp only: nth_mod_list_bound left_shift_size cong: if_cong)
  by (subst left_shift_list_nth;simp)

lemma left_shift_seq_nth_simps[simp]:
  assumes n_bounded: "n < length_seq l"
  shows
  "i \<ge> 0 \<Longrightarrow> n + i < length_seq l \<Longrightarrow> nth_seq (l << i) n = nth_seq l (n + i)"
  "i \<ge> 0 \<Longrightarrow> n + i \<ge> length_seq l \<Longrightarrow> nth_seq (l << i) n = 0"
  "i \<le> 0 \<Longrightarrow> n \<ge> nat (-i) \<Longrightarrow> nth_seq (l << i) n = nth_seq l (n - nat (-i))"
  "i \<le> 0 \<Longrightarrow> n < nat (-i) \<Longrightarrow> nth_seq (l << i) n = 0"
  using n_bounded
  by (auto simp: left_shift_seq_nth)

lemma right_shift_seq_nth:
  "n < length_seq l \<Longrightarrow> 
   nth_seq (l >> i) n = (if i \<le> 0
     then if n + nat (-i) < length_seq l
          then nth_seq l (n + nat (-i)) else 0
     else if nat i \<le> n
          then nth_seq l (n - (nat i)) else 0)"
  apply (subst right_shift_neg)
  by (simp add: left_shift_seq_nth)

lemma right_shift_seq_nth_simps[simp]:
  assumes n_bounded: "n < length_seq l"
  shows
  "i \<le> 0 \<Longrightarrow> n + nat (-i) < length_seq l \<Longrightarrow> nth_seq (l >> i) n = nth_seq l (n + nat (-i))"
  "i \<le> 0 \<Longrightarrow> n + nat (-i) \<ge> length_seq l \<Longrightarrow> nth_seq (l >> i) n = 0"
  "i \<ge> 0 \<Longrightarrow> i \<le> n \<Longrightarrow> nth_seq (l >> i) n = nth_seq l (n - i)"
  "i \<ge> 0 \<Longrightarrow> i > n \<Longrightarrow> nth_seq (l >> i) n = 0"
  using n_bounded
  by (auto simp: right_shift_seq_nth)


lemma left_rotate_seq_nth[simp]: 
  "(n :: nat) < length_seq l \<Longrightarrow> 
   nth_seq (l <<< i) n = nth_seq l (nat ((i + int n) mod (int (length_seq l))))"
  apply (simp only: nth_seq_def2 cong: if_cong)
  apply transfer
  by (simp add: nth_mod_list_bound nat_less_iff)

lemma right_rotate_seq_nth[simp]:
  "(n :: nat) < length_seq l \<Longrightarrow> 
   nth_seq (l >>> i) n = nth_seq l (nat ((int n - i) mod int (length_seq l)))"
  apply (simp only: nth_seq_def2 cong: if_cong)
  apply transfer
  by (simp add: nth_mod_list_bound nat_less_iff)


lemma transpose_len_eq:
  "length xs = length ys \<Longrightarrow> (\<And>i. length xs = length ys \<Longrightarrow> i < length xs \<Longrightarrow> length (xs ! i) = length (ys ! i)) \<Longrightarrow> 
         length (transpose xs) = length (transpose ys)"
  apply (simp add: length_transpose)
  apply (induct xs ys rule: list_induct2;simp)
  by (metis Suc_less_eq nth_Cons_0 nth_Cons_Suc
      zero_less_Suc)

lemma nth_seq_list[simp]:
  "i < length l \<Longrightarrow> i < LEN('n) \<Longrightarrow> nth_seq ((list_to_seq l) :: ('n,'a) seq) i = l ! i"
  apply transfer
  by (simp add: list_len_def)

lemma pcr_seqI: "length l = length_seq s \<Longrightarrow> 
       (\<And>i. i < length_seq s \<Longrightarrow> R (l ! i) (nth_seq s i)) \<Longrightarrow> pcr_seq R l s"
  by (simp add: pcr_seq_def2)

lemma pcr_seq_listI:
  "length xs = LEN('n) \<Longrightarrow> pcr_seq (=) xs ((list_to_seq xs) :: ('n,'a) seq)"
  by (rule pcr_seqI;simp)


lemma list_all2_len_helper:
  "list_all2 (pcr_seq (=)) xs (s :: ('n,'a) seq list) \<Longrightarrow> x \<in> set xs \<Longrightarrow> length x = LEN('n)"
  by (auto simp add: pcr_seq_def2 in_set_conv_nth list_all2_conv_all_nth)

lemma list_all2_pcrD[dest]:
  "list_all2 (pcr_seq (=)) xs (s :: ('n,'a) seq list) \<Longrightarrow> ((\<forall>x \<in> set xs. length x = LEN('n)) \<and> length xs = length s)"
  using list_all2_len_helper
    list_all2_lengthD by blast

lemma foldr_max[simp]:
  "xs \<noteq> [] \<Longrightarrow> foldr (\<lambda>x. max (y :: nat)) xs 0 = y"
  by (induct xs rule: list_nonempty_induct; simp)

lemma list_all2_filter_len:
  "list_all2 (list_all2 R) x y \<Longrightarrow> 
   list_all2 (list_all2 R) (filter (\<lambda>xs. f (length xs)) x) (filter (\<lambda>xs. f (length xs)) y)"
  apply (induct x y rule: list_all2_induct)
  by (auto simp: list_all2_lengthD)

lemma list_all2_pcr_seq[simp]:
  "list_all2 (pcr_seq (=)) xs b \<Longrightarrow> list_all2 (pcr_seq (=)) ys b \<Longrightarrow> xs = ys"
  by (simp add: cr_seq_def list_all2_conv_all_nth
      nth_equalityI seq.pcr_cr_eq)

lemma list_all2_nth_nth:
  "(list_all2 (list_all2 R)) x y \<Longrightarrow> i < length x \<Longrightarrow> j < length (x ! i) \<Longrightarrow> R (x ! i ! j) (y ! i ! j)"
  by (meson list_all2_conv_all_nth)


lemma transpose_transfer[transfer_rule]:
  "(list_all2 (list_all2 R) ===> list_all2 (list_all2 R)) transpose transpose"
  apply (rule rel_funI)+
  subgoal premises prems for x y
  proof -
    have same_len: "length (transpose x) = length (transpose y)"
      apply (insert prems)
      apply (rule transpose_len_eq)
       apply (simp add: list_all2_lengthD )
      by (simp add: list_all2_conv_all_nth)
    show ?thesis
      apply (rule list_all2_all_nthI[OF same_len])
        apply (simp add: list_all2_conv_all_nth)
        apply (rule context_conjI)
        apply (simp add: nth_transpose same_len)
         apply (rule list_all2_filter_len[THEN list_all2_lengthD, OF prems])
        apply clarsimp
        apply (simp add: nth_transpose same_len)
        apply (rule list_all2_nth_nth)
          apply (rule list_all2_filter_len[OF prems])
         apply simp+
        by (metis length_removeAll_less nat_neq_iff nth_mem
            removeAll_filter_not)
    qed
    done

lemma upto_seq_set[simp]: "set_seq (upto_seq :: ('n,nat) seq) = {0..<LEN('n)}"
  apply transfer
  apply simp
  done

lemma upto_seq_cong[cong]:
  "(\<And>i. i < LEN('n) \<Longrightarrow> f i = g i) \<Longrightarrow>
  map_seq f (upto_seq :: ('n,nat) seq) = map_seq g upto_seq"
  apply (rule seq.map_cong)
  apply simp+
  done

definition transpose_seq :: "('rows,('cols,'a) seq) seq \<Rightarrow> ('cols,('rows,'a) seq) seq" where
  "transpose_seq xs \<equiv> map_seq (\<lambda>i. map_seq (\<lambda>j. nth_seq (nth_seq xs j) i) upto_seq) upto_seq"

lemma transpose_seq_nth: 
  "i < LEN('cols) \<Longrightarrow> 
  nth_seq (transpose_seq (xs :: ('rows,('cols,'a) seq) seq)) i = map_seq (\<lambda>j. nth_seq (nth_seq xs j) i) upto_seq"
  by (simp add: transpose_seq_def)

lemma len_helper1: "LEN('rows::len) = 0 \<longrightarrow> LEN('cols) = 0" by simp
lemma len_helper2: "nonzero LEN('rows) \<Longrightarrow> LEN('rows) = 0 \<longrightarrow> LEN('cols) = 0" by simp

context assumes rc_0: "LEN('rows) = 0 \<longrightarrow> LEN('cols) = 0" begin

lift_definition transpose_seq2 :: "('rows,('cols,'a) seq) seq \<Rightarrow> ('cols,('rows,'a) seq) seq" 
  is transpose parametric transpose_transfer
  apply (clarsimp simp add: eq_OO relcompp_apply)
  subgoal for xs ys b
  apply (cases "length xs = 0";simp add: rc_0)
    apply (rule exI[of _ "map list_to_seq (transpose xs)"])
    apply (intro context_conjI)
      apply (rule list_all2_all_nthI;simp?)
      apply (rule pcr_seq_listI)
      apply (clarsimp 
               simp add: nth_transpose list_all2_len_helper length_transpose 
                         list_all2_lengthD
                   cong: filter_cong List.foldr_cong)+
    using list_all2_pcr_seq 
    by blast
  done

lemma transpose_seq_rectangle_nonzero: 
  assumes pos_len[transfer_rule]: "nonzero (LEN('rows))"
  shows "transpose_seq2 (xs :: ('rows,('cols, 'a) seq) seq) = map_seq (\<lambda>i. map_seq (\<lambda>j. nth_seq (nth_seq xs j) i) upto_seq) upto_seq"
  apply (simp add: nth_seq_def2)
  apply (rule sym)
  apply transfer
  apply (insert pos_len)
  apply (clarsimp dest!: list_all2_pcrD)
  apply (subst transpose_rectangle[where n="LEN('cols)"];simp)
  apply (simp add: nth_mod_list_def)
  done

lemma transpose_seq_def2: "transpose_seq = transpose_seq2"
  apply (rule ext)
  apply (cases "LEN('rows) = 0")
   apply (simp add: rc_0)
  by (simp add: transpose_seq_rectangle_nonzero transpose_seq_def)

lemmas transpose_seq_transfer = transpose_seq2.transfer[simplified transpose_seq_def2[symmetric]]

end

lemmas transpose_seq_tranfer[transfer_rule] = 
  transpose_seq_transfer[OF len_helper2]
  transpose_seq_transfer[OF len_helper1]

lemmas seq_eq_nthI = seq_all2_nthI[where R="(=)", OF refl, simplified seq_all2_is_eq]

lemma left_shift_seq_def2: 
  "(l :: ('n,'a :: zero) seq) << i =
     map_index_seq (\<lambda>n x. if ((i \<ge> 0 \<longrightarrow> n + (abs_nat i) < length_seq l) \<and> (i < 0 \<longrightarrow> n \<ge> abs_nat i)) then x else 0) (l <<< i)"
  by (transfer; simp add: left_shift_list_def2 cong: if_cong)
 

lemma right_shift_seq_def2: 
  "(l :: ('n,'a :: zero) seq) >> i =
     map_index_seq (\<lambda>n x. if ((i \<le> 0 \<longrightarrow> n + (abs_nat i) < length_seq l) \<and> (i > 0 \<longrightarrow> n \<ge> abs_nat i)) then x else 0) (l >>> i)"
  by (transfer; simp add: right_shift_list_def2 cong: if_cong)

lemma group_seq_nth: 
  assumes p_parts[simp]: "p < LEN('parts)"
  shows "nth_seq (group_seq (xs :: ((('parts * 'each),'a) seq))) p = map_seq (\<lambda>e. nth_seq xs ((p * LEN('each)) + e)) upto_seq"
  apply (rule seq_eq_nthI)
  apply simp
  apply (rule group_seq_nth_nth;simp)
  done

lemma group_seq_def2: 
  "group_seq (xs :: ((('parts * 'each),'a) seq)) = 
    map_seq (\<lambda>p. map_seq (\<lambda>e. nth_seq xs ((p * LEN('each)) + e)) upto_seq) upto_seq"
  apply (rule seq_eq_nthI)
  apply simp
  apply (rule group_seq_nth)
  apply simp
  done


lemma map_seq_weaken:
  "((R ===> Q) ===> seq_all2 R ===> seq_all2 Q) map_seq map_seq"
  apply (rule rel_funI)+
  apply transfer
  by (simp add: list_all2_conv_all_nth
      rel_funD)

lemma index_exists:"0 < (n::nat) \<Longrightarrow> 0 < (m::nat) \<Longrightarrow> i < n * m \<Longrightarrow>
    \<exists>x xa.
       x < n \<and>
       xa < m \<and> i = x * m + xa"
  apply (induct i)
   apply clarsimp
  apply clarsimp
  by (metis Ex_less_Suc add.commute
      add_Suc_right add_cancel_left_right
      mult_Suc nat_neq_iff not_gr_zero
      not_less_eq)

lemma seqs_eqI: "LEN('n) > 0 \<Longrightarrow> LEN('m) > 0 \<Longrightarrow> group_seq xs = group_seq ys \<Longrightarrow> (xs :: ('n \<times> 'm,'a) seq) = ys"
  apply (simp add: group_seq_def2)
  apply transfer
  apply simp
  apply (rule nth_equalityI)
   apply simp
  apply simp
  subgoal for xs ys i
    apply (insert index_exists[where i=i and n="LEN('n)" and m="LEN('m)"])
    apply clarsimp
    by (metis atLeastLessThan_iff le0
        nth_list_nth)
  done


lemma drop_concat_head: "length (hd xs) = i \<Longrightarrow> drop i (concat xs) = concat (drop 1 xs)"
  by (induct xs;simp)

lemma drop_concat:
  "\<forall>x\<in>(set xs). length x = b  \<Longrightarrow> i < length xs \<Longrightarrow> drop ( i * b) (concat xs) = concat (drop ( i) xs)"
  apply (induct i;simp)
  apply (subst drop_drop[symmetric])
  apply (simp add: hd_drop_conv_nth drop_concat_head)
  done

lemma take_concat:
  "xs \<noteq> [] \<Longrightarrow> \<forall>x\<in>(set xs). length x = b \<Longrightarrow> take b (concat xs) = hd xs"
  by (induct xs rule:list_nonempty_induct;simp)


lemma take_drop_grouped:
  "\<forall>x\<in>(set xs). length x = b \<Longrightarrow> i < length xs \<Longrightarrow> take b (drop (i * b) (concat xs)) = xs ! i"
  apply (simp add: drop_concat )
  apply (subst take_concat)
    apply simp
   apply (meson in_set_dropD)
  using hd_drop_conv_nth by blast
  
lemma concat_group_list[simp]: "length xs = a \<Longrightarrow> (\<forall>x\<in>(set xs). length x = b) \<Longrightarrow> group_list a b (concat xs) = xs"
  apply (rule nth_equalityI)
   apply (simp add: list_all2_lengthD)
  apply (subst group_list_part)
  apply (simp add: concat_fixed_len
      list_all2_len_helper
      list_all2_lengthD)
   apply simp
  apply (subst take_drop_grouped)
  using list_all2_len_helper apply blast
   apply (simp add: list_all2_lengthD)+
  done

lemma prod_len[transfer_rule]: "LEN('a \<times> 'b) = LEN('a) * LEN('b)"
  by simp

lemma concat_group_seq[simp]: "group_seq (concat_seq xs) = xs"
  apply transfer
  apply clarsimp
  apply (rule concat_group_list)
  by (simp add: list_all2_lengthD list_all2_len_helper)+

lemma group_concat_list[simp]: "length x = a * b \<Longrightarrow> concat (group_list a b x) = x"
  by (induct a arbitrary: x b;simp)

lemma group_concat_seq[simp]: "concat_seq (group_seq x) = x"
  by (transfer;simp)

lemma seq_all2_concat: 
  assumes [transfer_rule]:
    "LEN('nm) = LEN ('ij)" 
    "LEN('nm) = LEN('n) * LEN('m)"
    "LEN('ij) = LEN('i) * LEN('j)"
  shows 
    "seq_all2 (seq_all2 R) (x :: ('n,('m,'a) seq) seq) (y :: ('i,('j,'b) seq) seq) \<Longrightarrow> 
      seq_all2 R ((concat_seq x) :: ('nm,'a) seq) ((concat_seq y) :: ('ij,'b) seq)"
  apply transfer
  apply clarsimp
  by (metis apply_rsp' concat_transfer)

lemma concat_seq_eqI[intro]: 
  assumes
    "LEN('nm) = LEN('n) * LEN('m)"
    "LEN('nm) = LEN('i) * LEN('j)"
    "seq_all2 (seq_all2 (=)) xss yss"
  shows "(concat_seq (xss :: ('n, ('m, 'b) seq) seq) :: ('nm, 'b) seq) = concat_seq (yss :: ('i, ('j, 'b) seq) seq)"
  apply (subst seq_all2_is_eq[symmetric])
  apply (insert assms)
  apply (rule seq_all2_concat)
  by auto
  

end (* rotate_shift syntax *)

lemma pcr_seq_all2_transfer[transfer_rule]: "(((=) ===> (=) ===> (=)) ===> list_all2 (=) ===> pcr_seq (=) ===> (=)) list_all2 pcr_seq"
  apply (rule rel_funI)+
  apply (clarsimp simp add: Seq.pcr_seq_def relcompp_apply cr_seq_def)
  by (metis (full_types) list.rel_eq rel_fun_eq)

lemma seq_all_coerce[simp]: "LEN('a) = LEN('b) \<Longrightarrow>
   all_seq P (coerce_seq_len (s :: ('a,'c) seq) :: ('b,'c) seq) = all_seq P s"
  by (transfer;simp)

lemma seq_all_map[simp]: "all_seq P (map_seq f s) = all_seq (\<lambda>x. P (f x)) (s :: ('a,'c) seq)"
  apply transfer
  by (simp add: list_all_length)

lemma all_seq_upto[simp]: "all_seq P (upto_seq  :: ('n,nat) seq) = (\<forall>x. x < LEN('n) \<longrightarrow> P x)"
  apply transfer
  by (simp add: list_all_length)+

lemma map_seq_list_to_seq[simp]: "map_seq f ((list_to_seq xs) :: ('n,'a) seq) = list_to_seq (map f (list_len LEN('n) xs))"
  apply transfer
  by simp

lemma all_seq_list_to_seq[simp]: "all_seq f ((list_to_seq xs) :: ('n,'a) seq) = (list_all f (list_len LEN('n) xs))"
  apply transfer
  by simp

lemma nth_seq_list_to_seq[simp]: "nth_seq ((list_to_seq xs) :: ('n,'a) seq) i = nth_list (list_len LEN('n) xs) i"
  apply transfer
  by simp

lemma seq_all2_list_to_seq[simp]:
  "seq_all2 f ((list_to_seq xs) :: ('n,'a) seq) ((list_to_seq ys) :: ('m,'a) seq) =
  (list_all2 f (list_len LEN('n) xs)) (list_len LEN('m) ys)"
  apply transfer
  by simp

lemma zip_seq_list_to_seq[simp]:
  "zip_seq ((list_to_seq xs) :: ('n,'a) seq) ((list_to_seq ys) :: ('n,'a) seq) =
  list_to_seq ((zip (list_len LEN('n) xs)) (list_len LEN('n) ys))"
  apply transfer
  by simp


lemma take_seq_list_to_seq[simp]:
  "(take_seq ((list_to_seq xs) :: ('n,'a) seq) :: ('m,'a) seq) =
   list_to_seq ((list_len LEN('m) (list_len LEN('n) xs)))"
  apply (simp add: take_seq_def)
  apply transfer
  by simp

lemma drop_seq_list_to_seq[simp]:
  "(drop_seq ((list_to_seq xs) :: ('front + 'back,'a) seq) :: ('back,'a) seq) =
   list_to_seq ((drop LEN('front) (list_len LEN('front + 'back) xs)))"
  apply transfer
  by simp

lemma len_minus_0[simp]: "LEN('n - 0) = LEN('n)"
  by simp

lemma len_plus_0[simp]: "LEN('n + 0) = LEN('n)"
  by simp

lemmas [transfer_rule] = len_minus_0 len_minus_0[symmetric]
                         len_plus_0 len_plus_0[symmetric]

lemma map_seq_comp[simp]: "map_seq g (map_seq f v) = map_seq (\<lambda>x. g (f x)) v"
  by (simp add: map_nth_eqI)

lemma map_seq_coerce_upto[simp]: 
  "LEN('m) \<le> LEN('n) \<Longrightarrow> coerce_seq_len (map_seq f (upto_seq :: ('n,nat) seq)) = map_seq f (upto_seq :: ('m,nat) seq)"
  apply transfer
  by (simp add: take_map)


lemma nth_seq_coerce[simp]: 
  "LEN('n) = LEN('m) \<Longrightarrow> nth_seq ((coerce_seq_len (s :: ('n,'a) seq)) :: ('m,'a) seq) i = nth_seq s i"
  apply transfer
  apply simp
  done

lemma nth_seq_coerce_bound[simp]: 
  "LEN('m) \<le> LEN('n) \<Longrightarrow> i < LEN('m) \<Longrightarrow> nth_seq ((coerce_seq_len (s :: ('n,'a) seq)) :: ('m,'a) seq) i = nth_seq s i"
  apply transfer
  by simp

lemma append_drop_seq[simp]: 
  "drop_seq ( (append_seq (x :: ('front,'a) seq) (y :: ('back,'a) seq)) :: ('front + 'back,'a) seq) = y"
  apply transfer
  apply simp
  done


lemma append_take_seq[simp]: 
  "take_seq ( (append_seq (x :: ('front,'a) seq) (y :: ('back,'a) seq)) :: ('front + 'back,'a) seq) = x"
  apply transfer
  apply simp
  done

lemma coerce_append[simp]: 
  "LEN('n) = LEN('m) \<Longrightarrow> ((coerce_seq_len ((append_seq x y) :: ('n,'a) seq)) :: ('m,'a) seq) = append_seq x y"
  apply (induct x rule: list_to_seq_raw_induct)
  apply (induct y rule: list_to_seq_raw_induct)
  apply simp
  by (simp add: append_seq_def)

lemma concat_list_to_seq[simp]: 
  "length xs = LEN('n) \<Longrightarrow> 
   concat_seq ((list_to_seq xs) :: ('n,('m,'a) seq) seq) = list_to_seq (concat (map seq_to_list xs))"
  by (simp add: concat_seq_def)

lift_definition product_seq :: "('n,'a) seq \<Rightarrow> ('m,'b) seq \<Rightarrow> ('n \<times> 'm, ('a \<times> 'b)) seq" is
  "List.product" parametric List.product_transfer
    by simp

lemma product_seq_def2: "product_seq xs ys = concat_seq_map (\<lambda>x. map_seq (\<lambda>y. (x, y)) ys) xs"
  apply transfer
  by (simp add: product_concat_map)

lemma product_seq_nth[simp]: "i < LEN('n) * LEN('m) \<Longrightarrow>
    nth_seq (product_seq (xs :: ('n,'a) seq) (ys :: ('m,'b) seq)) i = 
    (nth_seq xs (i div LEN('m)), nth_seq ys (i mod LEN('m)))"
  apply transfer
  apply (simp add: List.product_nth)
  by (metis add_0 add_lessD1
      less_mult_imp_div_less mod_less_divisor
      nat_0_less_mult_iff nth_list_nth)

lemma zip_map_seq2[simp]: "zip_seq xs (map_seq f ys) = map_seq (\<lambda>(x,y). (x, f y)) (zip_seq xs ys)"
  apply transfer
  by (simp add: zip_map2)

lemma zip_map_seq1[simp]: "zip_seq (map_seq f xs) ys = map_seq (\<lambda>(x,y). (f x, y)) (zip_seq xs ys)"
  apply transfer
  by (simp add: zip_map1)

lemma coerce_concat_seq1[simp]: 
  "LEN('n) = LEN('l) \<Longrightarrow> 
  concat_seq ((coerce_seq_len (xss :: ('n,('m,'a) seq) seq)) :: ('l,('m,'a) seq) seq) = concat_seq xss"
  by (simp add: concat_seq_def)

lemma coerce_seq_len_list[simp]: 
  "((coerce_seq_len ((list_to_seq ls) :: ('n,'a) seq)) :: ('m,'a) seq) = list_to_seq (list_len LEN('n) ls)"
  apply transfer
  by (simp add: list_len_def)

lemma coerce_concat_seq2[simp]: 
  "LEN('k) = LEN('j) \<Longrightarrow> 
  ((coerce_seq_len ((concat_seq xss) :: ('k,'a) seq)) :: ('j,'a) seq) = concat_seq xss"
  apply (simp add: concat_seq_def)
  apply transfer
  by simp

lemma zip_seq_coerce[simp, coerce_seq]:
  "LEN('m) \<le> LEN('n) \<Longrightarrow> zip_seq ((coerce_seq_len (xs :: ('n,'a) seq)) :: ('m,'a) seq) (coerce_seq_len ys) = coerce_seq_len (zip_seq xs ys)"
  apply transfer
  by (simp add: take_zip)
  

lemma upto_coerce[simp]:
  "LEN('m) \<le> LEN('n) \<Longrightarrow> coerce_seq_len (upto_seq :: ('n,nat) seq)= (upto_seq :: ('m,nat) seq)"
  apply transfer
  apply simp
  done

lemma concat_seq_as_map':
  assumes "LEN('n) > 0" and "LEN('m) > 0"
  shows "(concat_seq (xs :: ('n,('m,'a) seq) seq) :: ('n \<times> 'm,'a) seq) = 
          map_seq (\<lambda>n. nth_seq (nth_seq xs ((n - (n mod LEN('m))) div LEN('m))) (n mod LEN('m))) upto_seq"
  apply (rule seqs_eqI)
    apply (rule assms)+
  apply (rule seq_eq_nthI)
  apply simp
  apply (subst group_seq_nth)
   apply assumption
  apply (rule seq_eq_nthI)
  apply simp
  apply (subst upto_seq_nth_f)
   apply simp
   apply (rule parts_each_bound)
    apply simp+
  done

lemma concat_seq_as_map:
  assumes [simp]: "LEN('nm) = LEN('n) * LEN('m)"
  shows "(concat_seq (xs :: ('n,('m,'a) seq) seq) :: ('nm,'a) seq) = 
          map_seq (\<lambda>n. nth_seq (nth_seq xs ((n - (n mod LEN('m))) div LEN('m))) (n mod LEN('m))) upto_seq"
  apply (subst coerce_concat_seq2[where 'k="'n \<times> 'm" and 'j='nm, symmetric])
   apply simp
  apply (cases "LEN('n) > 0"; cases "LEN('m) > 0")
     apply (subst concat_seq_as_map';simp?)
     apply (simp add: coerce_seq[symmetric] del: coerce_seq)
   apply simp+
  done

lemma concat_seq_nth:
  assumes nm_len[transfer_rule]: "LEN('nm) = LEN('n) * LEN('m)"
      and n_bound[simp]: "n < LEN('nm)"
    shows "nth_seq (concat_seq (xs :: ('n,('m,'a) seq) seq) :: ('nm,'a) seq) n = nth_seq (nth_seq xs ((n - (n mod LEN('m))) div LEN('m))) (n mod LEN('m))"
  apply (simp add: concat_seq_as_map nm_len)
  apply simp
  done

lemma coerce_len_eqI1[intro]:
  "seq_all2 (=) xs ys \<Longrightarrow> coerce_seq_len xs = ys"
  apply transfer
  apply (simp add: list_len_def)
  by (simp add: list.rel_eq cong: map_upto_cong)

lemma coerce_len_eqI2[intro]:
  "seq_all2 (=) xs ys \<Longrightarrow> xs = coerce_seq_len ys"
  apply transfer
  apply (simp add: list_len_def)
  by (simp add: list.rel_eq cong: map_upto_cong)


context includes rotate_shift_syntax begin
lemma drop_seq_shiftl_take:
  "drop_seq' (xs :: ('front + 'back,'a) seq) = take_seq (xs <<< LEN('front))"
  apply (simp add: take_seq_def)
  apply (rule sym)
  apply transfer
  apply simp
  apply (simp add: left_rotate_def2 rotate_drop_take)
  by (metis add.commute add_diff_cancel_right'
      append.right_neutral append_eq_conv_conj diff_self_eq_0
      gr_zeroI length_drop mod_less take_0 zero_diff
      zero_less_diff)
end

lemma list_upto_cong: "x = y \<Longrightarrow>
  (\<And>z. z < x \<Longrightarrow> f z = g z) \<Longrightarrow>
  map f [0..<x] = map g [0..<y]"
  by (rule list.map_cong;simp)


lemma list_append_as_map: "x @ y =
    map (\<lambda>z. if length x \<le> z then y ! (z - length x)
             else x ! z)
     [0..<length x + length y]"
  apply (induct y arbitrary: x)
  apply (clarsimp cong: list_upto_cong if_cong)
  subgoal for a y x
    apply (drule meta_spec[where x="x @ [a]"])
  by (simp add: linorder_not_le nth_Cons'
      nth_append)
  done

lemma append_seq_as_map: 
  assumes [transfer_rule]: "LEN('n) = length_seq x + length_seq y"
  shows
  "append_seq x y = map_seq
     (\<lambda>i. if length_seq x \<le> i
          then nth_seq y
                (i - length_seq x)
          else nth_seq x i) (upto_seq :: ('n,nat) seq)"
  apply transfer
  by (simp add: assms list_append_as_map cong: list.map_cong if_cong)


definition ext_list :: "nat \<Rightarrow> 'a \<Rightarrow> ('a) list \<Rightarrow> ('a) list" where
  "ext_list m pad xs \<equiv> (replicate (m - (length xs)) pad) @ (drop ((length xs) - m) xs)"

lemma ext_list_len[simp]: "length (ext_list n pad xs) = n"
  by (simp add: ext_list_def)

lemma ext_list_transfer[transfer_rule] : 
  shows "((=) ===> R ===> list_all2 R ===> list_all2 R) ext_list ext_list"
  unfolding ext_list_def
  by transfer_prover

lemma ext_list_transfer'[transfer_rule]: 
  shows "(R ===> list_all2 R ===> list_all2 R) (ext_list n) (ext_list n)"
  unfolding ext_list_def
  by transfer_prover

lemma ext_list_transfer''[transfer_rule]: 
  assumes A[transfer_rule]: "R x y"
  shows "(list_all2 R ===> list_all2 R) (ext_list n x) (ext_list n y)"
  unfolding ext_list_def
  by transfer_prover

lift_definition ext_seq ::  "'a \<Rightarrow> ('n,'a) seq \<Rightarrow> ('m,'a) seq" is
  "ext_list LEN('m)" parametric ext_list_transfer'
  by simp

lift_definition zext_seq ::  "('n,'a::zero) seq \<Rightarrow> ('m,'a::zero) seq" is
  "ext_list LEN('m) 0" parametric ext_list_transfer''[where x=0]
  by simp
  
lemma ext_list_0[simp]: "ext_list 0 x xs = []"
  by (simp add: zero_size)

lemma ext_list_empty[simp]: "ext_list n x [] = replicate n x"
  apply (induct n;simp)
  by (simp add: ext_list_def)

lemma ext_list_replicate[simp]: "ext_list n x (replicate m x) = replicate n x"
  apply (simp add: ext_list_def)
  by (metis add.commute
      add_diff_cancel_right' min.commute
      replicate_add rev_min_pm)

lemma zext_seq_0[simp]: "zext_seq (0 :: ('a,'c) seq) = (0:: ('b,'c::zero) seq)"
  by (cases "LEN('a) = 0"; cases "LEN('b) = 0";simp;transfer;simp)

lemma zext_seq_def2: "zext_seq xs = ext_seq 0 xs"
  apply transfer
  by simp

definition sign_list :: "('a :: zero) list \<Rightarrow> 'a" where
  "sign_list xs \<equiv> if length xs = 0 then 0 else xs ! 0"


lift_definition sign_seq ::  "('n,'a::zero) seq \<Rightarrow> 'a" is
  "sign_list" .


lemma sign_seq_def2: "sign_seq (xs :: ('n,'a::zero) seq) = (if LEN('n) > 0 then nth_seq xs 0 else 0)"
  apply transfer
  by (auto simp add: sign_list_def split: list.splits)


lemma sign_seq_transfer[transfer_rule]:
    assumes A:"(LEN('n) = 0 \<longrightarrow> R 0 0)"
    shows "(pcr_seq R ===> R) sign_list (sign_seq :: ('n,'a::zero) seq \<Rightarrow> 'a)"
  unfolding sign_seq_def2 sign_list_def
  apply (cases "LEN('n) = 0")
   apply (simp add: pcr_seq_len cong: rel_fun_cong)
   apply (rule rel_funI)
   apply (simp add: A)
  apply (simp add: pcr_seq_len cong: rel_fun_cong)
  apply (rule rel_funI)+
  apply transfer
  by (simp add: list_all2_nthD2)

definition sext_list :: "nat \<Rightarrow> ('a::zero) list \<Rightarrow> 'a list" where
  "sext_list n xs \<equiv> ext_list n (sign_list xs) xs"

lemma sext_list_length[simp]: "length (sext_list n xs) = n"
  by (simp add: sext_list_def)

lemma sext_list_zero: "length xs = 0 \<Longrightarrow> sext_list n xs = replicate n 0"
  by (auto simp add: sext_list_def ext_list_def sign_list_def)

lift_definition sext_seq ::  "('n,'a::zero) seq \<Rightarrow> ('m,'a::zero) seq" is
  "sext_list LEN('m)"
  by simp

lemma sext_seq_def2: "sext_seq xs = ext_seq (sign_seq xs) xs"
  apply transfer
  by (simp add: sext_list_def)

lemma sext_seq_zero: "LEN('n) = 0 \<Longrightarrow> sext_seq  = (\<lambda>(_ :: ('n,'a::zero) seq). 0)"
  apply (rule ext)
  apply (simp add:  zero_seq_def2)
  apply transfer
  by (simp add: sext_list_zero)


lemma sext_seq_transfer[transfer_rule]:
  assumes A[transfer_rule]:"LEN('n) = 0 \<longrightarrow> R 0 0"
  shows "(pcr_seq R ===> pcr_seq R) (sext_list LEN('m)) (sext_seq :: ('n,'a::zero) seq \<Rightarrow> ('m,'a) seq)"
  apply (simp add: sext_seq_def2[abs_def] sext_list_def[abs_def])
  by transfer_prover


lemma ext_seq_map_map:
  assumes inv: "\<And>x. x \<in> insert a (set_seq xs) \<Longrightarrow> g (f x) = x"
 shows "(ext_seq a (xs :: ('a,'b) seq) :: ('d,'b) seq) = map_seq g (ext_seq (f a) (map_seq f xs))"
  apply (insert assms)
  apply transfer
  apply (simp add: drop_map ext_list_def)
  by (metis comp_apply drop_map map_idI)

lemma ext_seq_zero_replicate: "LEN('a) = 0 \<Longrightarrow> ext_seq a (x :: ('a,'b) seq) = (replicate_seq a)"
  apply transfer
  by (simp add: ext_list_def)

lemma sign_seq_zero: "LEN('a) = 0 \<Longrightarrow> sign_seq (x :: ('a,'b::zero) seq) = 0"
  apply transfer
  by (simp add: sign_list_def)


lemma seq_to_list_eqI:
  "LEN('m) = LEN('n) \<Longrightarrow> 
  (LEN('m) = LEN('n) \<Longrightarrow> seq_all2 (=) xs ys) \<Longrightarrow>
  seq_to_list (xs :: ('m,'a) seq) = seq_to_list (ys :: ('n,'a) seq)"  
  using coerce_len_eqI2 by fastforce

lemma len_gt_plus:
  "LEN('m) > LEN('n) \<Longrightarrow> LEN('m) = LEN(('m-'n) len) + LEN('n)"
  by simp

lemma ext_seq_pos_def: 
  assumes A: "LEN('m) > LEN('n)"
  shows "(ext_seq pad (xs :: ('n,'a) seq) :: ('m,'a) seq) = 
                            append_seq ((replicate_seq pad) :: (('m-'n) len,'a) seq) xs"

  apply transfer
  unfolding ext_list_def
  using A
  by simp


lemma list_to_seq_take_absorb[simp]: 
  "LEN('n) \<le> LEN('m) \<Longrightarrow> ((list_to_seq (take LEN('m) xs)) :: ('n,'a) seq) = list_to_seq xs"
  apply transfer
  by (auto simp add: list_len_def split: nth_list_splits)

lemma ext_seq_down: 
  assumes A:"LEN('m) \<le> LEN('n)"
  shows "((ext_seq pad (xs :: ('n,'a::zero) seq)) :: ('m,'a::zero) seq) = drop_seq xs"
  apply transfer
  unfolding ext_list_def
  using A
  by simp

lemmas 
  zext_seq_defs[where pad=0, simplified zext_seq_def2[symmetric] zero_seq_def2[symmetric]] = 
    ext_seq_pos_def
    ext_seq_down

lemmas 
  sext_seq_defs[where xs="xs :: ('n,'a::zero) seq" and pad="sign_seq xs" for xs
               , simplified sext_seq_def2[symmetric] zero_seq_def2[symmetric]] = 
    ext_seq_pos_def
    ext_seq_down

lift_definition sum_seq :: "('n,'a::monoid_add) seq \<Rightarrow> 'a" is
  sum_list parametric sum_list_transfer .

(* NOTE: prod_list requires monoid_mult, which demands the zero_neq_one class, which
   is not satisified by zero-length seqs.
   We relax the constraints here for simplicity. *)

definition product_list :: "('a::{times,one}) list \<Rightarrow> 'a" where
  "product_list xs \<equiv> foldl (*) 1 xs"

lemma product_list_transfer[transfer_rule]:
  assumes A1[transfer_rule]: "A 1 1"
      and A_prod[transfer_rule]: "(A ===> A ===> A) (*) (*)"
  shows "(list_all2 A ===> A) product_list product_list"
  unfolding product_list_def
  by transfer_prover

lift_definition prod_seq :: "('n,'a::{times,one}) seq \<Rightarrow> 'a" is
  product_list parametric product_list_transfer .

definition list_updates :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_updates xs ixs ys \<equiv> foldl (\<lambda>xs' (y,ix). list_update xs' ix y) xs (zip ys ixs)"

lemma list_updates_length[simp]: "length (list_updates xs ixs ys) = length xs"
  unfolding list_updates_def
  by (induct ixs ys arbitrary: xs rule: list_induct2';simp)

lemma list_updates_transfer[transfer_rule]: 
  "(list_all2 A ===> list_all2 (=) ===> list_all2 A ===> list_all2 A) list_updates list_updates"
  unfolding list_updates_def
  by transfer_prover

lift_definition seq_updates :: "('n,'a) seq \<Rightarrow> ('k,nat) seq \<Rightarrow> ('k,'a) seq \<Rightarrow> ('n,'a) seq" is
  "list_updates"
  parametric list_updates_transfer
  by simp

lemma seq_updates_def2: "seq_updates xs ixs ys = foldl_seq (\<lambda>xs' (y,ix). seq_update xs' ix y) xs (zip_seq ys ixs)"
  apply transfer
  apply (simp add: list_updates_def)
  done

definition seq_updates_end :: "('n,'a) seq \<Rightarrow> ('k,nat) seq \<Rightarrow> ('k,'a) seq \<Rightarrow> ('n,'a) seq" where
  "seq_updates_end xs ixs ys \<equiv> seq_updates xs (map_seq (\<lambda>ix. LEN('n) - ix - 1) ixs) ys"

lemma seq_updates_end_transfer[transfer_rule]:
  "(pcr_seq A ===> pcr_seq (=) ===> pcr_seq A ===> pcr_seq A)
     (\<lambda>xs ixs. list_updates xs (map (\<lambda>ix. length xs - ix - 1) ixs)) seq_updates_end"
  unfolding seq_updates_end_def
  apply (simp add: pcr_seq_len cong: rel_fun_cong)
  by transfer_prover

lemma list_update_def2: 
  "xs[ix := x] = map (\<lambda>i. if i = ix then x else xs ! i) [0..<(length xs)]"
proof -
  have "\<And>n. length xs = n \<Longrightarrow> xs[ix := x] = map (\<lambda>i. if i = ix then x else xs ! i) [0..<n]"
    by (induct ix arbitrary: xs x; simp add: list_eq_iff_nth_eq)
  from this show ?thesis by simp
qed
  
lemma seq_update_def2: 
  "seq_update xs ix x =
    map_seq
     (\<lambda>i. if i = ix then x
          else nth_seq xs i)
     upto_seq"
  apply transfer
  apply (simp add: list_update_def2)
  done

lemma take_seq_absorb1[simp]: "LEN('n) = LEN('m) \<Longrightarrow> (take_seq (coerce_seq_len (y :: ('n,'a) seq) :: ('m,'a) seq)) = take_seq y"
  by (simp add: take_seq_def)

lemma take_seq_absorb2[simp]: "LEN('n) \<ge> LEN('m) \<Longrightarrow> ((coerce_seq_len (take_seq y :: ('n,'a) seq)) :: ('m,'a) seq) = take_seq y"
  apply (simp add: take_seq_def)
  apply transfer
  apply simp
  by (metis add_0 list_len_def take_map take_upt)

lemma drop_seq_absorb1[simp]: "LEN('n) = LEN('m) \<Longrightarrow> (drop_seq (coerce_seq_len (y :: ('n,'a) seq) :: ('m,'a) seq)) = drop_seq y"
  by (simp add: drop_seq_def)

lemma drop_seq_absorb2[simp]: "LEN('n) = LEN('m) \<Longrightarrow> (coerce_seq_len (drop_seq y :: ('n,'a) seq) :: ('m,'a) seq) = drop_seq y"
  by (simp add: drop_seq_def)

lemma append_seq0_1[simp]: "LEN('m) = 0 \<Longrightarrow> 
  (append_seq (x :: ('n,'a) seq) (y :: ('m,'a) seq) :: ('nm,'a) seq)  = coerce_seq_len x"
  apply (simp add: append_seq_def)
  apply transfer
  apply simp
  done

lemma append_seq0_2[simp]: "LEN('n) = 0 \<Longrightarrow> 
  (append_seq (x :: ('n,'a) seq) (y :: ('m,'a) seq) :: ('nm,'a) seq)  = coerce_seq_len y"
  apply (simp add: append_seq_def)
  apply transfer
  apply simp
  done

(* generalized append_take_drop_plus *)
lemma append_take_drop[simp]:
  "LEN('nm) = LEN('n) - LEN('m) \<Longrightarrow> LEN('l) = LEN('n) ==>
    append_seq (take_seq (x :: ('n,'a) seq) :: ('m,'a) seq) ((drop_seq x) :: ('nm,'a) seq) = (coerce_seq_len x :: ('l,'a) seq)"
  apply (cases "LEN('m) \<le> LEN('n)")
  subgoal
    unfolding append_seq_def take_seq_def drop_seq_def
    apply simp
    apply transfer
    by simp
  apply simp
  done

lemmas append_take_drop'[simp] = append_take_drop[OF _ refl, simplified coerce_seq_len_same]

(* lexographic list ordering, with head element as most significant *)
fun lex_list_order :: "('a::ord) list \<Rightarrow> 'a list \<Rightarrow> bool" where
   "lex_list_order (x#xs) (y#ys) = ((x \<le> y) \<and> (x = y \<longrightarrow> lex_list_order xs ys))"
 | "lex_list_order [] (y#ys) = True"
 | "lex_list_order (x#xs) [] = False"
 | "lex_list_order [] [] = True"

definition lex_list_order_strict :: "('a::ord) list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "lex_list_order_strict x y \<equiv> lex_list_order x y \<and> x \<noteq> y"

lemma list_induct3': "P [] [] [] \<Longrightarrow>
    (\<And>x xs. P (x # xs) [] []) \<Longrightarrow>
    (\<And>y ys. P [] (y # ys) []) \<Longrightarrow>
    (\<And>z zs. P [] [] (z # zs)) \<Longrightarrow>
    (\<And>x xs y ys. P (x # xs) (y # ys) []) \<Longrightarrow>
    (\<And>x xs z zs. P (x # xs) [] (z # zs)) \<Longrightarrow>
    (\<And>y ys z zs. P [] (y # ys) (z # zs)) \<Longrightarrow>
    (\<And>x xs y ys z zs.
        P xs ys zs \<Longrightarrow> P (x # xs) (y # ys) (z # zs)) \<Longrightarrow>
    P xs ys zs"
  apply (induct xs arbitrary: ys zs)
   apply (meson list_induct2')
  by (metis list_induct2')


(* interpretation of the linorder locale to avoid creating
   conflicting class instance for list order *)
interpretation lex_list_order: 
  linorder 
  "lex_list_order :: 'a :: linorder list \<Rightarrow> 'a list \<Rightarrow> bool"
  lex_list_order_strict
  unfolding lex_list_order_strict_def
  apply standard
  subgoal for x y
    by (induct x y rule: list_induct2';auto)
  subgoal for x
    by (induct x;auto)
  subgoal for x y z
    by (induct x y z rule: list_induct3';auto)
  subgoal for x y
    by (induct x y rule: list_induct2';auto)
  subgoal for x y
    by (induct x y rule: list_induct2';auto)
  done

instantiation seq :: (_, ord) ord begin
lift_definition less_eq_seq :: "('a,'b::ord) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> bool" is
  "lex_list_order" .

lift_definition less_seq :: "('a,'b::ord) seq \<Rightarrow> ('a,'b) seq \<Rightarrow> bool" is
  lex_list_order_strict .
instance ..
end

instantiation seq :: (_, linorder) linorder begin
instance
  by (standard;transfer;auto)
end


lemma ext_list_lex_order: "length x = length y \<Longrightarrow> c \<ge> length x \<Longrightarrow>
         lex_list_order  (x :: 'a :: linorder list) y \<Longrightarrow> lex_list_order
            (ext_list c z x)
            (ext_list c z y)"
  apply (induct c arbitrary: x y ;simp)
  subgoal for i j k
    apply (simp add: ext_list_def)
    apply (cases "Suc i = length k";simp?)
    apply (drule le_neq_implies_less;simp)
    apply (simp add: Suc_diff_le)
    done
  done

lemma ext_list_inj:
  "length x = length y \<Longrightarrow> c \<ge> length x \<Longrightarrow> ext_list c z x = ext_list c z y \<Longrightarrow> x = y"
  by (simp add: ext_list_def)

lemma ext_list_lex_order_strict: "length x = length y \<Longrightarrow> c \<ge> length x \<Longrightarrow>
         lex_list_order_strict  (x :: 'a :: linorder list) y \<Longrightarrow> lex_list_order_strict
            (ext_list c z x)
            (ext_list c z y)"
  by (clarsimp simp add: lex_list_order_strict_def ext_list_lex_order ext_list_inj)
  
lemma ext_seq_preserve_less:
  "LEN('c) \<ge> LEN('a) \<Longrightarrow> (x < y) \<Longrightarrow> ((ext_seq z (x :: ('a,'b::linorder) seq)) :: ('c,'b) seq) < (ext_seq z y)"
  apply transfer
  by (simp add: ext_list_lex_order_strict)

lemma ext_seq_preserve_less_eq:
  "LEN('c) \<ge> LEN('a) \<Longrightarrow> (x \<le> y) \<Longrightarrow> ((ext_seq z (x :: ('a,'b::linorder) seq)) :: ('c,'b) seq) \<le> (ext_seq z y)"
  apply transfer
  by (simp add: ext_list_lex_order)

lemma zext_seq_preserve_less:
  "LEN('c) \<ge> LEN('a) \<Longrightarrow> (x < y) \<Longrightarrow> ((zext_seq (x :: ('a,'b::{linorder,zero}) seq)) :: ('c,'b) seq) < (zext_seq y)"
  by (simp add: zext_seq_def2 ext_seq_preserve_less)

lemma zext_seq_preserve_less_eq:
  "LEN('c) \<ge> LEN('a) \<Longrightarrow> (x \<le> y) \<Longrightarrow> ((zext_seq (x :: ('a,'b::{linorder,zero}) seq)) :: ('c,'b) seq) \<le> (zext_seq y)"
  by (simp add: zext_seq_def2 ext_seq_preserve_less_eq)

lemma less_eq_seq_zero[simp]: "LEN('a) = 0 \<Longrightarrow> (x :: ('a,'b::linorder) seq) \<le> y"
  apply (rule eq_refl)
  apply simp
  done

lemma less_seq_zero[simp]: "LEN('a) = 0 \<Longrightarrow> \<not> (x :: ('a,'b::linorder) seq) < y"
  apply (subst linorder_not_less)
  by simp

lemma list_to_seq_eqI[intro]: "xs = ys \<Longrightarrow> list_to_seq xs = list_to_seq ys" by simp


lemma take_seq_map_map:
  assumes inv: "\<And>x. x \<in> set_seq xs \<Longrightarrow> g (f x) = x"
    and oob_inv: "\<And>xs :: 'b list. LEN('d) > LEN('a) \<Longrightarrow> oob_list_elem xs = g (oob_list_elem (map f xs))"
 shows "(take_seq (xs :: ('a,'b) seq) :: ('d,'b) seq) = map_seq g (take_seq (map_seq f xs))"
  apply (insert assms)
  apply transfer
  by (simp add: list_len_def nth_list_def)

lemma drop_seq_map_map:
  assumes inv: "\<And>x. x \<in> set_seq xs \<Longrightarrow> g (f x) = x"
    and oob_inv: "\<And>xs :: 'b list. LEN('d) > LEN('a) \<Longrightarrow> oob_list_elem xs = g (oob_list_elem (map f xs))"
 shows "(drop_seq (xs :: ('a,'b) seq) :: ('d,'b) seq) = map_seq g (drop_seq (map_seq f xs))"
  apply (insert assms)
  apply transfer
  by (auto simp add: list_len_def nth_list_def)

lemma append_seq_map_map:
  assumes inv: "\<And>x. x \<in> set_seq xs \<union> set_seq ys \<Longrightarrow> g (f x) = x"
    and oob_inv: "\<And>(xs :: 'b list). LEN('d) > (LEN('a) + LEN('c)) \<Longrightarrow> oob_list_elem xs = g (oob_list_elem (map f xs))"
 shows "(append_seq (xs :: ('a,'b) seq) (ys :: ('c,'b) seq)  :: ('d,'b) seq) = map_seq g (append_seq (map_seq f xs) (map_seq f ys))"
  apply (insert assms)
  apply transfer
  apply (clarsimp simp add: list_len_def nth_list_def comp_def)
  subgoal for xs ys g f x
    apply (cases "x < LEN('a)") 
     apply (simp add: nth_append_left)
    apply (simp add: nth_append_right)
    done
  done

lemma seq_to_list_map_map:
  assumes inv: "\<And>x. x \<in> set_seq xs \<Longrightarrow> g (f x) = x"
 shows "seq_to_list (xs :: ('a,'b) seq) = map g (seq_to_list (map_seq f xs))"
  apply (insert assms)
  apply transfer
  apply (simp add: comp_def)
  by (simp add: list.map_ident_strong)

lemma list_to_seq_map_map:
  assumes inv: "\<And>x. x \<in> set xs \<Longrightarrow> g (f x) = x"
    and oob_inv: "length xs < LEN('a) \<Longrightarrow> oob_list_elem xs = g (oob_list_elem (map f xs))"
 shows "(list_to_seq (xs :: 'b list) :: ('a,'b) seq) = map_seq g (list_to_seq (map f xs))"
  apply (insert assms)
  apply transfer
  by (simp add: comp_def list_len_def nth_list_def)

lemma seq_update_map:
  "n < length_seq x \<Longrightarrow> map_seq f (seq_update x n a) = seq_update (map_seq f x) n (f a)"
  apply transfer
  by (simp add: map_update)

lemma seq_update_oob:
  "n \<ge> length_seq x \<Longrightarrow> seq_update x n a = x"
  apply transfer
  by (simp add: map_update)

lemma seq_update_map_map:
  assumes inv: "\<And>x. x \<in> set_seq (seq_update xs n a) \<Longrightarrow> g (f x) = x"
  shows "n < length_seq xs \<Longrightarrow> seq_update xs n a = map_seq g (seq_update (map_seq f xs) n (f a))"
  apply (subst seq_update_map[symmetric];simp)
  apply (subst seq.map_id[where t="seq_update xs n a", symmetric])
  by (rule seq.map_cong;simp add: inv)


lemma right_shift_map:
  assumes zero: "f 0 = 0"
  shows "right_shift (map_seq f xs) n = map_seq f (right_shift xs n)"
  apply (insert assms)
  apply transfer
  by (simp add: right_shift_def shiftr_list_def shiftl_list_def drop_map take_map)

lemma right_shift_set:
  "set (right_shift xs n) \<subseteq> set xs \<union> {0}"
  apply (simp add: right_shift_def shiftr_list_def shiftl_list_def drop_map take_map)
  by (metis in_set_dropD in_set_replicate
      in_set_takeD insertCI
      subset_code(1))

lemma right_shift_set_seq:
  "set_seq (right_shift xs n) \<subseteq> set_seq xs \<union> {0}"
  apply transfer
  by (rule right_shift_set)


lemma left_shift_map_seq:
  assumes zero: "f 0 = 0"
  shows "left_shift (map_seq f xs) n = map_seq f (left_shift xs n)"
  by (simp add: left_shift_def right_shift_map zero)

lemma left_shift_set_seq:
  "set_seq (left_shift xs n) \<subseteq> set_seq xs \<union> {0}"
  unfolding left_shift_def
  by (rule right_shift_set_seq)

lemma right_rotate_map_seq:
  "right_rotate (map_seq f xs) n = map_seq f (right_rotate xs n)"
  apply transfer
  apply (simp add: right_rotate_def)
  apply (intro conjI impI)
  using rotate_map apply blast
  using rotater_map by blast

lemma rotater_set[simp]: "set (rotater n xs) = set xs"
  apply (induct n arbitrary: xs)
   apply simp+
  by (metis rotate1_lr set_rotate1)

lemma right_rotate_set:
  "set (right_rotate xs n) = set xs"
  by (simp add: right_rotate_def)

lemma right_rotate_set_seq:
  "set_seq (right_rotate xs n) = set_seq xs"
  apply transfer
  by (simp add: right_rotate_set)

lemma left_rotate_map_seq:
  "left_rotate (map_seq f xs) n = map_seq f (left_rotate xs n)"
  by (simp add: left_rotate_def right_rotate_map_seq)

lemma right_shift_map_map_seq:
  assumes inv: "\<And>x. x \<in> set_seq (right_shift xs n) \<Longrightarrow> g (f x) = x"
     and zero: "f 0 = 0"
   shows "right_shift xs n = map_seq g (right_shift (map_seq f xs) n)"
  apply (simp add: right_shift_map zero)
  apply (subst seq.map_id[of "right_shift xs n", symmetric])
  apply (rule seq.map_cong)
   apply simp
  apply simp
  apply (rule inv[symmetric])
  by simp

lemma left_shift_map_map_seq:
  assumes inv: "\<And>x. x \<in> set_seq (left_shift xs n) \<Longrightarrow> g (f x) = x"
     and zero: "f 0 = 0"
   shows "left_shift xs n = map_seq g (left_shift (map_seq f xs) n)"
  apply (simp add: left_shift_def)
  apply (rule right_shift_map_map_seq)
  by (auto simp: inv[simplified left_shift_def] zero)

lemma right_rotate_map_map_seq:
  assumes inv: "\<And>x. x \<in> set_seq xs \<Longrightarrow> g (f x) = x"
  shows "right_rotate xs n = map_seq g (right_rotate (map_seq f xs) n)"
  apply (simp add: right_rotate_map_seq)
  apply (subst seq.map_id[of "right_rotate xs n", symmetric])
  apply (rule seq.map_cong)
  by (simp add: right_rotate_set_seq inv)+

lemma left_rotate_map_map_seq:
  assumes inv: "\<And>x. x \<in> set_seq xs \<Longrightarrow> g (f x) = x"
  shows "left_rotate xs n = map_seq g (left_rotate (map_seq f xs) n)"
  apply (simp add: left_rotate_def)
  apply (rule right_rotate_map_map_seq)
  by (simp add: inv)


lemma append_seq_as_sum:
 "(append_seq (xs :: ('a,'b) seq) (ys :: ('c,'b) seq)  :: ('d,'b) seq) = 
    coerce_seq_len (append_seq xs ys :: ('a + 'c, 'b) seq)"
  by transfer simp

lemma concat_list_map_map:
  assumes inv: "\<And>x. x \<in> set (concat (xs :: 'c list list)) \<Longrightarrow> g (f x) = x"
  shows "concat xs = map g (concat (map (map f) xs))"
  by (metis (no_types, lifting) assms length_map map_concat
      nth_equalityI nth_map nth_mem)

lemma concat_seq_map_map:
  assumes A: "LEN('ab) = LEN('a) * LEN('b)"
    and inv: "\<And>x. x \<in> set_seq (concat_seq (xs :: ('a,('b,'c) seq) seq) :: ('ab,'c) seq) \<Longrightarrow> g (f x) = x"
  shows "(concat_seq xs :: ('ab,'c) seq) = map_seq g (concat_seq (map_seq (map_seq f) xs))"
  supply [transfer_rule] = concat_seq_transfer[OF A]
  apply (insert inv)
  apply transfer
  apply (rule concat_list_map_map)
  by blast

lifting_update Seq.seq.lifting

primrec "enum_list_n" :: "nat \<Rightarrow> ('a :: enum) list list" where
  "enum_list_n (Suc n) = [(x # xs). xs \<leftarrow> enum_list_n n, x \<leftarrow> enum]"
| "enum_list_n 0 = [[]]"

lemma enum_list_n_set: "set (enum_list_n n) = {xs. length xs = n}"
  apply (induct n;simp)
  apply (rule Set.set_eqI)
  apply clarsimp
  by (metis (no_types, lifting) length_Suc_conv rangeE rangeI)

lemma enum_list_n_distinct[simp]: "distinct (enum_list_n n)"
  apply (induct n;simp)
  apply (rule distinct_concat; simp add: distinct_map enum_list_n_set)
  subgoal by (rule inj_onI;auto)
  by (auto simp: distinct_map intro: injI)

lemma UNIV_seq: "(UNIV :: ('a,'b) seq set) = list_to_seq ` {xs. length xs = LEN('a)}"
  apply (rule UNIV_eq_I)
  by (metis image_iff seq_preserved seq_to_list)

instantiation seq :: (_,enum) enum begin
lift_definition "enum_seq" :: "('a, 'b::enum) seq list" is "enum_list_n LEN('a)"
  using Ball_set enum_list_n_set by auto
definition "enum_all_seq == (\<lambda>P. list_all P enum_class.enum) :: (('a, 'b) seq \<Rightarrow> bool) \<Rightarrow> bool"
definition "enum_ex_seq ==(\<lambda>P. list_ex P enum_class.enum) :: (('a, 'b) seq \<Rightarrow> bool) \<Rightarrow> bool"
instance
  apply standard
  subgoal H
    by (simp add: enum_seq.abs_eq enum_list_n_set UNIV_seq)
    apply (simp add: enum_seq.abs_eq distinct_map enum_list_n_set)
    apply (rule inj_onI)
    apply (metis list_to_seq_raw_inject)
  unfolding  enum_all_seq_def enum_ex_seq_def
  by (auto simp add: H list_all_iff list_ex_iff)
end


definition slice_seq :: "nat \<Rightarrow> ('n,'a) seq \<Rightarrow> ('m,'a) seq" where
  "slice_seq n xs \<equiv> take_seq (left_rotate xs n)"

definition slice_end_seq :: "nat \<Rightarrow> ('n,'a) seq \<Rightarrow> ('m,'a) seq" where
  "slice_end_seq n xs \<equiv> take_seq (left_rotate xs (LEN('n) - LEN('m) - n))"

lemma "(slice_end_seq 1 (list_to_seq [0,1,2,3,4] :: (5,int) seq) :: (2,int) seq) = list_to_seq [2,3]"
  by eval


context includes rotate_shift_syntax begin

private lemma take_drop_lemma: "m \<le> n \<Longrightarrow> m > 0 \<Longrightarrow>
       length xs = n \<Longrightarrow>
       take m
        (rotate (nat (int n - int m)) xs) =
       drop (n - m) xs"
  by (simp add: nat_minus_as_int rotate_drop_take)

private lemma take_rotate_drop_lemma: "m + n \<le> x \<Longrightarrow>
       length xs = x \<Longrightarrow>
       take m (rotate (nat (int x - (int m + int n))) xs) =
       drop (x - m) (shiftr_list a xs n)"
  apply (rule nth_equalityI)
   apply simp
  apply (simp add: shiftr_list_def nth_rotate)
  by (simp add: nat_diff_distrib' nat_int_add)

lemma shiftr_drop_as_rotatel_take: "LEN('m) + n \<le> LEN('n) \<Longrightarrow>
  (drop_seq (shiftr_seq a xs n) :: ('m,'a) seq) =
    take_seq
     ((xs :: ('n,'a) seq) <<< int LEN('n) - (int LEN('m) + int n))"
  apply (rule sym)
  apply (constrain 'n="'nn::len" and 'm="'mm::len")
  subgoal H[unconstrain_cases]
    apply transfer
    apply (simp add: right_shift_def left_rotate_def right_rotate_def)
    by (rule take_rotate_drop_lemma;simp)
  by (rule H; auto)
end

lemma slice_end_seq0_is_drop: 
  "LEN('m) \<le> LEN('n) \<Longrightarrow> (slice_end_seq 0 (x :: ('n,'a) seq) :: ('m,'a) seq) = drop_seq x"
  unfolding slice_end_seq_def
  by (simp add: shiftr_drop_as_rotatel_take[where n=0, simplified])

lemma nth_end_seq_drop: 
  "LEN('m) \<le> LEN('n) \<Longrightarrow> n < LEN('m) \<Longrightarrow>
  nth_end_seq (drop_seq (xs :: ('n,'a) seq) :: ('m,'a) seq) n = nth_end_seq xs n"
  by transfer simp

(* 
  like list_to_seq but mirrors the behavior of Word.of_bl: 
      - defined for all list lengths
      - if the length of xs is less than 'n then it is left-padded with zeros
      - if it is greater than 'n then extra elements are dropped from the sequence head
 *)

lift_definition list_to_seq_pad :: "'a list \<Rightarrow> ('n,'a::zero) seq" is
  "\<lambda>xs. (drop (length xs - LEN('n)) (replicate (LEN('n) - length xs) 0 @ xs))"
  by auto


lemma list_to_seq_pad_none: "length xs = LEN('n) \<Longrightarrow> (list_to_seq xs :: ('n,'a::zero) seq) = list_to_seq_pad xs"
  unfolding list_to_seq_pad_def
  by simp

lemma list_to_seq_pad_Cons: 
  "(list_to_seq_pad (x # xs) :: ('n,'b::zero) seq) = 
      (if length xs < LEN('n) then (seq_update_end (list_to_seq_pad xs) (length xs) x) else list_to_seq_pad xs)"
  apply (cases "length xs < LEN('n)")
  subgoal
    apply transfer
    apply simp
    by (metis Nat.diff_cancel Suc_diff_le Suc_leI
        append_Cons length_replicate
        list_update_length plus_1_eq_Suc
        replicate_Suc
        replicate_app_Cons_same)
  apply simp
  apply transfer
  by (simp add: drop_Cons')

lemma list_to_seq_pad_0_absorb: 
  "(list_to_seq_pad (0 # xs) :: ('n,'a::zero) seq) = list_to_seq_pad xs"
  apply (simp add: list_to_seq_pad_Cons)
  apply transfer
  apply simp
  by (metis diff_less_mono2 length_replicate
      lessI list_update_id nth_append_left
      nth_replicate)

lemma list_to_seq_pad_Nil:
  "(list_to_seq_pad [] :: ('n,'a::zero) seq) = 0"
  unfolding list_to_seq_pad_def zero_seq_def
  by simp

ML \<open>val seq_syntax = Attrib.setup_config_bool \<^binding>\<open>seq_syntax\<close> (K false);\<close>

bundle seq_syntax begin
declare [[seq_syntax]]

no_syntax "_bracket" :: "types \<Rightarrow> type \<Rightarrow> type" ("(\<open>notation=\<open>infix \<Rightarrow>\<close>\<close>[_]/ \<Rightarrow> _)" [0,0] 0)

syntax
  "_seq_type" :: "type \<Rightarrow> type \<Rightarrow> type" (\<open>('[_']_)\<close> [0,100] 100)
  "_seq_bool_type" :: "type \<Rightarrow> type" (\<open>'[_']\<close> 105)

syntax_types "_seq_type" \<rightleftharpoons> seq

translations
  (type) "['a]'b" \<rightharpoonup> (type) "('a,'b) seq"
  (type) "['a]" == (type) "('a,bool) seq"
  (type) "['a]'b" \<leftharpoondown> (type) "('a,'b) seq"

syntax
  "_seq" :: "args \<Rightarrow> 'a list"  (\<open>(\<open>indent=1 notation=\<open>mixfix list enumeration\<close>\<close>\<lbrakk>_\<rbrakk>)\<close>)
  "_seq_constrained" :: "args \<Rightarrow> type \<Rightarrow> 'a list"  (\<open>(\<open>indent=1 notation=\<open>mixfix list enumeration\<close>\<close>'(\<lbrakk>_\<rbrakk>/ ::/ _'))\<close>)

ML \<open>val seq_syntax_name = @{syntax_const "_seq"}\<close>
ML \<open>val seq_constrained_syntax_name = @{syntax_const "_seq_constrained"}\<close>

syntax_consts "_seq" \<rightleftharpoons> list_to_seq
syntax_consts "_seq_constrained" \<rightleftharpoons> list_to_seq
end


parse_translation
\<open>
let

fun mk_bintype n =
  let
    fun mk_bit 0 = Syntax.const \<^type_syntax>\<open>bit0\<close>
      | mk_bit 1 = Syntax.const \<^type_syntax>\<open>bit1\<close>;
    fun bin_of n =
      if n = 1 then Syntax.const \<^type_syntax>\<open>num1\<close>
      else if n = 0 then Syntax.const \<^type_syntax>\<open>num0\<close>
      else if n = ~1 then raise TERM ("negative type numeral", [])
      else
        let val (q, r) = Integer.div_mod n 2;
        in mk_bit r $ bin_of q end;
  in bin_of n end;

fun strip_args t = case t of
   (Const (@{syntax_const "_args"},_) $ t $ t2 ) => t :: strip_args t2
  | _ => [t]

fun constrain_len t n = Syntax.const @{syntax_const "_constrain"} $ t $ 
  (Syntax.const @{type_syntax seq} $ mk_bintype n $ Syntax.const @{type_syntax dummy}) 

fun mk_single x = constrain_len (Syntax.const @{const_syntax replicate_seq} $ x) 1

fun mk_appends (x :: xs) =  (Syntax.const @{const_syntax Cons} $ x $ mk_appends (xs))
 | mk_appends [] = Syntax.const @{const_syntax Nil}
in

[(seq_syntax_name, (fn ctxt =>
  fn [t] => 
   let val ts = (strip_args t)
       val seqT = Syntax.const @{type_syntax seq} $ (mk_bintype (length ts)) $ 
                  Syntax.const @{type_syntax dummy}
   in
   (Syntax.const @{syntax_const "_constrain"} $ (Syntax.const @{const_syntax "list_to_seq"} $ 
             (mk_appends ts)) $ seqT)
    end)),
(seq_constrained_syntax_name, (fn ctxt =>
  fn [t,T] => Syntax.const @{syntax_const "_constrain"} $
    (Syntax.const @{const_syntax "list_to_seq"} $ (mk_appends (strip_args t))) $ T))
]
end
\<close>

typed_print_translation \<open>
let

fun int_of [] = 0
  | int_of (b :: bs) = b + 2 * int_of bs;

fun bin_of (Const (\<^type_syntax>\<open>num0\<close>, _)) = []
  | bin_of (Const (\<^type_syntax>\<open>num1\<close>, _)) = [1]
  | bin_of (Const (\<^type_syntax>\<open>bit0\<close>, _) $ bs) = 0 :: bin_of bs
  | bin_of (Const (\<^type_syntax>\<open>bit1\<close>, _) $ bs) = 1 :: bin_of bs
  | bin_of _ = raise Match;

fun bin_of_typ ctxt T = int_of (bin_of (Syntax_Phases.term_of_typ ctxt T))

fun unpack_cons (Const (@{const_syntax Cons},_) $ x $ xs) = x :: unpack_cons xs
  | unpack_cons (Const (@{const_syntax Nil},_))  = []

fun to_args (x :: y :: xs) = 
   (Const (@{syntax_const "_args"},dummyT) $ x $ to_args (y :: xs))
 | to_args [x] = x

fun constrain_unless ctxt b e T = if b
  then Syntax.const @{syntax_const "_constrain"} $ e $ Syntax_Phases.term_of_typ ctxt T
  else e

fun get_seqT T = case Term.strip_type T of
  (_,Type(@{type_name "seq"},[T'',U])) => (T'',U)

fun valid_length ctxt i T = (i = bin_of_typ ctxt T)

in 
[(@{const_syntax list_to_seq}, fn ctxt => fn T =>  fn [ts] =>
  if Config.get ctxt seq_syntax then
  (let
      val xs = unpack_cons ts
      val (T',U) = get_seqT T
      val seqT = Type(@{type_name "seq"},[T',U])

      val valid_length' = valid_length ctxt (length xs) T'
        handle Match => false

      val ret = if valid_length'
        then Syntax.const seq_syntax_name $ to_args xs
        else Syntax.const seq_constrained_syntax_name $ to_args xs $ (Syntax_Phases.term_of_typ ctxt seqT)
  in ret end) else raise Match)]
end
\<close>

experiment begin
context includes seq_syntax begin

lemma "\<lbrakk>x,y,z\<rbrakk> = rev_seq \<lbrakk>z,y,x\<rbrakk>"
  apply transfer
  by simp

lemma "LEN('a) = 3 \<Longrightarrow> (\<lbrakk>x,y,z\<rbrakk> :: ['a]'b) = rev_seq (\<lbrakk>z,y,x\<rbrakk> :: ('a, 'b) seq)"
  apply transfer
  by simp


lemma X: "(TYPE(['a]['b]'c \<Rightarrow> ['d] \<Rightarrow> ['e]'e)) = TYPE(('a,('b, 'c)seq) seq \<Rightarrow> ('d,bool) seq \<Rightarrow> ('e,'e) seq)"
  by (rule refl)

typ "['a]['b]'c \<Rightarrow> ['d] \<Rightarrow> ['e]'e"
typ "['a]['b] \<Rightarrow> 'c"

end

thm X
end

end