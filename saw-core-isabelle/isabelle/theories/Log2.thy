theory Log2
imports Word_Lib.Word_Lib_Sumo Alt_Type_Length
begin

lemmas [simp] = list_update_beyond

definition divup :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "divup x y \<equiv> if y dvd x then x div y else Suc (x div y)"

lemma divup_le[simp]: "divup n 2 \<le> n"
  apply (simp add: divup_def)
  by (simp add: Suc_leI odd_pos)

fun log2_nat :: "nat \<Rightarrow> nat" where
  "log2_nat (Suc (Suc n)) = Suc (log2_nat (Suc (divup n 2)))"
| "log2_nat (Suc 0) = 0"
| "log2_nat 0 = 0"

lemma log2_nat_numeral_Bit0[simp]: "log2_nat (numeral (Num.Bit0 x)) = Suc (log2_nat (numeral x))"
  by (metis div2_Suc_Suc divup_def even_Suc even_numeral
      log2_nat.elims numeral_Bit0_div_2 numeral_eq_Suc
      one_eq_numeral_iff pred_numeral_simps(1)
      verit_eq_simplify(10) zero_neq_numeral)

lemma log2_nat_numeral_Bit1[simp]: "log2_nat (numeral (Num.Bit1 x)) = Suc (log2_nat (numeral (Num.inc x)))"
  by (metis div2_Suc_Suc divup_def eval_nat_numeral(3)
      even_Suc even_numeral log2_nat.simps(1) nat_of_num_inc
      nat_of_num_numeral numeral_Bit1_div_2
      numeral_eq_Suc)

lemma log2_nat_numeral_One[simp]: "log2_nat (numeral (Num.One)) = 0"
  by simp

experiment begin
lemma
  "map log2_nat [0, 1, 2,30,31,32,33,34,35,36,62,63,64,65] 
              = [0, 0, 1, 5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 7]"
  by auto
end

lemma divup_splits1: "P (divup n m) = ((m dvd n \<longrightarrow> P (n div m)) \<and> (\<not>(m dvd n) \<longrightarrow> P (Suc (n div m))))"
  by (simp add: divup_def)

lemma divup_splits2: "P (divup n m) = (\<not> ((m dvd n \<and> (\<not> P (n div m)) \<or> (\<not>(m dvd n) \<and> \<not> P (Suc (n div m))))))"
  by (simp add: divup_def)

lemma divup_dvd[simp]: "m dvd n \<Longrightarrow> divup n m = n div m"
  by (simp add: divup_def)

lemma divup_not_dvd[simp]: "\<not> (m dvd n) \<Longrightarrow> divup n m = Suc (n div m)"
  by (simp add: divup_def)

lemmas divup_splits = divup_splits1 divup_splits2

lemma log2_nat_mul2[simp]: "n > 0 \<Longrightarrow> log2_nat (2 * n) = Suc (log2_nat n)"
  by (induct n rule: log2_nat.induct;auto split: divup_splits)

lemma log2_nat_suc: "n > 0 \<Longrightarrow> log2_nat (Suc n) = Suc (log2_nat (divup (Suc n) 2))"
  by (cases n;simp split: divup_splits)

lemma log2_nat_mul2_suc[simp]: "n > 0 \<Longrightarrow> log2_nat (Suc (2 * n)) = Suc (log2_nat (Suc n))"
  by (induct n rule: log2_nat.induct;auto split: divup_splits)

lemma nat_bit_induct1: "P 0 \<Longrightarrow> P 1 \<Longrightarrow>
  (\<And>n. P n \<Longrightarrow> 0 < n \<Longrightarrow> P (2 * n)) \<Longrightarrow>
  (\<And>n. P n \<Longrightarrow> 0 < n \<Longrightarrow> P (Suc (2 * n))) \<Longrightarrow> P n"
  
  by (metis One_nat_def bot_nat_0.not_eq_extremum mult_is_0
      nat_bit_induct)


lemma pow2_mul2_split: "((2::nat) ^ (2 * (n::nat))) = (2^n) * (2^n)"
  by (simp add: semiring_normalization_rules)

lemma log2_nat_pow2_suc_case: "log2_nat (Suc x) \<noteq> log2_nat x \<Longrightarrow> log2_nat (Suc x) = Suc (log2_nat x)"
  by (induct x rule: nat_bit_induct1;simp)

lemma log2_suc_cases: 
  "((log2_nat (Suc x) = log2_nat x) \<Longrightarrow> P) \<Longrightarrow> (log2_nat (Suc x) = Suc (log2_nat x) \<Longrightarrow> P) \<Longrightarrow> P"
  by (induct x rule: nat_bit_induct1;simp)

lemma log2_nat_pow2_exact: "(log2_nat (Suc x) = Suc (log2_nat x)) = (2 ^ log2_nat x = x)"
  apply (rule iffI)
  subgoal by (induct x rule: nat_bit_induct1;simp)
  apply (induct x rule: nat_bit_induct1; simp)
  by (metis even_Suc even_mult_iff even_numeral)

lemma log2_nat_nonzero[simp]: "n > 1 \<Longrightarrow> log2_nat n > 0"
  by (metis One_nat_def Zero_not_Suc
      bot_nat_0.not_eq_extremum log2_nat_suc
      not0_implies_Suc not_less_eq)

lemma nat_bit_induct_strong:
  assumes P0: "P 0" and P1: "P 1"
          and even: "(\<And>n. (\<And>m. m < (2 * n) \<Longrightarrow> P m) \<Longrightarrow> 0 < n \<Longrightarrow> P (2 * n))"
          and odd: "(\<And>n. (\<And>m. m < Suc (2 * n) \<Longrightarrow> P m) \<Longrightarrow> 0 < n \<Longrightarrow> P (Suc (2 * n)))"
        shows "P n"
  apply (induct n rule: less_induct)
  subgoal for x
    apply (cases "x = 0")
     apply (simp add: P0)
    apply (cases "x = 1")
    using One_nat_def P1 apply presburger
    apply (subgoal_tac "P (x div 2)")
    prefer 2
     apply force
    apply (cases "even x")
    apply (metis Suc_n_div_2_gt_zero bot_nat_0.not_eq_extremum even
        even_Suc_div_two even_two_times_div_two)
    by (metis mod_mult_div_eq odd odd_one one_div_two_eq_zero
        parity_cases plus_1_eq_Suc zero_less_iff_neq_zero)
  done

lemma log2_nat_pow2_mul_add: "log2_nat (2 ^ m * 2 ^ n) = log2_nat(2 ^ m) + log2_nat(2 ^ n)"
  apply (induct m arbitrary: n;simp)
  by (simp add: mult.assoc)

lemma log2_nat_pow2[simp]: "log2_nat ((2::nat) ^ x) = x"
  apply (induct x rule: nat_bit_induct_strong;simp?)
  apply (simp add: pow2_mul2_split)
  apply (simp add: log2_nat_pow2_mul_add)
  done

definition is_pow2 :: "nat \<Rightarrow> bool" where
  "is_pow2 n \<equiv> \<exists>k. n = 2 ^ k"

lemma is_pow2_def2:
  "is_pow2 n = (log2_nat (Suc n) = Suc (log2_nat n))"
  apply (simp add: log2_nat_pow2_exact is_pow2_def)
  apply (rule iffI)
   apply clarsimp
  by metis

lemma is_pow2_def3[code]:
  "is_pow2 n = (n = 2 ^ (log2_nat n))"
  using is_pow2_def by auto

lemmas is_pow2_log2_suc[simp] = is_pow2_def2[THEN iffD1]

lemma not_pow2_log2[simp]:"\<not> (is_pow2 n) \<Longrightarrow> log2_nat (Suc n) = log2_nat n"
  by (meson is_pow2_def2
      log2_suc_cases)

lemma is_pow2_nonzero[simp]: "\<not> (is_pow2 0)"
  by (simp add: is_pow2_def)

lemma is_pow2_gt0[simp]: "is_pow2 n \<Longrightarrow> n > 0"
  using neq0_conv by fastforce

lemma is_pow2_one[simp]: "is_pow2 1" 
  by (metis is_pow2_def power_0)

lemma is_pow2_two[simp]: "is_pow2 2" 
  by (metis is_pow2_def power_one_right)

lemma is_pow2_one'[simp]: "is_pow2 (Suc 0)" 
  using is_pow2_one by auto

lemma is_pow2_mul2[simp]: "is_pow2 (2 * n) = is_pow2 n"
  by (metis (no_types, lifting) ext add_left_cancel gr0I
      is_pow2_def2 log2_nat_mul2 log2_nat_mul2_suc mult_0_right
      plus_1_eq_Suc)

lemma is_pow2_pow2[simp]: "is_pow2 (2 ^ n)"
  by (simp add: is_pow2_def)

lemma log2_nat_is_pow2_mul_add: 
  "is_pow2 a \<Longrightarrow> is_pow2 b \<Longrightarrow> log2_nat (a * b) = log2_nat a + log2_nat b"
  using is_pow2_def log2_nat_pow2_mul_add by force


lemma is_pow2_even: "n \<noteq> 1 \<Longrightarrow> is_pow2 n \<Longrightarrow> even n"
  unfolding is_pow2_def2
  by (induct n rule: nat_bit_induct_strong;simp)

lemma is_pow2_not_suc: "is_pow2 i \<Longrightarrow> (i = 1 \<or> \<not> (is_pow2 (Suc i)))"
  by (metis One_nat_def even_Suc
      is_pow2_even is_pow2_gt0
      less_irrefl_nat nat.sel(2))

lemma pow2_dvd: "is_pow2 i \<Longrightarrow> is_pow2 j \<Longrightarrow> i \<ge> j \<Longrightarrow> j dvd i"
  apply (clarsimp simp add: is_pow2_def)
  by (simp add: le_imp_power_dvd)

lemma pow2_sum_iff: "((2::nat) ^ i + (2::nat) ^ j = 2 ^ kb) = (i = j \<and> kb = Suc i)"
  by (metis Suc_mask_eq_exp add.commute
      dvd_add_triv_right_iff gcd_nat.eq_iff
      is_pow2_pow2 less_eq_Suc_le
      log2_nat_pow2 mult_2 not_add_less2
      not_less_eq pow2_dvd power_Suc)

lemma is_pow2_add_pows: "is_pow2 i \<Longrightarrow> is_pow2 j \<Longrightarrow> (is_pow2 (i + j) = (i = j))"
  unfolding is_pow2_def
  using pow2_sum_iff by force

lemma is_pow2_mul_weak: "is_pow2 (n * m) \<Longrightarrow> is_pow2 m"
  unfolding is_pow2_def3
  apply (induct n arbitrary: m rule: nat_bit_induct_strong;simp?)
  apply (metis is_pow2_def3 is_pow2_mul2
      less_2_cases_iff mult.assoc
      n_less_m_mult_n)
  subgoal for i j
    apply (induct j rule: nat_bit_induct_strong;simp?)
    subgoal
      by (metis bot_nat_0.not_eq_extremum
          distrib_left_numeral less_2_cases_iff
          mult.assoc n_less_m_mult_n not_less_eq
          numeral_2_eq_2
          numeral_Bit0_eq_double)
    by (metis add_diff_cancel_left' add_is_0
        bot_nat_0.not_eq_extremum even_add
        even_mult_iff even_numeral mult_is_0
        nat_power_eq_Suc_0_iff plus_1_eq_Suc
        semiring_parity_class.even_mask_iff
        zero_neq_numeral)
  done


lemma is_pow2_mul[simp]: "is_pow2 (n * m) = (is_pow2 n \<and> is_pow2 m)"
  apply (rule iffI)
   apply (metis is_pow2_mul_weak mult.commute)
  by (simp add: is_pow2_def3
      log2_nat_is_pow2_mul_add
      power_add)

lemma log2_nat_suc_suc2[simp]: "log2_nat (Suc (Suc (2 * a))) = Suc (log2_nat (Suc a))"
  by fastforce

lemmas [simp del] = log2_nat.simps(1)

lemma log2_nat_pow2_bound:
  "x \<le> 2 ^ n \<Longrightarrow> log2_nat x \<le> n"
  apply (induct x arbitrary: n rule: nat_bit_induct_strong;simp?)
  subgoal for i j by (induct j;simp)
  subgoal for i j by (induct j;simp)
  done

lemma log2_nat_decrease: "n > 0 \<Longrightarrow> log2_nat n < n"
  apply (induct n  rule: nat_bit_induct_strong;simp?)
  apply (meson less_2_cases_iff
      less_trans_Suc
      n_less_m_mult_n)
  by (metis Suc_lessD lessI log2_nat_mul2
      log2_suc_cases nat_0_less_mult_iff
      numeral_2_eq_2)

lemma log2_nat_pow2_bound_strict:
  "x < 2 ^ n \<Longrightarrow> log2_nat x < 2 ^ n"
  using less_or_eq_imp_le
    log2_nat_pow2_bound pow_mono_leq_imp_lt
  by presburger

lemma unat_mul2[simp]: "a < 2 ^ (LENGTH('a) - 1) \<Longrightarrow> (unat (2 * (a :: 'a :: len word))) = 2 * (unat a)"
  by (metis (no_types, opaque_lifting) One_nat_def
      Suc_pred len_gt_0 lessI power_one_right
      unat_eq_of_nat unat_mult_power_lem unat_power_lower
      unsigned_less word_less_nat_alt)

lemma unat_pos[simp]: "0 < a \<Longrightarrow> 0 < unat a"
  by (simp add: word_less_nat_alt)

lemma word_msb_hd[simp]: "to_bl a = x # xs \<Longrightarrow> msb a = x"
  by (simp add: word_msb_alt)

lemma 
  takeWhile_append_end:
  "(\<exists>x\<in>(set xs). \<not> P x) \<Longrightarrow> takeWhile P (xs @ [x]) = takeWhile P xs"
  by (induct xs arbitrary: x;simp)

lemma word_clz_not_msb:
  "a > 0 \<Longrightarrow> \<not> (msb a) \<Longrightarrow> word_clz (2 * a) = word_clz a - 1"
  apply (simp add: word_clz_def to_bl_double_eq)
  apply (cases "to_bl a")
   apply simp+
  apply (subst takeWhile_append_end)
   apply simp
  apply (metis eq_zero_set_bl order_less_irrefl
      set_ConsD)
  by simp


lemma 
  word_suc_no_carry:
  "\<not> lsb (a :: 'a :: len word) \<Longrightarrow> (1 + a) = semiring_bit_operations_class.set_bit 0 a"
  by (metis add.commute bit_0 even_half_succ_eq
      lsb_this_or_next set_bit_0
      set_bit_eq_idem_iff)

(* FIXME: duplicated from Seq *)
lemma list_upto_cong: "x = y \<Longrightarrow>
  (\<And>z. z < x \<Longrightarrow> f z = g z) \<Longrightarrow>
  map f [0..<x] = map g [0..<y]"
  by (rule list.map_cong;simp)

(* FIXME: duplicated from Seq *)
lemma list_update_def2: 
  "xs[ix := x] = map (\<lambda>i. if i = ix then x else xs ! i) [0..<(length xs)]"
proof -
  have "\<And>n. length xs = n \<Longrightarrow> xs[ix := x] = map (\<lambda>i. if i = ix then x else xs ! i) [0..<n]"
    by (induct ix arbitrary: xs x; simp add: list_eq_iff_nth_eq)
  from this show ?thesis by simp
qed

lemma map_rev_upto: "(map f (rev [0..<n])) = map (\<lambda>i. f (n - i - 1)) [0..<n]"
  apply (induct n)
   apply (simp cong: list_upto_cong)+
  by (metis (mono_tags, lifting) diff_Suc_1' diff_Suc_Suc
      list_upto_cong map_upt_Suc)

lemma map_rev_upto_update:
  "i < n \<Longrightarrow> (map f (rev [0..<n])) [i := x] = (map (\<lambda>j. if j = (n - i - 1) then x else f j) (rev [0..<n]))"
  by (auto simp add: map_rev_upto list_update_def2)

lemma set_bit_as_to_bl_update:
  "n < LENGTH('a) \<Longrightarrow> to_bl (semiring_bit_operations_class.set_bit n (a:: 'a word)) = 
        list_update (to_bl a) (LENGTH('a::len) - 1 - n) True"
  by (simp add: to_bl_eq_rev  bit_setBit_iff[abs_def] map_rev_upto_update)

lemma takeWhile_is_take_least:
  "(\<exists>x\<in>(set xs). \<not> P x) \<Longrightarrow> takeWhile P xs = take (LEAST i. \<not> P (xs ! i)) xs"
  apply (rule LeastI2_wellorder_ex)
  apply (metis nth_the_index)
  apply clarsimp
  by (metis linorder_not_le
      takeWhile_eq_take_P_nth)

lemma takeWhile_list_update:
  "(\<exists>i < n. \<not>P (xs ! i)) \<Longrightarrow> takeWhile P (xs [n := x]) = takeWhile P xs"
  apply (cases "n < length xs")
  apply (subst takeWhile_is_take_least)
   apply clarsimp
  apply (metis length_list_update not_less_iff_gr_or_eq
      nth_list_update_neq nth_mem order_less_trans)
  apply (subst takeWhile_is_take_least)
   apply fastforce
  apply (subst take_update_cancel)
  apply (metis dual_order.strict_trans linorder_not_le
      not_less_Least nth_list_update_neq
      order_less_irrefl)
  apply (rule arg_cong, rule Least_equality)  
  apply (metis LeastI_ex not_less_Least
      nth_list_update)
  apply (metis dual_order.strict_trans linorder_not_le
      not_less_Least nth_list_update_neq)
  apply simp
  done

lemma takeWhile_update_at_notP:
  "\<not> P x \<Longrightarrow> \<not> P (xs ! n) \<Longrightarrow> takeWhile P (xs[n := x]) = takeWhile P xs"
  apply (cases "n < length xs")
  prefer 2
   apply simp
  apply (cases "(\<exists>i < n. \<not>P (xs ! i))")
   apply (simp add: takeWhile_list_update)
  apply clarsimp
  by (metis list_update_id takeWhile_tail
      upd_conv_take_nth_drop)
  
lemma takeWhile_list_update_prefix_notP:
  "(\<exists>i \<le> n. \<not>P (xs ! i)) \<Longrightarrow> \<not> P x \<Longrightarrow> takeWhile P (xs [n := x]) = takeWhile P xs"
  apply clarsimp
  subgoal for i
    apply (cases "i = n")
     apply simp
     apply (simp add: takeWhile_update_at_notP)
    apply (subst takeWhile_list_update)
    using nat_less_le apply blast
    by simp
  done

lemma word_clz_not_lsb_suc:
  "a > 0 \<Longrightarrow> \<not> (lsb a) \<Longrightarrow> word_clz (1 + a) = word_clz a"
  apply (simp add: word_clz_def to_bl_double_eq word_suc_no_carry set_bit_as_to_bl_update)
  apply (subst takeWhile_list_update_prefix_notP;simp)
  by (simp add: eq_zero_set_bl in_set_conv_nth
      word_greater_zero_iff)

lemma word_clz_not_msb_pos: "\<not> (msb a) \<Longrightarrow> word_clz a > 0"
  apply (simp add: word_clz_def to_bl_double_eq)
  by (simp add: takeWhile_eq_Nil_iff
      word_msb_alt)

lemma word_log2_mul2[simp]: "(a :: 'a :: len word) > 0 \<Longrightarrow> 
       a < 2 ^ (LENGTH('a) - 1) \<Longrightarrow>
      word_log2 (2 * a) = Suc (word_log2 a)"
  apply (simp add: word_log2_def)
  apply (simp add: word_size not_msb_from_less word_clz_not_msb word_clz_not_msb_pos)
  by (metis Suc_diff_Suc word_clz_nonzero_max word_gt_0
      wsst_TYs(3))

lemma word_log2_mul2_suc[simp]: "(a :: 'a :: len word) > 0 \<Longrightarrow> 
       a < 2 ^ (LENGTH('a) - 1) \<Longrightarrow>
      word_log2 (1 + 2 * a) = Suc (word_log2 a)"
  apply (simp add: word_log2_def)
  apply (simp add: word_size not_msb_from_less word_clz_not_msb word_clz_not_msb_pos)
  apply (subst word_clz_not_lsb_suc)
  using double_eq_zero_iff word_greater_zero_iff
    apply blast
  using bit_double_iff apply blast
  apply (subgoal_tac "\<not> (msb a)")
  apply (simp add: word_clz_not_msb word_clz_not_msb_pos)
  apply (metis Suc_diff_Suc word_clz_nonzero_max word_gt_0
      wsst_TYs(3))
  apply (simp add: not_msb_from_less)
  done

lemma unat_plus_mul2_distrib[simp]:
  "(a :: 'a :: len word) < 2 ^ (LENGTH('a::len) - 1) \<Longrightarrow> unat(1 + 2 * a) = Suc (2 * unat a)"
  by (metis One_nat_def Suc_pred add.commute len_gt_0
      less_2p_is_upper_bits_unset mult.commute
      n_less_equal_power_2 nat_add_offset_less
      plus_1_eq_Suc power_Suc0_right unat_less_power
      unat_mul2 unat_plus_if' unsigned_1)

lemma word_log2_1[simp]: "word_log2 1 = 0"
  by (metis bit_1_iff bit_word_log2 zero_neq_one)

lemma word_log2_to_lg2_nat:
  "x > 0 \<Longrightarrow> word_log2 ((x :: 'a :: len word)) = log2_nat (Suc (unat x)) - 1"
  apply (induct x rule: word_bit_induct)
    apply clarsimp+
  subgoal for a
    apply (cases "0 < a";simp)
    by (simp add: word_gt_0)
  done

datatype 'a Width (\<open>(\<open>notation=\<open>prefix\<close>\<close>width _)\<close> 30) = WidthTypeCtr
instantiation Width :: (_)len0 begin
definition "len_of_Width == \<lambda>(_ :: 'a Width itself).(log2_nat (Suc LEN('a)))"
instance ..
end

datatype 'a lg2 = lg2TypeCtr
instantiation lg2 :: (_)len0 begin
definition "len_of_lg2 == \<lambda>(_ :: 'a lg2 itself).(log2_nat LEN('a))"
instance ..
end

lemmas [simp] = len_of_Width_def len_of_lg2_def

primrec is_pow2_numeral :: "num \<Rightarrow> bool" where
  "is_pow2_numeral (num.Bit0 n) = is_pow2_numeral n"
| "is_pow2_numeral (num.Bit1 n) = False"
| "is_pow2_numeral num.One = True"

function log2_numeral :: "num \<Rightarrow> nat" where
  "log2_numeral num.One = 0"
| "log2_numeral (num.Bit0 n) = Suc (log2_numeral n)"
| "log2_numeral (num.Bit1 n) = Suc (log2_numeral (Num.inc n))"
  by pat_completeness auto

termination 
  apply (relation "measure (\<lambda>x. nat_of_num x)")
    apply simp+
   apply (metis nat_of_num_pos)
  apply simp
  by (metis nat_of_num_pos nat_of_num_inc Suc_less_eq add.right_neutral add_less_cancel_left)

lemma log2_numeral: "log2_nat (numeral x) = log2_numeral x"
  by (induct x rule: log2_numeral.induct; simp)

lemma is_pow2_numeral: "is_pow2 (numeral x) = is_pow2_numeral x"
  apply (induct x; simp)
   apply (metis numeral_Bit0_eq_double is_pow2_mul2)
  using is_pow2_even numeral_eq_one_iff
    odd_numeral by blast

lemma is_pow2_is_push_bit_nat:
  "is_pow2 n \<Longrightarrow> push_bit (log2_nat n) 1 = of_nat n"
  using is_pow2_def by fastforce

lemma log2_numeral_size: "is_pow2_numeral x \<Longrightarrow> log2_numeral x = size x"
  by (induct x rule: log2_numeral.induct; simp)

lemma is_pow2_is_push_bit_numeral:
  "is_pow2_numeral x \<Longrightarrow> numeral x = push_bit (size x) 1"
  by (metis is_pow2_is_push_bit_nat
      is_pow2_numeral log2_numeral
      of_nat_numeral log2_numeral_size)


end