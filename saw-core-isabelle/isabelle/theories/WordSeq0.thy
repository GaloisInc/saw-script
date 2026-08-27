theory WordSeq0
imports WordSeq
begin

text\<open> 
This theory addresses the problematic @{class len} constraint on words by providing
@{term seq_to_word} and @{term word_to_seq} variants that convert to words with their type parameter 
wrapped in the @{typ "'a len"} type constructor. A @{typ "('a len) word"} has the same length as
@{typ "'a"} if it is nonzero, otherwise it has an undefined, nonzero length.

Converting a @{typ "('a,'b::bool) seq"} to a @{typ "('a len) word"} therefore simply requires
checking if the underlying @{typ 'a} is zero-length, and returning 0 if so.
\<close>

definition seq_to_word0 :: "('a,'b::bool) seq \<Rightarrow> ('a len) word" where
  "seq_to_word0 x \<equiv> if LEN('a) = 0 then 0 else seq_to_word (coerce_seq_len x)"

lemma seq_to_word0_bool: "seq_to_word0 xs = seq_to_word0 (map_seq bool_of xs)"
  unfolding seq_to_word0_def seq_to_word_bool_of[where 'b='b]
  by simp

lemma seq_to_word0_zero[simp]: "LEN('a) = 0 \<Longrightarrow> seq_to_word0 (x :: ('a,'b::bool) seq) = 0"
  unfolding seq_to_word0_def
  by simp

text \<open>In the other direction, if @{typ 'a} is zero-length we can simply return an empty sequence
(technically we could write any value here, since 0-length sequences are a singleton type, 0
is chosen arbitrarily)\<close>

definition word_to_seq0 :: "('a len) word \<Rightarrow> ('a,'b::bool) seq" where
  "word_to_seq0 x \<equiv> if LEN('a) = 0 then 0 else coerce_seq_len (word_to_seq x)"

lemma word_to_seq0_bool: "word_to_seq0 xs = map_seq of_bool (word_to_seq0 xs)"
  unfolding word_to_seq0_def word_to_seq_of_bool[where 'b='b]
  by simp

lemma seq_to_from_word0[simp]: "word_to_seq0 (seq_to_word0 xs) = xs"
  unfolding seq_to_word0_def word_to_seq0_def
  by auto

lemma seq_to_word0_len[simp]: "seq_to_word0 (x :: ('a::len,'b::bool) seq) = ucast (seq_to_word x)"
  unfolding seq_to_word0_def
  apply simp
  by transfer simp

lemma word_to_seq0_len[simp]: "word_to_seq0 (x :: ('a::len len) word) = coerce_seq_len (word_to_seq x)"
  unfolding word_to_seq0_def
  by simp

named_theorems word_seq_conv0

lemma zero_seq0[word_seq_conv0, code]: "zero_class.zero = word_to_seq0 0"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] by (simp add: word_seq_convs)
  by (rule H;simp)

lemma one_seq0[word_seq_conv0,code]: "one_class.one = word_to_seq0 1"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] by (simp add: word_seq_convs)
  by (rule H;simp)

lemma numeral_seq0[word_seq_conv0]: "(numeral x) = word_to_seq0 (numeral x)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] by (simp add: word_seq_convs)
  by (rule H;simp)

lemma plus_seq0[word_seq_conv0,code]: "x + y = word_to_seq0 (seq_to_word0 x + seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    by (simp add: ucast_ucast_add unsigned_ucast_eq)
  by (rule H;simp)

lemma times_seq0[word_seq_conv0,code]: "x * y = word_to_seq0 (seq_to_word0 x * seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by (simp add: take_bit_mult)
  by (rule H;simp)

lemma minus_seq0[word_seq_conv0,code]: "x - y = word_to_seq0 (seq_to_word0 x - seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by (simp add: take_bit_diff)
  by (rule H;simp)

lemma divide_seq0[word_seq_conv0,code]: "x div y = word_to_seq0 (seq_to_word0 x div seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by simp
  by (rule H;simp)

lemma mod_seq0[word_seq_conv0,code]: "x mod y = word_to_seq0 (seq_to_word0 x mod seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by simp
  by (rule H;simp)

lemma uint_seq0[word_seq_conv0,code]: "uint_seq x = uint (seq_to_word0 x)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by simp
  by (rule H;simp)


lemma sint_seq0[word_seq_conv0,code]: "sint_seq (x :: ('a,'b::bool) seq) = sint (seq_to_word0 x)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by simp
  by (rule H;simp)

lemma of_int_seq0[word_seq_conv0,code]: "of_int_seq i = word_to_seq0 (word_of_int i)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    by simp
  by (rule H;simp)

lemma to_int_seq0[word_seq_conv0,code]: "to_int x = uint (seq_to_word0 x)"
  by (simp add: uint_seq0)

lemma to_sint_seq0[word_seq_conv0,code]: "to_sint x = sint (seq_to_word0 x)"
  by (simp add: sint_seq0)

lemma power_seq0[word_seq_conv0]: "power x n = word_to_seq0 (power (seq_to_word0 x) n)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by (simp add: no_bintr_alt1 power_mod)
  by (rule H;simp)


lemma ucast_seq0[word_seq_conv0,code]: "ucast_seq x = word_to_seq0 (ucast (seq_to_word0 x))"
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by simp
  apply (rule H;simp)
  by (erule context_disjE;simp add: word_seq_conv0)

lemma scast_seq0[word_seq_conv0,code]: "scast_seq x = word_to_seq0 (scast (seq_to_word0 x))"
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by simp
  apply (rule H;simp)
  by (erule context_disjE;simp add: word_seq_conv0)

lemma zext_seq0[word_seq_conv0,code]: "zext_seq x = word_to_seq0 (ucast (seq_to_word0 x))"
  apply (subst ucast_seq0[symmetric])
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: zext_seq_def2)
    apply (subst ext_seq_map_map[where g=of_bool and f=bool_of];simp del: zero_bool_def)
    apply (subst zext_seq_def2[symmetric])
    apply (simp add: zext_is_ucast)
    by (metis seq_to_word0_bool ucast_seq0 word_to_seq0_bool)
  apply (rule H;simp)
  by (erule context_disjE;simp add: zext_seq_def2 ext_seq_zero_replicate zero_seq_def2)

lemma sext_seq0[word_seq_conv0,code]: "sext_seq x = word_to_seq0 (scast (seq_to_word0 x))"
  apply (subst scast_seq0[symmetric])
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: sext_seq_def2)
    apply (subst ext_seq_map_map[where g=of_bool and f=bool_of]; simp add: bool_of_sign_seq)
    apply (simp add: sext_seq_def2[symmetric])
    apply (simp add: sext_is_scast)
    by (metis scast_seq0 seq_to_word0_bool word_to_seq0_bool)
  apply (rule H;simp)
  by (erule context_disjE;simp add: sext_seq_def2 sign_seq_zero ext_seq_zero_replicate zero_seq_def2)

context includes rotate_shift_syntax begin

lemma right_shift_seq0[word_seq_conv0]: "x >> n = word_to_seq0 ((seq_to_word0 x) >> n)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply (simp add: shift_rotate_word_defs)
    apply transfer
    by (simp add: push_bit_take_bit)
  by (rule H;simp)

lemma left_shift_seq0[word_seq_conv0]: "x << n = word_to_seq0 ((seq_to_word0 x) << n)"
  unfolding left_shift_def
  by (simp add: right_shift_seq0)

lemma right_rotate_seq0[word_seq_conv0]: "x >>> n = word_to_seq0 ((seq_to_word0 x) >>> n)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply (simp add: shift_rotate_word_defs)
    apply transfer
    by (simp add: push_bit_take_bit)
  by (rule H;simp)

lemma left_rotate_seq0[word_seq_conv0]: "x <<< n = word_to_seq0 ((seq_to_word0 x) <<< n)"
  unfolding left_rotate_def
  by (simp add: right_rotate_seq0)
end

lemma signed_right_rotate_seq0[word_seq_conv0,code]: 
  "x >>$ i = word_to_seq0 (if i \<ge> 0 then sshiftr (seq_to_word0 x) (nat i) else shiftl (seq_to_word0 x) (nat (-i)))"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by (simp add: push_bit_take_bit)
  by (rule H;simp)

lemma less_seq0[word_seq_conv0]: "x < y = (seq_to_word0 x < seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply simp
    apply transfer
    apply simp
    apply transfer
    by simp
  by (rule H;simp)

lemma less_eq_seq0[word_seq_conv0]: "x \<le> y = (seq_to_word0 x \<le> seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] 
    apply simp
    apply transfer
    apply simp
    apply transfer
    by simp
  by (rule H;simp)

lemma take_seq0[word_seq_conv0]: "(take_seq (x :: ('a,'b::bool) seq) :: ('c,'b::bool) seq) = 
    (if LEN('c) < LEN('a) then
      (word_to_seq0 (ucast (drop_bit (LEN('a) - LEN('c)) (seq_to_word0 x))))
    else coerce_seq_len x)"
  apply (cases "LEN('c) < LEN('a)")
  apply simp
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases] for x
    apply (subst take_seq_map_map[where g=of_bool and f=bool_of];simp)
    apply (simp add: word_seq_convs)
    apply (subst take_seq_absorb1[where 'm="'cc + (('aa - 'cc) len)" and 'n="'aa",symmetric])
      apply simp
     apply (subst take_seq_is_drop_bit)
     apply (simp add: word_seq_convs)
     apply transfer
     apply (simp add: comp_def)
    apply transfer
    by simp
   apply (rule H;simp)
  by (simp add: take_seq_def2)

lemma word_to_seq_def2: "word_to_seq w = list_to_seq (map of_bool (to_bl w))"
  by (simp add: list_to_seq_to_bl')

lemma drop_seq_ucast_conv[word_seq_convs]:
  "(drop_seq (x :: ('a::len,'b::bool) seq) :: ('c::len,'b::bool) seq) = 
     (if LEN('a) > LEN('c) then word_to_seq (ucast (seq_to_word x)) else coerce_seq_len x)"
  apply (cases "LEN('a::len) > LEN('c::len)")
  apply (subst drop_seq_map_map[where g=of_bool and f=bool_of];simp)
   apply (simp add: drop_seq_def)
  apply (simp add: list_to_seq_to_word seq_to_list_conv)
  apply (simp only: word_to_seq_def2 word_rep_drop)
   apply (simp add: to_bl_ucast seq_to_word_bool_of[symmetric])
  apply simp
  apply transfer
  by simp

lemma drop_seq0[word_seq_conv0,code]: "(drop_seq (x :: ('a,'b::bool) seq) :: ('c,'b::bool) seq) = 
    (if LEN('c) < LEN('a) then
      (word_to_seq0 (ucast (take_bit (LEN('c)) (seq_to_word0 x))))
    else coerce_seq_len x)"
  apply (constrain 'a="'aa::len" and 'c="'cc::len")
  subgoal H[unconstrain_cases] for x
    apply (cases "LEN('cc) < LEN('aa)")
    subgoal
      apply (simp add: word_seq_convs)
       apply transfer
       apply simp
       apply transfer
      by simp
    by (simp add: word_seq_convs)
  apply (rule H;simp)
  apply (erule context_disjE;simp)
  apply transfer
  by simp

lemma rev_seq0[word_seq_conv0,code]: "rev_seq (x :: ('a,'b::bool) seq) = word_to_seq0 (word_reverse (seq_to_word0 x))"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply (simp add: word_reverse_def ucast_bl)
    apply transfer
    by (simp del: bin_to_bl_def)
  by (rule H;simp)

lemma append_seq0': 
  assumes A:"LEN('d) = LEN('a) + LEN('c)"
  shows "((append_seq (x :: ('a,'b::bool) seq) (y :: ('c,'b::bool) seq)) :: ('d,'b::bool) seq) = 
    (if LEN('a) = 0 then coerce_seq_len y else
    if LEN('c) = 0 then coerce_seq_len x else
    word_to_seq0 (word_cat (seq_to_word0 x) (seq_to_word0 y)))"
  apply (constrain 'a="'aa::len" and 'c="'cc::len" and 'd="'dd::len" notes A)
  subgoal H[unconstrain_cases] for x
    apply (subst append_seq_map_map[where g=of_bool and f=bool_of];simp)
    apply (simp add: word_seq_convs)
    apply (simp add:  seq_to_word_bool_of[symmetric] seq_to_word_of_bool)
    apply transfer
    apply simp
    apply transfer
    apply simp
    done
   apply (rule H;simp add: A)
  by (elim context_disjE;simp)

lemma append_seq0[word_seq_conv0]: "((append_seq (x :: ('a,'b::bool) seq) (y :: ('c,'b::bool) seq)) :: ('d,'b::bool) seq) = 
    (if LEN('a) = 0 then coerce_seq_len y else
    if LEN('c) = 0 then coerce_seq_len x else
    if LEN('d) = LEN('a) + LEN('c) then
     word_to_seq0 (word_cat (seq_to_word0 x) (seq_to_word0 y))
    else coerce_seq_len (word_to_seq0 (word_cat (seq_to_word0 x) (seq_to_word0 y)) :: ('a+'c,'b::bool) seq))"
  apply (cases "LEN('d) = LEN('a) + LEN('c)")
   apply (simp add: append_seq0')
  apply (subst append_seq_as_sum)
  apply (subst append_seq0';simp)
  done 

lemma seq_to_list0[word_seq_conv0]: 
 "seq_to_list (x :: ('a,'b::bool) seq) = (if LEN('a) = 0 then [] else of_bool_list (to_bl (seq_to_word0 x)))"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    apply (subst seq_to_list_map_map[where g=of_bool and f=bool_of])
    apply simp
    apply (simp add: seq_to_list_conv)
    apply (simp add:  seq_to_word_bool_of[symmetric])
    apply transfer
    by (simp add: to_bl_ucast)
  apply (rule H;simp)
  apply transfer
  apply simp
  done

lemma of_bool_swap: "bool_of x = y \<Longrightarrow> (x :: 'b :: bool) = of_bool y"
  by force


lemma nth_seq0[word_seq_conv0]: 
  assumes A: "i < LEN('a)"
  shows "nth_seq (x :: ('a,'b::bool) seq) i = (of_bool ((seq_to_word0 x) !! (LEN('a) - (Suc i))))"
  apply (rule of_bool_swap)
  apply (subst map_seq_nth[OF A, where f=bool_of,  symmetric])
  apply (constrain 'a="'aa::len" notes A)
  subgoal H[unconstrain]
    apply (subst nth_seq_conv,assumption)
    apply simp
    apply transfer
    apply (simp add: comp_def)
    apply transfer
    by (simp add: bit_take_bit_iff)
  apply (rule H)
  using A
  by auto

lemma nth_end_seq0[word_seq_conv0]: 
  assumes A: "i < LEN('a)"
  shows "nth_end_seq (x :: ('a,'b::bool) seq) i = (of_bool ((seq_to_word0 x) !! i))"
  unfolding nth_end_seq_def2[where i=i and 'b='a, simplified A, simplified]
  apply (subst nth_seq0)
  using A
  by auto

lemma carry_seq0[word_seq_conv0,code]: 
  "carry_seq x y = carry_word (seq_to_word0 x) (seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (simp add: carry_seq_conv carry_word_code carry_int_def unsigned_ucast_eq)
  by (rule H;simp add: carry_seq_def2 carry_word_def2)

lemma scarry_seq0[word_seq_conv0,code]: 
  "scarry_seq x y = scarry_word (seq_to_word0 x) (seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (simp add: scarry_seq_conv scarry_word_code unsigned_ucast_eq)
  by (rule H;simp add: scarry_seq_def2 scarry_word_def2)

lemma sborrow_seq0[word_seq_conv0,code]: 
  "sborrow_seq x y = sborrow_word (seq_to_word0 x) (seq_to_word0 y)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (simp add: sborrow_seq_conv sborrow_word_code unsigned_ucast_eq)
  by (rule H;simp add: sborrow_seq_def2 sborrow_word_def2)

lemma uminus_seq0[word_seq_conv0,code]: 
  "uminus x = word_to_seq0 (- (seq_to_word0 x))"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    apply (simp add: word_seq_convs)
    apply transfer
    apply simp
    apply transfer
    by (simp add: take_bit_diff take_bit_minus)
  by (rule H;simp)

end