(*Proofs about 0-length words. Note that the results in this theory do not require
  any additional axioms, but this imposes some limitations on what can be proven. 

  We can't prove instances for some algebraic classes, since we can't show, for example,
  that x + 0 = x for any x. Specifically we know that "Word.word.Abs_word UNIV" is the only
  possible result for any lifted word operation, but we can't prove that all zero-length words
  necessarily equal this value.

  The theory Unconstrain_Typedef provides the axiomatic extension to typedef that's needed to
  establish that 0-length words are actually a singleton type.

*)

theory Word0
  imports WordSeq
begin

instance word :: (_) "{zero,one,power,plus,times,minus,uminus,divide,ord}"
  by standard

setup \<open>Sign.qualified_path true @{binding trivial}\<close>

context
    fixes x :: "'a word" 
    assumes trivial_len[simp]: "LEN('a) = 0"
begin
lemmas [simp] = trivial_len[simplified len_of_alt_def2]

unconstraining
  Word.Word
begin

lemma Word: "Word.Word i = (Word.Word j :: 'a word)"
  unfolding Word.Word_def[unconstrain_def]
            Quotient.quot_type.abs_def[unconstrain_def]
  by simp

lemma Word0[simp]: "Word.Word i = (0 :: 'a word)"
  unfolding zero_word_def[unconstrain_def]
  by (rule Word)

end

unconstraining
  take_bit and drop_bit and unsigned and push_bit and cr_word and pcr_word and shiftl and shiftr and
  semiring_bit_operations_class.set_bit and bit and of_bl and to_bl and to_int and from_int and
  set_bit and unset_bit and of_int and of_nat
begin

lemma one[simp]: "(1 :: 'a word) = 0"
  unfolding one_word_def[unconstrain_def]
  by simp

lemma unsigned[simp]: "unsigned x = 0"
  unfolding unsigned_def[unconstrain_def] of_nat_def[unconstrain_def] 
  by simp

lemma take_bit[simp]: "take_bit n x = 0"
  unfolding take_bit_word_def[unconstrain_def]
  by simp

lemma drop_bit[simp]: "drop_bit n x = 0"
  unfolding drop_bit_word_def[unconstrain_def]
  by simp

lemma push_bit[simp]: "push_bit n x = 0"
  unfolding push_bit_word_def[unconstrain_def]
  by simp

(* note that cr_word and pcr_word do not hold for 
   all zero-length words without additional axiomatization *)

lemma cr_word[simp]: "cr_word i (0 :: 'a word)"
  unfolding cr_word_def[unconstrain_def]
  by simp

lemma pcr_word[simp]: "pcr_word i (0 :: 'a word)"
  unfolding pcr_word_def[unconstrain_def]
  by (simp add: relcompp_apply)

lemma plus_word[simp]: "x + y = 0"
  unfolding plus_word_def[unconstrain_def]
  by simp

lemma times_word[simp]: "x * y = 0"
  unfolding times_word_def[unconstrain_def]
  by simp

lemma div_word[simp]: "x div y = 0"
  unfolding divide_word_def[unconstrain_def]
  by simp

lemma power_word[simp]: "x ^ y = 0"
  by (induct y;simp)

lemma shiftl_word[simp]: "x << y = 0"
  unfolding shiftl_def[unconstrain_def]
  by simp

lemma shiftr_word[simp]: "x >> y = 0"
  unfolding shiftr_def[unconstrain_def]
  by simp

lemma set_bit[simp]: "semiring_bit_operations_class.set_bit n x = 0"
  unfolding set_bit_word_def[unconstrain_def]
  by simp

lemma unset_bit[simp]: "unset_bit n x = 0"
  unfolding unset_bit_word_def[unconstrain_def]
  by simp

lemma generic_set_bit[simp]: "set_bit x n b = 0"
  unfolding set_bit_eq[unconstrain_def]
  by simp

lemma bit[simp]: "bit x n = False"
  unfolding bit_word_def[unconstrain_def]
  by simp

lemma of_bl[simp]: "of_bl bl = (0 :: 'a word)"
  unfolding of_bl_def[unconstrain_def]
  by simp

lemma to_bl[simp]: "to_bl x = []"
  unfolding Reversed_Bit_Lists.to_bl_def[unconstrain_def]
  by simp

lemma less[simp]: "x < y = False"
  unfolding less_word_def[unconstrain_def]
  by simp

lemma less_eq[simp]: "x \<le> y = True"
  unfolding less_eq_word_def[unconstrain_def]
  by simp

lemma to_int[simp]: "to_int x = 0"
  unfolding to_int_word_def[unconstrain_def]
  by simp

lemma of_nat[simp]: "of_nat i = (0 :: 'a word)"
  unfolding semiring_1_class.of_nat_def[unconstrain_def]
  by (induct i;simp add: plus_word_def[unconstrain_def])

lemma of_int[simp]: "of_int i = (0 :: 'a word)"
  unfolding ring_1_class.of_int_def[unconstrain_def]
  by (simp add: minus_word_def[unconstrain_def])

lemma from_int[simp]: "from_int i = (0 :: 'a word)"
  unfolding from_int_word_def[unconstrain_def]
  by simp

end

unconstraining
  zint_to_word and
  word_to_zint
begin
context fixes z :: "'a Z\<^sup>2"  begin

lemma zint_to_word[simp]: "zint_to_word z = 0"
  unfolding zint_to_word_def[unconstrain_def]
  by simp

lemma word_to_zint[simp]: "word_to_zint x = 0"
  unfolding word_to_zint_def[unconstrain_def]
  apply simp
  apply transfer
  by simp

end
end

unconstraining
  seq_to_word and
  word_to_seq and
  eq_word_seq
begin

context fixes s :: "('a,bool) seq" begin

lemma seq_to_word[simp]: "seq_to_word s = 0"
  by (simp add: seq_to_word_def[unconstrain_def])

lemma word_to_seq[simp]: "word_to_seq x = 0"
  by simp

lemma eq_word_seq[simp]: "eq_word_seq x s"
  unfolding eq_word_seq_def[unconstrain_def]
  by simp

end
end
end

setup \<open>Sign.parent_path\<close>

instance word :: (_) semigroup_add
  apply (rule semigroup_add.intro_of_class)
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (rule semigroup_add_axioms)
  apply (rule H)
  apply standard
  by (simp add: plus_word_def[unconstrain_def])

instance word :: (_) semiring
  apply (rule semiring.intro_of_class)
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (rule semiring_axioms)
  apply (rule H)
  apply standard
  by (auto simp add: plus_word_def[unconstrain_def] times_word_def[unconstrain_def])

instance word :: (_) mult_zero
  apply (rule mult_zero.intro_of_class)
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (rule mult_zero_axioms)
  apply (rule H)
  apply standard
  by (auto simp add: times_word_def[unconstrain_def])


instance word :: (_) preorder 
  apply (rule preorder.intro_of_class)
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases]
    by (rule preorder_axioms)
  apply (rule H)
  apply standard
  by auto

unconstraining of_bl begin
lemma of_bl_empty[simp]: "of_bl [] = (0 :: 'a word)"
  apply (constrain 'a="'aa::len")
  subgoal H[unconstrain_cases] by simp
  by (rule H;simp)
end

unconstraining unsigned begin

lemma coerce_word[simp]: "LEN('a) = LEN('b) \<Longrightarrow> coerce (x :: 'a word) = (unsigned x :: 'b word)"
  supply [simp] = strip_word_def unstrip_word_def coerce_to1_def
  apply (constrain 'a="'aa::len" and 'b="'bb::len")
  subgoal H[unconstrain_cases] by (auto simp: ucast_bl[unconstrain])
  by (rule H;simp)

lemma heq_word: "((x :: 'a word) ?=? (y :: 'b word)) = (LEN('a) = LEN('b) \<and> unsigned x = y)"
  apply (constrain 'a="'aa :: len" and 'b="'bb :: len")
  subgoal H[unconstrain_cases] by (rule heq_word)
  apply (rule H)
  unfolding heq_def
  by auto

end

end