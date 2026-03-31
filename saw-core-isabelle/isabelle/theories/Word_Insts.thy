theory Word_Insts
  imports "HOL-Library.Word" Coercible_Insts Integral SignedCmp Logic_Class
begin

term "x !! y"
instantiation word :: (len0) len0 begin
definition "len_of_word == (\<lambda>_. LENGTH('a)) :: 'a word itself \<Rightarrow> nat"
instance ..
end

instantiation word :: (len) signedCmp begin
definition signed_lt_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  where
  "signed_lt_word w1 w2 \<equiv> sint w1 < sint w2"

definition signed_le_word :: "'a word \<Rightarrow> 'a word \<Rightarrow> bool"
  where
  "signed_le_word w1 w2 \<equiv> sint w1 \<le> sint w2"
instance ..
end

lemma word_abs_zero: "x \<noteq> 0 \<Longrightarrow> 0 < uint \<bar>x\<bar>"
  by (metis linorder_neqE_linordered_idom
      neg_equal_0_iff_equal uint_0_iff uint_lt_0
      word_abs_msb)


lemma word_of_int_bound: "uint ((word_of_int x) :: 'a :: len word) = x \<Longrightarrow>
           0 \<le> y \<Longrightarrow>
           y \<le> x \<Longrightarrow> uint ((word_of_int y) :: 'a :: len word) = y"
  by (simp add: take_bit_int_eq_self_iff
      uint_word_of_int_eq)
  

instantiation word :: (len) integral begin
definition "to_int_word \<equiv> uint :: 'a word \<Rightarrow> int"
definition "from_int_word \<equiv> of_int :: int \<Rightarrow> 'a word"

instance
  apply standard
  by (auto simp add: uint_minus_simple_alt word_less_def to_int_word_def 
                     from_int_word_def word_abs_zero word_of_int_bound)
end

lemmas [simp] = to_int_word_def from_int_word_def

instantiation word :: (len) logic begin
definition "nand_word (x :: 'a word) y \<equiv> NOT (x AND y)"
instance ..
end

lemma and_logic_word[simp]: "logic_class.and = ((AND) :: 'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word)"
  by (simp add: logic_class.and_def[abs_def] nand_word_def[abs_def])

lemma or_logic_word[simp]: "logic_class.or = ((OR) :: 'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word)"
  by (simp add: logic_class.or_def[abs_def] nand_word_def[abs_def])

lemma not_logic_word[simp]: "logic_class.not = (\<lambda>x. ~~ x)"
  by (simp add: logic_class.not_def[abs_def] nand_word_def[abs_def])

lemma xor_logic_word[simp]: "logic_class.xor = ((XOR) :: 'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word)"
  by (simp add: logic_class.xor_def[abs_def] nand_word_def[abs_def] bit.xor_def2[abs_def])


section \<open>Coercible instance\<close>

text 
\<open>We define the stripped representation of words based on the boolean list representation, and
define the stripped type to match seq. This allows for coercions between bool-valued seqs and words
(of nonzero length).\<close>

instantiation word :: (_) strip_type begin
definition "strip_type_word == (\<lambda>_. T [Tn (LEN('a)), strip_type TYPE(bool)] STR ''seq'') :: ('a) word itself \<Rightarrow> stripped_type"
instance ..
end

lemma word_type_name[simp]: "type_name TYPE(('n) word) = STR ''seq''"
  by (simp add: strip_type_word_def type_name_def)

instantiation word :: (_) strip begin
unconstraining to_bl begin
definition "strip_word (x :: 'a word) \<equiv> strip (if LEN('a) > 0 then to_bl x else [])"
end

instance ..
end

instantiation word :: (_) unstrip begin
unconstraining of_bl begin
definition "unstrip_word x \<equiv> of_bl (unstrip x)"
end
instance ..
end

instantiation word :: (len) coercible_atom begin
instance
  supply [simp] = strip_word_def unstrip_word_def
  by (standard;simp?)
end

lemma word_same_type[simp]: 
  "same_type (TYPE('a word)) (TYPE('b word)) = (LEN('a) = LEN('b))"
  by (simp add: same_type_def strip_type_word_def)

interpretation word: coercion "\<lambda>(x :: 'a :: len word). ucast x"
  apply standard
  by (simp add: strip_word_def unstrip_word_def ucast_bl)

lemma heq_word: "((x :: 'a :: len word) ?=? (y :: 'b :: len word)) = (LEN('a) = LEN('b) \<and> ucast x = y)"
  unfolding heq_def
  apply (constrain 'a="'aa :: len" and 'b="'bb :: len")
  subgoal H[unconstrain_cases]
    by (auto simp add: is_up.rep_eq uint_up_ucast)
  by (rule H) auto

end