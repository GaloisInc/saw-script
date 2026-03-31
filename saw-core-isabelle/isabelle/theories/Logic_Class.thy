theory Logic_Class
imports Main
begin

class logic =
  fixes nand :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "NAND" 70) begin

context begin
qualified definition "and" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "and x y \<equiv> (x NAND y) NAND (x NAND y)"

qualified definition or :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "or x y \<equiv> (x NAND x) NAND (y NAND y)"

qualified definition not :: "'a \<Rightarrow> 'a" where
  "not x \<equiv> x NAND x"

qualified definition xor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "xor x y \<equiv> and (or x y) (not (and x y))"

qualified definition implies :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "implies x y \<equiv> not (and x (not y))"

qualified definition iff :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "iff x y \<equiv> and (implies x y) (implies y x)"

end

end

bundle logic_syntax begin

context includes bit_operations_syntax begin

no_notation ring_bit_operations_class.not (\<open>NOT\<close>)
no_notation semiring_bit_operations_class.xor (infixr \<open>XOR\<close> 59)
no_notation semiring_bit_operations_class.and (infixr \<open>AND\<close> 64)
no_notation semiring_bit_operations_class.or (infixr \<open>OR\<close> 59)
end


notation logic_class.not (\<open>NOT\<close>)
notation logic_class.xor (infixr \<open>XOR\<close> 59)
notation logic_class.and (infixr \<open>AND\<close> 64)
notation logic_class.or (infixr \<open>OR\<close> 58)
notation logic_class.implies (infixr \<open>IMP\<close> 55)
notation logic_class.iff (infixr \<open>IFF\<close> 55)

end



instantiation bool :: logic begin
definition "nand_bool x y \<equiv> \<not> (x \<and> y)"
instance ..
end

context includes logic_syntax begin

lemma and_bool[simp]: "(AND) = (\<and>)"
  by (simp add: logic_class.and_def[abs_def] nand_bool_def)

lemma or_bool[simp]: "(OR) = (\<or>)"
  by (simp add: logic_class.or_def[abs_def] nand_bool_def)

lemma not_bool[simp]: "(NOT) = (\<lambda>x. \<not> x)"
  by (simp add: logic_class.not_def[abs_def] nand_bool_def)

lemma xor_bool[simp]: "(XOR) = (\<noteq>)"
  by (fastforce simp add: logic_class.xor_def[abs_def] nand_bool_def)

lemma implies_bool[simp]: "(IMP) = (\<longrightarrow>)"
  by (simp add: logic_class.implies_def[abs_def] nand_bool_def)

lemma iff_bool[simp]: "(IFF) = (\<longleftrightarrow>)"
  by (auto simp add: logic_class.iff_def[abs_def] nand_bool_def)

end






end