theory Fin
  imports
    Berlekamp_Zassenhaus.Finite_Field
    Word_Lib.Word_Lib_Sumo
    Alt_Type_Length
begin

class len2 = len +
  assumes nontriv: "1 < LENGTH('a)"

instance bit0 :: (len) len2
  apply intro_classes
  apply simp
  apply (subgoal_tac \<open>0 < LENGTH('a)\<close>)
  apply presburger
  by simp

instance bit1 :: (len) len2
  by intro_classes simp

class prime_len = len2 +
  assumes prime: "prime LENGTH('a)"

section \<open>Finite type generated from a type-level numeric literal.\<close>

definition fin_set :: "'a itself \<Rightarrow> int set" where
 "fin_set _ \<equiv> if LEN('a) > 0 then {(0::int) ..< LEN('a)} else {0}"

lemma fin_set_len_def[simp]: "fin_set TYPE('a::len) \<equiv> {(0::int) ..< LENGTH('a)}"
  by (simp add: fin_set_def)

typedef (overloaded) 'a fin = \<open>fin_set TYPE('a)\<close>
  morphisms fin_rep' fin_abs'
  by (force simp: fin_set_def)

abbreviation fin_abs :: "int \<Rightarrow> ('a::len) fin" where "fin_abs \<equiv> fin_abs'"
abbreviation fin_rep :: "('a::len) fin \<Rightarrow> int" where "fin_rep \<equiv> fin_rep'"

lemmas fin_lemmas[where 'a="'a::len", simplified fin_set_len_def] = 
         fin_abs'_cases fin_abs'_induct fin_abs'_inject
         fin_abs'_inverse fin_rep' fin_rep'_cases
         fin_rep'_induct fin_rep'_inject fin_rep'_inverse

lemmas fin_abs_cases = fin_lemmas(1)
lemmas fin_abs_induct = fin_lemmas(2)
lemmas fin_abs_inject = fin_lemmas(3)
lemmas fin_abs_inverse = fin_lemmas(4)
lemmas fin_rep = fin_lemmas(5)
lemmas fin_rep_cases = fin_lemmas(6)
lemmas fin_rep_induct = fin_lemmas(7)
lemmas fin_rep_inject = fin_lemmas(8)
lemmas fin_rep_inverse = fin_lemmas(9)

setup_lifting type_definition_fin

lemma CARD_fin: "CARD ('a::len fin) = LENGTH('a)"
  unfolding type_definition.card [OF type_definition_fin]
  by (simp add: fin_set_def)

lemma CARD_fin0: "CARD ('a::len0 fin) - 1 = LENGTH('a) - 1"
  unfolding type_definition.card [OF type_definition_fin]
  by (simp add: fin_set_def)

lemma fin_rep_mod_LENGTH[simp]:
  "fin_rep (x:: 'a::len fin) mod int LENGTH('a) = fin_rep x"
  using fin_rep[of x] by auto

lift_definition fmax :: \<open>'a::len fin\<close> is "int LENGTH('a) - 1"
  by simp

instantiation fin :: (_) comm_ring
begin

declare fin_set_def[simp]

lift_definition zero_fin :: "'a fin" is "0" by simp

lift_definition plus_fin :: "'a fin \<Rightarrow> 'a fin \<Rightarrow> 'a fin"
  is "(\<lambda>x y. (x+y) mod (int LEN('a)))"
  by auto

lift_definition uminus_fin :: "'a fin \<Rightarrow> 'a fin"
  is "(\<lambda>x. (uminus x) mod (int LEN('a)))"
  by auto

lift_definition minus_fin :: "'a fin \<Rightarrow> 'a fin \<Rightarrow> 'a fin"
  is "(\<lambda>x y. (x-y) mod (int LEN('a)))"
  by auto

lift_definition times_fin :: "'a fin \<Rightarrow> 'a fin \<Rightarrow> 'a fin"
  is "(\<lambda>x y. (x*y) mod (int LEN('a)))"
  by auto

instance 
proof 
  fix a b c :: \<open>'a fin\<close>
  show "a * b * c = a * (b * c)" 
    by (transfer, simp add: algebra_simps mod_mult_left_eq mod_mult_right_eq)
  show "a + b + c = a + (b + c)" 
    by (transfer, simp add: algebra_simps mod_add_left_eq mod_add_right_eq)
  show "(a + b) * c = a * c + b * c" 
    by (transfer, simp add: algebra_simps mod_add_right_eq  mod_mult_right_eq)
qed (transfer; auto simp add: algebra_simps mod_add_right_eq split: if_splits)+
end



instantiation fin :: (_) finite
begin

instance
proof
  show "finite (UNIV :: 'a fin set)"
    unfolding type_definition.univ [OF type_definition_fin]
    by auto
qed

end

instantiation fin :: (_) equal
begin

lift_definition equal_fin :: "'a fin \<Rightarrow> 'a fin \<Rightarrow> bool" is "(=)" .

instance
  apply intro_classes
  apply transfer
  by (metis eq_iff_diff_eq_0 minus_fin.rep_eq zero_fin.rep_eq)

end

definition modulo_rel :: \<open>'a::modulo \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  "modulo_rel n x y \<longleftrightarrow> x mod n = y mod n"

lemma modulo_rel_triv[simp]:
  "modulo_rel (n::int) x y \<longleftrightarrow> x = y"
  if "0 \<le> x" "x < n" "0 \<le> y" "y < n"
  using that by (simp add: modulo_rel_def)

lemma modulo_rel_intro[intro]:
  "modulo_rel n x y" if "x mod n = y mod n"
  using that by (metis modulo_rel_def)

lemma fin_eq_intro:
  "(x::'a::len fin) = y" if "modulo_rel LENGTH('a) (fin_rep x) (fin_rep y)"
  using that by (auto simp add: modulo_rel_def fin_rep_inject)

lemma fin_eq_transfer[transfer_rule]:
  "(pcr_fin ===> pcr_fin ===> (=))
   (modulo_rel (int LENGTH('a::len))) ((=) :: 'a fin \<Rightarrow> 'a fin \<Rightarrow> bool)"
  apply (intro rel_funI)
  by (simp add: fin.pcr_cr_eq cr_fin_def modulo_rel_def fin_rep_inject)

instantiation fin :: (len2) nontriv
begin
instance using nontriv by intro_classes (simp add: CARD_fin)
end

instantiation fin :: (len2) comm_ring_1
begin

lift_definition one_fin :: "'a fin" is 1
  using nontriv by auto

instance by intro_classes (transfer, simp)+

end

instantiation fin :: (prime_len) prime_card
begin
instance using prime by intro_classes (simp add: CARD_fin)
end

text \<open>This is the equivalent of \<open>Z a\<close> in Cryptol.\<close>
type_synonym 'a Z = \<open>'a fin mod_ring\<close>

term "(x :: 'a Z) + x = y"

instance mod_ring :: (_) "{zero,one,plus,times,power}"
  by standard

instance mod_ring :: (finite) "numeral"
  by standard

(* relaxed instances allow us to write these without additional constraints on 'a *)
term "1 :: 'a Z"
term "2 :: 'a Z"
term "(x :: 'a Z) + y"
term "(x :: 'a Z) * y"
term "(x :: 'a Z) ^ y"

end
