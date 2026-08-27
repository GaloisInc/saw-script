theory Integral
imports Main Fin Unconstrain
begin

class from_to_int = zero + one + linorder +
  fixes to_int :: "'a \<Rightarrow> int"
    and from_int :: "int \<Rightarrow> 'a"
  assumes to_int_zero[simp]: "to_int 0 = 0"
      and from_int_one[simp]: "from_int 1 = 1"
      and from_to_int[simp]: "\<And>x. to_int (from_int (to_int x)) = to_int x"
      and to_from_int[simp]: "\<And>x. from_int (to_int x) = x"
      and to_int_lt[simp]: "\<And>x y. (to_int x < to_int y) = (x < y)"
      and to_from_int_bounds: "\<And>(x::int) (y::int). 
            to_int (from_int x) = x \<Longrightarrow> 0 \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> to_int (from_int y) = y"


class from_to_int_1 = from_to_int +
  assumes to_int_1[simp]: "(0 :: 'a) \<noteq> 1 \<Longrightarrow> to_int 1 = 1"


class integral = from_to_int_1 + linorder + ring + divide + modulo + power + abs +
  fixes to_sint :: "'a \<Rightarrow> int"
  assumes abs_positive[simp]: "\<And>x. abs x \<ge> 0"
      and abs_zero[simp]: "\<And>x. (abs x > 0) = (x \<noteq> 0)"
      and to_int_trivial: "\<And>x. 0 = 1 \<Longrightarrow> to_int x = 0"
      and to_int_minus_distrib[simp]: "\<And>x y. x \<ge> y \<Longrightarrow> to_int (x - y) = to_int x - to_int y"

lemma integral_as_int: "(\<And>x. P (from_int x)) \<Longrightarrow>  P (n :: 'a :: integral)"
  by (metis to_from_int)

lemma from_int_zero[simp]: "from_int 0 = 0"
  by (metis to_from_int
      to_int_zero)

lemma to_int_le[simp]: "(to_int m \<le> to_int x) = (m \<le> x)"
  by (metis linorder_not_less to_int_lt )

lemma to_int_neg[simp]: "(to_int m \<le> 0) = (m \<le> 0)"
  by (simp add: to_int_le[where x=0,simplified]) 

lemma to_int_pos[simp]: "(0 \<le> to_int x) = (0 \<le> x)"
  by (simp add: to_int_le[where m=0,simplified])

lemma to_int_neg_strict[simp]: "(to_int m < 0) = (m < 0)"
  by (simp add: to_int_lt[where y=0,simplified])

lemma to_int_pos_strict[simp]: "(0 < to_int m) = (0 < m)"
  by (simp add: to_int_lt[where x=0,simplified])

lemma to_int_not_zero[simp]: "to_int i \<noteq> 0 = (i \<noteq> 0)"
  by (metis to_from_int to_int_zero)


instantiation nat :: from_to_int_1 begin
definition "to_int_nat == int :: nat \<Rightarrow> int"
definition "from_int_nat == nat :: int \<Rightarrow> nat"
instance
  apply standard
    apply (simp add: to_int_nat_def from_int_nat_def)+
  done
end

(* zero for negative values *)
definition to_nat :: "'a :: from_to_int \<Rightarrow> nat" where
  "to_nat x \<equiv> nat (to_int x)"

(* undefined for negative values *)
definition pos_nat :: "'a :: from_to_int \<Rightarrow> nat" where
  "pos_nat x \<equiv> if to_int x \<ge> 0 then to_nat x else undefined"

(* absolute value *)
definition abs_nat :: "'a :: from_to_int \<Rightarrow> nat" where
  "abs_nat x \<equiv> nat (abs (to_int x))"

 
definition from_nat :: "nat \<Rightarrow> 'a :: from_to_int" where
  "from_nat x \<equiv> from_int (int x)"

 
lemma to_nat_0[simp]: "to_nat 0 = 0"
  by (simp add: to_nat_def)

lemma to_nat_1[simp]: "(0 :: 'a) \<noteq> 1 \<Longrightarrow> to_nat (1 :: 'a :: from_to_int_1) = 1"
  by (simp add: to_nat_def)

lemma from_nat_0[simp]: "from_nat 0 = 0"
  by (simp add: from_nat_def)

lemma from_nat_1[simp]: "from_nat 1 = (1 :: 'a :: from_to_int_1)"
  by (simp add: from_nat_def)


lemma integral_as_nat[consumes 1]: "0 \<le> n \<Longrightarrow> (\<And>x. P (from_nat x)) \<Longrightarrow>  P (n :: 'a :: integral)"
  by (metis from_nat_def int_nat_eq to_from_int
      to_int_pos)

instantiation int :: integral begin
definition "to_int_int == id :: int \<Rightarrow> int"
definition "to_sint_int == id :: int \<Rightarrow> int"
definition "from_int_int == id :: int \<Rightarrow> int"
instance
  apply standard
    apply (simp add: to_int_int_def from_int_int_def)+
  done
end

lemmas [simp] = to_int_int_def from_int_int_def to_sint_int_def

lemma to_nat_int[simp]: "to_nat = nat"
  by (simp add: to_nat_def[abs_def])

lemma from_nat_int[simp]: "from_nat = int"
  by (simp add: from_nat_def[abs_def])

lemma pos_nat_simps[simp]: 
  "x \<ge> 0 \<Longrightarrow> pos_nat x = to_nat x"
  "pos_nat (int y) = y"  
  by (auto simp add: pos_nat_def)

lemma pos_x_to_from_nat[simp]: "x \<ge> 0 \<Longrightarrow> to_int (from_nat (to_nat (x::'a :: from_to_int)) :: 'a) = to_int x"
  by (simp add: from_nat_def to_nat_def)

lemma abs_nat_simps[simp]:
  "i \<ge> 0 \<Longrightarrow> abs_nat i = to_nat i"
  "i \<le> 0 \<Longrightarrow> abs_nat i = to_nat (- (to_int i))"
  by (simp add: abs_nat_def to_nat_def)+

(* NOTE: Isabelle's built-in coercions (unrelated to Coercible) implicitly
   coerce nats into ints wherever possible.
   As a result this is type-correct (note the insertion of "int"), despite no integral instance for nat *)
term "to_int (0 :: nat)"


lemma minus_one_to_nat: "(i :: 'a :: integral) > 0 \<Longrightarrow> (to_nat (i - 1)) = (to_nat i) - 1"
  apply (simp add: to_nat_def)
  apply (subst to_int_minus_distrib)
  apply (metis add_0 nless_le to_int_1 to_int_le to_int_pos_strict
      zless_imp_add1_zle)
  apply (cases "(0 :: 'a) = 1")
   apply (simp add: to_int_trivial)
  by simp

instantiation mod_ring :: (finite) linorder begin
definition "less_eq_mod_ring (x :: 'a mod_ring) (y :: 'a mod_ring) \<equiv> (to_int_mod_ring x) \<le> (to_int_mod_ring y)"
definition "less_mod_ring (x :: 'a mod_ring) (y :: 'a mod_ring) \<equiv> (to_int_mod_ring x) < (to_int_mod_ring y)"
instance
  apply standard
  apply (simp_all add: less_eq_mod_ring_def less_mod_ring_def)
  by linarith+
end


lemma of_int_mod_ring_one_nontriv: "of_int_mod_ring 1 = (1 :: 'a :: nontriv mod_ring)"
  by (metis of_int_hom.hom_one
      of_int_of_int_mod_ring)

lemma card1_singleton[rule_format]: "card s = 1 \<Longrightarrow> \<forall>x y. x \<in> s \<longrightarrow> y \<in> s \<longrightarrow> x = y"
  by (metis One_nat_def card_eq_SucD singletonD)

lemma CARD_1_singleton: "CARD('a) = 1 \<Longrightarrow> (x :: 'a) = y"
  by (rule card1_singleton[where s=UNIV];simp)

lemma not_nontriv_finite_1[simp]: "(\<not> class.nontriv TYPE('a::finite)) = (CARD('a) = 1)"
  apply (simp add: class.nontriv_def)
  using le_less_Suc_eq not_less_eq by auto

lemma of_int_mod_ring_one[simp]: "of_int_mod_ring 1 = (1 :: 'a :: finite mod_ring)"
  apply (rule of_int_mod_ring_one_nontriv[unconstrain_cases])
  apply (rule CARD_1_singleton)
  by simp

lemma to_int_mod_ring_bound:
  "to_int_mod_ring ((of_int_mod_ring x) :: 'a :: finite mod_ring) = x \<Longrightarrow>
           0 \<le> y \<Longrightarrow>
           y \<le> x \<Longrightarrow>
           to_int_mod_ring ((of_int_mod_ring y) :: 'a :: finite mod_ring) = y"
  apply transfer
  by (metis linorder_not_le mod_pos_pos_trivial
      of_nat_0_less_iff order_trans pos_mod_bound
      zero_less_card_finite)

instantiation mod_ring :: (finite) from_to_int begin
definition to_int_mod_ring :: "'a mod_ring \<Rightarrow> int" where
  "to_int_mod_ring \<equiv> Finite_Field.to_int_mod_ring"
definition from_int_mod_ring :: "int \<Rightarrow> 'a mod_ring" where
  "from_int_mod_ring \<equiv> of_int_mod_ring"
instance
  apply standard
  apply (auto simp add: of_int_mod_ring_one to_int_mod_ring_def from_int_mod_ring_def 
                        less_eq_mod_ring_def less_mod_ring_def to_int_mod_ring_bound)
  done
end

lemma nontriv_ofclass: "CARD('a) > 1 \<Longrightarrow> OFCLASS('a, nontriv_class)"
  apply standard
  by simp

instantiation mod_ring :: (finite) from_to_int_1 begin
instance
  apply (rule from_to_int_1.intro_of_class)
  apply (constrain 'a="'b::nontriv")
  subgoal H[unconstrain_cases]
    apply standard
    by (simp add: to_int_mod_ring_def)
  apply (rule H)
  apply standard
  by (simp add: CARD_1_singleton)
end

lemma to_int_mod_ring_1[simp]:
  "(0 :: 'a mod_ring) \<noteq> 1 \<Longrightarrow> to_int_mod_ring (1 :: ('a::finite) mod_ring) = 1"
  apply (subst to_int_mod_ring_def[symmetric])
  by (erule to_int_1)

instantiation bool :: zero_neq_one begin
definition "zero_bool \<equiv> False"
definition "one_bool \<equiv> True"
instance  
  apply (standard)
  by (simp add: zero_bool_def one_bool_def)+
end


instantiation bool :: from_to_int_1 begin
definition "to_int_bool \<equiv> \<lambda>b. if b then (1::int) else 0"
definition "from_int_bool \<equiv> (\<lambda>i. i \<noteq> (0::int))"
instance
  apply standard
  by (auto simp add: to_int_bool_def from_int_bool_def zero_bool_def one_bool_def)
end

instantiation mod_ring :: (_) abs begin
definition "abs_mod_ring \<equiv> (\<lambda>(x :: 'a mod_ring). x)"
instance ..
end

instance mod_ring :: (prime_card) integral
  apply standard
  unfolding abs_mod_ring_def less_eq_mod_ring_def less_mod_ring_def to_int_mod_ring_def
  by (transfer;auto)+

end