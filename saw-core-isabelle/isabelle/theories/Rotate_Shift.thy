theory Rotate_Shift
imports Main Word_Insts Alt_Type_Length
begin

class rotate_ops =
  fixes left_rotate_nat :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
    and right_rotate_nat :: "'a \<Rightarrow> nat \<Rightarrow> 'a"

class shift_ops =
  fixes left_shift_nat :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
    and right_shift_nat :: "'a \<Rightarrow> nat \<Rightarrow> 'a"

definition right_rotate :: "'a :: rotate_ops \<Rightarrow> int \<Rightarrow> 'a" where
  "right_rotate x i \<equiv> if i \<le> 0 then left_rotate_nat x (nat(-i)) else right_rotate_nat x (nat i)"

definition left_rotate :: "'a :: rotate_ops \<Rightarrow> int \<Rightarrow> 'a" where
  "left_rotate x i \<equiv> right_rotate x (-i)"

definition right_shift :: "'a :: shift_ops \<Rightarrow> int \<Rightarrow> 'a" where
  "right_shift x i \<equiv> if i \<le> 0 then left_shift_nat x (nat(-i)) else right_shift_nat x (nat i)"

definition left_shift :: "'a :: shift_ops \<Rightarrow> int \<Rightarrow> 'a" where
  "left_shift x i \<equiv> right_shift x (-i)"

context notes if_cong[cong] begin
lemmas left_rotate_def2 = left_rotate_def[simplified right_rotate_def,simplified]
lemmas left_shift_def2 = left_shift_def[simplified right_shift_def,simplified]
end

class rotate = rotate_ops +
  assumes  left_rotate_nat_0[simp]: "left_rotate_nat x 0 = x"
      and  right_rotate_nat_0[simp]: "right_rotate_nat x 0 = x"
      and  right_rotate_add: "right_rotate (right_rotate x n) m = right_rotate x (m + n)"
      and  right_rotate_mod: "right_rotate x (n mod size x) = right_rotate x n"

class shift = shift_ops +
 assumes  left_shift_nat_0[simp]: "left_shift_nat x 0 = x"
     and  right_shift_nat_0[simp]: "right_shift_nat x 0 = x"
     and  right_shift_add[simp]: "(0 \<le> n = (0 \<le> m)) \<Longrightarrow> right_shift (right_shift x n) m = right_shift x (m + n)"

class zero_size = size +
  assumes zero_size: "\<And>x y. size x = 0 \<Longrightarrow> size y = 0 \<Longrightarrow> x = y"

class shift_size = shift + zero_size +
  assumes right_shift_size[simp]: "size (right_shift (x :: 'a :: {shift_ops,size}) i) = size x"

class rotate_size = rotate + zero_size +
  assumes right_rotate_size[simp]: "size (right_rotate x i) = size x"

class rotate_shift = rotate + shift

class rotate_shift_size = shift_size + rotate_size

lemma right_rotate_0[simp]: "right_rotate (x :: 'a :: rotate) 0 = x"
  by (simp add: right_rotate_def)

lemma right_shift_0[simp]: "right_shift (x :: 'a :: shift) 0 = x"
  by (simp add: right_shift_def)

lemma rotate_mod0: "(nat (abs n)) mod size x = 0 \<Longrightarrow> right_rotate (x :: 'a :: rotate) n = x"
  apply (induct rule: int_of_nat_induct)
  apply simp
  subgoal by (metis int_ops(1) of_nat_mod
      right_rotate_0 right_rotate_mod)
  apply simp
  by (metis Suc_as_int add.commute
      add.right_inverse int_ops(1)
      minus_add_distrib of_nat_Suc of_nat_mod
      right_rotate_0 right_rotate_add
      right_rotate_mod
      uminus_add_conv_diff)
  

instantiation word :: (len) rotate_ops begin
definition "left_rotate_nat_word w n \<equiv> word_rotl n w"
definition "right_rotate_nat_word w n \<equiv> word_rotr n w"
instance ..
end

instantiation word :: (len) shift_ops begin
definition "left_shift_nat_word (w :: 'a word) n \<equiv> shiftl w n"
definition "right_shift_nat_word (w :: 'a word) n \<equiv> shiftr w n"
instance ..  
end

lemmas [simp] = left_rotate_nat_word_def right_rotate_nat_word_def
                left_shift_nat_word_def right_shift_nat_word_def

lemma right_rotate_word_def2: "right_rotate w i = word_roti i w"
  by (simp add: right_rotate_def)

lemma left_rotate_word_def2: "left_rotate w i = word_roti (-i) w"
  by (simp add: left_rotate_def2)

instantiation word :: (len) rotate_shift_size begin
instance
  supply [simp] = word_size
  apply standard
        apply simp+
       apply (simp only: right_rotate_word_def2)
     apply (simp only: right_rotate_word_def2 word_roti_add)
    apply (simp only: right_rotate_word_def2 )
      apply (metis word_roti_conv_mod')
     apply simp+
   apply (simp add: right_shift_def)
  apply (clarsimp simp: shiftl_shiftl nat_add_distrib )
  apply (intro impI conjI;clarsimp simp: shiftr_shiftr add.commute)
  apply (metis nat_add_distrib neg_0_le_iff_le
         uminus_add_conv_diff)
  by simp

end

bundle rotate_shift_syntax begin

no_notation sshiftr (infixl \<open>>>>\<close> 55)
no_notation shiftl (infixl \<open><<\<close> 55)
no_notation shiftr (infixl \<open>>>\<close> 55)

notation left_rotate (infixl \<open><<<\<close> 55)
notation right_rotate (infixl \<open>>>>\<close> 55)
notation left_shift (infixl \<open><<\<close> 55)
notation right_shift (infixl \<open>>>\<close> 55)

end


context includes rotate_shift_syntax begin


lemma left_shift0[simp]: "x << 0 = (x :: 'a :: shift)"
  by (simp add: left_shift_def)

lemma left_rotate0[simp]: "x <<< 0 = (x :: 'a :: rotate)"
  by (simp add: left_rotate_def)

lemma right_rotate_add[simp]: "(x :: 'a :: rotate) >>> n >>> m = x >>> (n + m)"
  apply (simp add: right_rotate_add)
  by (simp add: add.commute)

lemma left_rotate_add[simp]: "(x :: 'a :: rotate) <<< n <<< m = x <<< (n + m)"
  by (simp add: left_rotate_def)

lemmas left_rotate_neg = left_rotate_def

lemma right_rotate_neg: "x >>> n = x <<< (-n)"
  by (simp add: left_rotate_def)

lemmas left_shift_neg = left_shift_def

lemma right_shift_neg: "x >> n = x << (- n)"
  by (simp add: left_shift_def right_shift_def)

lemma left_shift_add[simp]: 
  "(n \<le> 0) = (m \<le> 0) \<Longrightarrow>
    x << n << m = (x :: 'a :: shift) << (n + m)"
  by (simp add: left_shift_def add.commute)

lemma left_rotate_noop[simp]: 
  "size x = 0 \<Longrightarrow> (x <<< i) = (x :: 'a :: rotate_size)"
  by (simp add: left_rotate_def zero_size)

lemma right_rotate_noop[simp]: 
  "size x = 0 \<Longrightarrow> (x >>> i) = (x :: 'a :: rotate_size)"
  by (simp add: zero_size)

lemma left_shift_noop[simp]: 
  "size x = 0 \<Longrightarrow> (x << i) = (x :: 'a :: shift_size)"
  by (simp add: left_shift_def zero_size)

lemma right_shift_noop[simp]: 
  "size x = 0 \<Longrightarrow> (x >> i) = (x :: 'a :: shift_size)"
  by (simp add: zero_size)

lemma left_rotate_size[simp]: 
  "size (x <<< i) = size (x :: 'a :: rotate_size)"
  by (simp add: left_rotate_def)

lemma left_shift_size[simp]: 
  "size (x << i) = size (x :: 'a :: shift_size)"
  by (simp add: left_shift_def)

context begin

private lemma test: 
  "((x :: 'a :: {shift,rotate}) << (2::int) << (3::int)) = (x << (5::int))"
  "(x <<< (2::int) <<< (3::int)) = (x <<< (5::int))"
  "(x >> (2::int) >> (3::int)) = (x >> (5::int))"
  "(x >>> (2::int) >>> (3::int)) = (x >>> (5::int))"
  "((y :: 'b :: shift) >> (to_int (2:: 32 word)) >> (to_int (3:: 32 word))) = (y >> (to_int (5::32 word)))"
  by simp+

end

definition shiftl_list :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "shiftl_list pad l n \<equiv> (drop n l) @ ((replicate (min n (length l)) pad))"

definition shiftr_list :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "shiftr_list pad l n \<equiv> ((replicate (min n (length l)) pad)) @ (take (length l - n) l)"

lemma shiftr_list_def2: "shiftr_list pad l n = rev (shiftl_list pad (rev l) n)"
  apply (simp add: shiftr_list_def shiftl_list_def)
  by (simp add: drop_rev)

lemma shiftr_length[simp]: "length (shiftr_list pad l n) = length l"
  by (simp add: shiftr_list_def)

lemma shiftl_length[simp]: "length (shiftl_list pad l n) = length l"
  by (simp add: shiftl_list_def)

lemma shiftl_list0[simp]: "shiftl_list pad l 0 = l"
  by (simp add: shiftl_list_def)

lemma shiftr_list0[simp]: "shiftr_list pad l 0 = l"
  by (simp add: shiftr_list_def)

lemma shiftr_list_nil[simp]: "shiftr_list pad [] n = []"
  by (simp add: shiftr_list_def)

lemma shiftl_list_nil[simp]: "shiftl_list pad [] n = []"
  by (simp add: shiftl_list_def)

lemma shiftl_list_cons[simp]: "shiftl_list pad (x#xs) (Suc n) = shiftl_list pad xs n @ [pad]"
  apply (simp add: shiftl_list_def)
  by (simp add: replicate_append_same)



lemma shiftl_list_step: "shiftl_list pad xs m = (if m = 0 then xs else (if length xs = 0 then [] else shiftl_list pad (tl xs) (m - 1) @ [pad]))"
  by (metis add_diff_inverse_nat length_0_conv
      less_one list.collapse plus_1_eq_Suc shiftl_length
      shiftl_list0 shiftl_list_cons)

lemma shiftl_list_tl[symmetric]:"shiftl_list pad x m = tl (shiftl_list pad (a # x) m)"
  apply (induct m arbitrary: x a)
   apply simp
  subgoal premises prems for m x a
    apply simp
    apply (cases x)
     apply simp
    apply simp
    subgoal for a list
      apply (subst prems[where a=a])
      by (metis length_0_conv list.distinct(1)
          shiftl_length tl_append2)
    done
  done


lemma shiftl_list_Suc_append: "shiftl_list pad xs (Suc n) = shiftl_list pad (tl xs) n @ (if length xs = 0 then [] else [pad])"
  by (cases xs;simp)

lemma shiftl_list_Suc: "shiftl_list pad x (Suc m) = shiftl_list pad (shiftl_list pad x m) 1"
  apply (induct x arbitrary: m)
   apply simp
  by (simp add: shiftl_list_Suc_append shiftl_list_tl)  

lemma shiftl_list_add: "shiftl_list pad (shiftl_list pad x n) m = shiftl_list pad x (m + n)"
  apply (induct m)
   apply simp
  apply simp
  apply (subst shiftl_list_Suc)+
  by simp

lemma shiftr_list_add: "shiftr_list pad (shiftr_list pad x n) m = shiftr_list pad x (m + n)"
  by (simp add: shiftr_list_def2 shiftl_list_add)

end

instantiation list :: (_) rotate_ops begin
definition "left_rotate_nat_list (w :: 'a list) n \<equiv> rotate n w"
definition "right_rotate_nat_list (w :: 'a list) n \<equiv> rotater n w"
instance ..
end


instantiation list :: (zero) shift_ops begin
definition "left_shift_nat_list (w :: 'a list) n \<equiv> shiftl_list 0 w n"
definition "right_shift_nat_list (w :: 'a list) n \<equiv> shiftr_list 0 w n"
instance ..
end

lemmas [simp] = left_rotate_nat_list_def right_rotate_nat_list_def
                left_shift_nat_list_def right_shift_nat_list_def


lemma rotate_helper: "m \<le> 0 \<Longrightarrow>
    \<not> m + n \<le> 0 \<Longrightarrow>
    rotate (nat (- m))
     (rotater (nat n) x) =
    rotater (nat (m + n)) x"
  apply (simp add: rotater_rev)
  by (metis equation_minus_iff
      le_iff_diff_le_0 nat_diff_distrib
      nat_mono neg_0_le_iff_le nle_le
      rotate_inv_rel rotater_rev
      uminus_add_conv_diff)

lemma rotate_list_defs:
  "i \<ge> 0 \<Longrightarrow> right_rotate (l :: 'a list) i = rotater (nat i) l"
  "i \<le> 0 \<Longrightarrow> right_rotate (l :: 'a list) i = rotate (nat (-i)) l"
  "i \<ge> 0 \<Longrightarrow> left_rotate (l :: 'a list) i = rotate (nat i) l"
  "i \<le> 0 \<Longrightarrow> left_rotate (l :: 'a list) i = rotater (nat (-i)) l"
  by (auto simp add: right_rotate_def left_rotate_def)

lemma shift_list_defs:
  "i \<ge> 0 \<Longrightarrow> right_shift (l :: 'a :: zero list) i = shiftr_list 0 l (nat i)"
  "i \<le> 0 \<Longrightarrow> right_shift (l :: 'a list) i = shiftl_list 0 l (nat (-i)) "
  "i \<ge> 0 \<Longrightarrow> left_shift (l :: 'a :: zero list) i = shiftl_list 0 l (nat i)"
  "i \<le> 0 \<Longrightarrow> left_shift (l :: 'a list) i = shiftr_list 0 l (nat (-i)) "
  by (auto simp add: right_shift_def left_shift_def)

lemma nat_mod_helper: 
  "i < m \<Longrightarrow> (i + (m - nat (- int n mod int m) mod m)) mod m = (n + i) mod m"
  apply (induct i)
  subgoal
    apply (rule nat_int.Rep_eqD)
    apply (simp add: zmod_int)
    by (simp add: mod_minus_eq)
  by (metis Suc_lessD add_Suc add_Suc_right
      mod_Suc_eq)

lemma rotate_as_rotater: "rotate n x = rotater (nat (- int n mod int (length x))) x"
  apply (rule nth_equalityI)
   apply simp
  by (simp add: nth_rotater nth_rotate nat_mod_helper)

instantiation list :: (_) rotate_size begin
instance
  apply (standard;simp?)
  apply (simp add: right_rotate_def)
  subgoal for x n m
    apply (cases "m \<ge> 0"; cases "n \<ge> 0"; cases "m + n \<ge> 0"; simp add: rotate_list_defs)
         apply (metis add.commute nat_add_distrib rotater_add)
        apply (simp add: diff_nat_eq_if rotate_inv_rel)
       apply (metis
        ab_group_add_class.ab_diff_conv_add_uminus
        ab_left_minus
        add_mono_thms_linordered_semiring(3)
        linorder_le_cases nat_diff_distrib
        nat_mono rotate_inv_rel
        uminus_add_conv_diff)
      apply (simp add: rotate_inv_plus)
      apply (metis add.right_neutral minus_add_cancel rotate_rl)
     apply (simp add: rotate_inv_plus)
    by (metis diff_conv_add_uminus linorder_not_le
        nat_int.Rep_inverse nat_int_add neg_int_cases
        rotate_rotate verit_minus_simplify(4))
  subgoal for x n
    apply (cases "n \<ge> 0"; cases "(n mod int (length x)) \<ge> 0"; simp add: rotate_list_defs)
       apply (simp add: nat_mod_distrib rotater_eqs(4))
    using mod_int_pos_iff apply force
    subgoal by (simp add: rotate_as_rotater)
    by (simp add: rotate_as_rotater)
  by (simp add: right_rotate_def)
end


instantiation list :: (zero) rotate_shift_size begin
instance
  apply (standard;simp?)
   apply (simp add: right_shift_def)
  subgoal for n m x
    apply (cases "(0 \<le> n)"; cases "0 \<le> m"; simp add: shift_list_defs shiftr_list_add shiftl_list_add )
     apply (metis int_nat_eq nat_int_add)
    by (metis abs_ge_zero abs_of_neg
        diff_conv_add_uminus linorder_not_le
        nat_add_distrib)
  by (simp add: right_shift_def)
end

context includes rotate_shift_syntax begin

lemma nth_as_shift_nat: 
  assumes n_valid: "n < length l"
  shows "l ! n = hd (l << n)"
  apply (subgoal_tac "l \<noteq> []")
  apply (insert n_valid)
   apply (induct l arbitrary: n rule: list_nonempty_induct)
    apply simp
   apply (simp add: shift_list_defs)
   apply (subst shiftl_list_step)
   apply clarsimp
   apply (metis hd_append2 length_0_conv shiftl_length)
  by force   


lemma left_shift_list_nth_int: "i \<ge> 0 \<Longrightarrow> nat (int n + i) < length l \<Longrightarrow> (l << i) ! n = l ! (nat (int n + i))"
  apply (simp add: shift_list_defs nth_as_shift_nat)
    apply (induct i arbitrary: l n)
   apply (simp add: shiftl_list_def from_nat_def to_nat_def nat_add_distrib)
  by linarith

lemma left_shift_list_nth_pos[simp]:
  "i \<ge> 0 \<Longrightarrow> n + (nat i) < length l \<Longrightarrow> (l << i) ! n = l ! (n + (nat i))"
  apply (subst left_shift_list_nth_int)
  by (simp add: nat_plus_as_int)+

lemma left_shift_list_nth_zero[simp]: "i \<ge> 0 \<Longrightarrow> n < length l \<Longrightarrow> n \<ge> (length l - nat i) \<Longrightarrow> (l << i) ! n = 0"
  by (simp add: shift_list_defs nth_as_shift_nat shiftl_list_def)

lemma shiftl_list_nth: "n < length l \<Longrightarrow> (shiftl_list 0 l i) ! n = (if (n + i) < length l then l ! (n + i) else 0)"
  apply (insert left_shift_list_nth_pos[where n=n and i="nat i" and l=l])
  apply (insert left_shift_list_nth_zero[where n=n and i="nat i" and l=l])
  by (auto simp: shift_list_defs)

lemma right_shift_list_nth_int: "i \<ge> 0 \<Longrightarrow> n < length l \<Longrightarrow> int n \<ge> i  \<Longrightarrow> (l >> i) ! n = l ! (nat (int n - i))"
  apply (simp add: shift_list_defs nth_as_shift_nat)
    apply (induct i arbitrary: l n)
   apply (simp add: shiftl_list_def shiftr_list_def from_nat_def to_nat_def 
                    nat_add_distrib drop_take nat_minus_as_int)
  by linarith

lemma right_shift_list_nth_pos[simp]: "i \<ge> 0 \<Longrightarrow> n < length l \<Longrightarrow> n \<ge> nat i  \<Longrightarrow> (l >> i) ! n = l ! (n - nat i)"
  apply (subst right_shift_list_nth_int)
  by (simp add: nat_minus_as_int)+

lemma right_shift_list_nth_zero[simp]: "i \<ge> 0 \<Longrightarrow> n < length l \<Longrightarrow> n < nat i \<Longrightarrow> (l >> i) ! n = 0"
  by (simp add: shift_list_defs shiftr_list_def nth_append)

lemma shiftr_list_nth: "n < length l \<Longrightarrow> (shiftr_list 0 l i) ! n = (if n \<ge> i then l ! (n - i) else 0)"
  apply (insert right_shift_list_nth_pos[where n=n and i="nat i" and l=l])
  apply (insert right_shift_list_nth_zero[where n=n and i="nat i" and l=l])
  by (auto simp: shift_list_defs)

lemma left_shift_list_nth:
  "n < length l \<Longrightarrow> 
   (l << (i::int)) ! n = (if i \<ge> 0 then
        (if n + (nat i) < length l then l ! (n + (nat i)) else 0)
        else (if n \<ge> nat (-i) then l ! (n - nat (-i)) else 0))"
  apply simp
  apply (intro impI conjI)
      apply (subst left_shift_neg)
        apply simp+
     apply (subst left_shift_neg)
     apply (rule right_shift_list_nth_zero)
  by simp+

lemma left_shift_list_nth_neg_simps[simp]:
  assumes n_bounded: "n < length l"
  shows
  "i \<le> 0 \<Longrightarrow> n \<ge> nat (-i) \<Longrightarrow> (l << i) ! n = l ! (n - nat (-i))"
  "i \<le> 0 \<Longrightarrow> n < nat (-i) \<Longrightarrow> (l << i) ! n = 0"
  using n_bounded
  by (auto simp: left_shift_list_nth)


lemma right_shift_list_nth:
  "n < length l \<Longrightarrow> 
   (l >> i) ! n = (if i \<le> 0
     then if n + nat (-i) < length l
          then l ! (n + nat (-i)) else 0
     else if i \<le> n
          then l ! (n - (nat i)) else 0)"
  apply (subst right_shift_neg)
  by (auto simp add:  left_shift_list_nth)

lemma right_shift_list_nth_simps[simp]:
  assumes n_bounded: "n < length l"
  shows
  "i \<le> 0 \<Longrightarrow> n + nat (-i) < length l \<Longrightarrow> (l >> i) ! n = l ! (n + nat (-i))"
  "i \<le> 0 \<Longrightarrow> n + nat (-i) \<ge> length l \<Longrightarrow> (l >> i) ! n = 0"
  using n_bounded
  by (auto simp: right_shift_list_nth)

context begin
private lemma nat_mod_helper2: "(i::int) > 0 \<Longrightarrow> n < m \<Longrightarrow>
    (n + (m - nat i mod m)) mod m = nat ((int n - i) mod int m)"
  apply (induct i rule: int_of_nat_induct)
  subgoal for na
    apply (induct na)
      apply (rule nat_int.Rep_eqD)
     apply (simp add: zmod_int)
    apply simp
    apply (clarsimp simp add: nat_mod_as_int nat_minus_as_int; intro impI conjI)
    apply (metis mod_add_self2 mod_diff_cong
        mod_mod_trivial)
    by (metis le_add2 linorder_not_le nat_int nle_le
        of_nat_add order_le_less_trans pos_mod_bound
        zless_nat_conj)
  apply simp
  done


private lemma nat_mod_helper3: "0 > (i::int) \<Longrightarrow> n < m \<Longrightarrow>
    (n + (m - nat (-i) mod m)) mod m = nat ((i + int n) mod int m)"
  by (metis minus_equation_iff nat_mod_helper2
      neg_0_less_iff_less uminus_add_conv_diff)

lemma left_rotate_list_nth[simp]: 
  "(n :: nat) < length l \<Longrightarrow> 
   (l <<< i) ! n = l ! (nat ((i + int n) mod (int (length l))))"
  apply (cases "i \<ge> 0")
   apply (simp add: rotate_list_defs)
   apply (simp add: nth_rotate to_nat_def nat_mod_as_int)
  apply (simp add: rotate_list_defs)
  by (simp add: nth_rotater to_nat_def nat_mod_helper3)

lemma right_rotate_list_nth[simp]: 
  "(n :: nat) < length l \<Longrightarrow> 
   (l >>> i) ! n = l ! (nat ((int n - i) mod int (length l)))"
  apply (subst right_rotate_neg)
  by simp

end

lemma shiftl_list_transfer[transfer_rule]: 
  "(R ===> list_all2 R ===> (=) ===> list_all2 R) shiftl_list shiftl_list"
  apply (simp add: shiftl_list_def[abs_def])
  by transfer_prover

lemma shiftr_list_transfer[transfer_rule]: 
  "(R ===> list_all2 R ===> (=) ===> list_all2 R) shiftr_list shiftr_list"
  apply (simp add: shiftr_list_def[abs_def])
  by transfer_prover

lemma right_shift_list_transfer[transfer_rule]:
  assumes R0[transfer_rule]: "R 0 0"
  shows "(list_all2 R ===> (=) ===> list_all2 R) (right_shift) (right_shift)"
  apply (simp add: right_shift_def[abs_def] cong: if_cong)
  by transfer_prover

lemma left_shift_list_transfer[transfer_rule]: 
  assumes R0[transfer_rule]: "R 0 0"
  shows "(list_all2 R ===> (=) ===> list_all2 R) (<<) (<<)"
  apply (simp add: left_shift_def[abs_def])
  by transfer_prover

lemma rotater1_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) rotater1 rotater1"
  unfolding rotater1_def
  apply (rule rel_funI)+
  subgoal for x y
    apply (cases x; cases y; clarsimp)
    by (auto simp: last_conv_nth list_all2_conv_all_nth nth_butlast)
  done

lemma rotater_transfer [transfer_rule]:
  "((=) ===> list_all2 A ===> list_all2 A) rotater rotater"
  unfolding rotater_def [abs_def] by transfer_prover

lemma rotate_int_list_transfer[transfer_rule]: 
  "(list_all2 R ===> (=) ===> list_all2 R) (right_rotate) (right_rotate)"
  apply (simp add: right_rotate_def[abs_def] cong: if_cong)
  by transfer_prover

lemma left_rotate_list_transfer[transfer_rule]: 
  "(list_all2 R ===> (=) ===> list_all2 R) (<<<) (<<<)"
  apply (simp add: left_rotate_def[abs_def])
  by transfer_prover

definition map_index_list :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_index_list f l = map (\<lambda>(idx,x). f idx x) (zip [0..<(length l)] l)"

lemma map_index_list_nth[simp]: 
  "i < length l \<Longrightarrow>  (map_index_list f l) ! i = f i (l ! i)"
  by (simp add: map_index_list_def)

lemma map_index_list_noop[simp]: "map_index_list (\<lambda>n x. x) l = l"
  apply (induct l rule: rev_induct)
  by (simp add: map_index_list_def)+

lemma map_index_list_length[simp]: 
  "length (map_index_list f l) = length l"
  by (simp add: map_index_list_def)

lemma map_index_list_transfer[transfer_rule]:
  "(((=) ===> A ===> B) ===> list_all2 A ===> list_all2 B) map_index_list map_index_list"
  apply (simp add: map_index_list_def[abs_def])
  by transfer_prover

lemma left_shift_list_pos: 
  "i \<ge> 0 \<Longrightarrow> (l :: 'a ::zero list) << i = map_index_list (\<lambda>n x. if n + (abs_nat i) < length l then x else 0) (l <<< i)"
  apply (rule nth_equalityI)
   apply simp
  apply (clarsimp simp: left_shift_list_nth to_nat_def)
  by (rule arg_cong, fastforce simp: nat_plus_as_int )


lemma right_shift_list_pos: 
  "i \<ge> 0 \<Longrightarrow> (l :: 'a ::zero list) >> i = map_index_list (\<lambda>n x. if n \<ge> nat i then x else 0) (l >>> i)"
  apply (cases "i = 0")
  apply simp
  apply (rule nth_equalityI)
   apply simp
  apply clarsimp
  apply (rule arg_cong[where f="nth l"])
  using nat_minus_as_int
  by (presburger)

lemma left_shift_list_def2: 
  "(l :: 'a :: zero list) << i =
     map_index_list (\<lambda>n x. if ((i \<ge> 0 \<longrightarrow> n + (nat i) < length l) \<and> (i < 0 \<longrightarrow> n \<ge> nat (-i))) then x else 0) (l <<< i)"
  apply (cases "i \<ge> 0")
   apply (simp add: left_shift_list_pos)
  apply (subst left_shift_neg)
  by (simp add: right_shift_list_pos left_rotate_neg )

lemma right_shift_list_def2: 
  "(l :: 'a :: zero list) >> i =
     map_index_list (\<lambda>n x. if ((i \<le> 0 \<longrightarrow> n + (abs_nat i) < length l) \<and> (i > 0 \<longrightarrow> n \<ge> abs_nat i)) then x else 0) (l >>> i)"
  by (simp add: right_shift_neg right_rotate_neg left_shift_list_def2 to_nat_def)

lemma right_shift_defs:
  "idx > 0 \<Longrightarrow> right_shift w idx = right_shift_nat w (nat idx)"
  "idx \<le> 0 \<Longrightarrow> right_shift w idx = left_shift_nat w (nat (-idx))"
  by (auto simp add: right_shift_def)

lemma right_rotate_defs:
  "idx > 0 \<Longrightarrow> right_rotate w idx = right_rotate_nat w (nat idx)"
  "idx \<le> 0 \<Longrightarrow> right_rotate w idx = left_rotate_nat w (nat (-idx))"
  by (auto simp add: right_rotate_def)

lemma right_shift_pos:
  "idx \<ge> 0 \<Longrightarrow> right_shift (w :: 'a :: shift) idx = right_shift_nat w (nat idx)"
  by (auto simp add: right_shift_def)

lemma right_rotate_pos:
  "idx \<ge> 0 \<Longrightarrow> right_rotate (w :: 'a :: rotate) idx = right_rotate_nat w (nat idx)"
  by (auto simp add: right_rotate_def)

end

end