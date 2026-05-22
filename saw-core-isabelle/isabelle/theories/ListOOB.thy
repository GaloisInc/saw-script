theory ListOOB
  imports Main Unconstrain
begin

(* this constant may be overloaded in order to define out of bounds
   list/seq accesses *)
consts oob_list_idx :: "nat \<Rightarrow> nat"

code_printing constant oob_list_idx \<rightharpoonup>
 (SML) "(raise/ Fail/ (\"Out of bounds list access\" ))"

consts undefined_bool :: bool

(* we define this for bool-like types so that we can get a consistent
   value when projecting in and out of actual bools.

   Ideally we could constrain this to the bool class from Bool_Class.thy, but
   that introduces a cyclic dependency without some reorganizing.
 *)
definition undefined_list_elem :: "'a :: {linorder,one,zero,zero_neq_one}" where
  "undefined_list_elem \<equiv> THE x. (UNIV :: 'a set) = {0,1} \<and> (x = (if undefined_bool then 1 else 0))"
unconstrain_const undefined_list_elem

declare [[code drop: undefined_list_elem]]

code_printing constant undefined_list_elem \<rightharpoonup>
 (SML) "(raise/ Fail/ (\"Out of bounds list access\" ))"

definition oob_list_elem :: "'a list \<Rightarrow> 'a" where
  "oob_list_elem xs \<equiv> if oob_list_idx (length xs) < length xs then
    xs ! oob_list_idx (length xs) else undefined_list_elem"

definition nth_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "nth_list xs n \<equiv> if n < length xs then xs ! n else oob_list_elem xs"

lemma nth_list_nth[simp]: "n < length xs \<Longrightarrow> nth_list xs n = xs ! n"
  by (simp add: nth_list_def)

lemma list_all_upto_cong[cong]: "i = i' \<Longrightarrow> j = j' \<Longrightarrow>
  (\<And>z. z \<ge> i' \<Longrightarrow> z < j' \<Longrightarrow> P z = Q z) \<Longrightarrow>
  list_all P [i..<j] = list_all Q [i'..<j']"
  by (rule list_all_cong;simp)

lemma nth_list_oob[simp]: 
  "nth_list [] n = oob_list_elem []"
  "length xs = 0 \<Longrightarrow> nth_list xs n = oob_list_elem []"
  "i \<ge> length xs \<Longrightarrow> nth_list xs i = oob_list_elem xs"
  by (auto simp add: nth_list_def)

lemma nth_list_splits:
  "P (nth_list xs n) = ((n < length xs \<longrightarrow> P (xs ! n)) \<and> (n \<ge> length xs \<longrightarrow> P (oob_list_elem xs)))"
  by (simp add: nth_list_def)

definition "nth_end_list xs n \<equiv> if n < length xs then xs ! (length xs - n - 1) else oob_list_elem (rev xs)"

lemma nth_end_list_nth[simp]: "n < length xs \<Longrightarrow> nth_end_list xs n = xs ! (length xs - n - 1)"
  by (simp add: nth_end_list_def)

lemma nth_end_list_splits:
  "P (nth_end_list xs n) = ((n < length xs \<longrightarrow> P (xs ! (length xs - n - 1))) \<and> (n \<ge> length xs \<longrightarrow> P (oob_list_elem (rev xs))))"
  by (simp add: nth_end_list_def)

lemma nth_end_list_oob[simp]: 
  "nth_end_list [] n = oob_list_elem []"
  "length xs = 0 \<Longrightarrow> nth_end_list xs n = oob_list_elem []"
  "i \<ge> length xs \<Longrightarrow> nth_end_list xs i = oob_list_elem (rev xs)"
  by (auto simp add: nth_end_list_def)

(* force a list to have the given length, dropping or adding undefined elements as needed *)
definition list_len :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "list_len n xs \<equiv> map (\<lambda>i. nth_list xs i) [0..<n]"

lemma map_upto_cong:
  "n = i \<Longrightarrow> m = j \<Longrightarrow>
  (\<And>x. x < m \<Longrightarrow> x < j \<Longrightarrow> f x = g x) \<Longrightarrow>
  map f [n..<m] = map g [i..<j]"
  by simp

lemma list_len_take[simp]: "n \<le> length xs \<Longrightarrow> list_len n xs = take n xs"
  apply (simp add: list_len_def cong: map_upto_cong)
  by (metis diff_is_0_eq dual_order.refl
      le_add_diff_inverse2 map_nth take_map
      take_upt)

lemma map_nth'[simp]: "n = length xs \<Longrightarrow> map ((!) xs) [0..<n] = xs"
  apply (simp add: map_nth)
  done

lemma list_len_noop[simp, code_unfold]: "length xs = n \<Longrightarrow> list_len n xs = xs"
  by (simp add: list_len_def cong: map_upto_cong)

lemma list_len_length[simp]: "length (list_len n xs) = n"
  by (simp add: list_len_def)

lemma
  "nth_list [1::int,2,3] 2 = 3"
  "nth_end_list [1::int,2,3] 2 = 1"
  "list_len 3 [1::int,2,3] = [1::int,2,3]"
  by eval+

value "nth_list [1::int,2,3] 2"

end