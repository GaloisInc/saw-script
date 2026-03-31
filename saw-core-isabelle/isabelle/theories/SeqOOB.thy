theory SeqOOB 
imports Seq
begin
(* defines out of bounds accesses to be the last element of the list if forward-indexed, or
   the first element if backwards-indexed *)
value "nth_seq ((list_to_seq [0::int,1,2]) :: (3,int) seq) 2" (* 2 *)
overloading oob_list_idx_end \<equiv> "oob_list_idx :: nat \<Rightarrow> nat" begin
definition "oob_list_idx_end n \<equiv> n - (1::nat)"
end

lemma oob_list_elem_end_def[code]: "oob_list_elem xs = (if xs \<noteq> [] then last xs else undefined_list_elem)"
  apply (simp add: oob_list_elem_def oob_list_idx_end_def)
  by (simp add: last_conv_nth)

value "nth_seq ((list_to_seq [0::int,1,2]) :: (3,int) seq) 3" (* 2 *)
value "nth_end_seq ((list_to_seq [0::int,1,2]) :: (3,int) seq) 3" (* 0 *)

lemma nth_seq_oob:
  "i \<ge> length_seq xs \<Longrightarrow> nth_seq xs i = nth_end_seq xs 0"
  apply (auto simp add: nth_end_seq_def2)
   apply transfer
   apply (simp add: oob_list_elem_end_def)
  apply (metis One_nat_def last_conv_nth
      length_greater_0_conv)
  apply transfer
  apply simp
  done

lemma nth_end_seq_oob:
  "i \<ge> length_seq xs \<Longrightarrow> nth_end_seq xs i = nth_seq xs 0"
  apply (auto simp add: nth_end_seq_def2)
   apply transfer
  apply (simp add: oob_list_elem_end_def)
  by (metis One_nat_def last_conv_nth
      length_greater_0_conv length_rev nth_list_def
      nth_rev_alt oob_list_elem_end_def)

end