theory Recursion_Proofs
imports "./isabelle/Recursion"
begin

primrec rec_fn_list :: "'b::cryptol_ring list \<Rightarrow> 'b" where
    "rec_fn_list (x#xs) = x + rec_fn_list xs"
  | "rec_fn_list [] = 0"

lemma rec_fn_list_sum: "rec_fn_list xs = sum_list xs"
  apply (induct xs;simp)
  done

overloading rec_fn' \<equiv> "rec_fn_impl_raw :: 'a tyarg \<Rightarrow> 'b tyarg \<Rightarrow> ('a, 'b::cryptol_ring) seq \<Rightarrow> 'b" begin
context includes cryptol_syntax and Seq.seq.lifting begin

lift_definition rec_fn' :: "{'a,'b::cryptol_ring} ['a]'b \<Rightarrow> 'b" is 
 "\<lambda>(_:: 'a tyarg) (_::'b tyarg) (xs :: 'b list). rec_fn_list xs" .

end
end

overloading rec_fn'' \<equiv> "rec_fnlba_gt_0rb_impl_raw :: 'a tyarg \<Rightarrow> 'b tyarg \<Rightarrow> ('a, 'b::cryptol_ring) seq \<Rightarrow> 'b" begin
context includes cryptol_syntax and Seq.seq.lifting begin

lift_definition rec_fn'' :: "{'a,'b::cryptol_ring} ['a]'b \<Rightarrow> 'b" is 
 "\<lambda>(_:: 'a tyarg) (_::'b tyarg) (xs :: 'b list). rec_fn_list xs" .

end
end

context includes cryptol_syntax begin

global_interpretation rec_fn_rec_spec
  apply standard
    unfolding rec_fn_spec_def rec_fnlba_eqeq_0rb_def
              rec_fnlba_gt_0rb_impl_def rec_fn_impl_def
              rec_fnlba_gt_0rb_spec_def
     apply simp_all
     apply (rule ext)+
     apply (rule assuming_cong;simp)
    apply transfer
     apply (simp add: rec_fn_list_sum)
    apply (metis drop_0 drop_Suc_nth sum_list.Cons)
    apply (intro impI conjI)
    apply (rule ext)+
     apply transfer
     apply simp
    apply (rule ext)+
    apply transfer
    apply simp
    done


lemma rec_fn_valid: "rec_fn_valid`{'a,'b::cryptol_ring} xs"
  unfolding rec_fn_valid_def rec_fn_def
  apply simp
  apply transfer
  apply (simp add: rec_fn_list_sum)
  done
  
end

end