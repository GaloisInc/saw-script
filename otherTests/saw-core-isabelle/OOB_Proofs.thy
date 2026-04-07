theory OOB_Proofs 
imports "isabelle/OOB" "Cryptol.SeqOOB"
begin

context includes cryptol_syntax begin

lemma "PRED (Literal 'n 'ix) \<Longrightarrow> at_oob`{'n,'a::coercible_atom,'ix::{cryptol_integral,numeral}} a i"
  unfolding at_oob_def
  supply litT[simp]
  apply (simp add: from_nat_def pos_nat_def to_nat_def)
  apply (intro impI conjI)
   apply (subst nth_seq_oob)
  apply (metis dual_order.refl le_nat_iff
      to_from_int to_int_le to_int_pos)
   apply simp
  by (metis dual_order.refl dual_order.trans
      of_nat_0_le_iff to_from_int to_int_pos)


lemma "PRED (Literal 'n 'ix) \<Longrightarrow> bang_oob`{'n,'a::coercible_atom,'ix::{cryptol_integral,numeral}} a i"
  unfolding bang_oob_def
  supply litT[simp]
  apply (simp add: from_nat_def pos_nat_def to_nat_def)
  apply (intro impI conjI)
   apply (subst nth_end_seq_oob)
  apply (metis dual_order.refl le_nat_iff
      to_from_int to_int_le to_int_pos)
   apply simp
  by (metis dual_order.refl dual_order.trans
      of_nat_0_le_iff to_from_int to_int_pos)

end

end