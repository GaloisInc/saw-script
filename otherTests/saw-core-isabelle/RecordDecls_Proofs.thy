theory RecordDecls_Proofs
imports "isabelle/RecordDecls"
begin

context includes cryptol_syntax begin

lemma "flipR_valid`{'n} x"
  unfolding flipR_valid_def flipR_def
  by simp

lemma "flipS_valid x"
  unfolding flipS_valid_def flipS_def
  by simp

lemma "LEN('m) =  LEN('n) +  LEN('n) \<Longrightarrow> flipR2_valid`{'n, 'm} x"
  unfolding flipR2_valid_def flipR2_def flipR_def
  apply simp
  apply (cases x)
  apply simp
  done

lemma R1_R2_zip_concrete
  unfolding R1_R2_zip_concrete_def R1_R2_zip_def zipWith_seq_def
  by (simp add: word_seq_convs)

lemma R1_R2_zip_concrete
  by eval

lemma "flipRN_valid`{'n} x"
  unfolding flipRN_valid_def flipRN_def RN_def
  by simp

lemma "swapS_valid x"
  unfolding swapS_valid_def swapS_def
  by simp

end

end