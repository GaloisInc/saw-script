theory "Bit"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition conj_truth_table :: "Bit" where
"conj_truth_table  \<equiv> ((False \<and> False) ==`{Bit} False) &&`{Bit} (((True \<and> False) ==`{Bit} False) &&`{Bit} (((False \<and> True) ==`{Bit} False) &&`{Bit} ((True \<and> True) ==`{Bit} True)))"

cryptol_definition disj_truth_table :: "Bit" where
"disj_truth_table  \<equiv> ((False \<or> False) ==`{Bit} False) &&`{Bit} (((True \<or> False) ==`{Bit} True) &&`{Bit} (((False \<or> True) ==`{Bit} True) &&`{Bit} ((True \<or> True) ==`{Bit} True)))"

cryptol_definition implies_truth_table :: "Bit" where
"implies_truth_table  \<equiv> ((False \<longrightarrow> False) ==`{Bit} True) &&`{Bit} (((True \<longrightarrow> False) ==`{Bit} False) &&`{Bit} (((False \<longrightarrow> True) ==`{Bit} True) &&`{Bit} ((True \<longrightarrow> True) ==`{Bit} True)))"

end
end
