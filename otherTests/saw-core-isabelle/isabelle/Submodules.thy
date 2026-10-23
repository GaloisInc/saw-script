theory "Submodules"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition x\<^sub>S\<^sub>u\<^sub>b\<^sub>_\<^sub>S\<^sub>u\<^sub>b\<^sub>S\<^sub>u\<^sub>b :: "[64]" where
"x\<^sub>S\<^sub>u\<^sub>b\<^sub>_\<^sub>S\<^sub>u\<^sub>b\<^sub>S\<^sub>u\<^sub>b  \<equiv> 0x6 :: [64]"

cryptol_definition p1 :: "Bit" where
"p1  \<equiv> x\<^sub>S\<^sub>u\<^sub>b\<^sub>_\<^sub>S\<^sub>u\<^sub>b\<^sub>S\<^sub>u\<^sub>b ==`{[64]} (0x6 :: [64])"

cryptol_definition x\<^sub>S\<^sub>u\<^sub>b_\<^sub>S\<^sub>u\<^sub>b\<^sub>S\<^sub>u\<^sub>b :: "[32]" where
"x\<^sub>S\<^sub>u\<^sub>b_\<^sub>S\<^sub>u\<^sub>b\<^sub>S\<^sub>u\<^sub>b  \<equiv> 0x5 :: [32]"

cryptol_definition p2 :: "Bit" where
"p2  \<equiv> x\<^sub>S\<^sub>u\<^sub>b_\<^sub>S\<^sub>u\<^sub>b\<^sub>S\<^sub>u\<^sub>b ==`{[32]} (0x5 :: [32])"

cryptol_definition x :: "[8]" where
"x  \<equiv> 0x3 :: [8]"

cryptol_definition x\<^sub>S\<^sub>u\<^sub>b :: "[16]" where
"x\<^sub>S\<^sub>u\<^sub>b  \<equiv> 0x4 :: [16]"

end
end
