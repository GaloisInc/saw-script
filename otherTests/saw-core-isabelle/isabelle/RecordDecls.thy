theory "RecordDecls"
imports "Cryptol.Cryptol" b_w_recordT s_s_recordT
begin

context includes cryptol_translation_syntax begin
type_synonym ('n) R = "\<lparr>b_w_recordT.b :: Bit,b_w_recordT.w :: ['n]\<rparr>"

type_synonym ('n) R2 = "\<lparr>b_w_recordT.b :: Bit,b_w_recordT.w :: [2 * 'n]\<rparr>"

type_synonym ('n) RN = "\<lparr>b_w_recordT.b :: Bit,b_w_recordT.w :: ['n]\<rparr>"

type_synonym S = "\<lparr>b_w_recordT.b :: Integer,b_w_recordT.w :: Integer\<rparr>"

type_synonym Z = "\<lparr>s_s_recordT.s :: Bit\<rparr>"

cryptol_definition R1_R2_zip :: "{'n,'m} ((fin 'n,fin 'm) =?> ((['n](2 * 'm) R) \<Rightarrow> ((['n]('m) R2) \<Rightarrow> (['n]('m) R2))))" where
"R1_R2_zip  \<equiv> zipWith`{'n,(2 * 'm) R,('m) R2,('m) R2} (\<lambda>(r :: (2 * 'm) R) (r2 :: ('m) R2). (\<lparr>b_w_recordT.b = ((b_w_recordT.b r) ||`{Bit} (b_w_recordT.b r2)),b_w_recordT.w = ((b_w_recordT.w r) ||`{[2 * 'm]} (b_w_recordT.w r2))\<rparr>))"

cryptol_definition R1_R2_zip_concrete :: "Bit" where
"R1_R2_zip_concrete  \<equiv> (R1_R2_zip`{2,16} (list_to_seq [(\<lparr>b_w_recordT.b = True,b_w_recordT.w = (0x64 :: [32])\<rparr>) : ((32) R),(\<lparr>b_w_recordT.b = False,b_w_recordT.w = (0x2 :: [32])\<rparr>) : ((32) R)] :: [2](32) R) (list_to_seq [(\<lparr>b_w_recordT.b = True,b_w_recordT.w = (0x1f4 :: [32])\<rparr>) : ((16) R2),(\<lparr>b_w_recordT.b = True,b_w_recordT.w = (0x5 :: [32])\<rparr>) : ((16) R2)] :: [2](16) R2)) ==`{[2](16) R2} (list_to_seq [(\<lparr>b_w_recordT.b = True,b_w_recordT.w = (0x1f4 :: [32])\<rparr>) : ((16) R2),(\<lparr>b_w_recordT.b = True,b_w_recordT.w = (0x7 :: [32])\<rparr>) : ((16) R2)] :: [2](16) R2)"

cryptol_definition RN :: "{'n} ((\<lparr>b_w_recordT.b :: Bit,b_w_recordT.w :: ['n]\<rparr>) \<Rightarrow> (\<lparr>b_w_recordT.b :: Bit,b_w_recordT.w :: ['n]\<rparr>))" where
"RN x \<equiv> x :: \<lparr>b_w_recordT.b :: Bit,b_w_recordT.w :: ['n]\<rparr>"

cryptol_definition Z_test :: "Z \<Rightarrow> Bit" where
"Z_test r \<equiv> s_s_recordT.s r"

cryptol_definition flipR :: "{'n} ((fin 'n) =?> ((('n) R) \<Rightarrow> (('n) R)))" where
"flipR i__p0 \<equiv> 
  let
    y = ((b_w_recordT.w i__p0) : (['n]));
    x = ((b_w_recordT.b i__p0) : Bit)
  in (\<lparr>b_w_recordT.b = (complement`{Bit} x),b_w_recordT.w = (complement`{['n]} y)\<rparr>)"

cryptol_definition flipR2 :: "{'n,'m} ((fin 'n,fin 'm,'m = (2 * 'n)) =?> ((('m) R) \<Rightarrow> (('n) R2)))" where
"flipR2 x \<equiv> flipR`{2 * 'n} x"

cryptol_definition flipR2_valid :: "{'n,'m} ((fin 'n,fin 'm,'m = (2 * 'n)) =?> ((('m) R) \<Rightarrow> Bit))" where
"flipR2_valid x \<equiv> x ==`{('m) R} (flipR2`{'n,2 * 'n} (flipR2`{'n,'m} x))"

cryptol_definition flipRN :: "{'n} ((fin 'n) =?> ((('n) RN) \<Rightarrow> (('n) RN)))" where
"flipRN r \<equiv> RN`{'n} (\<lparr>b_w_recordT.b = (complement`{Bit} (b_w_recordT.b r)),b_w_recordT.w = (complement`{['n]} (b_w_recordT.w r))\<rparr>)"

cryptol_definition flipRN_valid :: "{'n} ((fin 'n) =?> ((('n) RN) \<Rightarrow> Bit))" where
"flipRN_valid r \<equiv> ((b_w_recordT.b r) ==`{Bit} (b_w_recordT.b (flipRN`{'n} (flipRN`{'n} r)))) &&`{Bit} ((b_w_recordT.w r) ==`{['n]} (b_w_recordT.w (flipRN`{'n} (flipRN`{'n} r))))"

cryptol_definition flipR_valid :: "{'n} ((fin 'n) =?> ((('n) R) \<Rightarrow> Bit))" where
"flipR_valid w \<equiv> w ==`{('n) R} (flipR`{'n} (flipR`{'n} w))"

cryptol_definition flipS :: "S \<Rightarrow> S" where
"flipS i__p1 \<equiv> 
  let
    y = ((b_w_recordT.w i__p1) : Integer);
    x = ((b_w_recordT.b i__p1) : Integer)
  in (\<lparr>b_w_recordT.b = (negate`{Integer} x),b_w_recordT.w = (negate`{Integer} y)\<rparr>)"

cryptol_definition flipS_valid :: "S \<Rightarrow> Bit" where
"flipS_valid w \<equiv> w ==`{S} (flipS`{} (flipS`{} w))"

end
end
