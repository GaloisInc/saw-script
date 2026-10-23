theory Submodules_Proofs
imports "isabelle/Submodules"
begin

lemma p0
  by (simp add: p0_def x_def)

lemma p1
  by (simp add: p1_def Sub_SubSub.x_def)

lemma p2
  by (simp add: p2_def Sub.SubSub.x_def)

cryptol_termination Sub.fib
  apply (relation "measure (\<lambda>i. nat i)")
  by auto

lemma "\<And>n. p3 n"
  apply (simp add: p3_def)
  apply (subst Sub.fib_alt_def)
  by simp

lemma p4 by (simp add: p4_def)
lemma p5 by (simp add: p5_def)

lemma "\<And>x y z. p6 x y z"
  by (simp add: p6_def split: Sub.SubSub.MyEnum.splits)

end