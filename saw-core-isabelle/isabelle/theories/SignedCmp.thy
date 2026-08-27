theory SignedCmp
imports Main
begin


class signedCmp =
  fixes signed_lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(\<open>notation=\<open>infix <$\<close>\<close>_/ <$ _)\<close>  [51, 51] 50)
    and signed_le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(\<open>notation=\<open>infix <=$\<close>\<close>_/ <=$ _)\<close>  [51, 51] 50)

abbreviation (input)
  signed_ge  (infix \<open>>=$\<close> 50)
  where "x >=$ y \<equiv> y <=$ x"

abbreviation (input)
  signed_gt  (infix \<open>>$\<close> 50)
  where "x >$ y \<equiv> y <$ x"

instantiation int :: signedCmp begin
definition "signed_lt_int \<equiv> ((<) :: int \<Rightarrow> int \<Rightarrow> bool)"
definition "signed_le_int \<equiv> ((\<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
instance ..
end

end