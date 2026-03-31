(* Variant of type length that drops the need for a sort constraint.
   This is convenient because it allows us to omit the sort constraint
   from free type variables, but more specifically it works around issues
   with lift_bnf in the presence of sort constraints. *)

theory Alt_Type_Length
imports Main "HOL-Library.Type_Length" Unconstrain
begin

declare len0.intro_of_class[unconstrain_intro]

definition (in len0) "len_of_alt \<equiv> len_of"
unconstrain_const len_of_alt :: "'a :: type itself \<Rightarrow> nat"
lemmas len_of_alt_def2 = len_of_alt_def[unconstrain]

text \<open>
@{const len_of_alt} is equivalent to @{const len_of}, but with the
@{class len0} constraint dropped. For types without a @{class len0} instance
this is effectively an undefined value.
Note that although we could unconstrain @{const len_of} directly, this
has some unexpected effects on other tooling.
\<close>

syntax "_type_length_alt" :: "type \<Rightarrow> nat"  (\<open>(1LEN/(1'(_')))\<close>)
syntax_consts "_type_length_alt" \<rightleftharpoons> len_of_alt
translations "LEN('a)" \<rightharpoonup> "CONST len_of_alt TYPE('a)"

print_translation \<open>
  let
    fun len_of_itself_tr' ctxt [Const (\<^const_syntax>\<open>Pure.type\<close>, Type (_, [T]))] =
      Syntax.const \<^syntax_const>\<open>_type_length_alt\<close> $ Syntax_Phases.term_of_typ ctxt T
  in [(\<^const_syntax>\<open>len_of_alt\<close>, len_of_itself_tr')] end
\<close>


lemma len_alt_eq_len0:
  "LEN('a::len0) > 0 \<Longrightarrow> LEN('a) = LENGTH('a)"
  by (simp add: len_of_alt_def)

lemma len_alt_eq_len:
  "LEN('a::len) = LENGTH('a)"
  by (simp add: len_of_alt_def)



experiment begin

(* no sort constraints needed *)
lemma "LEN('a) = LEN('b) \<Longrightarrow> LEN('b) = LEN('a)" by simp

end

(* lift any type into a non-zero length by defining a 
   len_of_alt of 0 to be 1 *)
datatype 'a len = lenTypeCtr
instantiation len :: (_) len begin


definition len_of_len_raw_def:
 "len_of_len == (\<lambda>_. if LEN('a) = 0 then Suc undefined else LEN('a)) :: 'a len itself \<Rightarrow> nat"


instance
  apply standard
  apply (simp add: len_of_len_raw_def)
  done
end

(* we can't guard the actual definition since we need to know the result is non-zero
   regardless of LEN *)
lemma len_of_len_def: "LEN('a) > 0 \<Longrightarrow> (len_of :: ('a len itself) \<Rightarrow> nat) \<equiv> (\<lambda>_. LEN('a))"
  by (simp add: len_of_len_raw_def len_of_alt_def)

hide_fact len_of_len_raw_def

lemma len_wrapped_valid[simp]:
  "LEN('a) > 0 \<Longrightarrow> LENGTH('a len) = LEN('a)"
  by (simp add: len_of_alt_def len_of_len_def)

lemma len_wrapped_itself[simp]:
  "LENGTH('a len) = LENGTH('a::len)"
  by (simp add: len_of_alt_def len_of_len_def)

lemma len0_wrapped_itself[simp]:
  "LENGTH('a) > 0 \<Longrightarrow> LENGTH('a len) = LENGTH('a::len0)"
  by (simp add: len_of_alt_def len_of_len_def)


(* We can now define arithmetic expressions to have len0 instances without
   needing sort constraints on the type variables.
 *)


instantiation sum :: (_,_) len0 begin
definition "len_of_sum == (\<lambda>_. LEN('a) + LEN('b)) :: ('a + 'b) itself \<Rightarrow> nat"
instance ..
end

(* for most arithmetic operations, we can preserve the nonzero property *)

(* We only require one argument to be nonzero for sum, but this can't be described
   generally in the class instance. We arbitrarily pick the second argument, which
   allows us to have that ('a + 1) is nonzero regardless of 'a. *)
instantiation sum :: (_,len) len begin
instance
  apply standard
  by (simp add: len_of_sum_def len_of_alt_def)
end


instantiation prod :: (_,_) len0 begin
definition "len_of_prod == (\<lambda>_. LEN('a) * LEN('b)) :: ('a \<times> 'b) itself \<Rightarrow> nat"
instance ..
end

instantiation prod :: (len,len) len begin
instance
  apply standard
  by (simp add: len_of_prod_def len_of_alt_def)
end

(* Using datatype rather than typedecl helps with code generation. It simply establishes
   these types as singletons. *)

datatype ('a,'b) Minus (infixl \<open>-\<close> 65) = MinusTypeCtr
instantiation Minus :: (_,_) len0 begin
definition "len_of_Minus == \<lambda>(_ :: ('a,'b) Minus itself). LEN('a) - LEN('b)"
instance ..
end


datatype ('a,'b) Divide (\<open>(\<open>notation=\<open>infix\<close>\<close>_ '/ _)\<close> 65) = DivideTypeCtr
instantiation Divide :: (_,_) len0 begin
definition "len_of_Divide == \<lambda>(_ :: ('a,'b) Divide itself). LEN('a) div LEN('b)"
instance ..
end

datatype ('a,'b) Mod (infixl \<open>%\<close> 65) = ModTypeCtr
instantiation Mod :: (_,_) len0 begin
definition "len_of_Mod == \<lambda>(_ :: ('a,'b) Mod itself). LEN('a) mod LEN('b)"
instance ..
end

datatype ('a, 'b) Min = MinTypeCtr
instantiation Min :: (_,_)len0 begin
definition "len_of_Min == \<lambda>(_ :: ('a, 'b) Min itself). min (LEN('a)) (LEN('b))"
instance ..
end

instance Min :: (len,len) len
  apply standard
  by (simp add: len_of_Min_def len_of_alt_def)

datatype ('a, 'b) Max = MaxTypeCtr
instantiation Max :: (_,_)len0 begin
definition "len_of_Max == \<lambda>(_ :: ('a, 'b) Max itself). max (LEN('a)) (LEN('b))"
instance ..
end

instance Max :: (len,len) len
  apply standard
  apply (simp add: len_of_Max_def len_of_alt_def)
  using max.strict_coboundedI1 by blast

datatype ('a,'b) Exp (infixl \<open>^\<close> 65) = ExpTypeCtr
instantiation Exp :: (_,_) len0 begin
definition "len_of_Exp == \<lambda>(_ :: ('a,'b) Exp itself). LEN('a) ^ LEN('b)"
instance ..
end

instance Exp :: (len,_) len
  apply standard
  by (simp add: len_of_Exp_def len_of_alt_def)


text \<open>We use the code-preprocessor to drop redundant length checks when operating on sequences.\<close>
named_theorems length_code

lemmas [simp,length_code] = 
                len_of_sum_def len_of_prod_def 
                len_of_Minus_def len_of_Divide_def len_of_Mod_def
                len_of_Min_def len_of_Exp_def 

declare len_of_alt_def[simp]
declare len_of_alt_def2[length_code]

lemmas [length_code] = num_of_nat.simps(1) len_of_numeral_defs(1-2)

lemma [length_code]: "num_of_nat 1 = Num.One" by simp
lemma [length_code]: "num_of_nat (numeral x) = x" by (rule num_of_nat_numeral_eq)

lemma [length_code]: 
  "(HOL.equal LENGTH(('a::len0) bit0) (nat_of_num (num.Bit0 n))) = (HOL.equal LENGTH('a) (nat_of_num n))"
  "(HOL.equal LENGTH(('a::len0) bit0) LENGTH (('b::len0) bit0)) = HOL.equal LENGTH('a) LENGTH('b)"
  "(HOL.equal LENGTH(('a::len0) bit1) (nat_of_num (num.Bit1 n))) = (HOL.equal LENGTH('a) (nat_of_num n))"
  "(HOL.equal LENGTH(('a::len0) bit1) LENGTH (('b::len0) bit1)) = HOL.equal LENGTH('a) LENGTH('b)"
  "(HOL.equal LENGTH(('a::len0) bit1) LENGTH (('b::len0) bit0)) = False"
  "(HOL.equal LENGTH(('a::len0) bit0) LENGTH (('b::len0) bit1)) = False"
  "(HOL.equal (1 :: nat) (nat_of_num num.One)) = True"
  "(HOL.equal (nat_of_num num.One)) (1 :: nat) = True"
  "(HOL.equal LENGTH(('a::len0) bit0) (nat_of_num num.One)) = False"
  "(HOL.equal LENGTH(('a::len0) bit0) 1) = False"
  by (auto simp add: equal_eq Suc_double_not_eq_double double_not_eq_Suc_double )

lemma [length_code]:
  "(HOL.equal LENGTH(('a::len0) bit1) (nat_of_num (num.Bit0 n))) = False"
  "(HOL.equal LENGTH(('a::len0) bit0) (nat_of_num (num.Bit1 n))) = False"
  unfolding equal_eq
  apply simp
   apply (metis Suc_double_not_eq_double mult_2)
  by (metis dvdI len_bit0 nat_of_num_numeral odd_numeral)


lemma [length_code]:
  "(LENGTH(('a::len0) bit0)+1) = LENGTH(('a::len0) bit1)"
  "1+(LENGTH(('a::len0) bit0)) = LENGTH(('a::len0) bit1)"
  "(LENGTH(('a::len0) bit1)+1) = LENGTH(('a::len0+1) bit0)"
  "1+(LENGTH(('a::len0) bit1)) = LENGTH(('a::len0+1) bit0)"
  "(LENGTH(('a::len0) bit0) + LENGTH(('b::len0) bit0)) = LENGTH(('a + 'b) bit0)"
  "(LENGTH(('a::len0) bit0) + LENGTH(('b::len0) bit1)) = LENGTH(('a + 'b) bit1)"
  "(LENGTH(('a::len0) bit1) + LENGTH(('b::len0) bit0)) = LENGTH(('a + 'b) bit1)"
  "(LENGTH(('a::len0) bit1) + LENGTH (('b::len0) bit0)) = LENGTH(('a + 'b) bit1)"
  "(LENGTH(('a::len0) bit1) + LENGTH(('b::len0) bit1)) = LENGTH(('a + 'b) bit1 + 1)"
  "(LENGTH(('a::len0) bit1)-1) = LENGTH(('a::len0) bit0)"
  by simp+

lemma [length_code]:
  "(HOL.equal LENGTH(('a::len) bit1) (nat_of_num num.One)) = False"
  "(HOL.equal LENGTH(('a::len) bit1) 1) = False"
  by (auto simp add: equal_eq)

lemma [length_code]:
  "LENGTH('a::len0) = 0 \<Longrightarrow> LENGTH('a bit1) = 1"
  "LENGTH(0 bit1) = 1"
  by auto
  
lemma [length_code]:
  "(HOL.equal (nat_of_num n) LENGTH('a::len0)) = (HOL.equal LENGTH('a::len0) (nat_of_num n))"
  "(HOL.equal (i + j) LENGTH('a::len0)) = (HOL.equal LENGTH('a::len0) (i + j))"
   by (auto simp add: equal_eq)

lemma [length_code]: "((0::nat) < 1) = True" by simp
lemma [length_code]: "((0::nat) < 0) = False" by simp
lemma [length_code]: "((0::nat) < numeral x) = True"
  using nat_of_num_pos by auto
lemma [length_code]: "((0::nat) < nat_of_num x) = True"
  using nat_of_num_pos by auto
lemma [length_code]: "(if True then x else y) = x" by simp
lemma [length_code]: "(if False then x else y) = y" by simp

lemma list_length_code[length_code]: 
        "length (x # y # xs) = nat_of_num (Num.inc (num_of_nat (length (y # xs))))" 
        "length [x] = 1"
        "length [] = 0"
  using nat_of_num_inc num_of_nat_inverse
    apply force
  by auto

lemmas [length_code] = Num.inc.simps

lemma nat_1_triv[length_code]: "(n::nat) * 1 = n" by simp

lemma equal_refl[length_code]: "HOL.equal x x = True" 
  by (rule equal_class.equal_refl)

lemmas [length_code] = 
  arith_special conj.comm_neutral conj.left_neutral
  Nat.add_0_right add_0[where 'a=nat]

lemmas [code_unfold,code_post] = length_code

experiment begin

(* Now we can do length arithmetic without constraints, and still get the
   expected interpretation. *)
lemma "LEN('a * ('b + 'c)) = LEN(('a * 'c) + ('a * 'b))"
  by (simp add: distrib_left)

end


lemma len_cases': "(LEN('a) = 0 \<Longrightarrow> P) \<Longrightarrow> (LEN('a) > 0 \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases "LEN('a) > 0";simp)

lemma len_cases: "(LEN('a) = 0 \<Longrightarrow> P 0) \<Longrightarrow> (LEN('a) > 0 \<Longrightarrow> P (LEN('a))) \<Longrightarrow> P (LEN('a))"
  by (cases "LEN('a) > 0";simp)

lemma len_ofclass[intro!, unconstrain_intro]: "LEN('a) > 0 \<Longrightarrow> OFCLASS('a,len_class)"
  apply (rule len_class.intro)
   apply (rule len0.intro_of_class)
  apply (rule class.len.intro)
  apply (simp add: len_of_alt_def2)
  done

lemma len_pos: "p < LENGTH('a) \<Longrightarrow> p < LEN('a::len0)" 
  by simp

lemmas len_pos_unconstrain[intro] = len_pos[unconstrain]

context begin
private lemma un_ext: "f = g \<Longrightarrow> (\<And>x. f x = g x)" by simp
lemmas len_of_alt_def3 = len_of_alt_def2[THEN meta_eq_to_obj_eq, THEN un_ext, of "TYPE('a)"]
end

declare ofclass_type[intro!]

schematic_goal not_len_eq0[simp]: "(\<not> class.len (?len_of :: 'a itself \<Rightarrow> nat)) = (LEN('a) = 0)"
  apply (constrain 'a="'b::len0" and ?len_of=len_of)
  subgoal H[unconstrain] by (simp add: class.len_def)
  by (rule H)

end