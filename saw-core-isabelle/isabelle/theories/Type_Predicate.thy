theory Type_Predicate
imports Main Alt_Type_Length Type_Args Integral WordSeq Unconstrain
begin

(* encoding first-order predicates as types.
   Arithmetic on types is defined with respect to their
   LENGTH instance (if defined). *)
class pred =
  fixes holds0 :: "'a itself \<Rightarrow> bool"

consts holds :: "'a itself \<Rightarrow> bool"

overloading "holds1" \<equiv> "holds :: ('a :: pred itself) \<Rightarrow> bool" begin
definition "holds1 \<equiv> (holds0 :: 'a :: pred itself \<Rightarrow> bool)"
end

lemma pred_ofclass: "OFCLASS('a::type, pred_class)" by standard

lemmas holds_def = holds1_def[unconstrain, OF pred_ofclass]
declare holds_def[code_unfold]

type_alias And_Tuple = Type_Args.And_Tuple

syntax "_pred_holds" :: "type_list \<Rightarrow> bool"  (\<open>(\<open>notation=\<open>mixfix list enumeration\<close>\<close>PRED/('(_')))\<close>)

syntax_consts "_pred_holds" \<rightleftharpoons> holds

translations 
 "_pred_holds t" \<rightharpoonup> "CONST holds (_itself (_type_tuple t))"
 "_pred_holds (_type_tuple TYPE('a))" \<leftharpoondown> "CONST holds TYPE('a)"

term "PRED('a) :: bool"
term "PRED('a,'b)"

datatype True = TrueTypeCtr
instantiation True :: pred begin
definition "holds0_True \<equiv> \<lambda>(_ :: True itself). True"
instance ..
end

lemmas holds_True_def[simp] = holds1_def[where ?'a=True, simplified holds0_True_def]

lemma TrueT[simp]: "PRED(True)"
  by (simp add: holds1_def)


datatype 'a topT = topTTypeCtr
instantiation topT :: (_) pred begin
definition "holds0_topT \<equiv> \<lambda>(_ :: 'a topT itself). True"
instance ..
end

lemmas holds_topT_def[simp] = holds1_def[where ?'a="'a topT", simplified holds0_topT_def]

lemma topT[simp]: "PRED('a topT)"
  by (simp add: holds1_def)

datatype False = FalseTypeCtr
instantiation False :: pred begin
definition "holds0_False \<equiv> \<lambda>(_ :: False itself). False"
instance ..
end

lemmas holds_False_def[simp] = holds1_def[where ?'a=False, simplified holds0_False_def]

lemma FalseT[simp]: "PRED(False) = False"
  by (simp add: holds1_def)

datatype ('a,'b) And (infixr \<open>\<and>\<close> 35) = AndTypeCtr

instantiation And :: (_,_) pred begin
definition "holds0_And \<equiv> \<lambda>(_ :: ('a,'b) And itself). PRED('a) \<and> PRED('b)"
instance ..
end

lemmas holds_And_def[simp] = holds1_def[where ?'a="('a,'b) And", simplified holds0_And_def]

lemma AndT[simp]: "PRED('a \<and> 'b) = (PRED('a) \<and> PRED('b))"
  by (simp add: holds1_def)

datatype ('a,'b) Or (infixr \<open>\<or>\<close> 30) = OrTypeCtr

instantiation Or :: (_,_) pred begin
definition "holds0_Or \<equiv> \<lambda>(_ :: ('a,'b) Or itself). PRED('a) \<or> PRED('b)"
instance ..
end

lemmas holds_Or_def[simp] = holds1_def[where ?'a="('a,'b) Or", simplified holds0_Or_def]

lemma OrT[simp]: "PRED('a \<or> 'b) = (PRED('a) \<or> PRED('b))"
  by (simp add: holds1_def)

datatype ('a,'b) Implies (infixr \<open>\<longrightarrow>\<close> 25) = ImpliesTypeCtr

instantiation Implies :: (_,_) pred begin
definition "holds0_Implies \<equiv> \<lambda>(_ :: ('a,'b) Implies itself). PRED('a) \<longrightarrow> PRED('b)"
instance ..
end

lemmas holds_Implies_def[simp] = holds1_def[where ?'a="('a,'b) Implies", simplified holds0_Implies_def]

lemma ImpliesT[simp]: "PRED('a \<longrightarrow> 'b) = (PRED('a) \<longrightarrow> PRED('b))"
  by (simp add: holds1_def)

datatype ('a,'b) Iff (infixr \<open>\<longleftrightarrow>\<close> 25) = IffTypeCtr

instantiation Iff :: (_,_) pred begin
definition "holds0_Iff \<equiv> \<lambda>(_ :: ('a,'b) Iff itself). PRED('a) = PRED('b)"
instance ..
end

lemmas holds_Iff_def[simp] = holds1_def[where ?'a="('a,'b) Iff", simplified holds0_Iff_def]

lemma IffT[simp]: "PRED('a \<longleftrightarrow> 'b) = (PRED('a) \<longleftrightarrow> PRED('b))"
  by (simp add: holds1_def)

datatype ('a,'b) Leq (\<open>(\<open>notation=\<open>infix \<le>\<close>\<close>_/ \<le> _)\<close>  [51, 51] 50) = LeqTypeCtr

type_notation (ASCII)
  Leq  (infixr \<open><=\<close> 20)

instantiation Leq :: (_,_) pred begin
definition "holds0_Leq \<equiv> \<lambda>(_ :: ('a,'b) Leq itself). LEN('a) \<le> LEN('b)"
instance ..
end

lemmas holds_Leq_def[simp] = holds1_def[where ?'a="('a,'b) Leq", simplified holds0_Leq_def]

lemma LeqT[simp]: "PRED('a \<le> 'b) = (LEN('a) \<le> LEN('b))"
  by (simp add: holds1_def)

type_synonym ('a,'b) Geq = "('b,'a) Leq"
type_notation Geq (\<open>(\<open>notation=\<open>infix \<ge>\<close>\<close>_/ \<ge> _)\<close>  [51, 51] 50)


datatype ('a,'b) Lt (\<open>(\<open>notation=\<open>infix <\<close>\<close>_/ < _)\<close>  [51, 51] 50) = LtTypeCtr

instantiation Lt :: (_,_) pred begin
definition "holds0_Lt \<equiv> \<lambda>(_ :: ('a,'b) Lt itself). LEN('a) < LEN('b)"
instance ..
end

lemmas holds_Lt_def[simp] = holds1_def[where ?'a="('a,'b) Lt", simplified holds0_Lt_def]

lemma LtT[simp]: "PRED('a < 'b) = (LEN('a) < LEN('b))"
  by (simp add: holds1_def)

type_synonym ('a,'b) Gt = "('b,'a) Lt"
type_notation Gt (\<open>(\<open>notation=\<open>infix >\<close>\<close>_/ > _)\<close>  [51, 51] 50)

datatype ('a,'b) Equals (infixl \<open>=\<close> 50) = EqualsTypeCtr

instantiation Equals :: (_,_) pred begin
definition "holds0_Equals \<equiv> \<lambda>(_ :: ('a,'b) Equals itself). LEN('a) = LEN('b)"
instance ..
end

lemmas holds_Equals_def[simp] = holds1_def[where ?'a="('a,'b) Equals", simplified holds0_Equals_def]

lemma EqT[simp]: "PRED('a = 'b) = (LEN('a) = LEN('b))"
  by (simp add: holds1_def)



instantiation And_Tuple :: (_,_) pred begin
definition "holds0_And_Tuple \<equiv> \<lambda>(_ :: ('a,'b) And_Tuple itself). PRED('a) \<and> PRED('b)"
instance ..
end

lemmas holds_And_Tuple_def[simp] = holds1_def[where ?'a="('a,'b) And_Tuple", simplified holds0_And_Tuple_def]

lemma And_TupleT[simp]: "PRED(('a,'b) And_Tuple) = (PRED('a) \<and> PRED('b))"
  by (simp add: holds1_def)
   

consts assuming_undef :: "unit \<Rightarrow> 'a"

overloading assuming_undef_bool \<equiv> "assuming_undef :: unit \<Rightarrow> bool" begin
definition "assuming_undef_bool \<equiv> (\<lambda>_ :: unit. True)"
end

definition assuming:: "'a tyarg \<Rightarrow> 'b \<Rightarrow> 'b" where
  "assuming _ \<equiv> \<lambda>x. if PRED('a) then x else assuming_undef ()"

text \<open>In general @{term "assuming TY(False)"} is undefined, but we define it to be @{term True} for
 @{typ bool} as a special case. This allows us to prove the rule below, which simplifies the theorem statement
for a proof of an assuming-guarded definition. Without this, the assumption must be explicitly
reflected in the theorem statement.\<close> 

lemma assuming_intro_pred[intro!]: "(PRED('a) \<Longrightarrow> b) \<Longrightarrow> assuming TY('a) b"
  unfolding assuming_def assuming_undef_bool_def
  by (cases "PRED('a)"; simp)

hide_fact assuming_undef_bool_def
declare [[code abort:assuming_undef]]
hide_const assuming_undef

(* this is purely for syntax, where the guard gets pushed into
   the definition (see Cryptol_Definition) *)
datatype ('a, 'b) guarded = guardedTypeCtr

syntax
  "_guardedT" :: "type \<Rightarrow> type \<Rightarrow> type"
translations
  "_guardedT" \<rightharpoonup> (type) "guarded"

bundle assuming_syntax begin
unbundle type_arg_syntax

syntax
  "_guarded" :: "type_list \<Rightarrow> type \<Rightarrow> type" (\<open>('(_') =?> _)\<close> [1,0] 0)

syntax_types "_guarded" == guarded

syntax
  "_assuming" :: "type_list \<Rightarrow> term \<Rightarrow> term" (\<open>('(_') \<Rightarrow> _)\<close> [1,0] 0)

syntax (ASCII)
  "_assuming" :: "type_list \<Rightarrow> term \<Rightarrow> term" (\<open>('(_') => _)\<close> [1,0] 0)

translations
  "_guarded ts t" \<rightharpoonup> "_guardedT (_type_tuple ts) t"
  "_guarded (_type_tuple TYPE('a)) (_itself TYPE('b))" \<leftharpoondown> (type) "('a,'b) guarded"
  "_assuming xs x" \<rightharpoonup> "(CONST assuming (_tyarg xs) x)"
  "_assuming (_type_tuple xs) x" \<leftharpoondown> "(CONST assuming (_tyargCtr xs) x)"
end

context includes assuming_syntax begin

term "('a,'b,'c) => x"
term "('a,'b,'c) \<Rightarrow> x"
term "('a = 'b) => x"
typ "('a > 0, 'c = 0) =?> 'b"

lemma unguard_unfold_context[simp]: "PRED('a) \<Longrightarrow> (('a) \<Rightarrow> x) = x"
  by (simp add: assuming_def)

lemma unguard_unfold_pred: "PRED('a) \<Longrightarrow> P \<Longrightarrow> (('a) \<Rightarrow> P)"
  by (simp add: assuming_def)

lemma assuming_cong_strong: 
      "PRED('a) = PRED('b) 
  \<Longrightarrow> (PRED('a) \<Longrightarrow> PRED('b) \<Longrightarrow> x = y) 
  \<Longrightarrow> (('a) \<Rightarrow> x) = (('b) \<Rightarrow> y)"
  by (simp add: assuming_def)

lemma assuming_cong[cong]: 
      "(PRED('a) \<Longrightarrow> x = y) 
  \<Longrightarrow> (('a) \<Rightarrow> x) = (('a) \<Rightarrow> y)"
  by (simp add: assuming_def)

lemma assuming_iff[intro!]: 
  "PRED('a) = PRED('b) \<Longrightarrow> (('a) \<Rightarrow> x) = (('b) \<Rightarrow> x)"
  by (simp add: assuming_def)

lemma assuming_uncurry_And_Tuple[simp]: 
   "(('a) \<Rightarrow> ('b) \<Rightarrow> x)
  = (('a,'b) \<Rightarrow> x)"
  by (simp add: assuming_def)

end

hide_fact assuming_def


context includes assuming_syntax begin
lemma asmL[simp]: "PRED('a) \<Longrightarrow> (('a,'b) \<Rightarrow> x) = (('b) \<Rightarrow> x)"
  by (simp cong: assuming_cong_strong)

lemma asmR[simp]: "PRED('b) \<Longrightarrow> (('a,'b) \<Rightarrow> x) = (('a) \<Rightarrow> x)"
  by (simp cong: assuming_cong_strong)

lemma assuming_unsatisfied: 
  "\<not>PRED('a) \<Longrightarrow> \<not>PRED('b) \<Longrightarrow> (('a) \<Rightarrow> x) = (('b) \<Rightarrow> y)"
  apply (rule assuming_cong_strong)
  by simp+
end

experiment begin

context includes assuming_syntax begin

lemma "((True) \<Rightarrow> x) = x" 
      "(('a topT) \<Rightarrow> x) = x"
      "(('a, True) \<Rightarrow> x) = (('a) \<Rightarrow> x)"
    by simp+


lemma "(('a) \<Rightarrow> ('a \<longrightarrow> 'b) \<Rightarrow> x) = (('b \<and> 'a) \<Rightarrow> x)"
proof -
  have H: "(('a,'b) \<Rightarrow> x) = (('b \<and> 'a) \<Rightarrow> x)" by force
  show ?thesis
  apply (simp cong: assuming_cong_strong) (* congruence and uncurry *)
  apply (rule H)
    done
qed

term "x :: ('a,'b) =?> 'c"
typ "(1 < 2) =?> (('a \<Rightarrow> 'b))"
end
end

datatype ('a,'b) litT = litTTypeCtr

instantiation litT :: (_,from_to_int) pred begin
definition "holds0_litT \<equiv> \<lambda>(_ :: ('a,'b) litT itself). \<forall>i. 0 \<le> i \<longrightarrow> i \<le> LEN('a) \<longrightarrow> (\<exists>(x::'b). to_int x = int i)"
instance ..
end

lemma holds0_litT_def2[code]: 
 "holds0 = (\<lambda>(_ :: ('a,'b::from_to_int) litT itself). to_nat (from_nat LEN('a) :: 'b) = LEN('a))"
  unfolding holds0_litT_def to_nat_def from_nat_def
  apply (rule ext)
  apply (rule iffI)
   apply simp
  apply (metis dual_order.refl nat_int
      to_from_int)
  apply simp  
  by (metis dual_order.refl from_int_zero int_eq_iff
      int_nat_eq le_nat_iff to_from_int_bounds
      to_int_pos)


lemma litT: "PRED (('a,'b::from_to_int) litT) = (\<forall>i. 0 \<le> i \<longrightarrow> i \<le> LEN('a) \<longrightarrow> (\<exists>(x::'b). to_int x = int i))"
  apply (simp add: holds1_def holds0_litT_def[abs_def])
  done

context notes litT[simp] begin

lemma seq_len_lit[simp]: "LEN('a) < (2^LEN('b)) \<Longrightarrow> PRED(('a, ('b,bool) seq) litT)"
  apply clarsimp
  apply transfer
  apply transfer
  apply clarsimp
  done

lemma int_lit[simp]: "PRED(('a, int) litT)" by clarsimp

lemma bool_lit[simp]: "LEN('a) \<le> 1 \<Longrightarrow> PRED(('a, bool) litT)"
  apply (simp add: to_int_bool_def)
  by (metis le_Suc_eq le_zero_eq)

lemma zint_lit[simp]: "LEN('a) < LEN('b) \<Longrightarrow> PRED(('a, 'b Z) litT)"
  apply (simp add: to_int_mod_ring_def)
  apply transfer
  apply clarsimp
  apply (insert CARD_fin0[unconstrain, where 'a='b])
  apply (simp add: len_of_alt_def2)
  using  order_le_less_trans
  by fastforce

text \<open>Decision procedures for litT for code generation\<close>

lemma holds0_litT_int[code_unfold]: "(holds0 :: ('a, int) litT itself \<Rightarrow> bool) = (\<lambda>_. True)"
  unfolding holds0_litT_def
  apply simp
  done

value "PRED((25, int) litT)"

lemma holds0_litT_bool[code_unfold]: "(holds0 :: ('a, bool) litT itself \<Rightarrow> bool) = (\<lambda>_. (LEN('a) \<le> 1))"
  unfolding holds0_litT_def
  apply simp
  apply (rule ext)
  apply (rule iffI)
  apply (metis One_nat_def nat_int not_less_eq_eq
      of_nat_1 semiring_char_0_class.of_nat_neq_0
      to_int_bool_def)
  by (metis One_nat_def bool_lit le0 litT)

value "PRED((1, bool) litT)"
value "PRED((25, bool) litT)"

lemma holds0_litT_seq_def[code_unfold]:
  \<open>holds0 = (\<lambda>(_ :: (('a, ('b,bool) seq) litT) itself). (int LEN('a) < (int 2) ^ LEN('b)))\<close>
  unfolding holds0_litT_def
  apply (rule ext)
  apply (rule iffI)
  apply simp
   apply transfer
   apply transfer
   apply clarsimp
  apply clarsimp
  apply (erule(1) seq_len_lit[simplified, rule_format])
  done

value "PRED((25, (3,bool) seq) litT)"
value "PRED((25, (32,bool) seq) litT)"

lemma CARD_alt_fin0: "CARD ('a fin) - 1 = LEN('a) - 1"
  unfolding type_definition.card [OF type_definition_fin]
  by simp

lemma CARD_alt_fin: "LEN('a) > 0 \<Longrightarrow> CARD ('a fin) = LEN('a)"
  unfolding type_definition.card [OF type_definition_fin]
  by simp

lemma CARD_fin1: "LEN('a) = 0 \<Longrightarrow> CARD ('a fin) = 1"
  unfolding type_definition.card [OF type_definition_fin]
  by simp

lemma holds0_litT_zint[code_unfold]: 
  "(holds0 :: ('a, 'b Z) litT itself \<Rightarrow> bool) = (\<lambda>_. (LEN('a) < LEN('b)) \<or> (LEN('a) = 0 \<and> LEN('b) = 0))"
  unfolding holds0_litT_def to_int_mod_ring_def
  apply (cases "LEN('a) = 0"; cases "LEN('b) = 0"; force?)
  apply (metis (mono_tags, opaque_lifting)
        CARD_fin1 le0 le_refl less_nat_zero_code
        mod_by_1 of_int_mod_ring.rep_eq
        of_int_mod_ring_to_int_mod_ring of_nat_1
        of_nat_le_0_iff
        to_int_mod_ring.rep_eq)
  apply (rule ext)
  apply (rule iffI)
  subgoal
    by (metis (mono_tags, opaque_lifting)
        CARD_alt_fin le0 len_cases'
        less_irrefl_nat linorder_not_le nat_int
        nat_mod_lem of_int_mod_ring.rep_eq
        of_int_mod_ring_to_int_mod_ring
        to_int_mod_ring.rep_eq zmod_int)
  subgoal
    by (metis CARD_alt_fin
        dual_order.strict_trans2 nat_mod_lem
        of_int_mod_ring.rep_eq
        to_int_mod_ring.rep_eq zmod_int)
  done
  
value "PRED((25, 2 Z) litT)"
value "PRED((25, 26 Z) litT)"

end
end