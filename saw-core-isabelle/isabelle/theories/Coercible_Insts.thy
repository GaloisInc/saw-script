(* Supporting basic coercions by collapsing values into a uniform datatype.
   The intention here is that we should be able to coerce equivalently-sized
   types by collapsing and rebuilding them *)

theory Coercible_Insts
  imports Coercible "HOL-Library.Numeral_Type"  Fin Type_Args
begin

locale strip_drop_code = fixes a :: "('a::coercible) itself" begin
declare [[code abort: "strip :: 'a \<Rightarrow> stripped"]]
declare [[code abort: "unstrip :: stripped \<Rightarrow> 'a"]]
end

subsection \<open>Coercible instances\<close>

instantiation unit :: coercible_atom begin
definition "strip_type_unit == (\<lambda>_. T [] STR ''unit'') :: unit itself \<Rightarrow> stripped_type"
definition "strip_unit == \<lambda>(). Stripped_Atom (S [])"
definition "unstrip_unit == \<lambda>(_ :: stripped). ()"
instance
  supply [simp] = strip_unit_def unstrip_unit_def 
  by (standard;simp?)
end
interpretation strip_drop_code "TYPE(unit)" .


lemma unit_type_name[simp,code_unfold]: "type_name TYPE(unit) = STR ''unit''"
  by (simp add: strip_type_unit_def type_name_def)

text \<open>This allows us to coerce any function of the form @{typ "'a :: coercible_atom \<Rightarrow> 'b :: coercible"},
      where the function given to @{const Stripped_Fn} simply embeds the stripping and unstripping
      for the domain and range type as necessary.
      \<close>

instantiation "fun" :: (strip_type,strip_type) strip_type begin
definition "strip_type_fun == (\<lambda>_. T [strip_type (TYPE('a)), strip_type TYPE('b)] STR ''fun'') :: ('a \<Rightarrow> 'b) itself \<Rightarrow> stripped_type"
instance ..
end

lemma fun_type_name[simp,code_unfold]: "type_name TYPE(('a::strip_type) \<Rightarrow> ('b::strip_type)) = STR ''fun''"
  by (simp add: strip_type_fun_def type_name_def)

lemma same_type_fun[simp,code_unfold]: 
 "same_type (TYPE('a ::strip_type \<Rightarrow> 'c ::strip_type)) (TYPE('b ::strip_type \<Rightarrow> 'd ::strip_type)) 
   = (same_type TYPE('a) TYPE('b) \<and> same_type TYPE('c) TYPE('d))"
  by (simp add: strip_type_fun_def same_type_def)

instantiation "fun" :: (unstrip,strip) strip begin
definition "strip_fun (f :: ('a :: unstrip) \<Rightarrow> ('b :: strip)) \<equiv> 
  Stripped_Fn (\<lambda>sa. strip (f (unstrip_atom sa)))"
instance ..
end

instantiation "fun" :: (strip,unstrip) unstrip begin
definition "unstrip_fun (x :: stripped) \<equiv> case x of
  Stripped_Fn (f :: stripped_atom \<Rightarrow> stripped) \<Rightarrow> (\<lambda>(x :: 'a :: strip). (unstrip (f (strip_atom x)) :: 'b :: unstrip))"
instance ..
end

lemma strip_fn_not_atom[simp]:"\<not>(is_Stripped_Atom (strip (f :: 'a :: unstrip \<Rightarrow> 'b :: strip)))"
  by (simp add: strip_fun_def)


instantiation "fun" :: (coercible_atom,coercible) coercible begin
instance
  supply [simp] = strip_fun_def unstrip_fun_def
  by (standard;simp?)
end

lemma strip_unstrip_fn[simp]: 
  "unstrip (strip (f :: 'a :: unstrip \<Rightarrow> 'b :: strip)) = 
     (\<lambda>(x :: 'c :: coercible_atom). unstrip (strip (f (unstrip (strip x)))) :: 'd :: unstrip) "
  supply [simp] = strip_fun_def unstrip_fun_def
  by (auto simp add: comp_def coerce_to_def)


interpretation "fun": 
  coercion "\<lambda>(f :: 'a :: coercible_atom \<Rightarrow> 'b :: coercible).
            (\<lambda>(x :: 'c :: coercible_atom). coerce (f ((coerce x))) :: 'd :: coercible)"
  apply standard
  by (simp add: coerce_to_def)


text \<open>Since we can only coerce functions with atom arguments, we want to provide
      @{class coercible_atom} instances for base types.\<close>


instantiation nat :: coercible_atom begin
definition "strip_type_nat == (\<lambda>_. T [] STR ''nat'') :: nat itself \<Rightarrow> stripped_type"
definition "strip_nat n == strip (S (replicate n (S [])))"
definition "unstrip_nat == 
  (\<lambda>ms. case unstrip ms of (S n) \<Rightarrow> length n)"
instance
  supply [simp] = strip_nat_def unstrip_nat_def 
  by (standard;simp?)
end
interpretation strip_drop_code "TYPE(nat)" .

lemma nat_type_name[simp,code_unfold]: "type_name TYPE(nat) = STR ''nat''"
  by (simp add: strip_type_nat_def type_name_def)

text \<open>Once we have an instance, generated code will erase coercions.\<close>

value "coerce (1 :: nat) :: nat"

instantiation bool :: coercible_atom begin
definition "strip_type_bool == (\<lambda>_. T [] STR ''bool'') :: bool itself \<Rightarrow> stripped_type"
definition "strip_bool b == strip (if b then (1 :: nat)  else 0)"
definition "unstrip_bool == 
  (\<lambda>ms. case unstrip ms of 
     (Suc 0 :: nat) \<Rightarrow> True
  |  0 \<Rightarrow> False
  ) :: stripped \<Rightarrow> bool"
instance
  supply [simp] = strip_bool_def unstrip_bool_def
  by (standard;simp?)
end
interpretation strip_drop_code "TYPE(bool)" .

lemma bool_type_name[simp]: "type_name TYPE(bool) = STR ''bool''"
  by (simp add: strip_type_bool_def type_name_def)

value "coerce (True) :: bool"

instantiation prod :: (strip_type,strip_type) strip_type begin
definition "strip_type_prod == (\<lambda>_. T [strip_type TYPE('a), strip_type TYPE('b)] STR ''prod'') :: ('a \<times> 'b) itself \<Rightarrow> stripped_type"
instance ..
end

lemma prod_type_name[simp,code_unfold]: "type_name TYPE(('a::strip_type) \<times> ('b::strip_type)) = STR ''prod''"
  by (simp add: strip_type_prod_def type_name_def)

lemma same_type_prod[simp,code_unfold]: 
 "same_type (TYPE('a ::strip_type \<times> 'c ::strip_type)) (TYPE('b ::strip_type \<times> 'd ::strip_type)) 
   = (same_type TYPE('a) TYPE('b) \<and> same_type TYPE('c) TYPE('d))"
  by (simp add: strip_type_prod_def same_type_def)


text \<open>For container types, we want to produce an atom when possible, in order to
      allow for a @{class coercible_atom} instance when the element type is itself a @{class coercible_atom}.
     
     For a tuple, given two atoms we can encode the pair naturally, but if either is not an atom
     we can instead encode it as a function that takes a boolean and returns either the first or
     the second element based on the input.

     Again the choice of encoding is not important here, simply that it can be "unstripped"
     back into the same value.
 \<close>
instantiation "prod" :: (strip,strip) strip begin
definition "strip_prod \<equiv> (\<lambda>(x,y). if is_Stripped_Atom (strip x) \<and> is_Stripped_Atom (strip y) then
      strip (S[strip_atom x, strip_atom y])
 else strip (\<lambda>sx. case sx of True \<Rightarrow> strip x | False \<Rightarrow> strip y))"
instance ..
end

text \<open>Note that we need nested stripping here, first the values are stripped to give them a uniform
type, then used to define a function (taking a boolean argument) that is itself stripped.\<close>


instantiation "prod" :: (unstrip,unstrip) unstrip begin
definition "unstrip_prod \<equiv> \<lambda>x. if is_Stripped_Atom x then
    (case unstrip x of S[sx,sy] \<Rightarrow> (unstrip_atom sx, unstrip_atom sy))
    else (unstrip x True, unstrip x False)"
instance ..
end


instantiation "prod" :: (coercible,coercible) coercible begin
instance
  supply [simp] = strip_prod_def unstrip_prod_def
  by (standard;auto)
end

lemma is_stripped_prod[simp]:
  "(is_Stripped_Atom (strip (x::'a::strip, y :: 'b::strip))) = 
  (is_Stripped_Atom (strip x) \<and> is_Stripped_Atom (strip y))"
  by (auto simp add: strip_prod_def split: stripped.splits)


instantiation "prod" :: (coercible_atom,coercible_atom) coercible_atom begin
instance
  supply [simp] = strip_prod_def unstrip_prod_def
  apply standard
  by auto
end


lemma is_Stripped_Atom_prod[simp]: 
  "is_Stripped_Atom (strip x) = (is_Stripped_Atom (strip (fst x)) \<and> is_Stripped_Atom (strip (snd x)))"
  by (clarsimp simp add: strip_prod_def split: prod.splits)

lemma unstrip_strip_prod[simp]:
  "unstrip (strip (a :: 'a :: coercible, b :: 'b :: coercible)) = (unstrip (strip a), unstrip (strip b))"
  by (auto simp add: strip_prod_def unstrip_prod_def )

interpretation prod: 
  coercion "\<lambda>(x :: 'a :: coercible,y :: 'c :: coercible). 
            (coerce x :: 'b :: coercible, coerce y :: 'd :: coercible)"
  apply standard
  by (auto simp add: coerce_to_def)

value "coerce (True, 12 :: nat) :: (bool \<times> nat)"

instantiation list :: (strip_type) strip_type begin
definition "strip_type_list == (\<lambda>_. T [strip_type (TYPE('a))] STR ''list'') :: 'a list itself \<Rightarrow> stripped_type"
instance ..
end

lemma list_type_name[simp,code_unfold]: "type_name TYPE(('a::strip_type) list) = STR ''list''"
  by (simp add: strip_type_list_def type_name_def)

instantiation list :: (strip) strip begin
definition "strip_list (x :: 'a list) \<equiv> 
  let s = map strip x in
   if list_all is_Stripped_Atom s then
    strip (S (map atom s))
   else
    strip (length x, (\<lambda>idx. x ! idx))"
instance ..
end

instantiation list :: (unstrip) unstrip begin
definition "unstrip_list (x :: stripped) \<equiv> if is_Stripped_Atom x then
   (case unstrip x of S xs \<Rightarrow> (map unstrip_atom xs))
   else 
    case unstrip x of
      (len :: nat, (f :: nat \<Rightarrow> 'a)) \<Rightarrow> map (\<lambda>i. f (nat i)) [0..(int len) -1]"
instance ..
end

lemma map_nth_ident: "map (\<lambda>i. x ! nat i) [0..int (length x)-1] = x"
  apply (subst list.rel_eq[symmetric])
  apply (rule list_all2_all_nthI)
   apply simp
  apply simp
  done

instantiation list :: (coercible) coercible begin

instance
  supply [simp] = strip_list_def unstrip_list_def
  apply standard
  apply (simp add: Let_def list_all_iff comp_def)
  apply (safe intro!: map_idI)
   apply simp
  apply (simp add: map_nth_ident)
  done

end

instantiation list :: (coercible_atom) coercible_atom begin
instance
  supply [simp] = strip_list_def unstrip_list_def
  apply standard
  apply (simp add: list_all_iff)
  done
end


lemma same_type_list[simp,code_unfold]: "same_type (TYPE('a list)) (TYPE('b list)) = same_type TYPE('a::strip_type) TYPE('b::strip_type)"
  by (simp add: same_type_def strip_type_list_def)
  

lemma stripped_atom_list[simp]: 
  "(is_Stripped_Atom (strip (xs :: 'a :: strip list))) = (\<forall>x\<in>(set xs). is_Stripped_Atom (strip x))"
  by (simp add: strip_list_def list_all_iff)

lemma strip_as_map_atom[simp]: 
  "is_Stripped_Atom (strip (xs :: 'a :: strip list)) \<Longrightarrow> strip xs = Stripped_Atom (S (map strip_atom xs))"
  by (auto simp add: strip_list_def Let_def strip_atom_def)

lemma strip_atom_list_def: "is_Stripped_Atom (strip x) \<Longrightarrow> strip_atom (x :: 'a:: coercible list) = S (map strip_atom x)"
  by (auto simp add: strip_atom_def strip_list_def list_all_iff split: if_splits)

lemma unstrip_atom_list_def: 
  "unstrip_atom x = ((case x of S xs \<Rightarrow> map unstrip_atom xs) :: 'a :: coercible list)"
  by (cases x;simp add: unstrip_atom_def unstrip_list_def )

lemma unstrip_as_map_atom[simp]: 
  "is_Stripped_Atom x \<Longrightarrow> unstrip x = ((case atom x of S xs \<Rightarrow> map unstrip_atom xs) :: 'a :: coercible list)"
  by (cases x;simp add: unstrip_atom_def unstrip_list_def )


interpretation list: 
  coercion "\<lambda>(xs :: 'a :: coercible list).
            map (coerce :: 'a \<Rightarrow> 'b :: coercible) xs"
  apply standard
  apply (simp add: coerce_to_def)
  apply (clarsimp simp add: strip_list_def unstrip_list_def Let_def list_all_iff  )
  apply (subst list.rel_eq[symmetric])
  apply (rule list_all2_all_nthI;simp)
  done

value "(coerce [12 :: nat, 11]) :: nat list"

instantiation option :: (strip_type) strip_type begin
definition "strip_type_option == (\<lambda>_. T [strip_type TYPE('a)] STR ''option'') :: ('a option) itself \<Rightarrow> stripped_type"
instance ..
end

lemma option_type_name[simp,code_unfold]: "type_name TYPE(('a::strip_type) option) = STR ''option''"
  by (simp add: strip_type_option_def type_name_def)

lemma same_type_option[simp,code_unfold]: 
 "same_type (TYPE('a ::strip_type option)) (TYPE('b ::strip_type option)) 
   = (same_type TYPE('a) TYPE('b))"
  by (simp add: strip_type_option_def same_type_def)

instantiation "option" :: (strip) strip begin
definition "strip_option \<equiv> (\<lambda>mx. strip (case mx of Some x \<Rightarrow> [x] | None \<Rightarrow> []))"
instance ..
end

instantiation "option" :: (unstrip) unstrip begin
definition "unstrip_option \<equiv> \<lambda>x. case unstrip x of
    [y] \<Rightarrow> Some y
  | [] \<Rightarrow> None"
instance ..
end

instantiation option :: (coercible) coercible begin
instance
  supply [simp] = strip_option_def unstrip_option_def
  apply standard
  by (auto split: option.splits)
end

instantiation option :: (coercible_atom) coercible_atom begin
instance
  supply [simp] = strip_option_def unstrip_option_def
  apply standard
  by auto
end

interpretation option: 
  coercion "\<lambda>(xs :: 'a :: coercible option).
            map_option (coerce :: 'a \<Rightarrow> 'b :: coercible) xs"
  supply [simp] = strip_option_def unstrip_option_def
  apply standard
  by (auto simp add: coerce_to_def split: option.splits)

instantiation sum :: (strip_type,strip_type) strip_type begin
definition "strip_type_sum == (\<lambda>_. T [strip_type TYPE('a), strip_type TYPE('b)] STR ''sum'') :: ('a + 'b) itself \<Rightarrow> stripped_type"
instance ..
end

lemma sum_type_name[simp,code_unfold]: "type_name TYPE(('a::strip_type) + ('b::strip_type)) = STR ''sum''"
  by (simp add: strip_type_sum_def type_name_def)

lemma same_type_sum[simp,code_unfold]: 
 "same_type (TYPE('a ::strip_type + 'c ::strip_type)) (TYPE('b ::strip_type + 'd ::strip_type)) 
   = (same_type TYPE('a) TYPE('b) \<and> same_type TYPE('c) TYPE('d))"
  by (simp add: strip_type_sum_def same_type_def)


instantiation "sum" :: (strip,strip) strip begin
definition "strip_sum \<equiv> (\<lambda>mx. case mx of Inl x \<Rightarrow> strip (True,x) | Inr x \<Rightarrow> strip (False, x))"
instance ..
end

instantiation "sum" :: (unstrip,unstrip) unstrip begin
definition "unstrip_sum \<equiv> \<lambda>x. case unstrip x of
   (True, y) \<Rightarrow> Inl (unstrip y)
 | (False,y) \<Rightarrow> Inr (unstrip y)"
instance ..
end

instantiation "sum" :: (coercible,coercible) coercible begin
instance
  supply [simp] = strip_sum_def unstrip_sum_def
  apply standard
  apply (case_tac x)
  by (auto)
end

instantiation "sum" :: (coercible_atom,coercible_atom) coercible_atom begin
instance
  supply [simp] = strip_sum_def unstrip_sum_def
  apply standard
  apply (case_tac x)
  by auto
end

interpretation sum: 
  coercion "\<lambda>(xs :: 'a :: coercible + 'b :: coercible).
            map_sum (coerce :: 'a \<Rightarrow> 'c :: coercible) (coerce :: 'b \<Rightarrow> 'd :: coercible) xs"
  supply [simp] = strip_sum_def unstrip_sum_def
  apply standard
  subgoal for xs
    by (cases xs; auto simp add: coerce_to_def)
  done

instantiation int :: coercible_atom begin
definition "strip_type_int == (\<lambda>_. T [] STR ''int'') :: int itself \<Rightarrow> stripped_type"
definition "strip_int i == strip (i \<ge> 0, nat (abs i))"
definition "unstrip_int == 
  (\<lambda>ms. case unstrip ms of (b:: bool, n :: nat) \<Rightarrow> if b then int n else -(int n))"
instance
  supply [simp] = strip_int_def unstrip_int_def strip_atom_list_def
  by (standard;simp?)
end
interpretation strip_drop_code "TYPE(int)" .

lemma int_type_name[simp,code_unfold]: "type_name TYPE(int) = STR ''int''"
  by (simp add: strip_type_int_def type_name_def)

value "(coerce (-12 :: int)) :: int"

instantiation char :: coercible_atom begin
definition "strip_type_char == (\<lambda>_. T [] STR ''char'') :: char itself \<Rightarrow> stripped_type"
definition "strip_char c == case c of Char d0 d1 d2 d3 d4 d5 d6 d7 \<Rightarrow> strip [d0,d1,d2,d3,d4,d5,d6, d7]"
definition "unstrip_char x == case unstrip x of [d0, d1,d2,d3,d4,d5,d6,d7] \<Rightarrow> Char d0 d1 d2 d3 d4 d5 d6 d7"
instance
  supply [simp] = strip_char_def unstrip_char_def
  apply standard
  apply (case_tac x)
   apply simp
    apply (case_tac x)
  apply simp
  done
end
interpretation strip_drop_code "TYPE(char)" .

lemma char_type_name[simp,code_unfold]: "type_name TYPE(char) = STR ''char''"
  by (simp add: strip_type_char_def type_name_def)

value "(coerce ((\<lambda>x. int (x + 1)) :: nat \<Rightarrow> int) :: nat \<Rightarrow> int) 1"

text \<open>This instantiation allows for coercing first-order functions of any arity, since the
      class inference can be iteratively applied.\<close>

term "(\<lambda>x. unstrip (strip x)) 
    (f :: 'a::coercible_atom list \<Rightarrow> 'b::coercible_atom  list \<Rightarrow> int) 
      :: ('c::coercible_atom  list \<Rightarrow> 'd::coercible_atom  list \<Rightarrow> int)"

instantiation bit0 :: (_) strip_type begin
definition "strip_type_bit0 == (\<lambda>_. T [Tn (CARD('a bit0))] STR ''num'') :: 'a bit0 itself \<Rightarrow> stripped_type"
instance ..
end

lemma num_type_name0[simp]: "type_name TYPE('a bit0) = STR ''num''"
  by (simp add: strip_type_bit0_def type_name_def)

instantiation bit0 :: ("{strip_type, finite}") coercible_atom begin
definition "strip_bit0 (x :: 'a bit0) == strip (Rep_bit0 x)"
definition "unstrip_bit0 x == case unstrip x of (i :: int) \<Rightarrow> Abs_bit0 i"
instance
  supply [simp] = strip_bit0_def unstrip_bit0_def Rep_bit0_inverse
  by (standard;simp)
end
interpretation strip_drop_code "TYPE(('a::{strip_type, finite}) bit0)" .

instantiation bit1 :: (strip_type) strip_type begin
definition "strip_type_bit1 == (\<lambda>_. T [Tn (CARD('a bit1))] STR ''num'') :: 'a bit1 itself \<Rightarrow> stripped_type"
instance ..
end

lemma num_type_name1[simp,code_unfold]: "type_name TYPE(('a::strip_type) bit1) = STR ''num''"
  by (simp add: strip_type_bit1_def type_name_def)

instantiation bit1 :: ("{strip_type, finite}") coercible_atom begin
definition "strip_bit1 (x :: 'a bit1) == strip (Rep_bit1 x)"
definition "unstrip_bit1 x == case unstrip x of (i :: int) \<Rightarrow> Abs_bit1 i"
instance
  supply [simp] = strip_bit1_def unstrip_bit1_def Rep_bit1_inverse
  by (standard;simp)
end
interpretation strip_drop_code "TYPE(('a::{strip_type, finite}) bit1)" .

instantiation mod_ring :: (_) strip_type begin
definition "strip_type_mod_ring == (\<lambda>_. T [Tn (CARD('a))] STR ''mod_ring'') :: 'a mod_ring itself \<Rightarrow> stripped_type"
instance ..
end

lemma mod_ring_type_name[simp]: "type_name TYPE('a mod_ring) = STR ''mod_ring''"
  by (simp add: strip_type_mod_ring_def type_name_def)

instantiation mod_ring :: (finite) coercible_atom begin
definition "strip_mod_ring (x :: 'a mod_ring) == strip (Finite_Field.to_int_mod_ring x)"
definition "unstrip_mod_ring x == case unstrip x of (i :: int) \<Rightarrow> Finite_Field.of_int_mod_ring i"
instance
  supply [simp] = strip_mod_ring_def unstrip_mod_ring_def
  by (standard;simp)
end
interpretation strip_drop_code "TYPE(('a::finite) mod_ring)" .

instantiation fin :: (strip_type) strip_type begin
definition "strip_type_fin == (\<lambda>_. T [strip_type TYPE('a)] STR ''fin'') :: 'a fin itself \<Rightarrow> stripped_type"
instance ..
end

lemma fin_type_name[simp]: "type_name TYPE(('a::strip_type) fin) = STR ''fin''"
  by (simp add: strip_type_fin_def type_name_def)

abbreviation strip_type_from_Rep :: "String.literal \<Rightarrow> ('t \<Rightarrow> ('r :: strip_type)) \<Rightarrow> 't itself \<Rightarrow> stripped_type" where
  "strip_type_from_Rep nm _ _ \<equiv> T [strip_type (TYPE('r))] nm"


lemma strip_type_from_Rep_same[simp]: 
  "(strip_type_from_Rep nma (f :: 'ta \<Rightarrow> 'ra :: strip_type) ta = strip_type_from_Rep nmb (g :: 'tb \<Rightarrow> 'rb::strip_type) tb)
    = (nma = nmb \<and> same_type TYPE('ra) TYPE('rb))"
  apply (simp add: same_type_def )
  by meson

instantiation tyarg :: (strip_type) strip_type begin
definition "strip_type_tyarg == (\<lambda>_. T [strip_type TYPE('a)] STR ''tyarg'') :: 'a tyarg itself \<Rightarrow> stripped_type"
instance ..
end

lemma tyarg_type_name[simp]: "type_name TYPE(('a::strip_type) tyarg) = STR ''tyarg''"
  by (simp add: strip_type_tyarg_def type_name_def)

lemma tyarg_same_type[simp,code_unfold]: "same_type TYPE('a tyarg) TYPE('b tyarg) = same_type TYPE('a::strip_type) TYPE('b::strip_type)"
  by (simp add: strip_type_tyarg_def same_type_def)

primrec (nonexhaustive) index_of :: " 'a \<Rightarrow> 'a list \<Rightarrow> nat" where
   "index_of x (y # xs) = (if x = y then 0 else Suc (index_of x xs))"

lemma index_of_nth:
  "x \<in> set xs \<Longrightarrow> xs ! (index_of x xs) = x"
  by (induct xs;auto)

definition strip_enum :: "'a :: enum \<Rightarrow> stripped"  where
  "strip_enum x \<equiv> strip (index_of x enum)"

lemma strip_enum_atom[simp]: "is_Stripped_Atom (strip_enum x)"
  by (simp add: strip_enum_def)

definition unstrip_enum :: "stripped \<Rightarrow> 'a :: enum"  where
  "unstrip_enum x \<equiv> enum ! (unstrip x)"

lemma strip_unstrip_enum[simp]: "unstrip_enum (strip_enum x) = x"
  unfolding unstrip_enum_def strip_enum_def
  by (simp add: index_of_nth)

instantiation Enum.finite_1 :: coercible_atom begin
definition "strip_type_finite_1 == (\<lambda>_. T [] STR ''finite_1'') :: Enum.finite_1 itself \<Rightarrow> stripped_type"
definition "strip_finite_1 (x :: Enum.finite_1) == strip_enum x"
definition "unstrip_finite_1 x == (unstrip_enum x) :: Enum.finite_1"
instance
  apply standard
  unfolding strip_finite_1_def unstrip_finite_1_def
  by auto
end
interpretation strip_drop_code "TYPE(Enum.finite_1)" .

lemma finite_1_type_name[simp]: "type_name TYPE(Enum.finite_1) = STR ''finite_1''"
  by (simp add: strip_type_finite_1_def type_name_def)

(* it's convenient to have finite_2 coercible to bool, as it means that quickcheck will exercise
   any bool-class specific definitions *)

instantiation Enum.finite_2 :: coercible_atom begin
definition "strip_type_finite_2 == (\<lambda>_. T [] STR ''bool'') :: Enum.finite_2 itself \<Rightarrow> stripped_type"
definition "strip_finite_2 (x :: Enum.finite_2) == strip (x = 1)"
definition "unstrip_finite_2 x == (if unstrip x then 1 else 0) :: Enum.finite_2"
instance
  apply standard
  unfolding strip_finite_2_def unstrip_finite_2_def
  by auto
end
interpretation strip_drop_code "TYPE(Enum.finite_2)" .

lemma finite_2_type_name[simp]: "type_name TYPE(Enum.finite_2) = STR ''bool''"
  by (simp add: strip_type_finite_2_def type_name_def)

interpretation finite_2_to_bool: 
  coercion "\<lambda>(xs :: Enum.finite_2). xs = 1"
  apply standard
  by (simp add: unstrip_finite_2_def strip_finite_2_def)

interpretation bool_to_finite_2: 
  coercion "\<lambda>b. (of_bool b) :: Enum.finite_2"
  apply standard
  by (simp add: unstrip_finite_2_def strip_finite_2_def)

instantiation Enum.finite_3 :: coercible_atom begin
definition "strip_type_finite_3 == (\<lambda>_. T [] STR ''finite_3'') :: Enum.finite_3 itself \<Rightarrow> stripped_type"
definition "strip_finite_3 (x :: Enum.finite_3) == strip_enum x"
definition "unstrip_finite_3 x == (unstrip_enum x) :: Enum.finite_3"
instance
  apply standard
  unfolding strip_finite_3_def unstrip_finite_3_def
  by auto
end
interpretation strip_drop_code "TYPE(Enum.finite_3)" .


lemma finite_3_type_name[simp]: "type_name TYPE(Enum.finite_3) = STR ''finite_3''"
  by (simp add: strip_type_finite_3_def type_name_def)

instantiation Enum.finite_4 :: coercible_atom begin
definition "strip_type_finite_4 == (\<lambda>_. T [] STR ''finite_4'') :: Enum.finite_4 itself \<Rightarrow> stripped_type"
definition "strip_finite_4 (x :: Enum.finite_4) == strip_enum x"
definition "unstrip_finite_4 x == (unstrip_enum x) :: Enum.finite_4"
instance
  apply standard
  unfolding strip_finite_4_def unstrip_finite_4_def
  by auto
end
interpretation strip_drop_code "TYPE(Enum.finite_4)" .

lemma finite_4_type_name[simp]: "type_name TYPE(Enum.finite_4) = STR ''finite_4''"
  by (simp add: strip_type_finite_4_def type_name_def)

instantiation Enum.finite_5 :: coercible_atom begin
definition "strip_type_finite_5 == (\<lambda>_. T [] STR ''finite_5'') :: Enum.finite_5 itself \<Rightarrow> stripped_type"
definition "strip_finite_5 (x :: Enum.finite_5) == strip_enum x"
definition "unstrip_finite_5 x == (unstrip_enum x) :: Enum.finite_5"
instance
  apply standard
  unfolding strip_finite_5_def unstrip_finite_5_def
  by auto
end
interpretation strip_drop_code "TYPE(Enum.finite_5)" .

lemma finite_5_type_name[simp]: "type_name TYPE(Enum.finite_5) = STR ''finite_5''"
  by (simp add: strip_type_finite_5_def type_name_def)

instantiation num1 :: coercible_atom begin
definition "strip_type_num1 == (\<lambda>_. T [Tn 1] STR ''num'') :: num1 itself \<Rightarrow> stripped_type"
definition "strip_num1 (x :: num1) == strip (1 :: nat)"
definition "unstrip_num1 (x :: stripped) == (1 :: num1)"
instance
  apply standard
  unfolding strip_num1_def unstrip_num1_def
  by auto
end
interpretation strip_drop_code "TYPE(num1)" .

lemma not_same_type_prodL[simp,code_unfold]: "\<not> same_type TYPE('a::strip_type) TYPE('a \<times> ('b::strip_type))"
  apply (simp add: same_type_def strip_type_prod_def)
  apply (insert strip_type_nonrec[where 'a='a])
  apply (cases "strip_type TYPE('a)";simp)
  by (metis list.set_intros(1))

lemma not_same_type_prodR[simp,code_unfold]: "\<not> same_type TYPE('b::strip_type) TYPE(('a::strip_type) \<times> 'b)"
  apply (simp add: same_type_def strip_type_prod_def)
  apply (insert strip_type_nonrec[where 'a='b])
  apply (cases "strip_type TYPE('b)";simp)
  by (metis list.set_intros)

lemma not_same_type_sumL[simp,code_unfold]: "\<not> same_type TYPE('a::strip_type) TYPE('a + ('b::strip_type))"
  apply (simp add: same_type_def strip_type_sum_def)
  apply (insert strip_type_nonrec[where 'a='a])
  apply (cases "strip_type TYPE('a)";simp)
  by (metis list.set_intros(1))

lemma not_same_type_sumR[simp,code_unfold]: "\<not> same_type TYPE('b::strip_type) TYPE(('a::strip_type) + 'b)"
  apply (simp add: same_type_def strip_type_sum_def)
  apply (insert strip_type_nonrec[where 'a='b])
  apply (cases "strip_type TYPE('b)";simp)
  by (metis list.set_intros)

lemma not_same_type_fun_arg[simp,code_unfold]: "\<not> same_type TYPE('a::strip_type) TYPE('a \<Rightarrow> ('b::strip_type))"
  apply (simp add: same_type_def strip_type_fun_def)
  apply (insert strip_type_nonrec[where 'a='a])
  apply (cases "strip_type TYPE('a)";simp)
  by (metis list.set_intros(1))

lemma not_same_type_fun_ret[simp,code_unfold]: "\<not> same_type TYPE('b::strip_type) TYPE(('a::strip_type) \<Rightarrow> 'b)"
  apply (simp add: same_type_def strip_type_fun_def)
  apply (insert strip_type_nonrec[where 'a='b])
  apply (cases "strip_type TYPE('b)";simp)
  by (metis list.set_intros)

lemma not_same_type_list[simp,code_unfold]: "\<not> same_type TYPE('a::strip_type) TYPE('a list)"
  apply (simp add: same_type_def strip_type_list_def)
  apply (insert strip_type_nonrec[where 'a='a])
  apply (cases "strip_type TYPE('a)";simp)
  by (metis list.set_intros(1))

lemma not_same_type_option[simp,code_unfold]: "\<not> same_type TYPE('a::strip_type) TYPE('a option)"
  apply (simp add: same_type_def strip_type_option_def)
  apply (insert strip_type_nonrec[where 'a='a])
  apply (cases "strip_type TYPE('a)";simp)
  by (metis list.set_intros(1))

lemma not_same_type_sym: "\<not> same_type TYPE('a::strip_type) TYPE('b::strip_type) \<Longrightarrow> 
                          \<not> same_type TYPE('b::strip_type) TYPE('a::strip_type)"
  using same_type_sym by blast

lemmas [THEN not_same_type_sym, simp, code_unfold] = 
        not_same_type_prodL not_same_type_prodR
        not_same_type_sumL not_same_type_sumR
        not_same_type_fun_arg not_same_type_fun_ret
        not_same_type_list not_same_type_option


end