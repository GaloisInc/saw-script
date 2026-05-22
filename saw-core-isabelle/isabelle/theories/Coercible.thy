(* Supporting basic coercions by collapsing values into a uniform datatype.
   The intention here is that we should be able to coerce equivalently-sized
   types by collapsing and rebuilding them *)

theory Coercible
  imports Main
begin

section \<open>Stripping and unstripping: collapsing types into a common base\<close>

text \<open>Stripped Types: This represents a type constructor that has been stripped of the
      specific type used as a type-level natural number. This can be thought of as a quotient
      over the "typerep" class, where types used as type-level naturals are in the
      are in the same equivalence class if they represent the same natural number.

      Specifically, the types "1+1 word" and "2 word" would have equal stripped_type representations.

      These are used later to guard coercions, in order to specifically result in an invalid
      (undefined) result if a coercion is attempted between incompatible types.
}\<close>
datatype stripped_type = Tn nat | T "stripped_type list" "String.literal"

class strip_type = fixes strip_type :: "'a itself \<Rightarrow> stripped_type" begin
lemma strip_type_nonrec: 
  "case strip_type TYPE('a) of
          Tn _ \<Rightarrow> True
        | T ts _ \<Rightarrow> \<forall>t\<in>(set ts). t \<noteq> strip_type TYPE('a)"
  apply (induct rule: stripped_type.induct; simp)
  by fastforce
end

definition type_name :: "('a::strip_type) itself \<Rightarrow> String.literal" where
  "type_name _ \<equiv> case strip_type TYPE('a) of T _ nm \<Rightarrow> nm"

definition same_type :: "'a :: strip_type itself \<Rightarrow> 'b :: strip_type itself \<Rightarrow> bool" where
  "same_type a b \<equiv> strip_type a = strip_type b"

lemma type_name_neq_not_same_type[simp,code_unfold]:
  "type_name TYPE('a::strip_type) \<noteq> type_name TYPE('b::strip_type) \<Longrightarrow> \<not>same_type TYPE('a) TYPE('b)"
  apply (simp add: same_type_def type_name_def)
  by fastforce

lemma same_type_sym[sym,simp,code_unfold]: "same_type a b \<Longrightarrow> same_type b a"
  by (simp add: same_type_def)

lemma same_type_refl[simp,code_unfold]: "same_type a a"
  by (simp add: same_type_def)

text \<open>Stripped atomic values. Rather than including constructors for various base types,
      this representation is intentionally bare, as we can instead build these fairly easily
      from this single constructor, and it simplifies some of the reasoning later.

      This is treated as a "universal" type, which has no internal structure, and so projecting
      values back out requires that we know the source type. The encoding of each type is not 
      particularly significant, only that it can be reversed without information loss.

      We don't need to worry about overlapping encodings for different types, 
      since coercions will be guarded by @{term same_type}. This ensures, for example, that
      even if @{term "0 :: nat"} and @{term "False"} have the same "stripped_atom" representation,
      attempting to coerce @{term "0 :: nat"} into a boolean is still undefined.


   \<close>

datatype stripped_atom = 
      S "stripped_atom list"


text \<open>Stripped values. A stripped atom is essentially a value of any countable type. To include
      first-order functions, we define stripped values to also include functions from atoms
      to stripped values.
\<close>
datatype stripped = Stripped_Atom (atom: stripped_atom)
    (* we need to distinguish atoms for this case, since
       we can't have 'stripped \<Rightarrow> stripped' in a datatype *)
  | Stripped_Fn "(stripped_atom \<Rightarrow> stripped)"

class strip =  fixes strip :: "'a \<Rightarrow> stripped"
class unstrip = fixes unstrip :: "stripped \<Rightarrow> 'a"

subsection \<open>Combining @{const strip} and @{const unstrip} into coercions.\<close>

consts print_integer :: "integer \<Rightarrow> String.literal"

code_printing constant print_integer \<rightharpoonup>
 (SML) "IntInf.toString"

definition print_int :: "int \<Rightarrow> String.literal" where
  "print_int i \<equiv> print_integer (integer_of_int i)"

fun print_type :: "stripped_type \<Rightarrow> String.literal" 
  and print_types :: "stripped_type list \<Rightarrow> String.literal"
  where
    "print_type (T [] nm) = nm"
  | "print_type (T ts nm) = STR ''('' + print_types ts + STR '') '' + nm"
  | "print_type (Tn n) = print_int (int n)"
  | "print_types (t # t2 # ts) = print_type t + STR '','' + print_types (t2#ts)"
  | "print_types [t] =  print_type t"
  | "print_types [] = STR '''' "

definition error_message :: "String.literal \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "error_message _ x \<equiv> x ()"

declare [[code drop: error_message]]

code_printing 
    constant error_message \<rightharpoonup> (SML) "(fn '_ => (raise/ Fail/ _))"
  | constant error_message \<rightharpoonup> (Eval) "(fn '_ => (raise/ Fail/ _))"

text \<open>This generates a useful error message for generated code that contains invalid coercions.\<close>

consts invalid_coercion :: "'a itself \<Rightarrow> 'b itself \<Rightarrow> 'c"

overloading invalid_coercion1 \<equiv> "invalid_coercion :: 'a :: strip_type itself \<Rightarrow> 'b :: strip_type itself \<Rightarrow> 'c" begin
definition "invalid_coercion1 \<equiv> (\<lambda>(_ :: 'a :: strip_type itself) (_ :: 'b :: strip_type itself). 
  error_message (STR ''invalid coercion: '' + print_type (strip_type(TYPE('a))) + STR '' =/=> '' + print_type (strip_type(TYPE('b)))) (\<lambda>_. undefined))"
end

consts coerce_to :: "'a itself \<Rightarrow> 'b \<Rightarrow> 'a"

overloading coerce_to1 \<equiv> "coerce_to :: 'a :: {strip_type, unstrip} itself \<Rightarrow> 'b :: {strip_type, strip} \<Rightarrow> 'a" begin
definition "coerce_to1 (_ :: 'a :: {strip_type, unstrip} itself) \<equiv> 
  if same_type TYPE('a) TYPE('b:: {strip_type, strip}) then
  ((\<lambda>x. unstrip (strip x)) :: 'b \<Rightarrow> 'a)
  else (\<lambda>_. invalid_coercion TYPE('b) TYPE('a) )"
end
lemmas coerce_to_def = coerce_to1_def

abbreviation (input) coerce :: "'a \<Rightarrow> 'b" where
  "coerce \<equiv> coerce_to (TYPE('b))"


instantiation stripped_atom :: strip begin
definition "strip_stripped_atom \<equiv> Stripped_Atom"
instance ..
end

declare strip_stripped_atom_def[simp]

instantiation stripped_atom :: unstrip begin
definition "unstrip_stripped_atom (x :: stripped) \<equiv> atom x"
instance ..
end

declare unstrip_stripped_atom_def[simp]

instantiation stripped :: strip begin
definition "strip_stripped \<equiv> (\<lambda>(x :: stripped). x)"
instance ..
end

declare strip_stripped_def[simp]

instantiation stripped :: unstrip begin
definition "unstrip_stripped \<equiv> (\<lambda>(x :: stripped). x)"
instance ..
end

declare unstrip_stripped_def[simp]

definition unstrip_atom :: "stripped_atom \<Rightarrow> 'a :: unstrip" where
  "unstrip_atom \<equiv> \<lambda>x. unstrip (Stripped_Atom x)"


definition strip_atom :: "'a :: strip \<Rightarrow> stripped_atom" where
  "strip_atom \<equiv> \<lambda>x. atom (strip x)"

text \<open>A value of a coercible type can be stripped and then unstripped back into the same value.
      Notably unstripping is always partial, since an arbitrary stripped value cannot be
      (reliably) unstripped back into an arbitrary type. \<close>
class coercible = strip + unstrip + strip_type +
assumes strip_unstrip[simp]: "\<And>(x :: 'a). unstrip (strip x) = x"

(* heterogenous equality *)
definition heq :: "('a ::strip_type) \<Rightarrow> ('b :: strip_type) \<Rightarrow> bool" (infixr "?=?" 100) where
  "heq a b \<equiv> same_type TYPE('a) TYPE('b) \<and> (coerce a = b)"

lemma heq_same_type[simp]: "(x :: 'a :: coercible) ?=? (y :: 'b :: coercible) \<Longrightarrow> same_type TYPE('a) TYPE('b)"
  by (simp add: heq_def)

lemma heq_refl[simp]: "(a :: 'a :: coercible) ?=? (a :: 'a :: coercible)"
  by (simp add: heq_def coerce_to_def)

lemma heq_coerce[simp]: "x ?=? y \<Longrightarrow> coerce x = y"
  by (simp only: heq_def)


text \<open>Atomic coercible types are a restriction of coercible types, where we know that
      stripping results in an atom. This can be satisfied (given an appropriate encoding) for
      any countable type.\<close>

class coercible_atom = coercible + 
  assumes strip_is_atom[simp]: 
    "\<And>(x :: 'a). is_Stripped_Atom (strip (x :: 'a))"

lemma is_stripped_unstrip[simp]: "is_Stripped_Atom x \<Longrightarrow> unstrip_atom (atom x) = unstrip x"
  by (cases x;simp add: unstrip_atom_def)

text \<open>These allow us to treat @{typ stripped} and @{typ stripped_atom} uniformly.\<close>

instantiation stripped_atom :: coercible_atom begin
definition "strip_type_stripped_atom == (\<lambda>_. T [] STR ''stripped_atom'') :: stripped_atom itself \<Rightarrow> stripped_type"
instance
  apply (standard;clarsimp)
  done
end

lemma stripped_atom_type_name[simp]: "type_name TYPE(stripped_atom) = STR ''stripped_atom''"
  by (simp add: strip_type_stripped_atom_def type_name_def)

instantiation stripped :: coercible begin
definition "strip_type_stripped == (\<lambda>_. T [] STR ''strip_type_stripped'') :: stripped itself \<Rightarrow> stripped_type"
instance
  apply (standard;simp)
  done
end

lemma stripped_type_name[simp]: "type_name TYPE(stripped) = STR ''strip_type_stripped''"
  by (simp add: strip_type_stripped_def type_name_def)

lemma unstrip_atom_ident[simp]: "unstrip_atom = id"
  apply (rule ext)
  by (simp add: unstrip_atom_def)

lemma strip_atom_unfold: "is_Stripped_Atom (strip x) \<Longrightarrow> Stripped_Atom (strip_atom (x :: 'a :: coercible)) = strip x"
  by (cases "strip x";simp add: strip_atom_def)

lemma unstrip_atom_idem[simp]: "is_Stripped_Atom (strip x) \<Longrightarrow> (unstrip_atom (strip_atom (x :: 'a :: coercible))) = (unstrip (strip x))"
  apply (subst strip_atom_def unstrip_atom_def)+
  apply (subst strip_atom_unfold[symmetric])
  apply (simp)
  apply (simp add: strip_atom_unfold)
  done

lemma unstrip_strip_map[simp]:
  "\<forall>(x :: 'a :: coercible)\<in>(set xs). is_Stripped_Atom (strip x) \<Longrightarrow> map (\<lambda>x. unstrip_atom (strip_atom x)) xs = xs"
  by (simp add: list.map_ident_strong)


lemma stripped_atom_strip[simp]: "is_Stripped_Atom (strip (x :: stripped)) = is_Stripped_Atom x"
  by (simp)

declare strip_atom_unfold[simp]

lemma unstrip_comp_idem[simp]: "(unstrip \<circ> strip) = (id :: 'a :: coercible \<Rightarrow> 'a)" 
  apply (rule ext)
  apply simp
  done  

lemma unstrip_atom_comp_idem[simp]: "(unstrip_atom \<circ> strip_atom) = (id :: 'a :: coercible_atom \<Rightarrow> 'a)"
  apply (rule ext)
  apply simp
  done

lemma unstrip_rev_def : "(\<exists>y. x = Stripped_Atom y) \<Longrightarrow> (unstrip x :: 'a :: coercible_atom) = unstrip_atom (atom x)"
  apply (simp add: unstrip_atom_def )
  apply (cases x;simp)
  done

lemma strip_is_atom_ex[simp]: "\<exists>y. strip (x :: 'a :: coercible_atom) = Stripped_Atom y"
  apply (insert strip_is_atom[of x])
  apply (cases "strip x";simp)
  done


lemma strip_rev_def : "strip (x :: 'a :: coercible_atom) = Stripped_Atom (strip_atom x)"
  by simp

lemma unstrip_ident[simp]: "unstrip = id"
  apply (rule ext)
  by simp


text \<open>This locale puts it all together by allowing us to provide interpretations of
      coercions between compatible types.
      For base types this is trivially satisified (e.g. we can always coerce a nat to a nat as a 
      no-op).

     For bnfs it will just be mapping the coercion over the elements, and types that are parameterized
     over type-level naturals (e.g. words) will require type-specific interpretations
     (e.g. coerce :: 'a word \<Rightarrow> 'b word = ucast).
\<close>

(*
primrec coerce_exec :: "bool \<Rightarrow> 'a \<Rightarrow> (unit \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "coerce_exec True x _ = x"
| "coerce_exec False _ y = y ()"

declare coerce_exec.simps[code_unfold]
*)

definition coerce_guard :: "('a :: coercible \<Rightarrow> 'b :: coercible) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "coerce_guard f x \<equiv> (if (same_type TYPE('a) TYPE('b)) then (f x) else (invalid_coercion TYPE('a) TYPE('b)))"

lemma coerce_guard_unfold_valid[code_unfold]:
  "same_type TYPE('a) TYPE('b) \<Longrightarrow> 
    coerce_guard (f :: 'a ::coercible \<Rightarrow> 'b :: coercible) = f"
  unfolding coerce_guard_def
  by simp

lemma coerce_guard_unfold_invalid[code_unfold]:
  "\<not> same_type TYPE('a) TYPE('b) \<Longrightarrow> 
    coerce_guard (f :: 'a ::coercible \<Rightarrow> 'b :: coercible) = (\<lambda>_. invalid_coercion TYPE('a) TYPE('b))"
  unfolding coerce_guard_def
  by simp

locale coercion =
  fixes f :: "'a :: coercible \<Rightarrow> 'b :: coercible"
  assumes coerce_ident[simp]: "\<And>(x :: 'a). same_type (TYPE('a)) (TYPE('b)) \<Longrightarrow> unstrip (strip x) = f x" 
begin

lemma coerce[simp]: "\<And>x. same_type TYPE('a) TYPE('b) \<Longrightarrow> coerce x = f x"
  by (auto simp add: coerce_to1_def)

lemma coerce_exec[code_unfold]:
   "coerce_to TYPE('b) = coerce_guard f"
  apply (rule ext)
  by (clarsimp simp add: coerce_to1_def coerce_guard_def)

declare [[code abort: "strip :: 'a \<Rightarrow> stripped"]]
declare [[code abort: "strip :: 'b \<Rightarrow> stripped"]]
declare [[code abort: "unstrip :: stripped \<Rightarrow> 'a"]]
declare [[code abort: "unstrip :: stripped \<Rightarrow> 'b"]]

context begin
private lemma is_coerce: "\<And>x y. same_type TYPE('a) TYPE('b) \<Longrightarrow> (f x = y) \<Longrightarrow> (coerce x = y)"
  using coerce by blast

lemma heqD[dest]: "x ?=? y \<Longrightarrow> (f x = y \<and> same_type TYPE('a) TYPE('b)) "
  by (metis is_coerce heq_def)

lemma heqI[intro]: "same_type TYPE('a) TYPE('b) \<Longrightarrow> f x = y \<Longrightarrow> x ?=? y"
  using heq_def is_coerce by blast
end

end

lemma coerce_invalid[simp,code_unfold]: "\<not> same_type TYPE('a::{strip_type,strip}) TYPE('b::{strip_type,unstrip}) \<Longrightarrow> 
   (coerce (x :: 'a) :: 'b) = 
  invalid_coercion TYPE('a) TYPE('b)"
  by (auto simp add: coerce_to1_def same_type_def)

interpretation id: coercion "\<lambda>x. x"
  apply standard
   apply simp+
  done

lemma coerce_refl[simp,code_unfold]: "(coerce :: ('a :: coercible \<Rightarrow> 'a)) = id"
  apply (rule ext)
  by simp

lemmas record_raw_defs = 
                  Record.iso_tuple_snd_def Record.iso_tuple_fst_def
                  Record.tuple_iso_tuple_def Record.iso_tuple_cons_def

lemma abs_rep_to_record: "Abs (Rep x) = x \<Longrightarrow> 
  Record.iso_tuple_cons
          (tuple_isomorphism.Tuple_Isomorphism
            Rep Abs)
          (Record.iso_tuple_fst
            (tuple_isomorphism.Tuple_Isomorphism
              Rep Abs)
            x)
          (Record.iso_tuple_snd
            (tuple_isomorphism.Tuple_Isomorphism
              Rep Abs)
            x) =
         x"
  by (simp add: iso_tuple_cons_def
      iso_tuple_fst_def iso_tuple_snd_def)
end