(* 
    Author:     Daniel Matichuk
*)
theory Cryptol_Syntax
  
  imports Main Alt_Type_Length Seq Coercible_Insts Word_Insts Type_Predicate Type_Args
          WordSeq Cryptol_Definition "Word_Lib.Word_Syntax" "HOL-Library.Product_Plus"
          Log2 Cryptol_Quickcheck

begin

instantiation unit :: zero begin
definition "zero_unit \<equiv> ()"
instance ..
end

text \<open>
Check that all constants present in a given theorem are fully polymorphic with respect
to their primitive definition.

Specifically each constant in the theorem (excepting skipped consts) must satisfy the following requirements:
  1) Has at most one definition
  2) Primitive definition is of the form @{term "C \<equiv> \<lambda>x. B x"} for constant C.
  3) Appears in the theorem with the same type signature as in its definition.

If any constants fail these requirements, the attribute throws an error. Additionally, if any
constant has zero definitions (i.e. declared, but not defined) then the result is a dummy fact.

This is used as part of the scheme to support recursive functions in the Cryptol translation.
The underlying implementation of the recursive function is supplied via overloading, and this
attribute is attached to the definition within the locale specific to that function
(see "../tests/isabelle/Recursion.thy").

This enforces the policy that the definition of the recursive call may only be used once an implementation
has been provided, and that implementation has been proven to be consistent with respect to the Cryptol specification.

\<close>

attribute_setup export_global = \<open>
let
  val skipped = [@{const_name HOL.eq}, @{const_name HOL.Trueprop}, @{const_name Pure.type}
                , @{const_name tyargCtr}, @{const_name assuming}]

  fun consts_of thm = Term.add_consts (Thm.full_prop_of thm) []

  fun check_spec ctxt (nm,T) = if member (op =) skipped nm then true else
    let
      val thy = Proof_Context.theory_of ctxt
      val tsig = Sign.tsig_of thy
      val consts = Sign.consts_of thy
      val lhsT = Consts.type_scheme consts
      val defs = Theory.defs_of thy
      in case Defs.specifications_of defs (Defs.Const,nm) of
         (_::_::_) => error ("More than one specification for: " ^ nm)
         (* NOTE: We need to admit the case where there are zero specifications so that
            this check passes before any overloading has taken place. *)
       | [] => false
       | [spec] =>
         let
            val def = case #def spec of
              SOME def => def
            | NONE => error ("No definition found for: " ^ nm)
            val def_thm = Thm.axiom thy def
            fun def_err () = error ("Unexpected definition: " ^ Thm.string_of_thm_global thy def_thm)

            val lhsT = case Logic.dest_equals (Thm.prop_of def_thm) of
              (Const (nm',T'),_) => if nm' = nm then T' else def_err ()
             | _ => def_err ()
            val morph = Local_Theory.standard_morphism_theory ctxt

            val T' = Term.strip_sortsT (Morphism.typ morph T)

            in case Type.raw_equiv (T',Term.strip_sortsT lhsT) of
              true => true
            | false => error ("Fact is not fully polymorphic in constant: " ^ nm ^
                              "\nIn Theorem: " ^ Syntax.string_of_typ ctxt T' ^
                              "\nIn Definition: " ^ Syntax.string_of_typ_global thy lhsT)
            end
      end

  fun check_all_specs ctxt thm =
    let
      val all_defined = List.all (check_spec ctxt) (consts_of thm)
    in if all_defined then thm else Drule.dummy_thm
    end


in Scan.succeed (Thm.mixed_attribute
    (fn (context,thm) => (context, check_all_specs (Context.proof_of context) thm)))
end\<close>

(* Used to avoid issues with "mod_ring" requiring "nontriv" for its
   "one" class instance, which the "power" class requires.
   Instead we translate "power" into "alt_power" which has no constraints,
   and thus "cryptol_ring" can be relaxed to not require a "power" instance.

   Then "mod_ring" can be a "cryptol_ring" instance with only a "finite"
   constraint (rather than "nontriv").
*)

class cryptol_ring = ring + from_to_int + coercible_atom + power
class cryptol_integral = integral + cryptol_ring + numeral

instance int :: cryptol_integral by (standard;simp)
instance seq :: (_,bool) cryptol_integral ..
instance mod_ring :: (finite) cryptol_ring ..
instance mod_ring :: (prime_card) cryptol_integral ..

(*
From Cryptol.TypeCheck.Solver

nLenFromThenTo :: Nat' -> Nat' -> Nat' -> Maybe Nat'
nLenFromThenTo (Nat x) (Nat y) (Nat z)
  | step /= 0 = let len = div dist step + 1
                in Just $ Nat $ if x > y
                                  -- decreasing
                                  then (if z > x then 0 else len)
                                  -- increasing
                                  else (if z < x then 0 else len)
  where
  step = abs (x - y)
  dist = abs (x - z)
*)

definition nLenFromThenTo :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"nLenFromThenTo x y z \<equiv> 
   nat 
  (let
    step = abs (x - y);
    dist = abs (x - z)
  in if step = 0 then (undefined) else
      let len = (dist div step) + 1
      in if x > y then (if z > x then 0 else len)
      else (if z < x then 0 else len))"

datatype ('x, 'y, 'z) FromThenTo = FromThenToTypeCtr

instantiation FromThenTo :: (_,_,_) len0 begin
definition len_of_FromThenTo :: "('a,'b,'c) FromThenTo itself \<Rightarrow> nat" where
"len_of_FromThenTo _ \<equiv> nLenFromThenTo LEN('a) LEN('b) LEN('c)"
instance ..
end

lemma FromThenTo_simps[simp]:
  "LEN('x) < LEN('y) \<Longrightarrow> LEN('x) < LEN('z) \<Longrightarrow> LENGTH (('x,'y,'z) FromThenTo) = ((LEN('z) - LEN('x)) div (LEN('y) - LEN('x))) + 1"
  "LEN('x) < LEN('y) \<Longrightarrow> LEN('z) < LEN('x) \<Longrightarrow> LENGTH (('x,'y,'z) FromThenTo) = 0"

  "LEN('y) < LEN('x) \<Longrightarrow> LEN('x) < LEN('z) \<Longrightarrow> LENGTH (('x,'y,'z) FromThenTo) = 0"
  "LEN('y) < LEN('x) \<Longrightarrow> LEN('z) < LEN('x) \<Longrightarrow> LENGTH (('x,'y,'z) FromThenTo) = ((LEN('x) - LEN('z)) div (LEN('x) - LEN('y))) + 1"

  "LEN('x) \<noteq> LEN('y) \<Longrightarrow> LEN('z) = LEN('x) \<Longrightarrow> LENGTH (('x,'y,'z) FromThenTo) = 1"
  by (auto simp add: len_of_FromThenTo_def nLenFromThenTo_def Let_def 
                     div_int_pos_iff nat_add_distrib nat_div_as_int)


instantiation len :: (strip_type) strip_type begin
definition "strip_type_len == (\<lambda>_. T [strip_type TYPE('a)] STR ''len'') :: 'a len itself \<Rightarrow> stripped_type"
instance ..
end

instantiation len :: (len2) len2 begin
instance
  apply standard
  using len2_class.nontriv by force
end

instantiation "fun" :: (_,zero) zero begin
definition "zero_fun \<equiv> \<lambda>_. 0"
instance ..
end

(* cryptol indexing is undefined for negative values, so we use pos_nat here *)
abbreviation (input) selects :: "('a,'e) seq \<Rightarrow> ('b,'idx :: integral) seq \<Rightarrow> ('b,'e) seq"  where
  "selects s1 s2 \<equiv> selects_seq s1 (map_seq (\<lambda>idx. pos_nat idx) s2)"

abbreviation (input) selects_end :: "('a,'e) seq \<Rightarrow> ('b,'idx :: integral) seq \<Rightarrow> ('b,'e) seq"  where
  "selects_end s1 s2 \<equiv> selects_end_seq s1 (map_seq (\<lambda>idx. pos_nat idx) s2)"

(*
consts to_int_mod_ring' :: "'a mod_ring \<Rightarrow> int"

overloading to_int_mod_ring1 \<equiv> "to_int_mod_ring' :: 'a :: finite mod_ring \<Rightarrow> int" begin
definition "to_int_mod_ring1 \<equiv> to_int_mod_ring :: 'a :: finite mod_ring \<Rightarrow> int"
end
*)

context includes seq_syntax and type_arg_syntax begin

(* undefined/unsupported *)
cryptol_definition infFromThen :: "{'a} ('b \<Rightarrow> 'a)"


(* we'll leave these as definitions (aliased in the translation bundle) since keeping the
   type arguments around is likely preferable *)

cryptol_definition groupBy :: "{'each,'parts,'a} ['parts * 'each]'a \<Rightarrow> ['parts]['each]'a" where
  "groupBy x \<equiv> group_seq x"

abbreviation (input) split :: "{'parts,'each,'a} ['parts * 'each]'a \<Rightarrow> ['parts]['each]'a" where
  "split parts each a \<equiv> groupBy each parts a"

cryptol_definition join' :: "{'parts, 'each, 'a} ['parts]['each]'a \<Rightarrow> ['parts \<times> 'each]'a" where
  "join' s \<equiv> (concat_seq s :: ['parts \<times> 'each]'a)"

cryptol_definition drop' :: "{'front, 'back, 'a} ['front + 'back]'a \<Rightarrow> ['back]'a" where
  "drop' s \<equiv> drop_seq' s"

cryptol_definition take' :: "{'front, 'back, 'a} ['front + 'back]'a \<Rightarrow> ['front]'a" where
  "take' s \<equiv> (take_seq s :: ['front]'a)"

cryptol_definition number :: "{'a,('b :: from_to_int)} 'b" where
  "number \<equiv> (from_int (int (LEN('a))) :: 'b)"

cryptol_definition fromToLessThan :: "{'lo,'hi,'a::integral} ['hi - 'lo]'a" where
  "fromToLessThan \<equiv> (map_seq (\<lambda>x. from_nat (x + LEN('lo))) upto_seq :: ['hi - 'lo]'a)"

cryptol_definition fromTo :: "{'lo, 'hi, 'e} ((('hi - 'lo) + 1,('e::integral)) seq)" where
  "fromTo \<equiv> (map_seq (\<lambda>x. from_nat (x + LEN('lo))) upto_seq :: [('hi - 'lo)+1]'e)"

lemma fromTo_def2:
  "LEN('lo) \<le> LEN('hi) \<Longrightarrow> fromTo`{'lo,'hi,'a} = coerce_seq_len (fromToLessThan`{'lo,'hi+1,'a::integral})"
  unfolding fromToLessThan_def fromTo_def
  by simp

cryptol_definition zext :: "{'m,'n} ['n] \<Rightarrow> ['m]" where
  "zext xs \<equiv> (zext_seq xs :: ['m])"

cryptol_definition sext :: "{'m,'n} ['n] \<Rightarrow> ['m]" where
  "sext xs \<equiv> (sext_seq xs :: ['m])"

cryptol_definition splitAt :: "{'front,'back,'a} ['front + 'back]'a \<Rightarrow> (['front]'a \<times> ['back]'a)" where
  "splitAt xs \<equiv> (take'`{'front,'back,'a} xs, drop'`{'front,'back,'a} xs)"

cryptol_definition fromThenTo :: "{'first,'next,'last,'a::integral,'length} ['length]'a" where
  "fromThenTo \<equiv> (map_seq (\<lambda>x. from_int (((int (LEN('next)) - int (LEN('first))) * x) + LEN('first))) upto_seq :: ['length]'a)"

named_theorems cryptol_prim_defs

lemmas [cryptol_prim_defs] =
  groupBy_def
  Cryptol_Syntax.join'_def Cryptol_Syntax.drop'_def Cryptol_Syntax.take'_def
  Cryptol_Syntax.number_def fromToLessThan_def
  zip_seq_mismatched_def2 fromTo_def zext_def sext_def splitAt_def
  fromThenTo_def

cryptol_definition undefined' :: "{'a} 'a"

end


locale translation begin

context includes type_arg_syntax and seq_syntax begin

qualified abbreviation length :: "{'n,'a,'ix::integral} ['n]'a \<Rightarrow> 'ix" where
  "length _ _ _ \<equiv> (\<lambda>_. from_nat LEN('n))"

qualified abbreviation "and" :: "{'n} ['n] \<Rightarrow> bool" where
  "and _ w \<equiv> all_seq (\<lambda>x. x) w"

qualified abbreviation "or" :: "{'n} ['n] \<Rightarrow> bool" where
  "or _ w \<equiv> any_seq (\<lambda>x. x) w"

qualified abbreviation carry :: "{'n} ['n] \<Rightarrow> ['n] \<Rightarrow> bool" where
  "carry _ x \<equiv> carry_seq x"

qualified abbreviation scarry :: "{'n} ['n] \<Rightarrow> ['n] \<Rightarrow> bool" where
  "scarry _ x \<equiv> scarry_seq x"

qualified abbreviation sborrow :: "{'n} ['n] \<Rightarrow> ['n] \<Rightarrow> bool" where
  "sborrow _ x \<equiv> sborrow_seq x"

qualified abbreviation scanl :: "{'n,'b, 'a} ('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ['n]'a \<Rightarrow> [1 + 'n]'b" where
  "scanl _ _ _ f b xs \<equiv> scanl_seq f b xs"

qualified abbreviation scanr :: "{'n,'a, 'b} ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ['n]'a \<Rightarrow> [1 + 'n]'b" where
  "scanr _ _ _ f b xs \<equiv> scanr_seq f b xs"

qualified abbreviation sum :: "{'n,('a::ring)} ['n]'a \<Rightarrow> 'a" where
  "sum _ _ xs \<equiv> sum_seq xs"

qualified abbreviation product :: "{'n,('a::{ring,one})} ['n]'a \<Rightarrow> 'a" where
  "product _ _ xs \<equiv> prod_seq xs"

qualified abbreviation update :: "{'n,'a,'ix::integral} ['n]'a \<Rightarrow> 'ix \<Rightarrow> 'a \<Rightarrow> ['n]'a" where
  "update _ _ _ xs ix a \<equiv> seq_update xs (pos_nat ix) a"

qualified abbreviation updateEnd :: "{'n,'a,'ix::integral} ['n]'a \<Rightarrow> 'ix \<Rightarrow> 'a \<Rightarrow> ['n]'a" where
  "updateEnd _ _ _ xs ix a \<equiv> seq_update_end xs (pos_nat ix) a"

qualified abbreviation updates :: "{'n,'k,'ix::integral,'a} ['n]'a \<Rightarrow> ['k]'ix \<Rightarrow> ['k]'a \<Rightarrow> ['n]'a" where
  "updates _ _ _ _ xs ixs a \<equiv> seq_updates xs (map_seq pos_nat ixs) a"

qualified abbreviation updatesEnd :: "{'n,'k,'ix::integral,'a} ['n]'a \<Rightarrow> ['k]'ix \<Rightarrow> ['k]'a \<Rightarrow> ['n]'a" where
  "updatesEnd _ _ _ _ xs ixs a \<equiv> seq_updates_end xs (map_seq pos_nat ixs) a"

qualified abbreviation zero :: "{'a::zero} 'a" where
  "zero _ \<equiv> (0 :: 'a)"

qualified abbreviation map :: "{'n,'a,'b} ('a \<Rightarrow> 'b) \<Rightarrow> ['n]'a \<Rightarrow> ['n]'b" where
  "map _ _ _ f s \<equiv> map_seq f s"

qualified abbreviation reverse :: "{'len,'e} ['len]'e \<Rightarrow> ['len]'e" where
  "reverse _ _ s \<equiv> rev_seq s"

qualified abbreviation zip :: "{'n,'a,'b} ['n]'a \<Rightarrow> ['n]'b \<Rightarrow> ['n]('a \<times> 'b)" where
  "zip _ _ _ a b \<equiv> zip_seq a b"

qualified abbreviation zipWith :: "{'n,'a,'b,'c} ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow>  ['n]'a \<Rightarrow> ['n]'b \<Rightarrow> ['n]'c" where
  "zipWith _ _ _ _ f a b \<equiv> zipWith_seq f a b"

qualified abbreviation zip_mismatch :: "{'n,'a,'m,'b} ['n]'a \<Rightarrow> ['m]'b \<Rightarrow> [('n,'m) Min]('a \<times> 'b)" where
  "zip_mismatch _ _ _ _ a b \<equiv> zip_seq_mismatched a b"

qualified abbreviation seq_concat_map :: "{'n,'a,'m,'b} ('a \<Rightarrow> ['n]'b) \<Rightarrow> ['m]'a \<Rightarrow> ['m \<times> 'n]'b" where
  "seq_concat_map _ _ _ _ f s \<equiv> concat_seq_map f s"

qualified abbreviation  complement :: "{'a::logic} (('a) \<Rightarrow> 'a)" where
  "complement _ x \<equiv> logic_class.not x"

qualified abbreviation negate :: "{'a :: ring} 'a \<Rightarrow> 'a" where
  "negate _ x \<equiv> uminus x"

qualified abbreviation fromZ :: "{'n} 'n Z \<Rightarrow> int" where
  "fromZ _ z \<equiv> to_int_mod_ring z"

qualified abbreviation fromInteger :: "{'a::from_to_int} int \<Rightarrow> 'a" where
  "fromInteger _ z \<equiv> (from_int z :: 'a)"        

qualified abbreviation toSignedInteger :: "{'a} ['a] \<Rightarrow> int" where
  "toSignedInteger _ z \<equiv> to_sint z"

qualified abbreviation toInteger :: "{'a::from_to_int} 'a \<Rightarrow> int" where
  "toInteger _ z \<equiv> to_int z"

qualified abbreviation all :: "{'n,'a} ('a \<Rightarrow> bool) \<Rightarrow> ['n]'a \<Rightarrow> bool" where
  "all _ _ f z \<equiv> all_seq f z"

qualified abbreviation any :: "{'n,'a} ('a \<Rightarrow> bool) \<Rightarrow> ['n]'a \<Rightarrow> bool" where
  "any _ _ f z \<equiv> any_seq f z"

qualified abbreviation foldl :: "{'n,'a,'b} ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> ['n]'b \<Rightarrow> 'a" where
  "foldl _ _ _ f x s \<equiv> foldl_seq f x s"

(* The Eq class doesn't make sense in Isabelle, so foldl and foldl' are the same *)
qualified abbreviation "foldl' \<equiv> Cryptol_Syntax.translation.foldl"

(* The Eq class doesn't make sense in Isabelle, so foldr and foldr' are the same *)
qualified abbreviation foldr :: "{'n,'a,'b} ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> ['n]'a \<Rightarrow> 'b" where
  "foldr _ _ _ f x s \<equiv> foldr_seq f s x"

qualified abbreviation "foldr' \<equiv> Cryptol_Syntax.translation.foldr"

qualified abbreviation transpose :: "{'rows,'cols,'a} ['rows]['cols]'a \<Rightarrow> ['cols]['rows]'a" where
  "transpose _ _ _ s \<equiv> transpose_seq s"


qualified abbreviation min :: "{'a::ord} 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "min _ x y \<equiv> Orderings.ord_class.min x y"

qualified abbreviation max :: "{'a::ord} 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "max _ x y \<equiv> Orderings.ord_class.max x y"

qualified abbreviation head :: "{'n,'a} [1+'n]'a \<Rightarrow> 'a" where
  "head _ _ s \<equiv> nth_seq s 0"

qualified abbreviation tail :: "{'n,'a} [1+'n]'a \<Rightarrow> ['n]'a" where
  "tail _ _ s \<equiv> drop_seq s"

qualified abbreviation last :: "{'n,'a} [1+'n]'a \<Rightarrow> 'a" where
  "last _ _ s \<equiv> nth_seq s LEN('n)"

qualified abbreviation lg2 :: "{'n} ['n] \<Rightarrow> ['n]" where
  "lg2 _ x \<equiv> from_nat (log2_nat (to_nat x))"

end

end

(* This is a workaround for the fact that print translations
   need to be defined globally, but we want a print translation
   that only triggers when the coerce_syntax bundle is opened.

   We define local theory data that just tracks if we're in the bundle,
   by mapping it to a private attribute that's only declared in that
   bundle.

   There are other ways to do this (i.e. explicitly checking for
   a named target), but this is the most straightforward.
   *)
ML \<open>structure Coerce_Syntax = Generic_Data
(
  type T = bool
  val empty : T = (false)
  fun merge ((t1,t2)) = (t1 orelse t2)
)
\<close>

ML \<open>val show_coerce_types = Attrib.setup_config_bool @{binding show_coerce_types} (K false)\<close>

ML \<open>fun show_coerce_enabled context = 
  let val in_bundle = Coerce_Syntax.get context
      val opt_set = Config.get_generic context show_coerce_types
  in (in_bundle andalso opt_set) end
\<close>

bundle coerce_syntax begin
context begin
private attribute_setup in_coerce_syntax = \<open>Scan.succeed (Thm.declaration_attribute (K (Coerce_Syntax.map (fn _ => true))))\<close>
declare [[in_coerce_syntax]]
end

no_notation (ASCII)
  Set.member  (\<open>'(:')\<close>) and
  Set.member  (\<open>(\<open>notation=\<open>infix :\<close>\<close>_/ : _)\<close> [51, 51] 50)

syntax
  "_constrain2" :: "term \<Rightarrow> type \<Rightarrow> term" (\<open>(\<open>notation=\<open>mixfix\<close>\<close>_/ :/ _)\<close>  [4,0] 3)
  "_constrain_op" :: "type \<Rightarrow> term" (\<open>(\<open>notation=\<open>prefix\<close>\<close>('(:')/ _))\<close>  [0] 3)
  "_constrain_op2" :: "type \<Rightarrow> term" (\<open>(\<open>notation=\<open>mixfix\<close>\<close>('(:')/ ::/ _))\<close>  [0] 3)

syntax_consts "_constrain2" == coerce_to
          and "_constrain_op" == coerce_to
          and "_constrain_op2" == coerce_to

translations 
  "x : 'a" == "CONST coerce_to (TYPE('a)) x "
  "(:) 'a" == "CONST coerce_to (TYPE('a))"
  "((:) :: 'a)" \<rightharpoonup> "(CONST coerce) :: 'a"

ML \<open>
val constrain2_nm = @{syntax_const "_constrain2"}
val constrain_op2_nm = @{syntax_const "_constrain_op2"}
\<close>

term \<open>((:) bool)\<close>
term \<open>((:) bool) :: 'a \<Rightarrow> bool\<close>

term \<open>((:) :: 'a \<Rightarrow> bool)\<close>
term \<open>((x :: 'a) : 'b)\<close>
term \<open>\<lambda>x. ((x :: 'a) : 'b)\<close>

end

syntax (output)
  "_constrain_force" :: "term \<Rightarrow> type \<Rightarrow> term" (\<open>_ :: _\<close> [4, 0] 3)

ML \<open>
  fun coerce_to_tr cnst ctxt typ args = if show_coerce_enabled (Context.Proof ctxt) then
      case (Term.binder_types typ, Term.body_type typ, args) of
        ([_, t1], t2, [_, arg]) =>  
          Syntax.const cnst  $ (Syntax.const @{syntax_const "_constrain_force"} $ arg $ (Syntax_Phases.term_of_typ ctxt t1)) $ 
             (Syntax_Phases.term_of_typ ctxt t2)
        | ([_,t1], t2, [_]) => Syntax.const constrain_op2_nm $ (Syntax_Phases.term_of_typ ctxt (t1 --> t2))
        | _ => raise Match
  else raise Match
\<close>


typed_print_translation
  \<open> [(@{const_syntax coerce_to}, coerce_to_tr constrain2_nm)] \<close>

context includes coerce_syntax and seq_syntax begin
declare [[show_coerce_types]]
term " x :: ['a]"
term " x : ['a]"
term "((:) ['a])"
term "(:) :: 'b \<Rightarrow> ['a]"
declare [[show_coerce_types=false]]
term " x : ['a]"
term "((:) ['a])"
term "(y :: ['a]): ['b]"
end

bundle cryptol_syntax begin
unbundle coerce_syntax
unbundle rotate_shift_syntax
unbundle seq_syntax
unbundle assuming_syntax

declare [[quickcheck_set_default_types "1 Z" and "2 Z" and "3 Z" and "(5 prime) Z" and "8 Z" and "32 Z" and "64 Z" and "(67 prime) Z" and int]]
declare [[quickcheck_finite_types=false]]

no_notation sshiftr (infixl \<open>>>>\<close> 55)
no_notation shiftl (infixl \<open><<\<close> 55)
no_notation shiftr (infixl \<open>>>\<close> 55)

translations
  (type) "'a Z" \<leftharpoondown> (type) "('a len) fin mod_ring"


syntax
  "_literal" :: "type \<Rightarrow> type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>Literal/ _/ _)\<close>)

syntax_types "_literal" == litT


translations
  (type) "Literal 'a 'b" \<rightharpoonup> (type) "('a,'b) litT"
  (type) "Literal 'a 'b" \<leftharpoondown> (type) "('a,'b) litT"


(* NOTE: "fin" means nothing in our translation, because all numeric types
   are necessarily finite (since LENGTH is a natural number) *)
syntax
  "_fin" :: "type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>fin/ _)\<close>)

translations
  (type) "fin 'a" \<rightharpoonup> (type) "'a topT"


(* NOTE: these are trivial predicates that are introduced simply
   to hold the sort constraint. Sort constraints are only valid on
   free type variables, so this will cause a parse error if used otherwise
   (e.g. "Ring ('a word)") *)

syntax
  "_ring" :: "type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>Ring/ _)\<close>)

(* Note that Cryptol Rings also have a power operation *)
translations
  (type) "Ring 'a" \<rightharpoonup> (type) "('a :: cryptol_ring) topT"

typ "Ring 'a"

syntax
  "_integral" :: "type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>Integral/ _)\<close>)

translations
  (type) "Integral 'a" \<rightharpoonup> (type) "('a :: cryptol_integral) topT"

syntax
  "_zero" :: "type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>Zero/ _)\<close>)

translations
  (type) "Zero 'a" \<rightharpoonup> (type) "('a :: {zero,coercible_atom}) topT"

syntax
  "_logic" :: "type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>Logic/ _)\<close>)

translations
  (type) "Logic 'a" \<rightharpoonup> (type) "('a :: {logic,coercible_atom}) topT"

syntax
  "_signedCmp" :: "type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>SignedCmp/ _)\<close>)

translations
  (type) "SignedCmp 'a" \<rightharpoonup> (type) "('a :: {signedCmp,coercible_atom}) topT"

syntax
  "_Cmp" :: "type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>Cmp/ _)\<close>)

translations
  (type) "Cmp 'a" \<rightharpoonup> (type) "('a :: {ord,coercible_atom}) topT"

syntax
  "_eq" :: "type \<Rightarrow> type"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>Eq/ _)\<close>)

(* all Isabelle types support equality, so it's unclear if this means anything at all *)
translations
  (type) "Eq 'a" \<rightharpoonup> (type) "('a :: coercible_atom) topT"

end


abbreviation (input) power_op :: "('a :: power) \<Rightarrow> ('b :: from_to_int) \<Rightarrow> 'a"
  where "power_op \<equiv> (\<lambda>x y. power x (pos_nat y))"

abbreviation (input) nth_seq_op :: "('len,'e) seq \<Rightarrow> ('b :: from_to_int) \<Rightarrow> 'e"
  where "nth_seq_op \<equiv> (\<lambda>x y. nth_seq x (pos_nat y))"

abbreviation (input) nth_end_seq_op :: "('len,'e) seq \<Rightarrow> ('b :: from_to_int) \<Rightarrow> 'e"
  where "nth_end_seq_op \<equiv> (\<lambda>x y. nth_end_seq x (pos_nat y))"

abbreviation (input) signed_shift_op :: "('n,bool) seq \<Rightarrow> ('ix :: from_to_int) \<Rightarrow> ('n,bool) seq"
  where "signed_shift_op \<equiv> (\<lambda>x y. signed_shift x (to_int y))"

abbreviation (input) right_rotate_op :: "('n,'a) seq \<Rightarrow> ('ix :: from_to_int) \<Rightarrow> ('n,'a) seq"
  where "right_rotate_op \<equiv> (\<lambda>x y. right_rotate x (to_int y))"

abbreviation (input) left_rotate_op :: "('n,'a) seq \<Rightarrow> ('ix :: from_to_int) \<Rightarrow> ('n,'a) seq"
  where "left_rotate_op \<equiv> (\<lambda>x y. left_rotate x (to_int y))"

abbreviation (input) right_shift_op :: "('n,'a::zero) seq \<Rightarrow> ('ix :: from_to_int) \<Rightarrow> ('n,'a) seq"
  where "right_shift_op \<equiv> (\<lambda>x y. right_shift x (to_int y))"

abbreviation (input) left_shift_op :: "('n,'a::zero) seq \<Rightarrow> ('ix :: from_to_int) \<Rightarrow> ('n,'a) seq"
  where "left_shift_op \<equiv> (\<lambda>x y. left_shift x (to_int y))"

text \<open>This is input-only syntax used to simplify the translation. It should be in scope
when processing any definitions produced by the translator, but generally should not
be needed outside of that context. In particular, this overrides some Isabelle-native symbols
(e.g. @, ^^, !, with the type-application syntax), which could cause confusion if exported.
\<close>

bundle cryptol_translation_syntax begin

unbundle cryptol_syntax
unbundle implicit_coerce

no_notation compower (infixr \<open>^^\<close> 80)
no_notation power (infixr \<open>^\<close> 80)

no_notation wordAND (infixr \<open>&&\<close> 64)
no_notation wordOR (infixr \<open>||\<close> 59)

no_notation Not (\<open>(\<open>open_block notation=\<open>prefix ~\<close>\<close>~ _)\<close> [40] 40)

no_notation List.nth (infixl \<open>!\<close> 100)
no_notation List.append (infixr \<open>@\<close> 65)
no_notation List.Cons (infixr \<open>#\<close> 65)

translations
  (type) "Literal 'a 'b" \<rightharpoonup> (type) "('a,'b::{from_to_int,numeral,coercible_atom}) litT"

syntax
  "_eq_param" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ ==`'{_'} _)\<close>)
  "_eq_param_op" :: "type \<Rightarrow> term" (\<open>'\<lblot>==`'{_'}'\<rblot>\<close>)

syntax_consts "_eq_param" == HOL.eq and "_eq_param_op" == HOL.eq

translations
  "x ==`{'a} y"  \<rightharpoonup> "(x : 'a) = (y : 'a)"
  "\<lblot>==`{'a}\<rblot>"  \<rightharpoonup> "(=) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax
  "_neq_param" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ !=`'{_'} _)\<close>)
  "_neq_param_op" :: "type \<Rightarrow> term" (\<open>'\<lblot>!=`'{_'}'\<rblot>\<close>)

syntax_consts "_neq_param" == not_equal and "_neq_param_op" == not_equal

translations
  "x !=`{'a} y"  \<rightharpoonup> "(x : 'a) \<noteq> (y : 'a)"
  "\<lblot>!=`{'a}\<rblot>"  \<rightharpoonup> "(\<noteq>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

term "(x ==`{'b} y)"

type_synonym Bit = bool
type_synonym Integer = int
type_synonym Bool = bool


syntax
  "_selects" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ @@`'{_,_,_,_'} _)\<close> 65)
  "_selects_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term" (\<open>'\<lblot>@@`'{_,_,_,_'}'\<rblot>\<close>)

syntax_consts "_selects" == selects and "_selects_op" == selects

translations
  "x @@`{'t1,'t2,'t3,'t4} y"  \<rightharpoonup> "CONST selects (x : ('t1,'t4) seq) (y : ('t2,'t3) seq)"
  "\<lblot>@@`{'t1,'t2,'t3,'t4}\<rblot>"  \<rightharpoonup> "CONST selects :: ('t1,'t4) seq \<Rightarrow> ('t2,'t3) seq"

syntax
  "_selects_end" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ !!`'{_,_,_,_'} _)\<close> 65)
  "_selects_end_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term" (\<open>'\<lblot>!!`'{_,_,_,_'}'\<rblot>\<close>)

syntax_consts "_selects_end" == selects_end and "_selects_end_op" == selects_end

translations
  "x !!`{'t1,'t2,'t3,'t4} y"  \<rightharpoonup> "CONST selects_end (x : ('t1,'t4) seq) (y : ('t2,'t3) seq)"
  "\<lblot>!!`{'t1,'t2,'t3,'t4}\<rblot>"  \<rightharpoonup> "CONST selects_end :: ('t1,'t4) seq \<Rightarrow> ('t2,'t3) seq"

term "(x ==`{[2][32]} (list_to_seq [(7 :: [32]),(20 :: [32])] :: [2][32]))"

syntax
  "_left_shift" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ <<`'{_,_,_'} _)\<close>)
  "_left_shift_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot><<`'{_,_,_'}'\<rblot>\<close>)

syntax_consts "_left_shift" \<rightleftharpoons> "left_shift" and "_left_shift_op" \<rightleftharpoons> "left_shift"

translations
  "x <<`{'len,'idx,'a} y"  \<rightharpoonup> "CONST left_shift_op (x : ['len]'a) (y : 'idx)"
  "\<lblot><<`{'len,'idx,'a}\<rblot>" \<rightharpoonup> "CONST left_shift_op :: ['len]'a \<Rightarrow> 'idx \<Rightarrow> ['len]'a"

term "x <<`{'len,'idx::integral,'a::zero} y"
term "\<lblot><<`{'len,'idx::integral,'a::zero}\<rblot>"

syntax
  "_right_shift" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ >>`'{_,_,_'} _)\<close>)
  "_right_shift_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot>>>`'{_,_,_'}'\<rblot>\<close>)

syntax_consts "_right_shift" \<rightleftharpoons> "right_shift" and "_right_shift_op" \<rightleftharpoons> "right_shift"

translations
  "x >>`{'len,'idx,'a} y"  \<rightharpoonup> "CONST right_shift_op (x : ['len]'a) (y : 'idx)"
  "\<lblot>>>`{'len,'idx,'a}\<rblot>" \<rightharpoonup> "CONST right_shift_op :: ['len]'a \<Rightarrow> 'idx \<Rightarrow> ['len]'a"

term "x >>`{'len,'idx::integral,'a::zero} y"
term "\<lblot>>>`{'len,'idx::integral,'a::zero}\<rblot>"

syntax
  "_left_rotate" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ <<<`'{_,_,_'} _)\<close>)
  "_left_rotate_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot><<<`'{_,_,_'}'\<rblot>\<close>)

syntax_consts "_left_rotate" \<rightleftharpoons> "left_rotate" and "_left_rotate_op" \<rightleftharpoons> "left_rotate"

translations
  "x <<<`{'len,'idx,'a} y"  \<rightharpoonup> "CONST left_rotate_op (x : ['len]'a) (y : 'idx)"
  "\<lblot><<<`{'len,'idx,'a}\<rblot>" \<rightharpoonup> "CONST left_rotate_op :: ['len]'a \<Rightarrow> 'idx \<Rightarrow> ['len]'a"

term "x <<<`{'len,'idx::integral,'a} y"
term "\<lblot><<<`{'len,'idx::integral,'a}\<rblot>"

syntax
  "_right_rotate" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ >>>`'{_,_,_'} _)\<close>)
  "_right_rotate_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot>>>>`'{_,_,_'}'\<rblot>\<close>)

syntax_consts "_right_rotate" \<rightleftharpoons> "right_rotate" and "_right_rotate_op" \<rightleftharpoons> "right_rotate"

translations
  "x >>>`{'len,'idx,'a} y"  \<rightharpoonup> "CONST right_rotate_op (x : ['len]'a) (y : 'idx)"
  "\<lblot>>>>`{'len,'idx,'a}\<rblot>" \<rightharpoonup> "CONST right_rotate_op :: ['len]'a \<Rightarrow> 'idx \<Rightarrow> ['len]'a"

term "x >>>`{'len,'idx::integral,'a} y"
term "\<lblot>>>>`{'len,'idx::integral,'a}\<rblot>"

syntax
  "_signed_shift" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ >>$`'{_,_'} _)\<close>)
  "_signed_shift_op" :: "type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot>>>$`'{_,_'}'\<rblot>\<close>)

syntax_consts "_signed_shift" \<rightleftharpoons> "signed_shift" and "_signed_shift_op" \<rightleftharpoons> "signed_shift" 

translations
  "x >>$`{'n,'ix} y"  \<rightharpoonup> "CONST signed_shift_op (x : ['n]) (y : 'ix)"
  "\<lblot>>>$`{'n,'ix}\<rblot>" \<rightharpoonup> "CONST signed_shift_op :: ['n] \<Rightarrow> 'ix \<Rightarrow> ['n]"

term "x >>$`{'len,'idx::integral} y"
term "\<lblot>>>$`{'len,'idx::integral}\<rblot>"

syntax
  "_times" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ *`'{_'} _)\<close>)
  "_times_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>*`'{_'}'\<rblot>\<close>)

syntax_consts "_times" \<rightleftharpoons> "times" and "_times_op" \<rightleftharpoons> "times"

translations
  "x *`{'a} y" \<rightharpoonup> "(x : 'a) * (y : 'a)"
  "\<lblot>*`{'a}\<rblot>" \<rightharpoonup> "(*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"

syntax
  "_divide" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ '/`'{_'} _)\<close>)
  "_divide_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>'/`'{_'}'\<rblot>\<close>)

syntax_consts "_divide" \<rightleftharpoons> "divide" and "_divide_op" \<rightleftharpoons> "divide"

translations
  "x /`{'a} y" \<rightharpoonup> "(x : 'a) div (y : 'a)"
  "\<lblot>/`{'a}\<rblot>" \<rightharpoonup> "(div) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"


syntax
  "_mod" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ '%`'{_'} _)\<close>)
  "_mod_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>'%`'{_'}'\<rblot>\<close>)

syntax_consts "_mod" \<rightleftharpoons> "modulo" and "_mod_op" \<rightleftharpoons> "modulo"

translations
  "x %`{'a} y" \<rightharpoonup> "(x : 'a) mod (y : 'a)"
  "\<lblot>%`{'a}\<rblot>" \<rightharpoonup> "(mod) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"

syntax
  "_plus" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ +`'{_'} _)\<close>)
  "_plus_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>+`'{_'}'\<rblot>\<close>)

syntax_consts "_plus" \<rightleftharpoons> "plus" and "_plus_op" \<rightleftharpoons> "plus"

translations
  "x +`{'a} y" \<rightharpoonup> "(x : 'a) + (y : 'a)"
  "\<lblot>+`{'a}\<rblot>" \<rightharpoonup> "(+) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"


syntax
  "_minus" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ -`'{_'} _)\<close>)
  "_minus_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>-`'{_'}'\<rblot>\<close>)

syntax_consts "_minus" \<rightleftharpoons> "minus" and "_minus_op" \<rightleftharpoons> "minus"

translations
  "x -`{'a} y" \<rightharpoonup> "(x : 'a) - (y : 'a)"
  "\<lblot>-`{'a}\<rblot>" \<rightharpoonup> "(-) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"


syntax
  "_power" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ ^^`'{_,_'} _)\<close>)
  "_power_op" :: "type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot>^^`'{_,_'}'\<rblot>\<close>)

syntax_consts "_power" \<rightleftharpoons> "power_op" and "_power_op" \<rightleftharpoons> "power_op"

translations
  "x ^^`{'a,'b} y" \<rightharpoonup> "CONST power_op (x : 'a) (y : 'b)"
  "\<lblot>^^`{'a,'b}\<rblot>" \<rightharpoonup> "CONST power_op :: 'a \<Rightarrow> 'b \<Rightarrow> 'a"

syntax
  "_xor" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ ^`'{_'} _)\<close>)
  "_xor_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>^`'{_'}'\<rblot>\<close>)

syntax_consts "_xor" \<rightleftharpoons> "logic_class.xor" and "_xor_op" \<rightleftharpoons> "logic_class.xor"

translations
  "x ^`{'a} y" \<rightharpoonup> "CONST logic_class.xor (x : 'a)  (y : 'a)"
  "\<lblot>^`{'a}\<rblot>" \<rightharpoonup> "CONST logic_class.xor :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"


syntax
  "_conj" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ &&`'{_'} _)\<close>)
  "_conj_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>&&`'{_'}'\<rblot>\<close>)

syntax_consts "_conj" \<rightleftharpoons> "logic_class.and" and "_conj_op" \<rightleftharpoons> "logic_class.and"

translations
  "x &&`{'a} y" \<rightharpoonup> "CONST logic_class.and (x :: 'a) (y : 'a)"
  "\<lblot>&&`{'a}\<rblot>" \<rightharpoonup> "CONST logic_class.and :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"

term "x &&`{Bit} y"

syntax
  "_disj" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ ||`'{_'} _)\<close>)
  "_disj_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>||`'{_'}'\<rblot>\<close>)

syntax_consts "_disj" \<rightleftharpoons> "logic_class.or" and "_disj_op" \<rightleftharpoons> "logic_class.or"

translations
  "x ||`{'a} y" \<rightharpoonup> "CONST logic_class.or (x : 'a) (y : 'a)"
  "\<lblot>||`{'a}\<rblot>" \<rightharpoonup> "CONST logic_class.or :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"

syntax
  "_not" :: "type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>~`'{_'} _)\<close>)
  "_not_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>~`'{_'}'\<rblot>\<close>)

syntax_consts "_not" \<rightleftharpoons> "logic_class.not" and "_not_op" \<rightleftharpoons> "logic_class.not"

translations
  "~`{'a} x" \<rightharpoonup> "CONST logic_class.not (x : 'a)"
  "\<lblot>~`{'a}\<rblot>" \<rightharpoonup> "CONST logic_class.not :: 'a \<Rightarrow> 'a"

notation signed_modulo (infix \<open>%$\<close> 50)

syntax
  "_signed_word_mod" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ %$`'{_'} _)\<close>)
  "_signed_word_mod_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>%$`'{_'}'\<rblot>\<close>)

syntax_consts "_signed_word_mod" == signed_modulo and "_signed_word_mod_op" == signed_modulo

translations
  "x %$`{'n} y" \<rightharpoonup> "(x : ['n]) %$ (y : ['n])"
  "\<lblot>%$`{'a}\<rblot>" \<rightharpoonup> "(%$) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"

notation signed_divide (infix \<open>'//$\<close> 50)

syntax
  "_signed_word_div" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ '//$`'{_'} _)\<close>)
  "_signed_word_div_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>'//$`'{_'}'\<rblot>\<close>)

syntax_consts "_signed_word_div" == signed_divide and "_signed_word_div_op" == signed_divide

translations
  "x /$`{'n} y" \<rightharpoonup> "(x : ['n]) /$ (y : ['n])"
  "\<lblot>/$`{'a}\<rblot>" \<rightharpoonup> "(/$) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a"

syntax
  "_signed_gt" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ >$`'{_'} _)\<close>)
  "_signed_gt_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>>$`'{_'}'\<rblot>\<close>)

syntax_consts "_signed_gt" == signed_gt and "_signed_gt_op" == signed_gt

translations
  "x >$`{'a} y" \<rightharpoonup> "(x : 'a) >$ (y : 'a)"
  "\<lblot>>$`{'a}\<rblot>" \<rightharpoonup> "(>$) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax
  "_seq_append" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ #`'{_,_,_'} _)\<close>)
  "_seq_append_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot>#`'{_,_,_'}'\<rblot>\<close>)

syntax_consts "_seq_append" == append_seq and "_seq_append_op" == append_seq

translations
  "x #`{'len1,'len2,'a} y" \<rightharpoonup> "CONST append_seq (x : ['len1]'a) (y : ['len2]'a) :: ['len1 + 'len2]'a"
  "\<lblot>#`{'len1,'len2,'a}\<rblot>" \<rightharpoonup> "CONST append_seq :: (['len1]'a \<Rightarrow> ['len2]'a \<Rightarrow> ['len1 + 'len2]'a)"

term "x #`{1,2,'a} y"

syntax
  "_nth_seq" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ @`'{_,_,_'} _)\<close>)
  "_nth_seq_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot>@`'{_,_,_'}'\<rblot>\<close>)

syntax_consts "_nth_seq" == nth_seq and "_nth_seq_op" == nth_seq

translations
  "x @`{'len,'e,'idx} y" \<rightharpoonup> "CONST nth_seq_op (x : ['len]'e) (y : 'idx) :: 'e"
  "\<lblot>@`{'len,'e,'idx}\<rblot>" \<rightharpoonup> "CONST nth_seq_op :: (['len]'e \<Rightarrow> 'idx \<Rightarrow> 'e)"

term "(x :: ['len]'e) @`{'len,'e,Integer} 1"

syntax
  "_seq_select_fromend" :: "term \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_ !`'{_,_,_'} _)\<close>)
  "_seq_select_fromend_op" :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> term"  (\<open>'\<lblot>!`'{_,_,_'}'\<rblot>\<close>)

syntax_consts "_seq_select_fromend" == nth_end_seq and "_seq_select_fromend_op" == nth_end_seq

translations
  "x !`{'len,'e,'idx} y" \<rightharpoonup> "CONST nth_end_seq_op (x : ('len, 'e) seq) (y : 'idx) :: 'e"
  "\<lblot>!`{'len,'e,'idx}\<rblot>" \<rightharpoonup> "CONST nth_end_seq_op :: (['len]'e \<Rightarrow> 'idx \<Rightarrow> 'e)"

syntax
  "_lt" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_/ <`{_} _)\<close>)
  "_lt_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot><`'{_'}'\<rblot>\<close>)

syntax_consts "_lt" \<rightleftharpoons> "less" and "_lt_op" == less

translations
  "x <`{'a} y" \<rightharpoonup> "(x : 'a) < (y : 'a)"
  "\<lblot><`{'a}\<rblot>" \<rightharpoonup> "(<) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax
  "_le" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_/ <=`{_} _)\<close>)
  "_le_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot><=`'{_'}'\<rblot>\<close>)

syntax_consts "_le" \<rightleftharpoons> "less_eq" and "_le_op" == "less_eq"

translations
  "x <=`{'a} y" \<rightharpoonup> "(x : 'a) \<le> (y : 'a)"
  "\<lblot><=`{'a}\<rblot>" \<rightharpoonup> "(\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax
  "_ge" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_/ >=`{_} _)\<close>)
  "_ge_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>>=`'{_'}'\<rblot>\<close>)

syntax_consts "_ge" \<rightleftharpoons> "greater_eq" and "_ge_op" == "greater_eq"

translations
  "x >=`{'a} y" \<rightharpoonup> "(x : 'a) \<ge> (y : 'a)"
  "\<lblot>>=`{'a}\<rblot>" \<rightharpoonup> "(\<ge>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax
  "_gt" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_/ >`{_} _)\<close>)
  "_gt_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>>`'{_'}'\<rblot>\<close>)

syntax_consts "_gt" \<rightleftharpoons> "greater" and "_gt_op" == "greater"

translations
  "x >`{'a} y" \<rightharpoonup> "(x : 'a) > (y : 'a)"
  "\<lblot>>`{'a}\<rblot>" \<rightharpoonup> "(>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax
  "_signed_lt" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_/ <$`{_} _)\<close>)
  "_signed_lt_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot><$`'{_'}'\<rblot>\<close>)

syntax_consts "_signed_lt" \<rightleftharpoons> "signed_lt" and "_signed_lt_op" \<rightleftharpoons> "signed_lt"

translations
  "x <$`{'a} y" \<rightharpoonup> "(x :: 'a) <$ (y : 'a)"
  "\<lblot><$`{'a}\<rblot>" \<rightharpoonup> "CONST signed_lt :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

syntax
  "_signed_le" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_/ <=$`{_} _)\<close>)
  "_signed_le_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot><=$`'{_'}'\<rblot>\<close>)

syntax_consts "_signed_le" \<rightleftharpoons> "signed_le" and "_signed_le_op" \<rightleftharpoons> "signed_le"

translations
  "x <=$`{'a} y" \<rightharpoonup> "(x :: 'a) <=$ (y : 'a)"
  "\<lblot><=$`{'a}\<rblot>" \<rightharpoonup> "CONST signed_le :: 'a \<Rightarrow> 'a \<Rightarrow> bool"


syntax
  "_signed_ge" :: "term \<Rightarrow> type \<Rightarrow> term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_/ >=$`{_} _)\<close>)
  "_signed_ge_op" :: "type \<Rightarrow> term"  (\<open>'\<lblot>>=$`'{_'}'\<rblot>\<close>)

syntax_consts "_signed_ge" \<rightleftharpoons> "signed_ge" and "_signed_ge_op" \<rightleftharpoons> "signed_ge"

translations
  "x >=$`{'a} y" \<rightharpoonup> "(x :: 'a) >=$ (y : 'a)"
  "\<lblot>>=$`{'a}\<rblot>" \<rightharpoonup> "CONST signed_ge :: 'a \<Rightarrow> 'a \<Rightarrow> bool"

alias length = Cryptol_Syntax.translation.length
alias join = Cryptol_Syntax.join'
alias take = Cryptol_Syntax.take'
alias drop = Cryptol_Syntax.drop'

alias zero = Cryptol_Syntax.translation.zero
alias map = Cryptol_Syntax.translation.map
alias seq_compr = Cryptol_Syntax.translation.map
alias reverse = Cryptol_Syntax.translation.reverse
alias zip = Cryptol_Syntax.translation.zip
alias zipWith = Cryptol_Syntax.translation.zipWith
alias zip_mismatch = Cryptol_Syntax.translation.zip_mismatch
alias seq_concat_map = Cryptol_Syntax.translation.seq_concat_map
alias complement = Cryptol_Syntax.translation.complement
alias sum = Cryptol_Syntax.translation.sum
alias product = Cryptol_Syntax.translation.product
alias update = Cryptol_Syntax.translation.update
alias updateEnd = Cryptol_Syntax.translation.updateEnd
alias updates = Cryptol_Syntax.translation.updates
alias updatesEnd = Cryptol_Syntax.translation.updatesEnd

alias carry = Cryptol_Syntax.translation.carry
alias scarry = Cryptol_Syntax.translation.scarry
alias sborrow = Cryptol_Syntax.translation.sborrow
alias "and" = Cryptol_Syntax.translation.and
alias or = Cryptol_Syntax.translation.or

alias negate = Cryptol_Syntax.translation.negate
alias fromZ = Cryptol_Syntax.translation.fromZ
alias fromInteger = Cryptol_Syntax.translation.fromInteger
alias toSignedInteger = Cryptol_Syntax.translation.toSignedInteger
alias toInteger = Cryptol_Syntax.translation.toInteger
alias all = Cryptol_Syntax.translation.all
alias any = Cryptol_Syntax.translation.any

alias scanl = Cryptol_Syntax.translation.scanl
alias scanr = Cryptol_Syntax.translation.scanr
alias foldl = Cryptol_Syntax.translation.foldl
alias foldl' = Cryptol_Syntax.translation.foldl'
alias foldr = Cryptol_Syntax.translation.foldr
alias foldr' = Cryptol_Syntax.translation.foldr'
alias transpose = Cryptol_Syntax.translation.transpose

alias min = Cryptol_Syntax.translation.min
alias max = Cryptol_Syntax.translation.max

alias head = Cryptol_Syntax.translation.head
alias tail = Cryptol_Syntax.translation.tail
alias last = Cryptol_Syntax.translation.last
alias lg2 = Cryptol_Syntax.translation.lg2

end


experiment begin

context includes cryptol_translation_syntax begin

lemma "(x *`{['a + 'b]} y) = ((x : ['a + 'b]) * (y : ['a + 'b]))"
  apply (rule refl)
  done


lemma "(x /`{['a + 'b]} y) = ((x : ['a + 'b]) div (y : ['a + 'b]))"
  apply (rule refl)
  done

lemma "coerce_to TYPE((256, (16, bool) seq) seq) 
         (zipWith_seq (coerce_to TYPE((16, bool) seq \<Rightarrow> (16, bool) seq \<Rightarrow> (16, bool) seq \<times> (16, bool) seq) (+)) (xs:: ['a][16]) ys) 
        = invalid_coercion TYPE(['a]([16] \<times> [16])) TYPE([256][16])"
  by simp

end

end

end