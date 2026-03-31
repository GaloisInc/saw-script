theory Cryptol_Definition
  imports Main Type_Args Type_Predicate
  keywords "cryptol_definition":: thy_defn 
       and "cryptol_termination":: thy_goal_defn
begin

ML\<open>                 
signature CRYPTOL_DEFINITION =
sig
  val cryptol_definition_cmd :
    binding * string * mixfix -> string option -> string list -> 
    (binding * string option * mixfix) list -> local_theory -> local_theory
  val cryptol_termination_cmd : string -> Bundle.xname list -> theory -> Proof.state
  val rec_prover_tac : Proof.context -> thm -> thm -> thm list -> tactic

  val set_cryptol_hash : int -> theory -> theory
  val get_cryptol_hash : theory -> int

  val set_const_hash : string -> int -> theory -> theory
  val get_const_hash : theory -> string -> int option
  val set_const_hash_attrib : string -> int -> attribute

  val check_const_hash_thm : theory -> thm -> int option

end
\<close>

ML \<open>
structure Cryptol_Definition: CRYPTOL_DEFINITION =
struct

structure Hashes = Theory_Data
(
  type T = int Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (op =);
);

val dummy_var = ("'_dummy_", ~1);

(* collect constraints so they are consistent *)
fun constraint (xi, raw_S) env =
  let 
    val (_, S) = Term_Position.decode_positionS raw_S 
in
    if xi = dummy_var orelse S = dummyS then env
    else
      Vartab.map_default (xi, []) (fn x => S @ x) env
  end;

fun mkenv tys = 
      Vartab.build (tys |> (fold o fold_atyps)
        (fn TFree (x, S) => constraint ((x, ~1), S)
          | TVar v => constraint v
          | _ => I))

fun rebuild s env (T : typ) = case T of
      Type(nm,Ts) => Type (nm, map (rebuild s env) Ts)
    | TFree(idx, _) => (case (Vartab.lookup env (idx,~1)) of
          SOME s' => TFree(idx, s @ s')
        | NONE => T)
    | TVar(idx,_) => (case (Vartab.lookup env idx) of 
          SOME s' => TVar(idx, s @ s')
        | NONE => T)


fun normalize_sorts' ctxt s env T = 
  let val (_,[T']) = Proof_Context.prepare_sortsT ctxt [rebuild s env T]
  in T' end

fun normalize_sorts ctxt s T = normalize_sorts' ctxt s (mkenv [T]) T

fun normalize_sorts_term ctxt s T t =
  let val env = mkenv (Term.fold_types (fn ty => fn tys => ty::tys) t [T])
  in  (Term.map_types o Term.map_atyps_same) (normalize_sorts' ctxt s env) t
  end

fun dest_funT t = SOME (Term.dest_funT t) handle Term.TYPE _ => NONE

fun is_trivial_coerce t = case dest_funT t of
    SOME (_, U) => (case dest_funT U of
      SOME (V, W) => V = W
     | NONE => false)
  | NONE => false

fun unwrap_no_coerce x = case x of
      (Const (\<^const_name>\<open>coerce_to\<close>, T) $ U $ y) => if is_trivial_coerce T then unwrap_no_coerce y
        else Const (\<^const_name>\<open>coerce_to\<close>, T) $ U $ unwrap_no_coerce y
    | Const (\<^const_name>\<open>coerce_to\<close>, T) => 
        if is_trivial_coerce T then Term.Abs ("x", T, Term.Bound 0) else x
    | y $ z => unwrap_no_coerce y $ unwrap_no_coerce z
    | Abs (nm, T, y) => Abs (nm, T, unwrap_no_coerce y)
    | _ => x

fun strip_guard  T = case T of
      Type("fun", [ (targ as Type (\<^type_name>\<open>tyarg\<close>, _)), T2]) => (case strip_guard T2 of
        SOME (T1, T2') => SOME (T1, targ --> T2')
        | NONE => NONE)
        
    | Type(\<^type_name>\<open>guarded\<close>, [T1, T2]) => SOME (T1, T2)
    | _ => NONE

fun strip_tyargs T = case T of
      Type("fun", [ Type (\<^type_name>\<open>tyarg\<close>, [targ]), T2 ]) =>
        let val (tyargs, retT) = strip_tyargs T2 in (targ::tyargs, retT) end
    | _ => ([], T)

fun add_dummies t n = case Term_Position.strip_positions t of
       (Const ("_constrain",T) $ t1) => Const ("_constrain",T) $ add_dummies t1 n
     | (Const ("_type_constraint_",T) $ t1) => Const ("_type_constraint_",T) $ add_dummies t1 n
     | t1 $ t2 => add_dummies t1 n $ t2
     | _ => if n > 0 then (add_dummies t (n-1)) $ Term.dummy_pattern dummyT else t

fun fix_arg_term arg = case arg of
       (Const ("_constrain",T) $ t1) => Const ("_constrain",T) $ fix_arg_term t1
     | (Const ("_type_constraint_",T) $ t1) => Const ("_type_constraint_",T) $ fix_arg_term t1
     | Const (nm, _) => Free(Long_Name.base_name nm, dummyT)
     | t1 $ t2 => (fix_arg_term t1) $ (fix_arg_term t2)
     | _ => arg
 

(* peel out the "guarded" type and push it into the definition *)
fun adjust_header (x : (binding * typ * mixfix) ) = case x of
      (b,T,mfx) => (case strip_guard T of
        SOME (T1,T2) => (SOME T1, (b, SOME T2,mfx))
      | NONE => (NONE, (b,SOME T,mfx)))

fun dest_equals (e $ t $ u) = (case Type.strip_constraints (Term_Position.strip_positions e )of
      Const ("Pure.eq",_) => (t, u)
    | e' => raise TERM ("dest_equals", [e', t, u]))
  | dest_equals t = raise TERM ("dest_equals", [t])

fun map_decl_typ (f : 'a -> 'b) ((b, T,mfx) : (binding * 'a * mixfix)) = (b,(f T), mfx)

fun rhs_type args Ts retT = case (args,Ts) of
      (_::xs,_::ts) => rhs_type xs ts retT
    | ([],_) => Ts ---> retT
    | _ => raise TERM ("rhs_type: Unexpected number of arguments", args)

fun add_constraints args Ts = case (args,Ts) of
     (x::xs,T::Ts') => (Type.constraint T x :: add_constraints xs Ts')
   | ([], _) => []
   | _ => raise TERM ("add_constraints: Unexpected number of arguments", args)

fun tyarg T = Const (\<^const_name>\<open>tyargCtr\<close>, Type (@{type_name tyarg}, [T]))

fun cryptol_definition_cmd decl mspec prems params lthy =
let 
  val decl0 = map_decl_typ (normalize_sorts lthy [] o Syntax.parse_typ lthy) decl
  val (mguard, decl1) = adjust_header decl0
  val ((b,SOME T,mfx), lthy0) = Proof_Context.cert_var decl1 lthy          
  val (params', lthy1) = fold_map Proof_Context.read_var (params) lthy0
  val prems' = map (Syntax.parse_prop lthy1) prems
  
  val (raw_concl, lthy2, lthy_outer) = case mspec of
        SOME raw_spec => 
                let 
                    val (lhs, _) = dest_equals (Syntax.parse_prop lthy1 raw_spec)
                    val (_, args) = Term.strip_comb (Type.strip_constraints (Term_Position.strip_positions lhs))
                    val args' = map fix_arg_term args
                    val lthy2 = fold Variable.declare_term args' lthy1
                in (normalize_sorts_term lthy2 [] T (Syntax.parse_prop lthy2 raw_spec),lthy2,lthy) end
        (* generate a "raw" background constant that can be overridden *)
      | NONE => let
         val (Const(global_nm, _), lthy2) = Local_Theory.background_theory_result
           (Sign.declare_const_global ((Binding.suffix_name "_raw" b,T),mfx)) lthy1
         val (tyArgs, baseT) = strip_tyargs T
         val (argTs, _) = Term.strip_type baseT
         val args = Name.invent_names (Variable.names_of lthy2) "" argTs
         val arg_terms = map Free args
         val lthy3 = fold Variable.declare_term arg_terms lthy2
         val concl = Const (\<^const_name>\<open>Pure.eq\<close>, dummyT) $ 
           (Term.list_comb (Free (Binding.name_of b, dummyT), arg_terms)) $
           (Term.list_comb (Const (global_nm, dummyT), (map tyarg tyArgs @ arg_terms)))
         in (concl, lthy3, lthy2) end
  
  val concl = 
    let val (lhs, rhs) = dest_equals raw_concl
        val (lhs', rhs') =
               let
                 val (base, args) = Term.strip_comb (Type.strip_constraints (Term_Position.strip_positions lhs))
                 val (tyArgs, baseT) = strip_tyargs T
                 val (argTs, retT) = Term.strip_type baseT
                 val rhsT = rhs_type args argTs retT
                 val lhs' = Term.list_comb (base, add_constraints args argTs)
                 val lhs'' = add_dummies lhs' (length tyArgs)
               in (lhs'', Syntax.const (\<^const_name>\<open>coerce_to\<close>) $ Logic.mk_type rhsT $ rhs) end
        val rhs'' = case mguard of
          SOME T1 => (Const (\<^const_name>\<open>assuming\<close>, dummyT)) $ (tyarg T1) $ rhs'
        | NONE => rhs'
    in Const (\<^const_name>\<open>Pure.eq\<close>, dummyT) $ lhs' $ rhs'' end
  val concl' = unwrap_no_coerce (Syntax.check_term (Proof_Context.allow_dummies lthy2) concl)
  val lthy3 = #2 (Specification.definition (SOME (b,SOME T,mfx)) params' prems' (Binding.empty_atts, concl') lthy_outer)
  in lthy3 end


fun set_const_hash nm hash = Hashes.map (Symtab.insert (op =) (nm, hash))

fun set_const_hash_attrib nm hash = 
  Thm.declaration_attribute (fn _ => Context.mapping (set_const_hash nm hash) 
    (Local_Theory.map_contexts (fn i => if i = 1 then Proof_Context.background_theory (set_const_hash nm hash) else I)))

fun get_const_hash thy nm = Symtab.lookup (Hashes.get thy) nm

fun set_cryptol_hash hash = 
  Hashes.map (Symtab.insert (op =) ("", hash))

fun get_cryptol_hash thy = case get_const_hash thy "" of
   SOME i => i
 | NONE => error "get_cryptol_hash: no cryptol hash set"

fun check_const_hash_thm thy thm = 
  let
    val (Const (nm,_),args) = Term.strip_comb (HOLogic.dest_Trueprop (Thm.full_prop_of thm))
    val T = Consts.the_const_type (Sign.consts_of thy) nm
    val ctxt = Proof_Context.init_global thy
   
    val T' = Logic.unvarifyT_global T
    val (Ts,_) = Term.strip_type T'
    val args' = map Free (Variable.variant_names ctxt (map (fn t => ("",t)) Ts))
    val goal = HOLogic.mk_Trueprop (Term.list_comb (Const (nm,T'), args'))

    (* final check, theorem must prove that the constant is true on all arguments *)
    val _ = Goal.prove ctxt [] [] goal (fn st => resolve_tac (#context st) [thm] 1)
    val _ = writeln (Syntax.string_of_term ctxt goal)

  in get_const_hash thy nm end
  handle 
      Bind => NONE
    | TERM _ => NONE

fun rec_prover_tac ctxt impl_def spec_def simps =
        Classical.standard_tac ctxt []
  THEN (Local_Defs.unfold_tac ctxt [impl_def, spec_def])
  THEN (Method.try_intros_tac ctxt @{thms ext assuming_cong_strong[rotated 1]} [])
    (* unfold the recursive step on the right hand side exactly once *)
  THEN (resolve_tac ctxt @{thms sym} 1)
  THEN (EqSubst.eqsubst_tac ctxt [1] simps 1 THEN defer_tac 1)
  THEN (REPEAT_DETERM (EqSubst.eqsubst_tac ctxt [0] @{thms unguard_unfold_context} 1 THEN defer_tac 1))
  THEN Clasimp.auto_tac ctxt

(* extract a leading "assuming" clause, if it exists *)
fun get_asms ctxt t = case t of
  (Const(@{const_name assuming},_) $
      (Const(@{const_name tyargCtr},Type (@{type_name tyarg},[asmT]))) $ e) =>
        (Syntax.check_term (Proof_Context.allow_dummies ctxt)
          (HOLogic.mk_Trueprop (Const(@{const_name holds},dummyT) $ Logic.mk_type asmT)),e)
  | _ => (@{prop True},t)

fun dest_def ctxt const_name = 
  let val thm = Proof_Context.get_thm ctxt (const_name ^ "_spec_def")
      val ((_,[thm']),_) = Variable.import true [thm] ctxt
      val (lhs,rhs) = Logic.dest_equals (Thm.prop_of thm')
      val (Const(_,T), args) = Term.strip_comb lhs

      val rec_t = Const(const_name ^ "_impl", T)
      val rec_t_raw = Const(const_name ^ "_impl_raw", T)

      val varnm = Long_Name.base_name (Term.dest_Const_name rec_t_raw)

      val free_t = Free(varnm, T)
      val rhs' = Term.map_aterms (fn t => if t = rec_t then free_t else t) rhs
      val (asm,_) = get_asms ctxt rhs'

  in (thm, rec_t_raw, T, free_t, args, asm, rhs') end

fun extract_goal st = 
  let val g = #goal (Proof.simple_goal st)
  in Thm.term_of (Conjunction.mk_conjunction_balanced (Thm.cprems_of g)) end

fun solve_extracted_tac ctxt asm thms = 
  Method.insert_tac ctxt asm 1 THEN
  Goal.recover_conjunction_tac THEN 
  (solve_tac ctxt thms 1)

(* drops _rec_spec and locale qualifier *)
fun base_name nm = 
  let
     val q = Long_Name.qualifier nm
  in String.substring (q, 0, String.size q - 9) end

fun cryptol_termination_cmd const_name_raw includes_raw thy =
  let   
    val ctxt = Proof_Context.init_global thy
    val includes = map (Bundle.check_name ctxt) includes_raw
    val Const(full_const_name, _) = Proof_Context.read_const {proper=false,strict=false} ctxt const_name_raw
    val const_name = base_name full_const_name
    val rec_spec_locale = Long_Name.qualifier full_const_name

    (* construct a function equation based on the shape of the _spec definition *)
    val (spec_def, raw_const, T, free_t, args, asm, rhs) = dest_def ctxt const_name

    val f = HOLogic.mk_eq (Term.list_comb (free_t,args), rhs)
    val specs = [(((Binding.empty,[]),HOLogic.mk_Trueprop f), [], []) ]
    val rec_nm = fst (Term.dest_Free free_t)

    val lthy_ov = Overloading.overloading [(rec_nm, Term.dest_Const raw_const, false)] thy
    val b_ov = Binding.name rec_nm
    val fun_cfg = Function_Common.default_config

    (* we expect the pattern coverage proof to be trivial, since there is exactly one
       equation, thus we simply use "auto" rather than adding another manual proof step *)
    val (_, lthy_ov') =            
      Function.add_function [(b_ov, SOME T, NoSyn)] specs fun_cfg Clasimp.auto_tac lthy_ov

    val lthy = lthy_ov'
      |> Local_Theory.exit_global
      |> Named_Target.init includes ""
      |> Local_Theory.begin_nested
      |> snd

    (* we want to override the after_qed action for the termination proof, so we
       start an interactive proof, extract the subgoal(s), and then discard the proof state.
       Then we initiate the proof again via "Proof.theorem" and install our own after_qed hook. *)
    val term_goal = extract_goal (Function.termination (SOME raw_const) lthy)
    val expr = (rec_spec_locale, (("",false),(Expression.Positional [], [])))
    val impl_def = Proof_Context.get_thm lthy (const_name ^ "_impl_def")

    val lthy1 = Variable.declare_term term_goal lthy
  
    fun afterqed thmss ctxt0 = 
      let
        (* we can assume the guard on the type signature for the purposes of termination,
           since we can discharge it when proving the final lemma *)
        val (info,ctxt1) = ctxt0
          |> Assumption.add_assumes [Thm.cterm_of ctxt0 asm]
          |-> (fn [asm_thm] =>  
               Function.prove_termination (SOME raw_const) 
                (solve_extracted_tac ctxt0 [asm_thm] (flat thmss)))

        val SOME [simp] = #simps info

        val [simp_global_abs] =
          Proof_Context.export ctxt1 lthy [Local_Defs.abs_def_rule ctxt1 simp]

        val ctxt2 = ctxt1
          |> Local_Theory.end_nested
          |> `(fn ctxt_ => #simps (Function.get_info ctxt_ raw_const))
          |-> (fn SOME [simp_global] => Simplifier.del_simp simp_global)
          |> Interpretation.global_interpretation ([expr],[]) []
          |> Proof.refine_singleton (Method.Basic (fn ctxt_ => fn _ => 
               CONTEXT_TACTIC (rec_prover_tac ctxt_ impl_def spec_def [simp_global_abs])))
          |> Proof.global_done_proof

        val (([simp_term]),ctxt3) = Variable.import_terms true [Thm.prop_of simp] ctxt2

        fun to_base t = case t of
          Const(nm, U) => if nm = dest_Const_name raw_const then Const(full_const_name, U) else raise Same.SAME
         | _ => raise Same.SAME
        val goal = Term.map_aterms_same to_base simp_term

        (* newly-introduced definition from locale intepretation *)
        val def = Proof_Context.get_thm ctxt3 ((Long_Name.base_name const_name) ^ "_def")

        fun tac ctxt = 
                Local_Defs.unfold_tac ctxt [def] 
           THEN (Method.try_intros_tac ctxt @{thms ext assuming_cong_strong[rotated 1]} [])
           THEN (EqSubst.eqsubst_tac ctxt [1] [simp_global_abs] 1 THEN defer_tac 1)
           THEN (REPEAT_DETERM (EqSubst.eqsubst_tac ctxt [0] @{thms unguard_unfold_context} 1 THEN defer_tac 1))
           THEN Clasimp.auto_tac ctxt

        val alt_def = Goal.prove ctxt3 [] [] goal (fn st => tac (#context st))
        val [alt_def'] = Variable.export ctxt3 ctxt2 [alt_def]

      in ctxt3
       |> Local_Theory.note ((Binding.name ((Long_Name.base_name const_name) ^ "_alt_def"),[Code.singleton_default_equation_attrib]),[alt_def'])
       |-> K Local_Theory.exit
      end

    val st = Proof.theorem NONE afterqed [[(Logic.mk_implies (asm, term_goal),[])]] lthy1

 in st end
end
\<close>

attribute_setup set_const_hash = \<open>
let
  (* TODO: This is a bit of a hack to parse hex values as outer syntax. We need some additional
           input validation, as Lexicon.read_num will simply return zero given invalid input.

           Ideally this would instead be provided as a primitive and
           stored as a proper Num or Nat token. *)

  val parse_zero = Parse.int >> (fn i => if i = 0 then () else Scan.fail i)
  val parse_hex = (parse_zero |-- Parse.name) >> (fn str => 
    let val chars = Symbol.explode str
        val valid = length chars > 1 andalso
                    List.all Symbol.is_ascii_hex (tl chars) andalso 
                    hd chars = "x"
    in if valid then #value (Lexicon.read_num ("0"^str)) else Scan.fail str end)
in (Args.term -- Scan.lift parse_hex) >> 
    (fn (t,hash) => Cryptol_Definition.set_const_hash_attrib (dest_Const_name t) hash) end
\<close>
\<open>Tag a constant (taken from the provided definition) with a given hash.\<close>


ML\<open>
val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>cryptol_definition\<close> "constant definition"
    (Parse.const_binding -- (Scan.option (Parse.where_ |-- Parse.prop)) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, (mspec)), prems), params) => 
         Cryptol_Definition.cryptol_definition_cmd decl mspec prems params))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>cryptol_termination\<close> "install a recursive schema given a termination proof"
    (Parse.const -- Scan.optional Parse_Spec.includes []  >> (fn (const_name_raw, incls) => 
       Toplevel.theory_to_proof (Cryptol_Definition.cryptol_termination_cmd const_name_raw incls)))
\<close>



syntax "_forall" :: "term \<Rightarrow> bool"  (\<open>(\<open>notation=\<open>prefix\<close>\<close>FORALL)\<close>)

parse_translation
\<open>
let
  fun forall_tr ctxt [x] = case Type.strip_constraints (Term_Position.strip_positions x) of
      Free (nm,_) => 
        let val Const(_,T) = Proof_Context.read_const {proper=false, strict=false} ctxt nm
            val (Ts,_) = Term.strip_type T
            val args = map Free (Variable.variant_names ctxt (map (fn _ => ("",dummyT)) Ts))
        in Term.list_comb (x,args) end
    | _ => error ("FORALL: unexpected term: " ^ Syntax.string_of_term ctxt x)
in [(@{syntax_const "_forall"}, forall_tr)] end
\<close>

setup \<open>Sign.add_path "experiment"\<close>

(* when a definition body is omitted, an auxiliary constant is
   created that can be overridden *)

context includes type_arg_syntax and assuming_syntax begin

cryptol_definition test2 :: "{'a} ('a > 0) =?> (int \<Rightarrow> 'a \<Rightarrow> nat)"

declare [[set_const_hash test2 0xA]]

ML \<open>case Cryptol_Definition.get_const_hash @{theory} (dest_Const_name @{term test2}) of
  SOME 10 => ()
 | _ => error "get_const_hash failed"
\<close>

private lemma "test2`{'a} x y = (('a > 0) \<Rightarrow> (test2_raw`{'a}) x y)"
  unfolding test2_def
  by simp
end

overloading test2' \<equiv> "test2_raw :: ('a::len) tyarg \<Rightarrow> int \<Rightarrow> 'a \<Rightarrow> nat" begin
definition "test2' \<equiv> (\<lambda>(_ :: 'a tyarg) (_ :: int) (_ :: 'a) . LENGTH('a::len))"
end

context includes type_arg_syntax begin
private lemma "test2`{1} x y = 1"
  unfolding test2_def test2'_def
  by simp
end

hide_const test2_raw test2
hide_fact test2'_def

experiment begin
context includes type_arg_syntax and assuming_syntax begin

cryptol_definition add_sym :: "{'a, 'b :: ring} ('a > 0) =?> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "add_sym x y \<equiv> LEN('a) > 0 \<and> x + y = y + x"

declare [[set_const_hash add_sym 0xA]]

ML \<open>(dest_Const_name @{term add_sym})\<close>

ML \<open>case Cryptol_Definition.get_const_hash @{theory} (dest_Const_name @{term add_sym}) of
  SOME 10 => ()
 | _ => error "get_const_hash failed"
\<close>

lemma add_sym:"FORALL add_sym"
  unfolding add_sym_def
  by auto

ML \<open>Sign.consts_of @{theory}\<close>
ML \<open>Consts.the_const_type (Sign.consts_of @{theory}) (dest_Const_name @{term add_sym})\<close>

ML \<open>Cryptol_Definition.check_const_hash_thm @{theory} @{thm add_sym}\<close>

end
end

text\<open>@{command cryptol_termination} installs a recursive implementation for a function
based on its recursive schema. It assumes the naming convention below: "_impl" is
the stub (where _impl_raw is the constant to be overridden), "_spec" is the recursive
schema that the implementation needs to match, and the "_rec_spec" locale ultimately defines
the target constant.

Given this setup, the command automates the override process when the recursive call in the spec
definition has the same type signature as the spec constant. In this case, the schema can be used
to generate a valid equation for the "function" command, which is ultimately used to generate
the underlying implementation.

The pattern-completeness obligation is trivial (discharged by auto), as is the witness/validity
obligation from the "rec_spec" locale (discharged by rec_prover_tac). The only proof that the user
must provide is termination.

The result is an "alt_def" theorem which has the same shape as the "spec" theorem but with the
target constant on the left hand side and recursive calls on the right hand side.

NOTE: Because this installs a definition for the _impl_raw constant via an override, this command
is only allowed at the toplevel.
\<close>

context includes type_arg_syntax and assuming_syntax begin

cryptol_definition rec_test_impl :: "{'a} ('a > 0) =?> (int \<Rightarrow> 'a itself \<Rightarrow> nat)" 

cryptol_definition rec_test_spec :: "{'a} ('a > 0) =?>  (int \<Rightarrow> 'a itself \<Rightarrow> nat)"  where
  "rec_test_spec x y \<equiv>
      if LEN('a) = 0 then rec_test_impl`{'a} x y else
      if x > 0 then rec_test_impl`{'a} (x-1) y else if x < 0 then rec_test_impl`{'a} (x+1) y else 0"

end

locale rec_test_rec_spec =
  assumes "rec_test_spec = rec_test_impl"
begin

definition [simplified rec_test_impl_def[abs_def]]: 
  "rec_test = rec_test_impl"

end

alias rec_test = rec_test_rec_spec.rec_test

declare [[set_const_hash rec_test 0xB]]

ML \<open>case Cryptol_Definition.get_const_hash @{theory} (dest_Const_name @{term rec_test}) of
  SOME 11 => ()
 | _ => error "get_const_hash failed"
\<close>

cryptol_termination rec_test
  apply (relation "measure (\<lambda>(_, i, _). nat (abs i))")
  by auto

print_theorems
thm rec_test_alt_def
value "rec_test TY(32) 12 TYPE(32)"

hide_const rec_test_impl rec_test_spec rec_test

hide_fact rec_test_impl_def rec_test_spec_def
          rec_test_alt_def rec_test_def rec_test_impl_raw.elims 
          rec_test_impl_raw.simps rec_test_impl_raw.induct rec_test_rec_spec_axioms

end