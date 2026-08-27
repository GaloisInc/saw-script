(* Axiomatic extension that allows for relaxing type constraints on the core "type_definition" axiom
from the typedef package. The soundness argument follows from the fact that the existing axiom is
agnostic of the logical content of the class, similar to the underlying axioms for const definitions.

As a sanity check, internally "typedef" is called with the target type constructor signature. 
The resulting axiom is compared against the generated one and the process succeeds only if they match
exactly, modulo renaming the type and Abs/Rep constants. *)

theory Unconstrain_Typedef
  imports Unconstrain
  keywords "unconstrain_typedef" :: thy_goal
begin

ML \<open>
signature UNCONSTRAIN_TYPEDEF =
sig
  val unconstrain_typedef_axiom : typ -> thm -> theory -> theory
  val unconstrain_typedef_axiom_cmd : typ -> theory -> Proof.state
end
\<close>

ML \<open>

structure Unconstrain_Typedef : UNCONSTRAIN_TYPEDEF =
struct

fun term_rule ct =
let
  val prems = Drule.strip_imp_prems ct
  val concl = Drule.strip_imp_concl ct
in Drule.implies_intr_list prems (Drule.mk_term concl) end

fun rule_term thm =
let
  val concl = Drule.dest_term thm
  val prems = Thm.cprems_of thm
  val prems0 = Drule.strip_imp_prems concl
  val concl0 = Drule.strip_imp_concl concl
in Drule.list_implies (prems @ prems0,concl0) end

fun mk_ofsort thy (TVar(xi,[])) S U = 
   if Sign.subsort thy ([U], S)
   then (Logic.mk_of_sort (TVar(xi,[]),S))
   else error ("Given sort constraint is not a subsort of existing: \n" ^ 
               Syntax.string_of_sort_global thy S ^ " vs. " ^
               Syntax.string_of_sort_global thy [U])
  | mk_ofsort _ _ _ _ = raise Fail "mk_ofsort: invalid tvar sort"


fun drop_ofclass_prefix thy (sort::sorts) (prem :: prems) = 
  (case try Logic.dest_of_class prem of
      SOME (ty,cl) => (mk_ofsort thy ty sort cl @ drop_ofclass_prefix thy sorts prems)
    | NONE => (prem :: prems))
 | drop_ofclass_prefix _ [] prems = prems
 | drop_ofclass_prefix _ _ _ = raise Fail "Unexpected number of sort constraints."

fun type_axiom_name thy nm = 
let
  val [(rep_info, _)] = Typedef.get_info_global thy nm
in  #axiom_name rep_info end

fun validate_sort thy (TFree(_,S)) = if Sign.subsort thy (S, @{sort type}) then (SOME S) else NONE 
  | validate_sort _ _ = NONE

fun dest_sort thy t = case validate_sort thy t of
    SOME x => x
  | NONE => error ("Invalid sort for unconstraining: " ^ Syntax.string_of_typ_global thy t)

fun dest_type_sorts thy (Type(_, ts)) = map (dest_sort thy) ts
  | dest_type_sorts thy t = 
      error ("Invalid type signature for unconstraining: " ^ Syntax.string_of_typ_global thy t)

fun relax_thm_sorts thy tp thm =
let
  val sorts = dest_type_sorts thy tp
  val prems = drop_ofclass_prefix thy sorts (Thm.prems_of thm)
in Logic.unvarify_global (Logic.list_implies (prems, Thm.concl_of thm)) end

fun unconstrain_typedef_axiom_term tp thy = 
let
  val nm = dest_Type_name tp
  val [(rep_info, _)] = Typedef.get_info_global thy nm
  val axnm = type_axiom_name thy nm
  val ax = Thm.axiom thy axnm
in relax_thm_sorts thy tp ax end

fun dest_class t = SOME (Logic.dest_of_class t)
  handle TERM _ => NONE

fun of_class_rule ctxt (t,s) = SOME (Thm.of_class (Thm.ctyp_of ctxt t,s))
  handle THM _ => NONE

fun of_class_intro_exact_tac ctxt i st = if Thm.nprems_of st < i then Seq.empty else
 case (dest_class (Thm.prem_of st i)) of
  SOME (TVar(xi,S),cl) => (case of_class_rule ctxt (TVar(xi,cl::S),cl) of
   SOME rl => resolve_tac ctxt [rl] i st
   | NONE => Seq.empty)
 | _ => Seq.empty

fun solve_classes ctxt st =
let val thm' = Seq.hd (TRYALL (of_class_intro_exact_tac ctxt) st)
in Goal.norm_result ctxt thm' end

fun dest_type_definition _ (Const (@{const_name Trueprop},_) $ ((Const (@{const_name type_definition},_)$ Const t1 $ Const t2) $ t3)) = (t1,t2,t3)
  | dest_type_definition thy t = raise Fail ("Unexpected type definition shape:" ^ Syntax.string_of_term_global thy t)

fun set_path' (p :: ps) thy = set_path' ps (Sign.add_path p thy)
  | set_path' [] thy = thy

fun set_path ps thy = set_path' ps (Sign.root_path thy)

fun drop_unconstrain_prefix_string nm = 
let
  fun proc (base :: "unconstrained" :: rest) = base :: rest
    | proc (base :: rest) = base :: (proc rest)
    | proc [] = []

in Long_Name.implode (List.rev (proc (List.rev (Long_Name.explode nm)))) end

fun drop_unconstrain_prefix' (Const (nm,T)) = Const (drop_unconstrain_prefix_string nm,T)
  | drop_unconstrain_prefix' t = t

fun drop_unconstrain_prefixT' (Type (nm,S)) = Type (drop_unconstrain_prefix_string nm,S)
  | drop_unconstrain_prefixT' t = t

val drop_unconstrain_prefixT = Term.map_atyps drop_unconstrain_prefixT'
val drop_unconstrain_prefix = Term.map_types drop_unconstrain_prefixT o Term.map_aterms drop_unconstrain_prefix'

fun unconstrain_typedef_finalize axiom_shape inhabited thy = 
let
  val ((rep,repT),(abs,absT),rep_set) = dest_type_definition thy (Thm.term_of (Drule.dest_term axiom_shape))
  val (Type(nm,args),_) = dest_funT repT

  val args' = map dest_TFree args
  val base_tp_nm = (Long_Name.base_name nm)
 
  fun mk_bind nm' = Binding.qualify false base_tp_nm (Binding.name (Long_Name.base_name nm')) 

  val bindings = 
    { Rep_name = mk_bind rep , 
      Abs_name = mk_bind abs, 
      type_definition_name = Binding.suffix_name ("_" ^ base_tp_nm) (Binding.name "type_definition") }

  val thy0 = Sign.add_path "unconstrained" (set_path (Long_Name.explode (Long_Name.qualifier nm)) thy)

  (* note that the resulting theory is not used, we're only calling typedef in order to validate
     that the axiom has the expected shape *)

  val ((_,info), thy0') = Typedef.add_typedef_global {overloaded = true} 
    (Binding.name base_tp_nm,args',NoSyn) rep_set (SOME bindings)
    (fn ctxt => resolve_tac ctxt [inhabited] 1) thy0

  val typedef_spec_axiom = drop_unconstrain_prefix (Thm.prop_of (Thm.axiom thy0' (#axiom_name (fst info))))

  val axiom_term = axiom_shape
    |> Thm.varifyT_global
    |> Thm.unconstrainT
    |> rule_term
    |> Thm.term_of
    |> Logic.unvarify_types_global

  (* check that typedef emits the correct axiom *)
  val _ = Pattern.first_order_match thy (typedef_spec_axiom, axiom_term)
  

  val base_ax = Binding.name (Long_Name.base_name (type_axiom_name thy nm))
  
  val ((_,thm),thy1) = Thm.add_axiom_global (base_ax,axiom_term) thy
  val thm1 = solve_classes (Proof_Context.init_global thy1) (Thm.varifyT_global thm)
  val thm2 = (thm1 OF [inhabited])

  val [(_,info)] = Typedef.get_info_global thy nm
  
  val (envT,envt) = VarEnv.uncert_Vars (Thm.first_order_match (Thm.cprop_of thm2, Thm.cprop_of (#type_definition info)))

  val _ = if Vars.size envt > 0 then
    raise Fail "Unexpected variable binding in type definition" else ()

  (* final sanity check *)
  val _ = TVars.map (fn (_,S) => fn TVar(_,U) => if Sign.subsort thy (U,S) then () else 
    raise Fail "Resulting type definition is not a sort generalization of the existing one") envT
  
in thy1
  |> Global_Theory.store_thm (base_ax, thm2)
  |> snd
  |> Proof_Context.init_global
  |> Unconstrain.unconstrain_const {unchecked=true} (rep,SOME repT)
  |> Unconstrain.unconstrain_const {unchecked=true} (abs,SOME absT)
  |> Proof_Context.theory_of
end

fun unconstrain_typedef_shape t thy = 
let  
  val axiom_term = unconstrain_typedef_axiom_term t thy
  val axiom_shape = term_rule (Thm.global_cterm_of thy axiom_term)
 
  val lthy = Proof_Context.init_global thy
  val thm'' = solve_classes lthy (Thm.varifyT_global axiom_shape)

  val ((insts,_),_) = Variable.importT [Thm.trivial (Thm.cconcl_of thm'')] lthy
in Thm.instantiate (insts,Vars.empty) thm'' end


fun unconstrain_typedef_axiom t inhabited thy = 
let
  val axiom_shape = unconstrain_typedef_shape t thy
in unconstrain_typedef_finalize axiom_shape inhabited thy end

fun unconstrain_typedef_axiom_cmd t thy = 
let 
  val axiom_shape = unconstrain_typedef_shape t thy
  val [goal] = Thm.prems_of axiom_shape

  fun after_qed_thy inhabited = unconstrain_typedef_finalize axiom_shape inhabited
  val after_qed = (fn [[th]] => Proof_Context.background_theory (after_qed_thy th))
in Proof.theorem NONE after_qed [[(goal, [])]] (Proof_Context.init_global thy) end
end
\<close>

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>unconstrain_typedef\<close> "local theory context with relaxed const constraints"
  (Parse.typ >> 
    (fn tp => Toplevel.theory_to_proof (fn thy => Unconstrain_Typedef.unconstrain_typedef_axiom_cmd (Syntax.read_typ_global thy tp) thy)))
\<close>

typedef (overloaded) 'a not_zero = "{x :: ('a:: semiring_1). x \<noteq> 0 }" 
  morphisms  from_not_zero to_not_zero
  by (rule exI[of _ 1]) simp

hide_fact type_definition_not_zero

unconstrain_typedef "'b::zero_neq_one not_zero"
  by (metis mem_Collect_eq zero_neq_one)

experiment begin
interpretation not_zero: type_definition from_not_zero to_not_zero "{x :: 'a :: zero_neq_one. x \<noteq> 0}"
  by (rule type_definition_not_zero)

lemma "from_not_zero x \<in> {x. x \<noteq> 0}"
  by (rule not_zero.Rep)
end

(* cleanup *)
hide_type not_zero
hide_const from_not_zero
hide_const to_not_zero
hide_fact type_definition_not_zero


end