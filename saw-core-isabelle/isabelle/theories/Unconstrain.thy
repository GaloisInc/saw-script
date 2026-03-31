(* Tools for manipulating class constraints *)

theory Unconstrain
  imports VarEnv
  keywords "unconstrain_const" :: thy_decl
        and "unconstraining" :: thy_decl_block
begin

local_setup \<open>
 let
    fun class_axioms context = 
      let 
        val thy = Context.theory_of context
        val classes = Sign.all_classes thy;
        val class_infos = map_filter (try (Axclass.get_info thy)) classes;
        val class_trivs = map (Thm.class_triv thy) classes;
        val class_axioms = flat (map #axioms class_infos)
      in (class_axioms @ class_trivs) end
 in Local_Theory.add_thms_dynamic (@{binding class_axioms}, class_axioms) end\<close>

lemma prop_eq_true: "PROP A \<Longrightarrow> A \<equiv> (Trueprop True)"
  by (rule equal_intr_rule;simp)

local_setup \<open>
 let
    fun class_defs context = 
      let 
        val thy = Context.theory_of context
        val classes = Sign.all_classes thy;
        val class_infos = map_filter (try (Axclass.get_info thy)) classes;
        val class_trivs = map (Thm.class_triv thy) classes;
        val class_trivs_conv = 
          map (fn thm => Drule.zero_var_indexes (@{thm prop_eq_true} OF [thm])) class_trivs
      in class_trivs_conv @ (map #def class_infos) end
 in Local_Theory.add_thms_dynamic (@{binding class_defs}, class_defs) end\<close>

local_setup \<open>
 let
    fun class_intros context = 
      let 
        val thy = Context.theory_of context
        val classes = Sign.all_classes thy;
        val class_intros = map_filter (try (#intro o Axclass.get_info thy)) classes;
      in class_intros end
 in Local_Theory.add_thms_dynamic (@{binding class_intros}, class_intros) end\<close>

thm class_axioms
thm class_defs
thm class_intros

locale unconstrain_intro begin
named_theorems unconstrain_intro \<open>User-provided intro rules for OFCLASS constraints when unconstraining.\<close>
end
setup \<open>Global_Theory.alias_fact @{binding unconstrain_intro} "Unconstrain.unconstrain_intro.unconstrain_intro"\<close>

(* Wrap the "add" attribute to filter for valid OFCLASS intro rules, so the tactic doesn't
   need to second-guess them. *)
setup \<open>
let
 fun check_ofclass context thm = case try Logic.dest_of_class (Thm.concl_of thm) of
   SOME (TVar _,cl) => ()
 | _ => error ("unconstrain_intro: rule must introduce OFCLASS(?'a,class_name):\n" 
     ^ Thm.string_of_thm (Context.proof_of context) thm)
 fun add_filter (context,thm) = 
  (check_ofclass context thm;  Named_Theorems.add @{named_theorems unconstrain_intro} (context,thm))
 val del = Named_Theorems.del @{named_theorems unconstrain_intro}
in Attrib.setup @{binding unconstrain_intro} (Attrib.add_del add_filter del) 
   "declaration of unconstrain_intro rules" end\<close>

lemma ofclass_type[unconstrain_intro]: "OFCLASS('a::type,type_class)" by standard

experiment begin
lemma "OFCLASS('a::type,type_class)" by (rule unconstrain_intro)

declare ofclass_type[unconstrain_intro del]

lemma "OFCLASS('a::type,type_class)"
  apply (rule unconstrain_intro)?
  apply (rule ofclass_type)
  done
end

ML\<open>                 
signature UNCONSTRAIN =
sig
  val of_class_tac : Proof.context -> int -> tactic

  (* unconstrainT that only unconstrains schematic type variables *)
  val unconstrainT_schematic : Proof.context -> thm -> thm

  val unconstrainT_schematic_cases : Proof.context -> thm -> thm
  val named_insts :  (((indexname * Position.T) * string) list * (binding * string option * mixfix) list) parser
  (* Duplicate the head subgoal, rewriting the given free type variables and schematics.  *)
  val constrain_tac : Proof.context -> (((indexname * Position.T) * string) list * (binding * string option * mixfix) list)  -> thm list -> int -> tactic
  (* Relax sort constraints for a const. If not unchecked, the given type must be an instance of
     the existing constraint. *)
  val unconstrain_const : {unchecked : bool} -> (string * typ option) -> local_theory -> local_theory
  val init_unconstrain_context : (string * typ option) list -> Context.generic -> local_theory

  (* Don't unfold definitions from the given list of theory names *)
  val default_filter_thys : string list
  val unfold_consts_tac : Proof.context -> {filter_thys : string list} -> int -> tactic
  val prove_def_tac : Proof.context -> {max_iterations : int, filter_thys : string list} -> int -> tactic

 (* Unconstrain a definitional theorem via its underlying axioms. Requires that the given theorem
    has the same shape as the underlying axiom, modulo eta-contraction, sort constraints, and
    additional premises. *)
  val unconstrain_definition: 
    Proof.context -> {max_iterations : int, drop_prems : bool, filter_thys : string list} -> thm -> thm

end
\<close>

context begin

lemma case_split_protected: "PROP Pure.prop (P \<Longrightarrow> PROP Pure.prop (Trueprop Q)) \<Longrightarrow> (\<not>P \<Longrightarrow> Q) \<Longrightarrow> Q"
  unfolding Pure.prop_def
  apply blast
  done

(* Allows for safely reversing atomized rules without clobbering HOL
   primitives that were already present before atomizing *)

private definition conj_protect :: "prop \<Rightarrow> prop \<Rightarrow> prop" where
  "conj_protect P Q \<equiv> (PROP P &&& PROP Q)"

private definition imp_safe :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "imp_safe \<equiv> (\<longrightarrow>)"

private definition all_safe :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "all_safe \<equiv> HOL.All"

private lemma atomize_imp_safe: "(A \<Longrightarrow> B) \<equiv> (Trueprop (imp_safe A B))"
  apply (simp add: imp_safe_def)
  apply (rule atomize_imp)
  done

private lemma atomize_all_safe: "(\<And>x. P x) \<equiv> (Trueprop (all_safe (\<lambda>x. P x)))"
  apply (simp add: all_safe_def)
  apply (rule atomize_all)
  done

private definition conj_protect_bool_safe :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "conj_protect_bool_safe P Q \<equiv> P \<and> Q"

private lemma conj_protect_bool_safe: "P = P' \<Longrightarrow> Q = Q' \<Longrightarrow> conj_protect_bool_safe P Q = conj_protect_bool_safe P' Q'"
  by simp

private lemma atomize_conj_protect_safe: "(conj_protect (Trueprop P) (Trueprop Q)) \<equiv> (Trueprop (conj_protect_bool_safe P Q))"
  unfolding conj_protect_def conj_protect_bool_safe_def
  apply (rule atomize_conj)
  done

lemmas atomize_safe = atomize_imp_safe atomize_all_safe atomize_conj_protect_safe
lemmas deatomize_safe = atomize_safe[symmetric]

ML\<open>
structure Unconstrain: UNCONSTRAIN =
struct


fun get_defs thy (nm,T) =
let
  val defs = Theory.defs_of thy
  val specs = Defs.specifications_of defs (Defs.Const,nm)
  fun get_of_spec spec = case try (Thm.axiom thy o the o #def) spec of
     SOME def => (case try Logic.dest_equals (Thm.concl_of def) of
        SOME (Const(nm',T'), _) => if nm = nm' andalso Type.could_match (T',T) then SOME def else NONE
       | _ => SOME def)
   | NONE => NONE
in map_filter get_of_spec specs end

fun filter_const thynms nm = List.exists (fn x => (hd (Long_Name.explode nm)) = x) thynms

fun defs_of_term thy thynms t = Term.fold_aterms 
 (fn Const(nm,T) => (fn defs => defs @ (if filter_const thynms nm then [] else get_defs thy (nm,T))) | _ => I) t []

fun unfold_consts_tac ctxt {filter_thys} = SUBGOAL (fn (goal,i) =>
  let
    val thy = Proof_Context.theory_of ctxt
    val defs = defs_of_term thy filter_thys goal
    
  in Raw_Simplifier.rewrite_goal_tac ctxt defs i end)

fun prove_def_tac ctxt {max_iterations, filter_thys} = SUBGOAL (fn (_,i) =>
let
  val conv = Local_Defs.meta_rewrite_conv ctxt
  val core_tac = resolve_tac ctxt @{thms Pure.reflexive} ORELSE' unfold_consts_tac ctxt {filter_thys = filter_thys}
  fun init_tac j = PRIMITIVE (Conv.gconv_rule conv j) THEN resolve_tac ctxt @{thms Pure.transitive} j
  
in init_tac i THEN unfold_consts_tac ctxt {filter_thys=[]} i THEN (REPEAT_DETERM_N max_iterations (HEADGOAL core_tac))  end)


fun dest_class t = SOME (Logic.dest_of_class t)
  handle TERM _ => NONE

fun of_class_rule ctxt (t,s) = SOME (Thm.of_class (Thm.ctyp_of ctxt t,s))
  handle THM _ => NONE

 fun of_class_tac ctxt i st = if Thm.nprems_of st < i then Seq.empty else
   case (dest_class (Thm.prem_of st i)) of
    SOME t => (case of_class_rule ctxt t of
     SOME rl => resolve_tac ctxt [rl] i st
     | NONE => Seq.empty)
   | NONE => Seq.empty

fun of_class_intro_tac ctxt i st = if Thm.nprems_of st < i then Seq.empty else
  let 
    fun maybe_from_eq thm = @{thm Pure.equal_elim_rule2} OF [thm]
    fun mk_rule thm = the_default thm (try maybe_from_eq thm)

    val user_rules = Named_Theorems.get ctxt @{named_theorems unconstrain_intro}
  in resolve_tac ctxt (map mk_rule user_rules) i st end

fun add_assumes asms ctxt  =
  let
    val (_,ctxt') = Assumption.add_assumes asms ctxt
  in (map Thm.assume asms, ctxt') end

fun implies_intr_asms ctxt thm = Drule.implies_intr_list (Assumption.all_assms_of ctxt) thm

(* import a theorem into a fresh context. The first result is the context with
   theorem variables declared, second result is the context with only the free variables declared
   that were originally free *)

fun import_global thy thm = 
  let
    val ctxt = Proof_Context.init_global thy
    val tfrees = Term.add_tfrees (Thm.prop_of thm) []
    val ctxt1 = fold (fn t => Variable.declare_typ (TFree t)) tfrees ctxt
    val thm1 = Thm.legacy_freezeT thm
    val ctxt2 = Variable.declare_thm thm1 ctxt1
  in (ctxt2,ctxt1,thm1) end

fun zip (x :: xs) (y :: ys) = (x,y) :: zip xs ys
  | zip _ _ = []

(* loose matching: drops mismatched premises prefix, allows mismatched sorts *)
fun match_thms_loose thm1 thm0 = 
  let
    val thy = Thm.theory_of_thm thm0
    fun do_match (t1,t0) env = Pattern.first_order_match thy (Term.strip_sorts t1,Term.strip_sorts t0) env
      handle Pattern.MATCH => env

    val thm1_ts = Thm.concl_of thm1 :: (List.rev (Thm.prems_of thm1))
    val thm0_ts = Thm.concl_of thm0 :: (List.rev (Thm.prems_of thm0))
    val (tenv,_) = fold do_match (zip thm1_ts thm0_ts) (Vartab.empty,Vartab.empty)

    val (sort_env,_) = Pattern.first_order_match thy (Term.strip_sorts (Thm.prop_of thm1), (Thm.prop_of thm1))
      (Vartab.empty, Vartab.empty)

    fun get_sort (x,i) = case Vartab.lookup sort_env (x,i) of
      SOME (_,TVar (_,S)) => S
      | _ => []

    fun mk_cTinst ((x,i), (_, TVar(yi,_))) = 
     let val xi_sort = get_sort (x,i)
     in (((x,i),xi_sort), Thm.global_ctyp_of thy (TVar(yi,xi_sort))) end
      | mk_cTinst ((x,i), (_, t)) = (((x,i),get_sort (x,i)), Thm.global_ctyp_of thy t)
  in TVars.build (Vartab.fold (TVars.add o mk_cTinst) tenv) end

fun restore_vars_fn thm0 thm1 =
 let
    val tenv = match_thms_loose thm1 thm0
    val thm2 = Thm.instantiate (tenv, Vars.empty) thm1
  in thm2 end

fun restore_vars (f : thm -> thm) thm0 = restore_vars_fn thm0 (f thm0)
fun restore_vars_tac (f : tactic) st = Seq.map (restore_vars_fn st) (f st)

fun of_class_intro ctxt thm = Seq.hd (TRYALL (fn i => fn st => restore_vars_tac (of_class_intro_tac ctxt i) st) thm)
fun of_class_trivial ctxt thm = Seq.hd (TRYALL (of_class_tac ctxt) thm)

fun relaxS_same thy S = if Sign.subsort thy (S,Sign.defaultS thy) then Sign.defaultS thy else raise Same.SAME

fun relaxT_same thy (TVar(xi,S)) = TVar(xi, relaxS_same thy S)
  | relaxT_same thy (TFree(x,S)) = TFree(x, relaxS_same thy S)
  | relaxT_same _ _ = raise Same.SAME

fun has_constraintT ctxt (TFree (nm,_)) = Vartab.defined (snd (Variable.constraints_of ctxt)) (nm,~1)
  | has_constraintT _ _ = false

fun relaxT ctxt = Term.map_atyps 
 (fn T => if has_constraintT ctxt T then raise Same.SAME else relaxT_same (Proof_Context.theory_of ctxt) T)

fun relaxT_global thy = Term.map_atyps (relaxT_same thy)

fun unconstrain_definition ctxt opts thm =
let
  val goal_spec = Term.map_types (relaxT ctxt) (Thm.prop_of thm)
  val (inst,ctxt') = Variable.import_inst true [goal_spec] (Variable.set_body false ctxt)
  val opts' = {max_iterations = #max_iterations opts, filter_thys = #filter_thys opts}

  val export = VarEnv.cert_Frees ctxt (Variable.import_inst_revert inst)
  val tac = prove_def_tac ctxt opts' 1 THEN (fn st => if Thm.no_prems st then Seq.single st else
    (error ("Unconstrain definition failed: " ^ Goal_Display.print_goal ctxt "" st)))
  val goal = Term_Subst.instantiate inst goal_spec          
  val goal' = if #drop_prems opts then Logic.strip_imp_concl goal else goal
  val result = Goal.prove_internal ctxt' [] (Thm.cterm_of ctxt' goal') (K tac)
in Thm.instantiate_frees export result end

val default_filter_thys = ["HOL","Fun"]

fun unconstrainT_schematic (ctxt0 : Proof.context) thm0 = 
  let
    val ctxt = Variable.declare_thm thm0 ctxt0
    val thm1 = Goal.protect 0 (implies_intr_asms ctxt (Goal.protect 0 thm0))
    val thm2 = restore_vars Thm.unconstrainT (Drule.zero_var_indexes (Thm.varifyT_global thm1))
    val thm2 = of_class_intro ctxt thm2
    val (tenv,env) = Thm.first_order_match (Thm.cconcl_of thm2, Thm.cconcl_of thm1)
    
    val tenv_frees = TVars.make (filter (fn (_,v) => is_TFree (Thm.typ_of v)) (TVars.dest tenv))
    val morphT = Morphism.instantiate_morphism (tenv_frees, Vars.empty)
    val env_frees = Vars.map (fn _ => fn v => Morphism.cterm morphT v) env
    val morph = Morphism.instantiate_morphism (tenv_frees, env_frees)
    
    val thm3 = of_class_trivial ctxt (Morphism.thm morph thm2)
    val (ctxt1,ctxt_outer,thm4) = import_global (Proof_Context.theory_of ctxt) thm3
    val (ofclass_asms,ctxt2) = add_assumes (Thm.cprems_of thm4) ctxt1
    val thm6 = Drule.implies_elim_list thm4 ofclass_asms
    val thm7 = Goal.conclude thm6
    val thm8 = Drule.implies_elim_list thm7 (map Thm.assume (Thm.cprems_of thm7))
    val [thm9] = Variable.export ctxt2 ctxt1 [thm8]
    val thm10 = Drule.implies_intr_list (map Thm.cprop_of ofclass_asms) (Goal.conclude thm9)
    val [thm11] = Variable.export ctxt1 ctxt_outer [thm10]
    
  in Drule.zero_var_indexes thm11 end

fun rewrite ctxt thms thm = Raw_Simplifier.rewrite_rule ctxt thms thm

fun rewrite_concl ctxt thms st =  
  Conv.fconv_rule (Conv.concl_conv (Thm.nprems_of st) (Raw_Simplifier.rewrite ctxt true thms)) st

fun unconstrainT_schematic_cases (ctxt0 : Proof.context) thm0 =
  let
    val class_intros = Proof_Context.get_thms ctxt0 "Unconstrain.class_intros"
    val intros_all = TRYALL (REPEAT_ALL_NEW (resolve_tac ctxt0 class_intros ORELSE' of_class_tac ctxt0))

    val thm2 = unconstrainT_schematic ctxt0 (Goal.protect 0 thm0)
    val tvars = Term.add_tvars (Thm.prop_of thm2) []
    fun add_type_constrain (xi,[]) = Thm.ctyp_of ctxt0 (TVar (xi, Proof_Context.default_sort ctxt0 xi))
      | add_type_constrain t = Thm.ctyp_of ctxt0 (TVar t)
    val tenv = TVars.make (map (fn t => (t,add_type_constrain t)) tvars)
    val thm3 = thm2
      |> Thm.instantiate (tenv,Vars.empty)
      |> (the o SINGLE intros_all)

    in if Thm.nprems_of thm3 = 0 then Goal.conclude thm3 else
    let
      val res = thm3
        |> rewrite_concl ctxt0 @{thms atomize_safe}
        |> (fn th => Conjunction.uncurry_balanced (Thm.nprems_of th) th)
        |> Conv.fconv_rule (Conv.prems_conv 1 (Object_Logic.atomize ctxt0))
        |> Goal.protect 0
        |> (fn th => @{thm case_split_protected} OF [th])
        |> rewrite ctxt0 @{thms deatomize_safe}
        |> Drule.zero_var_indexes
    in res end
   end

fun list_all ([], t) = t
  | list_all ((a, T) :: vars, t) = list_all (vars, Logic.all_const T $ lambda (Free(a,T)) t)

val named_insts =
  Parse.and_list1
    (Parse.position Args.var -- (Args.$$$ "=" |-- Parse.!!! Parse.embedded_inner_syntax))
    -- Parse.for_fixes;


(* workaround for where_rule deciding to generalize type variables when
   they don't have associated free variables *)
fun where_rule ctxt0 insts fixes thm = 
  let
    val freesT = Term.add_tvars (Thm.full_prop_of thm) []
    val frees = map (fn ((x,i),s) => ("__" ^ x,TVar((x,i),s))) freesT
    val ctxt1 = Variable.declare_thm thm ctxt0
    val frees' = Variable.variant_names ctxt1 frees
    val frees_ct = map (fn t => Thm.cterm_of ctxt1 (Free t)) frees'
    val frees_conj = Conjunction.intr_balanced (map Drule.mk_term frees_ct)
    val ctxt2 = Variable.declare_thm frees_conj ctxt1
    val thm' = Rule_Insts.where_rule ctxt2 insts fixes (Conjunction.intr thm frees_conj)
  in fst (Conjunction.elim thm') end

fun constrain_tac ctxt insts_raw  notes i st = if Thm.nprems_of st < i then Seq.empty else
      let  
          val notes' = map (Thm.prop_of o Thm.forall_intr_vars) notes
          val goal0 = Logic.list_implies (notes', Thm.prem_of st i)

          val goal1 = Drule.mk_term (Thm.cterm_of ctxt goal0)
          val global_ctxt = (Proof_Context.init_global (Proof_Context.theory_of ctxt))
          val [goal2] = Variable.exportT ctxt global_ctxt [goal1]
          val goal3 = Drule.zero_var_indexes goal2
          val env = Thm.first_order_match (Thm.cprop_of goal3, Thm.cprop_of goal1)
          val (instsT,insts) = List.partition (fn (((s,_),_),_) => String.isPrefix "'" s) (fst insts_raw)

          val goal4 = where_rule global_ctxt instsT [] goal3
          val goal5 = Thm.instantiate env goal4
          val ctxt1 = Variable.declare_thm goal5 global_ctxt

          val goal6 = where_rule ctxt1 insts (snd insts_raw) goal5

          val [_,goal7] = Drule.zero_var_indexes_list [st, goal6]

          val goal_term = Thm.term_of (Drule.dest_term goal7)
          val env2 = Thm.first_order_match (Thm.cprop_of goal3, Thm.cprop_of goal4)

          val morph1 = Morphism.instantiate_morphism env
          val morph2 = Morphism.instantiate_morphism env2

          val frees = Term.add_frees (Thm.term_of (Drule.dest_term goal3)) []
          
          fun morph_free (x,T) =
                (* generalize over variables that were changed by "where" *)
                let val T' = Morphism.typ morph2 T
                    val T'' = Morphism.typ morph1 T'

                in if T = T' then NONE else SOME (x,T'') end

          val dep_frees = map_filter morph_free frees
          val goal_term2 = list_all (dep_frees, goal_term)
      in Seq.single (Thm.implies_intr (Thm.cterm_of ctxt goal_term2) st)  end

fun string_of_const_full thy (c,ty) =
  let
    val thy' = thy
     |> Config.put_global show_sorts true 
     |> Config.put_global show_types true
     |> Config.put_global show_question_marks false
    val Const(c',ty') = Term_Subst.zero_var_indexes (Const(c,ty))

  in Syntax.string_of_term_global thy' (Const (c',ty')) ^ "::" ^
     Syntax.string_of_typ_global thy' ty'
  end

fun to_constraint thy (nm,opt_ty) = 
let
  val ty' = Sign.the_const_constraint thy nm
  val ty = case opt_ty of
     SOME ty => ty
   | NONE => Logic.unvarifyT_global (relaxT_global thy ty')
  
in (ty',ty) end

fun unconstrain_const {unchecked} (nm,opt_ty) lthy = 
  let 
      val thy = Proof_Context.theory_of lthy
      val (ty',ty) = to_constraint thy (nm,opt_ty)
      val ty'' = Logic.varifyT_global ty

      val ex = "Existing:\n" ^ (string_of_const_full thy (nm, ty'))
      val new = "Given:\n" ^ (string_of_const_full thy (nm, ty''))

      val _ = if not unchecked then
       ((case Sign.typ_instance thy (ty',ty'') of
          true => ()
        | false => error 
           ("Given constraint is not an instance of existing constraint:\n\n" ^ ex ^ "\n\n" ^ new));
       (case Axclass.class_of_param thy nm of
          SOME _ => warning "Changing constraints for class consts is not recommended."
        | NONE => ())) else ()
      val constrain_global = Sign.add_const_constraint (nm, SOME ty)
      val constrain = Proof_Context.add_const_constraint (nm, SOME (Logic.varifyT_global ty))
 (*      
       
       val constrain = Proof_Context.add_const_constraint (nm, SOME (Logic.varifyT_global ty))

       val context' = Context.mapping constrain_global (Proof_Context.background_theory constrain_global) context
       val context'' = Context.mapping I (fn lthy => Local_Theory.map_contexts (K constrain) (constrain lthy)) context'
*)
  in lthy
    |> Local_Theory.raw_theory constrain_global
    |> constrain
    |> Local_Theory.map_contexts (K constrain)

end

fun init_unconstrain_context cs context =
  let
    val lthy = Context.cases Named_Target.theory_init (snd o Local_Theory.begin_nested) context
    val thy = Proof_Context.theory_of lthy

    fun constrain (nm,opt_ty) lthy =
      let val (_,ty_new) = to_constraint thy (nm,opt_ty)
          val f = Proof_Context.add_const_constraint (nm, SOME (Logic.varifyT_global ty_new))
      in Local_Theory.map_contexts (K f) (f lthy) end

  in fold constrain cs lthy end;
end
\<close>
end


ML \<open>
local

fun read_constraint lthy (t,SOME tp) = (Syntax.read_term lthy t, SOME (Syntax.read_typ lthy tp))
  | read_constraint lthy (t,NONE) = (Syntax.read_term lthy t, NONE)

fun eval_constraint _ (Const(nm,_), ty) = (nm,ty)
  | eval_constraint lthy (t,_) = error ("Provided term is not a constant: " ^ Syntax.string_of_term lthy t)

fun read_eval lthy (t,tp) = eval_constraint lthy (read_constraint lthy (t, tp))

in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>unconstraining\<close> "local theory context with relaxed const constraints"
  ((Parse.and_list1 (Parse.term --  Scan.option (\<^keyword>\<open>::\<close> |-- Parse.typ)) --|  Parse.begin) >> 
    (fn ts => Toplevel.begin_nested_target (fn context => Unconstrain.init_unconstrain_context (map (read_eval (Context.proof_of context)) ts) context)))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>unconstrain_const\<close> "weaken sort constraints for constant"
    (Args.mode "unchecked" -- (Parse.term -- Scan.option (\<^keyword>\<open>::\<close> |-- Parse.typ)) >> (fn (unchecked, (t,tp)) => (fn lthy => 
      Unconstrain.unconstrain_const {unchecked=unchecked} (read_eval lthy (t,tp)) lthy)))
end
\<close>


(* Similar to unconstrain_const, but the constraints are restored after the context ends *)
unconstraining 1 and 0 begin

lemma "(1 :: 'b :: type) = 1 \<and> (0 :: 'c :: type) = 0" 
  by (intro conjI refl)

end

method_setup of_class = \<open>Scan.succeed ( fn ctxt => 
  SIMPLE_METHOD ( (fn thm => (Unconstrain.of_class_tac ctxt 1 thm))))\<close>
  \<open>Discharge trivial OFCLASS constraints\<close>

attribute_setup unconstrain = \<open>Scan.succeed
   (Thm.rule_attribute [] (fn context => fn thm => 
     Unconstrain.unconstrainT_schematic (Context.proof_of context) thm))\<close>
  \<open>Strip sort constraints from schematic types and introduce corresponding OFCLASS preconditions\<close>

attribute_setup unconstrain_def = \<open>Scan.succeed
   (Thm.rule_attribute [] (fn context => fn thm => 
     Unconstrain.unconstrain_definition (Context.proof_of context) 
       {max_iterations=4,drop_prems=true,filter_thys=Unconstrain.default_filter_thys} thm))\<close>
  \<open>Strip sort constraints and premises from definition\<close>

attribute_setup unconstrain_cases = \<open>Scan.succeed
   (Thm.rule_attribute [] (fn context => fn thm => 
     Unconstrain.unconstrainT_schematic_cases (Context.proof_of context) thm))\<close>
  \<open>Strip sort constraints from schematic types and case split over when they are satisified\<close>

experiment begin

context fixes x :: "'a :: zero" and y :: "int" 
  assumes Z: "\<And>(z::'b). z = z \<Longrightarrow> x = 0"
      and W:"y = 0" 
      and U :"\<And>(z::'b). z = z \<Longrightarrow> 0 = x"
begin

lemma X: "((z :: 'e:: one) = 1) \<Longrightarrow> k = 0 \<longrightarrow> 0 = y \<longrightarrow> 0 = x \<and> ((z :: 'e:: one) = 1)"
  by (simp add: Z)

lemmas X_unconstrained = X[unconstrain]
lemmas X_unconstrained_cases = X[unconstrain_cases]

schematic_goal "OFCLASS('e, one_class) \<Longrightarrow> OFCLASS('c, zero_class) \<Longrightarrow> 
                 ((z :: 'e) = ?o) \<Longrightarrow> (k::'c) = ?z \<longrightarrow> 0 = y \<longrightarrow> 0 = x \<and> z = ?o"
  by (rule X_unconstrained[where 'c='c and k=k];assumption)

schematic_goal "OFCLASS('e, one_class) \<Longrightarrow> OFCLASS('c, zero_class) \<Longrightarrow> 
                 ((z :: 'e) = ?o) \<Longrightarrow> (k::'c) = ?z \<longrightarrow> 0 = y \<longrightarrow> 0 = x \<and> z = ?o"
  supply X_unconstrained_local = X[unconstrain]
  thm X_unconstrained_local
  by (rule X_unconstrained_local[where 'c='c and k=k];assumption)

definition "(x = x) \<Longrightarrow> foos (z :: 'a) (w :: 'bb :: linorder) = (1 :: 'ee :: one,x)"

lemma dup: "A \<Longrightarrow> A \<Longrightarrow> True"
  by simp

thm foos_def[unconstrain]
thm foos_def[unconstrain_def]

schematic_goal foos_def2: "?foos (z :: 'a) (w :: 'bb :: type) = (?one,x)"
  by (rule foos_def[unconstrain_def])

lemma 
  fixes B
  assumes A: "\<And>A. A \<Longrightarrow> A \<Longrightarrow> B"
  shows B
  apply (rule A[OF foos_def2])
  apply (rule foos_def)
  apply (rule refl)
  done


schematic_goal "((z :: 'e) = ?o) \<Longrightarrow> (k::'c) = ?z \<longrightarrow> 0 = y \<longrightarrow> 0 = x \<and> z = ?o"
  supply X_unconstrained_cases = X[unconstrain_cases]
  thm X_unconstrained_cases
  by (rule X_unconstrained_cases)

end
end


method_setup constrain = \<open>((Scan.lift Unconstrain.named_insts -- 
  (Scan.optional (Scan.lift (Args.$$$ "notes") |-- Attrib.thms) []))) >> 
  (fn (ts,ns) => fn ctxt => 
  SIMPLE_METHOD ( (fn thm => (Unconstrain.constrain_tac ctxt ts ns 1 thm))))\<close>
  \<open>Duplicate the head subgoal, rewriting the given free type variables and schematic variables.\<close>


experiment begin
context fixes x z assumes A:"\<And>y. (x :: 'a :: ord) = y" and B:"(z :: 'b :: zero) = 0" 
      notes A B
begin

schematic_goal "0 = ?z \<and> y = x \<and> z = 0 \<and> x = (?zz :: 'a :: ord) \<and> x = (?zzz :: 'a)"
  (* combine with subgoal command to generate an ad-hoc lemma with additional class constraints *)
  (* schematics may also be instantiated in the copied subgoal, which is applied after type
     rewriting. Note that these instantiations only apply to the copied goal - the original
     goal is left unmodified *)
    (* noted theorems are copied as subgoal premises before constraining. This allows us to 
       include rewritten variants of assumptions *)
  apply (constrain 'a="'d::{linorder,zero}" and z=0 and zzz=0 notes A)
  subgoal H premises prems for x' y'
    by (simp add: prems[symmetric] B prems)
  apply (cases "class.linorder ((\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) (<)")
   supply H_unconstrained = H[unconstrain]
   thm H
   thm H_unconstrained
   apply (rule H_unconstrained[where 'd='a])
  subgoal by standard
    apply (erule linorder.intro_of_class)
   apply (rule A)
  apply (simp add: A B)
  by (simp add: A[symmetric])

schematic_goal "0 = ?z \<and> y = x \<and> z = 0 \<and> x = (?zz :: 'a :: ord) \<and> x = (?zzz :: 'a)"
  (* combine with subgoal command to generate an ad-hoc lemma with additional class constraints *)
  (* schematics may also be instantiated in the copied subgoal, which is applied after type
     rewriting. Note that these instantiations only apply to the copied goal - the original
     goal is left unmodified *)
    (* noted theorems are copied as subgoal premises before constraining. This allows us to 
       include rewritten variants of assumptions *)
  apply (constrain 'a="'d::{linorder,zero}" and z=0 and zzz=0 notes A)
  subgoal H premises prems for x' y'
    by (simp add: prems[symmetric] B prems)
  supply H_unconstrained = H[unconstrain_cases]
  thm H_unconstrained
  apply (rule H_unconstrained[where 'd='a])
  by (simp add: A B A[symmetric])+



definition my_linorder :: "'e :: ord  itself \<Rightarrow> bool" where
  "my_linorder _ \<equiv> class.linorder ((\<le>) :: 'e \<Rightarrow> 'e \<Rightarrow> bool) (<)"

lemma my_linorder_ofclass: "(my_linorder TYPE('e)) \<Longrightarrow> OFCLASS('e:: ord,linorder_class)"
  apply (rule linorder.intro_of_class)
  apply (simp add: my_linorder_def)
  done

lemma "x > y \<Longrightarrow> 0 = z \<Longrightarrow> z = 0"
  supply [unconstrain_intro] = zero.intro_of_class my_linorder_ofclass
  apply (constrain 'a="'d::{linorder,zero}")
  subgoal H[unconstrain_cases] by simp
  apply (rule H;assumption?)
  apply (subgoal_tac "\<not> my_linorder TYPE('a)")
   apply simp
  apply assumption
  done

end

end

experiment begin
context fixes a b :: "'c :: semiring_1" begin

definition "a = b \<Longrightarrow> foo (z :: 'a :: linorder) x \<equiv> x \<in> {y::nat. y = 0 \<and> 0 = x \<and> a = a}"

lemma "foo (z :: 'a :: linorder) x \<equiv> x \<in> {y::nat. y = 0 \<and> 0 = x \<and> a = a}"
  by (rule foo_def[unconstrain_def])

end


end


context fixes x :: "'a :: linorder" begin
definition "baz \<equiv> x"

unconstrain_const Unconstrain.baz
end

lemma "baz (x :: 'a :: type) = x"
  by (simp add: baz_def[unconstrain_def])

hide_const baz
hide_fact baz_def

context begin
unconstraining 
  power and of_nat
begin

lemma [unconstrain_def]: "(^) :: 'a :: {one,times} \<Rightarrow> nat \<Rightarrow> 'a \<equiv> \<lambda>uu uua. rec_nat (\<lambda>a. 1) (\<lambda>n na a. a * na a) uua uu"
  by (rule power_def[unconstrain_def])


lemma [unconstrain_def]: "of_nat n = ((+) 1 ^^ n) (0 :: 'a :: {one,plus,zero})"
  by (rule of_nat_def[unconstrain_def])
end
end

end