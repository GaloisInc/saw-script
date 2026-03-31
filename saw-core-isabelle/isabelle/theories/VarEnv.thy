(* Library for for Frees and Vars environments*)

theory VarEnv
imports Main
begin

ML\<open>                 
signature VARENV =
sig
  val map_sortsT_same : (sort -> sort) -> typ -> typ
  val map_sortsT : (sort -> sort) -> typ -> typ

  val map_sorts_same : (sort -> sort) -> term -> term
  val map_sorts : (sort -> sort) -> term -> term 
  
  val map_typ_Vars : (typ -> typ) -> typ TVars.table * term Vars.table -> 
    typ TVars.table * term Vars.table
  val map_typ_Frees : (typ -> typ) -> typ TFrees.table * term Frees.table -> 
    typ TFrees.table * term Frees.table 

  val map_sort_Vars : (sort -> sort) -> typ TVars.table * term Vars.table -> 
    typ TVars.table * term Vars.table
  val map_sort_Frees : (sort -> sort) -> typ TFrees.table * term Frees.table -> 
    typ TFrees.table * term Frees.table

  val map_sort_keys_Vars : (sort -> sort) -> 'a TVars.table * 'b Vars.table -> 
    'a TVars.table * 'b Vars.table
  val map_sort_keys_Frees : (sort -> sort) -> 'a TFrees.table * 'b Frees.table -> 
    'a TFrees.table * 'b Frees.table

  val reflect_Vars : 'a TVars.table * 'b Vars.table -> typ TVars.table * term Vars.table
  val reflect_Frees : 'a TFrees.table * 'b Frees.table -> typ TFrees.table * term Frees.table

  (* drops entries that are not TFree/Free *)
  val vars_to_Frees : typ TVars.table * term Vars.table -> typ TFrees.table * term Frees.table

  (* drops entries that are not TVar/Var *)
  val frees_to_Vars : typ TFrees.table * term Frees.table -> typ TVars.table * term Vars.table

  val cert_Frees : Proof.context -> typ TFrees.table * term Frees.table ->
    ctyp TFrees.table * cterm Frees.table
  val cert_Vars : Proof.context -> typ TVars.table * term Vars.table ->
    ctyp TVars.table * cterm Vars.table

  val uncert_Frees : ctyp TFrees.table * cterm Frees.table -> typ TFrees.table * term Frees.table
  val uncert_Vars : ctyp TVars.table * cterm Vars.table -> typ TVars.table * term Vars.table

  val string_of_Frees : Proof.context -> typ TFrees.table * term Frees.table -> string
  val string_of_Vars : Proof.context -> typ TVars.table * term Vars.table -> string

  (* applies type environment first, then term environment *)
  val instantiate_frees : ctyp TFrees.table * cterm Frees.table -> thm -> thm
end
\<close>

ML \<open>
structure VarEnv: VARENV =
struct

fun map_asortsT_same f (TVar(xi,S)) = TVar(xi, f S)
  | map_asortsT_same f (TFree(x,S)) = TFree(x, f S)
  | map_asortsT_same _ _ = raise Same.SAME

fun map_sortsT_same f = Term.map_atyps_same (map_asortsT_same f)
val map_sortsT = Same.commit o map_sortsT_same
val map_sorts_same = Term.map_types_same o Term.map_atyps_same o map_asortsT_same
val map_sorts = Same.commit o map_sorts_same

fun map_typ_Vars f (envT, env) = (TVars.map (K f) envT , Vars.map (K (Term.map_types f)) env)
fun map_typ_Frees f (envT, env) = (TFrees.map (K f) envT, Frees.map (K (Term.map_types f)) env)

fun map_sort_Vars f (envT, env) = (TVars.map (K (map_sortsT f)) envT , Vars.map (K (map_sorts f)) env)
fun map_sort_Frees f (envT, env) = (TFrees.map (K (map_sortsT f)) envT , Frees.map (K (map_sorts f)) env)

fun map_sort_keys_Vars f (envT, env) = 
  (TVars.make (map (fn ((xi,S),v) => ((xi,f S),v)) (TVars.dest envT)),
  (Vars.make (map (fn ((xi,T),v) => ((xi,map_sortsT f T),v)) (Vars.dest env))))

fun map_sort_keys_Frees f (envT, env) = 
  (TFrees.make (map (fn ((xi,S),v) => ((xi,f S),v)) (TFrees.dest envT)),
  (Frees.make (map (fn ((xi,T),v) => ((xi,map_sortsT f T),v)) (Frees.dest env))))

fun reflect_TVars envT = TVars.map (fn xi => fn _ => TVar xi) envT
fun reflect_TFrees env = TFrees.map (fn xi => fn _ => TFree xi) env

fun reflect_Frees_term envT = Frees.map (fn xi => fn _ => Free xi) envT
fun reflect_Vars_term env = Vars.map (fn xi => fn _ => Var xi) env

fun reflect_Frees (envT, env) = (reflect_TFrees envT, reflect_Frees_term env)
fun reflect_Vars (envT, env) = (reflect_TVars envT, reflect_Vars_term env)


fun var_to_freeT env =
  TFrees.make (map_filter (fn (xi,TFree (yi,S)) => SOME ((yi,S), TVar xi) | _ => NONE) (TVars.dest env))

fun var_to_free env =
  Frees.make (map_filter (fn (xi,Free (yi,S)) => SOME ((yi,S), Var xi) | _ => NONE) (Vars.dest env))

fun vars_to_Frees (envT,env) = (var_to_freeT envT, var_to_free env)

fun free_to_varT env =
  TVars.make (map_filter (fn (xi,TVar (yi,S)) => SOME ((yi,S), TFree xi) | _ => NONE) (TFrees.dest env))

fun free_to_var env =
  Vars.make (map_filter (fn (xi,Var (yi,S)) => SOME ((yi,S), Free xi) | _ => NONE) (Frees.dest env))

fun frees_to_Vars (envT,env) = (free_to_varT envT, free_to_var env)

fun cert_Frees ctxt (envT, env) = (TFrees.map (K (Thm.ctyp_of ctxt)) envT,Frees.map (K (Thm.cterm_of ctxt)) env)
fun cert_Vars ctxt (envT, env) = (TVars.map (K (Thm.ctyp_of ctxt)) envT,Vars.map (K (Thm.cterm_of ctxt)) env)

fun uncert_Frees (envT, env) = (TFrees.map (K (Thm.typ_of)) envT,Frees.map (K (Thm.term_of)) env)
fun uncert_Vars (envT, env) = (TVars.map (K (Thm.typ_of)) envT,Vars.map (K (Thm.term_of)) env)

fun env_ctxt ctxt = ctxt
 |> Config.put show_sorts true 
 |> Config.put show_types true

fun print_typ_full ctxt tp = Syntax.string_of_typ (env_ctxt ctxt) tp
fun print_term_full ctxt t = Syntax.string_of_term (env_ctxt ctxt) t
fun tl' [] = []
  | tl' xs = tl xs

fun TFrees_to_string ctxt envT =
  "{" ^ String.concat (tl' (((TFrees.fold_rev (fn (xi,tp) => fn s => 
    "; " :: print_typ_full ctxt (TFree xi) ^ " \<rightarrow> " ^ 
    print_typ_full ctxt tp :: s))) envT [])) ^ "}"

fun Frees_term_to_string ctxt env =
  "{" ^ String.concat (tl' (((Frees.fold_rev (fn (xi,tp) => fn s => 
    "; " :: print_term_full ctxt (Free xi) ^ " \<rightarrow> " ^ 
    print_term_full ctxt tp :: s))) env [])) ^ "}"

fun string_of_Frees ctxt (envT, env) =
  TFrees_to_string ctxt envT ^ "\n" ^ Frees_term_to_string ctxt env

fun TVars_to_string ctxt envT =
  "{" ^ String.concat (tl' (((TVars.fold_rev (fn (xi,tp) => fn s => 
    "; " :: print_typ_full ctxt (TVar xi) ^ " \<rightarrow> " ^ 
    print_typ_full ctxt tp :: s))) envT [])) ^ "}"

fun Vars_term_to_string ctxt env =
  "{" ^ String.concat (tl' (((Vars.fold_rev (fn (xi,tp) => fn s => 
    "; " :: print_term_full ctxt (Var xi) ^ " \<rightarrow> " ^ 
    print_term_full ctxt tp :: s))) env [])) ^ "}"

fun string_of_Vars ctxt (envT, env) =
  TVars_to_string ctxt envT ^ "\n" ^ Vars_term_to_string ctxt env

fun instantiate_frees (envT, env) = 
     Thm.instantiate_frees (TFrees.empty, env)
  #> Thm.instantiate_frees (envT, Frees.empty)
end

\<close>

end