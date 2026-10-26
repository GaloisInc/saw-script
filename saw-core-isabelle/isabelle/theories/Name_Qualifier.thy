theory Name_Qualifier
  imports Pure
  keywords "qualifier" "end_qualifier" :: thy_decl
begin

text \<open>
  @{text "qualifier A"} ... @{text "end_qualifier A"} adds a mandatory qualifier @{text A} to all
  names declared in between, in both global and local theory contexts. Declared names are only
  accessible as @{text "A.x"}, both inside and outside the qualified region.

  A long qualifier @{text "A.B"} is equivalent to nested qualifiers @{text A} and @{text B}.
  Trailing dots are ignored, e.g. @{text "A."} is the same as @{text A}. Without an argument (or
  with an argument consisting only of dots), @{text qualifier} and @{text end_qualifier} do nothing.

  A qualifier must be closed in the same context it was opened in, e.g. a qualifier opened inside
  a @{command context} block must be closed before the corresponding @{command end}.
\<close>

ML \<open>
signature NAME_QUALIFIER =
sig
  val qualifier: string * Position.T -> Context.generic -> Context.generic
  val end_qualifier: string * Position.T -> Context.generic -> Context.generic
end;

structure Name_Qualifier: NAME_QUALIFIER =
struct

(*the working context of a local theory is reset to its top-level target after each command,
  so both need to be updated*)
fun map_local_naming f lthy =
  let val n = Local_Theory.level lthy in
    lthy
    |> Local_Theory.map_background_naming f
    |> Local_Theory.map_contexts (fn i => i >= n - 1 ? Proof_Context.map_naming f)
  end;

fun map_naming f = Context.mapping (Sign.map_naming f) (map_local_naming f);

fun current_prefix naming = Long_Name.qualifier (Name_Space.full_name naming (Binding.name "_"));

fun explode_qualifier (qual, pos) =
  let
    val qual' = implode (drop_suffix (fn c => c = ".") (raw_explode qual));
    val quals = if qual' = "" then [] else Long_Name.explode qual';
  in
    if exists (fn q => q = "") quals
    then error ("Bad qualifier " ^ quote qual ^ Position.here pos)
    else quals
  end;

fun check_qualifier (qual, pos) q gthy =
  let
    val naming =
      (case gthy of
        Context.Theory thy => Sign.naming_of thy
      | Context.Proof lthy => Local_Theory.background_naming_of lthy);
    val prefix = current_prefix naming;
    val _ =
      Long_Name.base_name prefix = q orelse
        error ("Qualifier " ^ quote qual ^ " does not match innermost qualifier " ^
          quote (Long_Name.base_name prefix) ^ Position.here pos);
    val _ =
      (case gthy of
        Context.Proof lthy =>
          prefix <> current_prefix (Sign.naming_of (Proof_Context.theory_of lthy)) orelse
            error ("Qualifier " ^ quote qual ^ " was opened outside this local theory" ^
              Position.here pos)
      | _ => true);
  in gthy end;

fun qualifier qual =
  fold (map_naming o Name_Space.mandatory_path) (explode_qualifier qual);

fun end_qualifier qual =
  fold_rev (fn q => check_qualifier qual q #> map_naming Name_Space.parent_path)
    (explode_qualifier qual);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>qualifier\<close> "push mandatory name qualifier"
    (Scan.option Parse.name_position >> (Toplevel.generic_theory o fold qualifier o the_list));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>end_qualifier\<close> "pop mandatory name qualifier"
    (Scan.option Parse.name_position >> (Toplevel.generic_theory o fold end_qualifier o the_list));

end;
\<close>

experiment begin

qualifier
definition z :: "prop \<Rightarrow> prop" where "z P \<equiv> P"
end_qualifier

qualifier "."
definition z' :: "prop \<Rightarrow> prop" where "z' P \<equiv> P"
end_qualifier "."

qualifier "F."
definition w :: "prop \<Rightarrow> prop" where "w P \<equiv> P"
end_qualifier F

ML \<open>
\<^assert> (is_Const (Syntax.read_term \<^context> "z'"));
\<^assert> (is_Free (Syntax.read_term \<^context> "w"));
\<^assert> (is_Const (Syntax.read_term \<^context> "F.w"));
\<close>

ML \<open>\<^assert> (is_Const (Syntax.read_term \<^context> "z"))\<close>

qualifier A
definition x :: "prop \<Rightarrow> prop" where "x P \<equiv> P"
qualifier B
definition x :: "prop \<Rightarrow> prop" where "x P \<equiv> PROP A.x P"
end_qualifier B
end_qualifier A

ML \<open>
\<^assert> (is_Free (Syntax.read_term \<^context> "x"));
\<^assert> (not (can (Syntax.read_term \<^context>) "B.x"));
\<^assert> (String.isSuffix ".A.B.x" (dest_Const_name (Syntax.read_term \<^context> "A.B.x")));
\<close>

thm A.x_def A.B.x_def

qualifier C.D
definition y :: "prop \<Rightarrow> prop" where "y P \<equiv> PROP A.B.x P"
qualifier E
definition y :: "prop \<Rightarrow> prop" where "y P \<equiv> PROP C.D.y P"
end_qualifier D.E
end_qualifier C

ML \<open>
\<^assert> (is_Free (Syntax.read_term \<^context> "y"));
\<^assert> (not (can (Syntax.read_term \<^context>) "D.y"));
\<^assert> (String.isSuffix ".C.D.E.y" (dest_Const_name (Syntax.read_term \<^context> "C.D.E.y")));
\<close>

thm C.D.y_def C.D.E.y_def

end

end
