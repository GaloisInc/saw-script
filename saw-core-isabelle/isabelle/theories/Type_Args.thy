(* syntax for explicit type argument abstraction and application *)

theory Type_Args
imports Main Coercible
begin

(* analagous to "itself", but distinct so we can treat it specially during printing and parsing *)
datatype 'a tyarg = tyargCtr

lemma tyarg_single[simp]:
  "(x :: 'a tyarg) = y"
  by (cases x; cases y;simp)

abbreviation tyarg :: "'a itself \<Rightarrow> 'a tyarg" where
  "tyarg _ \<equiv> tyargCtr :: 'a tyarg"

syntax
  "_maybe_coerce" :: "term \<Rightarrow> term"

translations
  "_maybe_coerce x" \<rightharpoonup> "x"

(* if in scope, causes the type application syntax to
   implicitly coerce its arguments *)

bundle implicit_coerce begin
translations
  "_maybe_coerce x" \<rightharpoonup> "CONST coerce x"
end

(* Using datatype rather than typedecl helps with code generation. It simply establishes
   these types as singletons. *)

datatype ('a,'b) And_Tuple = And_TupleTypeCtr

nonterminal type_list
nonterminal tlist_funapp

syntax
  "_type_list_one" :: "type \<Rightarrow> type_list" (\<open>_\<close>)
  "_type_list" :: "type \<Rightarrow> type_list \<Rightarrow> type_list" (\<open>_,_\<close>)
  "_and_tuple" :: "type \<Rightarrow> type \<Rightarrow> type"
  "_type_tuple" :: "type_list \<Rightarrow> type"

translations 
 "_and_tuple" \<rightharpoonup> (type) "And_Tuple"

syntax
  "_tyargT" :: "type \<Rightarrow> type"
  "_tyargCtr" :: "type \<Rightarrow> term"
  "_tyarg" :: "type_list \<Rightarrow> term" (\<open>(1TY/(1'(_')))\<close>)
  "_itself" :: "term \<Rightarrow> term"
  "_fun"   :: "type \<Rightarrow> type \<Rightarrow> type"
  "_collect" :: "term \<Rightarrow> type_list \<Rightarrow> term"

syntax_types
  "_tyargT" \<rightleftharpoons> tyarg

syntax_consts 
  "_tyarg" == tyarg

typed_print_translation \<open>
  let
    fun tyargCtr_tr ctxt (Type (@{type_name tyarg},[U])) []  =
      Syntax.const \<^syntax_const>\<open>_tyargCtr\<close> $ 
        (Const (\<^const_syntax>\<open>Pure.type\<close>, Type (@{type_name itself}, [U])))
  in [(\<^const_syntax>\<open>tyargCtr\<close>, tyargCtr_tr)] end
\<close>

ML \<open>val type_arg_syntax_config = Attrib.setup_config_bool \<^binding>\<open>type_arg_syntax\<close> (K false);\<close>

type_synonym ('a) it = 'a
translations
  "_itself" \<rightharpoonup> (type) "it"
  (type) "'a it" \<rightharpoonup> "TYPE('a)"

  "_type_tuple (_type_list_one t)" \<rightharpoonup> "t"
  "_type_tuple (_type_list t ts)" \<rightharpoonup> "_and_tuple t (_type_tuple ts)"

  "_type_tuple t" \<rightharpoonup> "t"

  "_type_list (_itself TYPE('a)) (_type_tuple (TYPE('b)))"  \<leftharpoondown> "_type_tuple (TYPE(('a,'b) And_Tuple))"
  "_type_list_one (_itself t)" \<leftharpoondown> "_type_tuple t"
  
  (type) "'a" \<leftharpoondown> "_itself (TYPE('a))"

  "_tyarg t" \<rightharpoonup> "CONST tyarg (_itself (_type_tuple t))"
  "_tyarg (_type_tuple t)" \<leftharpoondown> "_tyargCtr t"

hide_type it

term "TY('a list, 'b)"
term "TY('a list)"

lemma "TY('a list,'b,'c  set) = (x :: ('a list, ('b, 'c set) And_Tuple) And_Tuple tyarg)" by (rule tyarg_single)
lemma "TY(int) = (x :: int tyarg)" by (rule tyarg_single)


bundle type_arg_syntax begin

syntax
  "_tlist_args" :: "type_list \<Rightarrow> type \<Rightarrow> type"  (\<open>(\<open>indent=1 notation=\<open>mixfix list enumeration\<close>\<close>{_}/ _)\<close> 0)

translations
  "_tyargT" \<rightharpoonup> (type) "tyarg"

translations
  "_tlist_args (_type_list_one t) x" \<rightharpoonup> "_fun (_tyargT t) x"
  "_tlist_args (_type_list t ts) x"  \<rightharpoonup> "_fun (_tyargT t) (_tlist_args ts x)"
  "_fun" \<rightharpoonup> (type) "fun"

  "_type_list_one (_itself y)" \<leftharpoondown> "_itself (_type_list_one y)"
  "(_type_list (_itself x) (_itself y))" \<leftharpoondown> "_itself (_type_list x y)"

syntax
  "_tlist_funapp" :: "type_list \<Rightarrow> tlist_funapp" (\<open>_\<close>)

syntax
  "_appT" :: "term \<Rightarrow> tlist_funapp \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_`'{_'})\<close> [100,0])


translations
  "(_appT f (_tlist_funapp (_type_list x xs))) y z w v" \<rightharpoonup> "(_appT (f (_tyarg  x)) (_tlist_funapp xs)) y z w v"
  "(_appT f (_tlist_funapp (_type_list_one x))) y z w v" \<rightharpoonup> "f (_tyarg x) (_maybe_coerce y) (_maybe_coerce z) (_maybe_coerce w) (_maybe_coerce v)"

  "(_appT f (_tlist_funapp (_type_list x xs))) y z w" \<rightharpoonup> "(_appT (f (_tyarg  x)) (_tlist_funapp xs)) y z w"
  "(_appT f (_tlist_funapp (_type_list_one x))) y z w" \<rightharpoonup> "f (_tyarg x) (_maybe_coerce y) (_maybe_coerce z) (_maybe_coerce w)"

  "(_appT f (_tlist_funapp (_type_list x xs))) y z" \<rightharpoonup> "(_appT (f (_tyarg  x)) (_tlist_funapp xs)) y z"
  "(_appT f (_tlist_funapp (_type_list_one x))) y z" \<rightharpoonup> "f (_tyarg x) (_maybe_coerce y) (_maybe_coerce z)"


  "(_appT f (_tlist_funapp (_type_list x xs))) y" \<rightharpoonup> "(_appT (f (_tyarg  x)) (_tlist_funapp xs)) y"
  "(_appT f (_tlist_funapp (_type_list_one x))) y" \<rightharpoonup> "f (_tyarg x) (_maybe_coerce y)"


  "(_appT f (_tlist_funapp (_type_list_one x)))" \<rightharpoonup> "f (_tyarg x)"
  "(_appT f (_tlist_funapp (_type_list x xs)))" \<rightharpoonup> "(_appT (f (_tyarg  x)) (_tlist_funapp xs))"

  "_appT f (_tlist_funapp (_type_list x xs))" \<rightharpoonup> "_appT (f (_tyarg  x)) (_tlist_funapp xs)"

  "_collect f (_type_list_one (_itself x))"  \<leftharpoondown> "f (_tyargCtr x)"
  "_collect f (_type_list x y)"  \<leftharpoondown> "_collect (_collect f x) y"
  "_appT f (_tlist_funapp xs)" \<leftharpoondown> "_collect f xs"
  "_tuple TY('a) x" \<leftharpoondown>"_tuple`{'a} x"

syntax
  "_appTNone" :: "term \<Rightarrow> term"  (\<open>(\<open>notation=\<open>infix\<close>\<close>_`'{'})\<close> [1])

translations
  "(_appTNone f) y z w v" \<rightharpoonup> "f (_maybe_coerce y) (_maybe_coerce z) (_maybe_coerce w) (_maybe_coerce v)"
  "(_appTNone f) y z w" \<rightharpoonup> "f (_maybe_coerce y) (_maybe_coerce z) (_maybe_coerce w)"
  "(_appTNone f) y z" \<rightharpoonup> "f (_maybe_coerce y) (_maybe_coerce z)"
  "(_appTNone f) y" \<rightharpoonup> "f (_maybe_coerce y)"
  "(_appTNone f)" \<rightharpoonup> "f"

ML \<open>
val type_list_one_nm = \<^syntax_const>\<open>_type_list_one\<close>
val type_list_nm =  \<^syntax_const>\<open>_type_list\<close>
val tlist_args_nm =  \<^syntax_const>\<open>_tlist_args\<close>
\<close>

declare [[type_arg_syntax]]

end

print_translation \<open>
let
  fun strip_fn t = case t of
       (Const ( \<^type_syntax>\<open>fun\<close> , _) $ t1 $ t2) => t1 :: strip_fn t2
     | _ => [t]

  fun build_fn ts = case ts of
       [t] => t
     | (t1::ts') => Const ( \<^type_syntax>\<open>fun\<close> , dummyT) $ t1 $ (build_fn ts')

  fun build_tlist ts = case ts of
          [t] => Syntax.const type_list_one_nm $ t
        | (t::ts') => Syntax.const type_list_nm $ t $ build_tlist ts'

  fun strip_tyargs ctxt ts = case ts of
          ((Const ( \<^type_syntax>\<open>tyarg\<close>,_) $ t))::ts' => 
              let val (ts1,ts2) = strip_tyargs ctxt ts' in (t::ts1,ts2) end
         | (t::_) => (([], ts))
          
  fun to_tlist_top ctxt [t,u] = 
       if Config.get ctxt type_arg_syntax_config then
            (let val ts = strip_fn u                
                val (targs, rest) = strip_tyargs ctxt (t::ts)
                val body = build_fn rest
             in  Syntax.const tlist_args_nm $ (build_tlist targs) $ body end)
       else raise Match
  
in
  [(\<^type_syntax>\<open>fun\<close>,fn ctxt => fn t => to_tlist_top ctxt t)]
end
\<close>


instantiation tyarg :: (_) enum begin
definition "enum_tyarg == [TY('a)] :: 'a tyarg list"
definition "enum_all_tyarg == (\<lambda>f. f TY('a)) :: ('a tyarg \<Rightarrow> bool) \<Rightarrow> bool"
definition "enum_ex_tyarg == (\<lambda>f. f TY('a)) :: ('a tyarg \<Rightarrow> bool) \<Rightarrow> bool"
instance
  apply standard
  unfolding enum_tyarg_def enum_all_tyarg_def enum_ex_tyarg_def
  by (auto; metis tyarg.exhaust)+
end

experiment begin
context includes type_arg_syntax begin
definition test :: "{'a, 'b} 'd" where "test \<equiv> undefined"
end
term test
end

context includes type_arg_syntax begin
term "x :: {'a, 'b} 'd"
term "x :: {'a} 'd"
term "x :: 'a \<Rightarrow> 'd"
term "(x :: {'a, 'b, 'c} 'd)"
term "(x :: {'a, 'b, 'c} 'd \<Rightarrow> 'e) = (x :: ('a tyarg \<Rightarrow> 'b tyarg \<Rightarrow> 'c tyarg \<Rightarrow> 'd \<Rightarrow> 'e))"
term "(TY('a list),TY('b),TY('c),z)"

term "(x :: {'a,'b,'c} 'y \<Rightarrow> 'z \<Rightarrow> 'k)`{'a,'b,'c} y z"
term "(x :: 'y \<Rightarrow> 'z \<Rightarrow> 'k)`{} (y::'y) z"

context includes implicit_coerce begin
term "(x :: {'a,'b,'c} ('y \<Rightarrow> 'z \<Rightarrow> 'k))`{'a,'b,'c} y z"
term "(x :: 'y \<Rightarrow> 'z \<Rightarrow> 'k)`{} (y::'a) z"
end
term "(x :: {'a,'b,'c} ('y \<Rightarrow> 'z \<Rightarrow> 'k))`{'a,'b,'c} y z"

end


end