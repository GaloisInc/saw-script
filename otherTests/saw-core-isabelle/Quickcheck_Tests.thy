theory Quickcheck_Tests
  imports Cryptol.Cryptol
begin

context includes cryptol_syntax begin

(* Checks that code generation works properly for expressions involving sequences with 
   symbolic lengths, sequence arithmetic, and coercions.
   Notably this requires the cryptol_syntax bundle, which sets up quickcheck to attempt nontrivial
   sequence lengths. *)

ML \<open>
let
fun init_proof ctxt t = ctxt
  |> Variable.declare_term t
  |> Proof.init 
  |> Proof.have false NONE (K I) [] [ ] [ ((Binding.empty,[]),[(t,[])])] false
  |> snd

fun qc t = case Quickcheck.quickcheck [] 1 (init_proof @{context} t) of
    SOME _ => ()
  | NONE => error ("Quickcheck self-test failed: " ^ Syntax.string_of_term @{context} t)


in
qc @{prop "PRED('a > 8) \<Longrightarrow> (y :: ['a + 'b]) + (x :: ['a + 'b]) = ((x : ['b + 'a]) * (y : ['b + 'a]) : ['a + 'b])"};
qc @{prop "PRED('a > 8) \<Longrightarrow> (y :: ['a]'b) = rev_seq y"};
qc @{prop "(y :: ['a]'b) \<noteq> rev_seq y "};
qc @{prop "CARD('a) > 10 \<Longrightarrow> (x :: 'a :: {integral,numeral}) < 12"}
end
\<close>


end
end