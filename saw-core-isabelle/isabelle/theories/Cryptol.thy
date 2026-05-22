theory Cryptol
imports Seq_Code Cryptol_Syntax Fin Seq_Lib ZInt_Code
begin

setup \<open>
let
  fun path_ord (p1,p2) = string_ord (Path.file_name p1,Path.file_name p2)
  
  fun thy_path thy = the (Resources.find_theory_file (Context.theory_long_name thy))
  
  fun thy_info thy = 
    let
      val thy_nm = Context.theory_long_name thy
      val p = thy_path thy
    in Resources.check_thy p thy_nm end
  
  fun same_dir p1 p2 = (Path.dir p1 = Path.dir p2) 
  
  fun local_deps_of thy = 
    let 
      val thys = Theory.nodes_of thy
    in List.filter (fn th => same_dir (thy_path thy) (thy_path th)) thys end
  
  fun sha1_comb xs = SHA1.digest (String.concat (map SHA1.rep xs))

  fun sha1_to_int h = #value (Lexicon.read_num ("0x" ^ SHA1.rep h))

  (* not imported here, but should be included *)

  val seqoob = "Cryptol.SeqOOB"
  val SOME seqoob_path = Resources.find_theory_file seqoob
  val seqoob_info = Resources.check_thy seqoob_path seqoob
   
  fun thy_info_ord (info1,info2) = path_ord (fst (#master info1), fst (#master info2))
  val cryptol_thys = sort thy_info_ord (seqoob_info :: (map thy_info (local_deps_of @{theory})))
  val cryptol_shas = map (fn info => snd (#master info)) cryptol_thys

  val cryptol_theory_hash = sha1_comb cryptol_shas

in
  Cryptol_Definition.set_cryptol_hash (sha1_to_int cryptol_theory_hash)
end
\<close>

ML \<open>
local
fun hex_prefix ms = "0x" ^ implode ms;
in
fun hex n = hex_prefix (map hex_digit (radixpand (16, n)));
end
\<close>

ML \<open>hex (Cryptol_Definition.get_cryptol_hash @{theory})\<close>

end