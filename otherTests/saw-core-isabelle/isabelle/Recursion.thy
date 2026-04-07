theory "Recursion"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
(* Recursive call stub (to be overridden)*)
cryptol_definition rec_fnlba_gt_0rb_impl :: "{'a,'b} ((fin 'a,Ring 'b,Zero 'b,'a > 0) =?> ((['a]'b) \<Rightarrow> 'b))"

(* Recursive call stub (to be overridden)*)
cryptol_definition rec_fn_impl :: "{'a,'b} ((fin 'a,Ring 'b,Zero 'b) =?> ((['a]'b) \<Rightarrow> 'b))"

(* Recursive call schema*)
cryptol_definition rec_fnlba_gt_0rb_spec :: "{'a,'b} ((fin 'a,Ring 'b,Zero 'b,'a > 0) =?> ((['a]'b) \<Rightarrow> 'b))" where
"rec_fnlba_gt_0rb_spec x \<equiv> (head`{'a - 1,'b} x) +`{'b} (rec_fn_impl`{'a - 1,'b} (tail`{'a - 1,'b} x))"

cryptol_definition rec_fnlba_eqeq_0rb :: "{'a,'b} ((fin 'a,Ring 'b,Zero 'b,'a = 0) =?> ((['a]'b) \<Rightarrow> 'b))" where
"rec_fnlba_eqeq_0rb x \<equiv> zero`{'b}"

(* Recursive call schema*)
cryptol_definition rec_fn_spec :: "{'a,'b} ((fin 'a,Ring 'b,Zero 'b) =?> ((['a]'b) \<Rightarrow> 'b))" where
"rec_fn_spec  \<equiv> 
  let
    s_mono = ((if PRED('a > 0) then ((rec_fnlba_gt_0rb_impl`{'a,'b}) : ((['a]'b) \<Rightarrow> 'b)) else coerce (('a = 0) \<Rightarrow> ((rec_fnlba_eqeq_0rb`{'a,'b}) : ((['a]'b) \<Rightarrow> 'b)))) : ((['a]'b) \<Rightarrow> 'b))
  in s_mono"

end

locale rec_fn_rec_spec =
  assumes "rec_fnlba_gt_0rb_spec = rec_fnlba_gt_0rb_impl"and "rec_fn_spec = rec_fn_impl"
begin

definition [simplified rec_fnlba_gt_0rb_impl_def[abs_def],export_global]: 
  "rec_fnlba_gt_0rb = rec_fnlba_gt_0rb_impl"

definition [simplified rec_fn_impl_def[abs_def],export_global]: 
  "rec_fn = rec_fn_impl"

end

alias rec_fnlba_gt_0rb = rec_fn_rec_spec.rec_fnlba_gt_0rb
alias rec_fn = rec_fn_rec_spec.rec_fn

hide_fact rec_fn_rec_spec.rec_fnlba_gt_0rb_def
hide_fact rec_fn_rec_spec.rec_fn_def

context includes cryptol_translation_syntax begin

cryptol_definition rec_fn_valid :: "{'a,'b} ((fin 'a,Ring 'b,Zero 'b,Eq 'b) =?> ((['a]'b) \<Rightarrow> Bit))" where
"rec_fn_valid x \<equiv> (rec_fn`{'a,'b} x) ==`{'b} (sum`{'a,'b} x)"

end
end
