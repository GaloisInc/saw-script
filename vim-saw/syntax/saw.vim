" SAW syntax file
" Language:     saw
" Author:       Stanley Roberts
 
if exists("b:current_syntax")
      finish
endif

syn keyword sawInclude import include

syn keyword sawConstant true false

syn keyword sawType Int String Bool LLVMType Term CrucibleSetup JVMSetup JavaType SetupValue JVMValue LLVMModule CrucibleMethodSpec ProofScript SatResult TopLevel JavaClass JVMMethodSpec Theorem Simpset

syn keyword sawKeyword do let and return as hiding rec in
syn keyword sawConitional if then else

syn keyword sawFunction abc list_term abstract_symbolic llvm_alias add_cryptol_defs llvm_alloc add_cryptol_eqs llvm_alloc_aligned add_prelude_defs llvm_alloc_global add_prelude_eqs llvm_alloc_readonly add_x86_preserved_reg llvm_alloc_readonly_aligned addsimp llvm_array addsimps llvm_array_value admit llvm_cfg approxmc llvm_conditional_points_to assume_unsat llvm_conditional_points_to_at_type assume_valid llvm_conditional_points_to_untyped auto_match llvm_declare_ghost_state basic_ss llvm_double beta_reduce_goal llvm_elem beta_reduce_term llvm_equal bitblast llvm_execute_func boolector llvm_extract caseProofResult llvm_field caseSatResult llvm_float check_convertible llvm_fresh_expanded_val check_goal llvm_fresh_pointer check_term llvm_fresh_var codegen llvm_ghost_value concat llvm_global core_axiom llvm_global_initializer core_thm llvm_int crucible_alloc llvm_load_module crucible_alloc_aligned llvm_null crucible_alloc_global llvm_packed_struct_type crucible_alloc_readonly llvm_packed_struct_value crucible_alloc_readonly_aligned llvm_pointer crucible_array llvm_points_to crucible_conditional_points_to llvm_points_to_at_type crucible_conditional_points_to_untyped llvm_points_to_untyped crucible_declare_ghost_state llvm_postcond crucible_elem llvm_precond crucible_equal llvm_return crucible_execute_func llvm_sizeof crucible_field llvm_spec_size crucible_fresh_expanded_val llvm_spec_solvers crucible_fresh_pointer llvm_struct crucible_fresh_var llvm_struct_type crucible_ghost_value llvm_struct_value crucible_global llvm_symbolic_alloc crucible_global_initializer llvm_term crucible_java_extract llvm_type crucible_llvm_extract llvm_unsafe_assume_spec crucible_llvm_unsafe_assume_spec llvm_verify crucible_llvm_verify load_aig crucible_null mathsat crucible_packed_struct nth crucible_points_to null crucible_points_to_untyped offline_aig crucible_postcond offline_aig_external crucible_precond offline_cnf crucible_return offline_cnf_external crucible_spec_size offline_extcore crucible_spec_solvers offline_smtlib2 crucible_struct offline_unint_smtlib2 crucible_symbolic_alloc offline_w4_unint_cvc4 crucible_term offline_w4_unint_yices cryptol_add_path offline_w4_unint_z3 cryptol_extract parse_core cryptol_load parser_printer_roundtrip cryptol_prims print cryptol_ss print_goal cvc4 print_goal_consts default_x86_preserved_reg print_goal_depth define print_goal_size disable_crucible_assert_then_assume print_term disable_crucible_profiling print_term_depth disable_debug_intrinsics print_type disable_lax_arithmetic prove disable_lax_pointer_ordering prove_core disable_smt_array_memory_model prove_print disable_what4_hash_consing qc_print disable_x86_what4_hash_consing quickcheck dsec_print read_aig dump_file_AST read_bytes empty_ss read_core enable_crucible_assert_then_assume replace enable_crucible_profiling enable_debug_intrinsics rewrite enable_deprecated rme enable_experimental run enable_lax_arithmetic sat enable_lax_pointer_ordering sat_print enable_smt_array_memory_model save_aig enable_what4_hash_consing save_aig_as_cnf env sbv_abc eval_bool sbv_boolector eval_int sbv_cvc4 eval_list sbv_mathsat eval_size sbv_unint_cvc4 exec sbv_unint_yices exit sbv_unint_z3 external_aig_solver sbv_yices external_cnf_solver sbv_z3 fails set_ascii false set_base for set_color fresh_symbolic set_min_sharing get_opt sharpSAT goal_eval show goal_eval_unint show_cfg head show_term hoist_ifs simplify str_concat java_array tail java_bool term_size java_byte term_tree_size java_char time java_class trivial java_double true java_float type java_int undefined java_load_class unfold_term java_long unfolding java_short unint_cvc4 jvm_alloc_array unint_yices jvm_alloc_object unint_z3 jvm_array_is w4 jvm_elem_is w4_abc_aiger jvm_execute_func w4_abc_smtlib2 jvm_extract w4_abc_verilog jvm_field_is w4_offline_smtlib2 jvm_fresh_var w4_unint_cvc4 jvm_modifies_array w4_unint_yices jvm_modifies_elem w4_unint_z3 jvm_modifies_field with_time jvm_modifies_static_field write_aig jvm_null write_aig_external jvm_postcond write_cnf jvm_precond write_cnf_external jvm_return write_core jvm_static_field_is write_saig jvm_term write_saig' jvm_unsafe_assume_spec write_smtlib2 jvm_verify write_smtlib2_w4 lambda yices lambdas z3 length

syn match sawOperator "<-" "=" "=="

syn match sawComment "\v//.*$"
syn region sawComment start="/\*" end="\*/"

syn match   sawEsc contained "\\\""
syn match   sawEsc contained "\\'"
syn match   sawEsc contained "\\\\"
syn match   sawEsc contained "\\n"
syn match   sawEsc contained "\\t"
syn match   sawEsc contained "\\r"
syn match   sawEsc contained "\\\d\+"
syn match   sawEsc contained "\\\(x\|X\)\x\+"
syn region  sawString start="\"" skip="\\\"" end="\"" contains=sawEsc
syn region  sawByte   start="'"  skip="\\'"  end="'"  contains=sawEsc

syn match sawParentheses "("
syn match sawParentheses ")"

syn match   sawNumber "\(0\(x\|X\|b\|B\|o\|O\)\x\+\)\|-\?\(\d\|_\)\+"
syn match ddlIdent "\(\l\|\u\)\(\a\|\d\|_\|'\)*"

" inline cryptol highlight
if filereadable("syntax/cryptol.vim")
      syn include @cry syntax/cryptol.vim
endif
syn region crySnip matchgroup=Snip start="{{" end="}}" contains=@cry

hi def link Snip SpecialComment

hi def link sawInclude        Include
hi def link sawKeyword        Keyword
hi def link sawConditional    Conditional
hi def link sawConstant       Constant
hi def link sawFunction       Function
hi def link sawType           Type
hi def link sawOperator       Operator
hi def link sawParentheses    Delimiter
hi def link sawComment        Comment

hi def link sawEsc            Special
hi def link sawString         String
hi def link sawByte           Character

hi def link sawNumber         Number

let b:current_syntax = "saw"