from pygments.lexer import RegexLexer, bygroups, using
from pygments.lexers.haskell import CryptolLexer
# See https://pygments.org/docs/tokens/ for the specs on these.
from pygments.token import (
    Punctuation,
    Literal,
    Comment,
    Operator,
    Keyword,
    Name,
    String,
    Number,
    Whitespace,
)


class SAWScriptLexer(RegexLexer):
    name = "SAWScript"
    aliases = ["sawscript", "saw-script"]
    filenames = ["*.saw", "*.isaw"]
    tokens = {
        "root": [
            # Whitespace-like tokens
            (r"\s+", Whitespace),
            (r"//.*?$", Comment.Singleline),
            (r"/\*", Comment.Multiline, "comment"),
            # String literals
            (r"\"", String.Double, "string"),
            # Embedded Cryptol
            (r"\{\{|\{\|", Literal, "cryptol"),
            # Symbols
            (r"<-|->|==>", Operator.Word),
            (r"~|-|\*|\+|/|%|\^|#|>>|>=|>|<<|<=|<|==|!=|&&|&|\|\||\||@", Operator),
            (r"=", Operator.Word),
            (r",|;|\(|\)|::|:|\[|\]|\{|\}|\.|\\", Punctuation),

            # Identifiers of various kinds
            # These require at least a space after (so we don't eat part of some
            # other identifier)

            # Reserved words used in declarations
            (
                r"(let|rec|and|in|typedef|rebindable)(\s+)",
                bygroups(Keyword.Declaration, Whitespace),
            ),
            # Reserved words used in imports
            (
                r"(import|submodule|as|hiding)(\s+)",
                bygroups(Keyword.Namespace, Whitespace),
            ),
            # Other reserved words
            (
                r"(do|if|then|else)(\s+)",
                bygroups(Keyword.Reserved, Whitespace),
            ),
            # Builtin type names
            # (some of these are reserved words, some not; pretend they
            # all are for simplicity)
            (
                r"(Int|String|Term|Type|Bool|AIG|CFG|"
                r"CryptolModule|ProofResult|SatResult|"
                r"SimpSet|Theorem|"
                r"Ghost|"
                r"LLVMSetup|JVMSetup|MIRSetup|ProofScript|TopLevel|"
                r"LLVMModule|LLVMType|LLVMValue|LLVMSpec|"
                r"FunctionProfile|FunctionSkeleton|ModuleSkeleton|SkeletonState|"
                r"JavaClass|JavaType|JVMValue|JVMMethodSpec|JVMSpec|"
                r"MIRModule|MIRAdt|MIRType|MIRValue|MIRSpec|"
                r"YosysSequential|YosysTheorem|"
                r"SetupValue|CrucibleSetup|CrucibleMethodSpec|"
                r"BisimTheorem)(\s+)",
                bygroups(Keyword.Type, Whitespace),
            ),
            # Builtin functions
            # We don't attempt to list all 400-odd builtins (if we want to do
            # that, we should find a way to extract or dump out the builtins
            # table from the SAW source so there's one copy of the info), but
            # it seems worth listing a few of the commonly used ones.
            (
                r"(return|include|show|print|type|exit|"
                r"fail|fails|undefined|"
                r"eval_bool|eval_int|eval_size|eval_list|"
                r"enable_experimental|enable_deprecated|"
                r"for|null|nth|head|tail|concat|length|"
                r"str_concat|str_concats|"
                r"prove|prove_print|sat|"
                r"unfolding|simplify|normalize_term|goal_normalize|"
                r"goal_apply|admit|"
                r"abc|bitwuzla|boolector|cvc4|cvc5|z3|mathsat|yices|rme|"
                r"offline_rocq|"
                r"empty_ss|basic_ss|cryptol_ss|addsimp|rewrite|"
                r"parse_core|"
                r"declare_ghost_state|"
                r"llvm_sizeof|llvm_type|llvm_int|llvm_float|llvm_array|"
                r"llvm_alias|llvm_struct_type|llvm_pointer|"
                r"llvm_fresh_var|llvm_fresh_cryptol_var|llvm_fresh_pointer|"
                r"llvm_term|llvm_struct_value|llvm_elem|llvm_field|"
                r"llvm_alloc|llvm_alloc_aligned|llvm_alloc_readonly|"
                r"llvm_alloc_global|llvm_global|"
                r"llvm_points_to|llvm_null|"
                r"llvm_ghost_value|"
                r"llvm_assert|llvm_execute_func|llvm_return|"
                r"llvm_load_module|llvm_verify|llvm_unsafe_assume_spec|"
                r"java_bool|java_byte|java_char|java_short|java_int|"
                r"java_long|java_float|java_double|java_array|java_class|"
                r"jvm_fresh_var|jvm_alloc_object|jvm_alloc_array|jvm_term|"
                r"jvm_term|"
                r"jvm_ghost_value|"
                r"jvm_assert|jvm_execute_func|jvm_return|"
                r"jvm_verify|jvm_unsafe_assume_spec"
                r"mir_bool|mir_char|mir_{i,u}{8,16,32,64,128}|"
                r"mir_{i,u}size|mir_f{32,64}|mir_str|mir_tuple|"
                r"mir_ref|mir_ref_mut|mir_lifetime|"
                r"mir_find_adt|mir_adt|mir_array|"
                r"mir_fresh_var|mir_fresh_cryptol_var|"
                r"mir_alloc|mir_alloc_mut|"
                r"mir_term|mir_array_value|mir_elem_ref|mir_elem_value|"
                r"mir_enum_value|mir_struct_value|"
                r"mir_static|"
                r"mir_points_to|"
                r"mir_ghost_value|"
                r"mir_assert|mir_execute_func|mir_return|"
                r"mir_load_module|mir_verify|mir_unsafe_assume_spec|"
                r"yosys_import|yosys_import_sequential|yosys_verify|"
                r"summarize_verification)(\s+)",
                bygroups(Name.Builtin, Whitespace)
            ),
            # Builtin constants
            (r"(true|false)(\s+)", bygroups(Keyword.Constant, Whitespace)),
            # All other identifiers
            (r"[a-zA-Z_][\w']*", Name),

            # Number literals
            (r"0[bB][0-1]+", Number.Bin),
            (r"0[oO][0-7]+", Number.Oct),
            (r"0[xX][0-9a-fA-F]", Number.Hex),
            (r"\d+", Number.Integer),
        ],
        "comment": [
            (r"[^*/]", Comment.Multiline),
            # Allows for arbitrary nesting
            (r"/\*", Comment.Multiline, "#push"),
            (r"\*/", Comment.Multiline, "#pop"),
            (r"[*/]", Comment.Multiline),
        ],
        "string": [
            ('[^"]+', String.Double),
            ('"', String.Double, "#pop"),
        ],
        "cryptol": [
            (r"[^|}]", using(CryptolLexer)),
            (r"\|\}|\}\}", Literal, "#pop"),
            (r"[|}]", using(CryptolLexer)),
        ],
    }
