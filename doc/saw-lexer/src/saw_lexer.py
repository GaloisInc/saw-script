from pygments.lexer import RegexLexer, bygroups, using
from pygments.lexers.haskell import CryptolLexer
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
    filenames = ["*.saw"]
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
            # Reserved words (Keywords, types, constants, builtins)
            # These require at least a space after (so we don't eat part of some
            # other identifier)
            (
                r"(import|and|let|rec|in|do|if|then|else|as|hiding|typedef)(\s+)",
                bygroups(Keyword.Reserved, Whitespace),
            ),
            (
                (
                    r"(JavaSetup|LLVMSetup|MIRSetup|ProofScript|"
                    r"TopLevel|CrucibleSetup|Int|String|Term|Type|Bool|AIG|"
                    r"CFG|CrucibleMethodSpec|LLVMSpec|JVMMethodSpec|JVMSpec|"
                    r"MIRSpec)(\s+)"
                ),
                bygroups(Keyword.Type, Whitespace),
            ),
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
