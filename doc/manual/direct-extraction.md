# Direct Extraction

In the case of the `max` function described earlier, the relevant inputs
and outputs are immediately apparent. The function takes two integer
arguments, always uses both of them, and returns a single integer value,
making no other changes to the program state.

In cases like this, a direct translation is possible, given only an
identification of which code to execute. Two functions exist to handle
such simple code. The first, for LLVM is the more stable of the two:

* `llvm_extract : LLVMModule -> String -> TopLevel Term`

A similar function exists for Java, but is more experimental.

* `jvm_extract : JavaClass -> String -> TopLevel Term`

Because of its lack of maturity, it (and later Java-related commands)
must be enabled by running the `enable_experimental` command beforehand.

* `enable_experimental : TopLevel ()`

The structure of these two extraction functions is essentially
identical. The first argument describes where to look for code (in
either a Java class or an LLVM module, loaded as described in the
previous section). The second argument is the name of the method or
function to extract.

When the extraction functions complete, they return a `Term`
corresponding to the value returned by the function or method as a
function of its arguments.

These functions currently work only for code that takes some fixed
number of integral parameters, returns an integral result, and does not
access any dynamically-allocated memory (although temporary memory
allocated during execution is allowed).
