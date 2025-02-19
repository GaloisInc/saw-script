(repl-reference)=
# REPL Reference

The primary mechanism for interacting with SAW is through the `saw`
executable included as part of the standard binary distribution. With no
arguments, `saw` starts a read-evaluate-print loop (REPL) that allows
the user to interactively evaluate commands in the SAWScript language.
With one file name argument, it executes the specified file as a SAWScript
program.

In addition to a file name, the `saw` executable accepts several
command-line options:

`-h, -?, --help`
: Print a help message.

`-V, --version`
: Show the version of the SAWScript interpreter.

`-c path, --classpath=path`
: Specify a colon-delimited list of paths to search for Java classes.

`-i path, --import-path=path`
: Specify a colon-delimited list of paths to search for imports.

`-t, --extra-type-checking`
: Perform extra type checking of intermediate values.

`-I, --interactive`
: Run interactively (with a REPL). This is the default if no other
  arguments are specified.

`-j path, --jars=path`
: Specify a colon-delimited list of paths to `.jar` files to search
  for Java classes.

`-b path, --java-bin-dirs`
: Specify a colon-delimited list of paths to search for a Java
  executable.

`-d num, --sim-verbose=num`
: Set the verbosity level of the Java and LLVM simulators.

`-v num, --verbose=num`
: Set the verbosity level of the SAWScript interpreter.

`--clean-mismatched-versions-solver-cache[=path]`
: Run the `clean_mismatched_versions_solver_cache` command on the solver
  cache at the given path, or if no path is given, the solver cache at the
  value of the `SAW_SOLVER_CACHE_PATH` environment variable, then exit. See
  the section **Caching Solver Results** for a description of the
  `clean_mismatched_versions_solver_cache` command and the solver caching
  feature in general.

SAW also uses several environment variables for configuration:

`CRYPTOLPATH`
: Specify a colon-delimited list of directory paths to search for Cryptol
  imports (including the Cryptol prelude).

(path-definition)=
`PATH`
: If the `--java-bin-dirs` option is not set, then the `PATH` will be
  searched to find a Java executable.

`SAW_IMPORT_PATH`
: Specify a colon-delimited list of directory paths to search for imports.

`SAW_JDK_JAR`
: Specify the path of the `.jar` file containing the core Java
  libraries. Note that that is not necessary if the `--java-bin-dirs` option
  or the `PATH` environment variable is used, as SAW can use this information
  to determine the location of the core Java libraries' `.jar` file.

(saw-solver-cache-path-definition)=
`SAW_SOLVER_CACHE_PATH`
: Specify a path at which to keep a cache of solver results obtained during
  calls to certain tactics. A cache is not created at this path until it is
  needed. See the section **Caching Solver Results** for more detail about this
  feature.

On Windows, semicolon-delimited lists are used instead of colon-delimited
lists.
