(commandline-reference)=
# Command Line Reference

This chapter documents the command-line interfaces of the `saw` and
`saw-remote-api` executables in full detail.

## `saw` Command Line

There are three ways to run the `saw` executable:

- `saw` _[options]_
: runs the interactive REPL.

- `saw` _[options]_ _filename_`.saw`
: loads and runs the SAWScript proof logic in the given filename.

- `saw` _[options]_ `-B` _filename_`.isaw`
: loads and runs the filename as a series of REPL commands.

The `-I` option forces REPL mode, even if a filename is given.
Any such filename is ignored.
There is, for the time being at least, no easy way to first load a
file and then enter the REPL.
(The best way to do that is to start the REPL and then load the file
manually with `include`.
Another way is to add the experimental command `subshell` to the end
of the file.)

The `-I` and `-B` options cannot be used together.

Files loaded with the `-B` option can contain REPL `:`-commands.
However, because the file is fed into the system one line at a time,
as if each line were typed separately, each line must be syntactically
complete.
The adjustments and affordances in the REPL meant for interactive use
are also engaged, which can in some cases produce unexpected results.
In general the `-B` option is mostly useful for testing SAW.

The `-B` option can also be spelled `--batch` and the `-I` option can
also be spelled `--interactive`.

The following additional options are available:

`-h`, `-?`, `--help`
: Print a usage message.
  This lists all the available options.

`-V`, `--version`
: Show the version of the SAWScript interpreter.

`-c` _list_, `--classpath=`_list_
: Specify a list of directories to search for Java classes.
  If multiple `-c` options are found, the lists given are concatenated
  in the order seen on the command line.
  The `CLASSPATH` environment variable is also used; its contents go
  on the search path last.
  (That is, directories given with `-c` are searched before directories
  in `CLASSPATH`.)
  Per convention, on Unix (including MacOS) the list is delimited by
  colons; on Windows, use semicolons.

`-i` _list_, `--import-path=`_list_
: Specify a list of directories to search for SAWScript includes.
  If multiple `-i` options are found, the lists given are concatenated
  in the order seen on the command line.
  The `SAW_IMPORT_PATH` environment variable is also used; its contents
  go on the search path last.
  (That is, directories given with `-i` are searched before directories
  in `SAW_IMPORT_PATH`.)
  On Unix (including MacOS) the list is delimited by colons; on
  Windows, use semicolons.

`-t`, `--extra-type-checking`
: Perform extra type checking of intermediate values.
  This option no longer does anything and will be removed eventually.

`-j` _list_, `--jars=`_list_
: Specify a list of paths to `.jar` files to search
  for Java classes.
  The search ordering of `.jar` files given with `-j` relative to `.jar`
  files given with `-c` or in the `CLASSPATH` environment variable is
  not specified.
  <!--
     XXX which is a bug. It depends on the order the variables appear
     in the process environment, because we don't read it carefully
     enough.
  -->
  On Unix (including MacOS) the list is delimited by colons; on
  Windows, use semicolons.

`-b` _list_, `--java-bin-dirs=`_list_
: Specify a list of directories to search for a Java
  executable.
  If this option is not given, the `PATH` environment variable will be
  used instead.
  On Unix (including MacOS) the list is delimited by colons; on
  Windows, use semicolons.

`-d` _num_, `--sim-verbose`=_num_
: Set the verbosity level of the LLVM/Java/MIR symbolic simulator.

`-v num, --verbose=num`
: Set the verbosity level of the SAWScript interpreter.

`--clean-mismatched-versions-solver-cache[=`_dir_`]`
: Run the `clean_mismatched_versions_solver_cache` command on the solver
  cache in the given directory.
  If no directory is given, the `SAW_SOLVER_CACHE_PATH` environment variable
  is used to find the solver cache.
  After cleaning out the cache, exit.
  See [Caching Solver Results](caching-solver-results) for a description of the
  `clean_mismatched_versions_solver_cache` command and the solver caching
  feature in general.

## `saw` Environment Variables

The following environment variables also affect `saw`:

`CLASSPATH`
: Specify a colon-delimited list of directories to search for Java
  classes.
  Note that paths can also be specified using the `-c` (aka `--classpath`)
  command-line option.
  Paths given with `-c` take priority.  
  On Unix (including MacOS) the list is delimited by colons; on
  Windows, use semicolons.

`CRYPTOLPATH`
: Specify a list of directories to search for Cryptol
  imports (including the Cryptol prelude).
  On Unix (including MacOS) the list is delimited by colons; on
  Windows, use semicolons.

(path-definition)=
`PATH`
: If the `--java-bin-dirs` option is not given, then the `PATH` will be
  searched to find a Java executable.

`SAW_IMPORT_PATH`
: Specify a list of directory paths to search for imports.
  Note
  that paths can also be specified using the `-i` (aka `--import-path`)
  command-line option.
  Paths given with `-i` take priority.
  On Unix (including MacOS) the list is delimited by colons; on
  Windows, use semicolons.

`SAW_JDK_JAR`
: Specify the path of the `.jar` file containing the core Java
  libraries. This is only necessary if a Java executable is not found on the
  `PATH` or via the `--java-bin-dirs` option.
  <!-- XXX and won't things just not run if a Java executable is not found? -->

(saw-solver-cache-path-definition)=
`SAW_SOLVER_CACHE_PATH`
: Specify a path at which to keep a cache of solver results obtained during
  calls to certain tactics. A cache is not created at this path until it is
  needed.
  See [Caching Solver Results](caching-solver-results) for further information.
