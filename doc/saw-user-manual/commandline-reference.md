(commandline-reference)=
# Command Line Reference

This chapter documents the command-line interfaces of the `saw` and
`saw-remote-api` executables in full detail.

## `saw` Command Line

There are three ways to run the `saw` executable:

- `saw` [_options_]
: runs the interactive REPL.

- `saw` [_options_] _filename_`.saw`
: loads and runs the SAWScript proof logic in the given filename.

- `saw` [_options_] `-B` _filename_`.isaw`
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

A number of the following options take lists of filenames and/or
directories.
Per convention, on Unix (including MacOS) these lists are delimited by
colons; on Windows, use semicolons.

The following additional options are available:

`-b` _list_, `--java-bin-dirs=`_list_
: Specify a list of directories to search for a Java
  executable.
  If this option is not given, the `PATH` environment variable will be
  used instead.

`-c` _list_, `--classpath=`_list_
: Specify a list of directories to search for Java classes.
  If multiple `-c` options are found, the lists given are concatenated
  in the order seen on the command line.
  The `CLASSPATH` environment variable is also used; its contents go
  on the search path last.
  (That is, directories given with `-c` are searched before directories
  in `CLASSPATH`.)

`--clean-mismatched-versions-solver-cache[=`_dir_`]`
: Run the `clean_mismatched_versions_solver_cache` command on the solver
  cache in the given directory.
  If no directory is given, the `SAW_SOLVER_CACHE_PATH` environment variable
  is used to find the solver cache.
  After cleaning out the cache, exit.
  See [Caching Solver Results](#caching-solver-results) for a description of the
  `clean_mismatched_versions_solver_cache` command and the solver caching
  feature in general.

`-d` _num_, `--sim-verbose`=_num_
: Set the verbosity level of the LLVM/Java/MIR symbolic simulator.

`--detect-vacuity`
: Check for contradictory assumptions.
  This is not the default because it can be expensive and is rarely needed.

`-f` _format_, `--summary-format=`_format_
: Set the output format for the verification summary generated with `-s`.
  The recognized formats are `json` and `pretty`; the default is `json`.
  `pretty` is intended to be more human-readable.

`-h`, `--help`, `-?`
: Print a usage message.
  This lists all the available options.

`-i` _list_, `--import-path=`_list_
: Specify a list of directories to search for SAWScript includes.
  If multiple `-i` options are found, the lists given are concatenated
  in the order seen on the command line.
  The `SAW_IMPORT_PATH` environment variable is also used; its contents
  go on the search path last.
  (That is, directories given with `-i` are searched before directories
  in `SAW_IMPORT_PATH`.)

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

`--no-color`
: Disable <!-- angry fruit salad --> terminal colors and also Unicode
  character output.

`--output-locations`
: Print the current SAWScript source location with every output message.
  This feature is eventually intended to be replaced with a more helpful
  tracing facility.

`-s` _filename_, `--summary=`_filename_
: Write a verification summary to the given file after all proofs are
  done.

`-t`, `--extra-type-checking`
: Perform extra type checking of intermediate values.
  This option no longer does anything and will be removed eventually.

`-T`, `--timestamping`
: Add a timestamp to messages printed during execution.

`-v` _num_, `--verbose=`_num_
: Set the verbosity level of the SAWScript interpreter.
  Recognized verbosity levels range from 0 to 5, and the default is 4.
  This option is eventually intended to be replaced with a more directed
  scheme for controlling the output of different operations and subsystems.

`-V`, `--version`
: Show the version of the SAWScript interpreter.

## `saw` Environment Variables

The following environment variables also affect `saw`.

Some of these hold lists of filenames and/or directories.
Per convention, on Unix (including MacOS) these lists are delimited by
colons; on Windows, use semicolons.

`CLASSPATH`
: Specify a list of directories to search for Java
  classes.
  Note that paths can also be specified using the `-c` (aka `--classpath`)
  command-line option.
  Paths given with `-c` take priority.  

`CRYPTOLPATH`
: Specify a list of directories to search for Cryptol
  imports (including the Cryptol prelude).

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
  See [Caching Solver Results](#caching-solver-results) for further information.


## `saw-remote-api` Command Line

The general form of the `saw-remote-api` command line is one of:

- `saw-remote-api` `-h`
: Print the command-line usage text and exit.
  `-h` can also be spelled `--help` and `-?` is also accepted.

- `saw-remote-api` `-v`
: Print the SAW version and exit.
  `-v` can also be spelled `--version`.

`saw-remote-api` doc
: Dump out the API documentation text.

`saw-remote-api` _mode_ `-h`
: Print the usage text for the given _mode_.
  `-h` can also be spelled `--help`.

`saw-remote-api` [_overall-options_] _mode_ [_mode-options_] [_mode-args_]
: Run the remote API server in the given _mode_.

The available modes are `stdio`, `socket`, and `http`.

### Overall Options

The following options are accepted in any mode:

`--log` _destination_
: Enables fairly verbose connection logs.
  The _destination_ should be either a filename or the magic string
  `stderr` to print to `saw-remote-api`'s standard error.

`--read-only`
: Avoids generating any output files.
  Useful if running on a read-only file system.
  By default `saw-remote-api` saves state to disk so server
  crashes don't lose client context.
  <!--
     XXX: how much, what, when, and in which modes? This is
     argo functionality and argo is mostly undocumented.
  -->

`--max-occupancy` _num_
: Sets the maximum number of sessions allowed at once.
  The default is 1.

`--no-evict`
: Don't evict old sessions if someone connects when the server is
  full.

### `stdio` mode

`saw-remote-api stdio` communicates over `stdin` and `stdout`.

The only _mode-option_ for `stdio` mode is `-h`.
There are no _mode-args_.

### `socket` mode

In socket mode `saw-remote-api` communicates over a socket using a
simple "netstrings" protocol wrapping the basic JSON packets.

The Python bindings will run `saw-remote-api` in socket mode by
default if not pointed to another location.
<!-- Note 20260327: a bunch of things say it uses stdio mode, but it does not. -->

The _mode-options_ for socket mode (besides `-h`) are:

`--session` _session-name_
: Serve as the named session _session-name_.
  Fails if there's already a server for that session.

`--host` _hostname_
: Set the listen hostname or interface address.
  On multihomed machines, listening on specific addresses allows
  accepting connections from some networks and not others.
  To listen for connections from anywhere, use `0.0.0.0` or `::`.
  To restrict connections to the same machine, use `127.0.0.1` or `::1`.
  The default is `::1`.

`--port` _port_
: Set the listen port number.
  If no explicit port is selected `saw-remote-api` lets the OS pick one.
  In any case the port number is printed to standard output during startup.

Socket mode uses no _mode-args_.

### `http` mode

In HTTP mode `saw-remote-api` communicates over a socket using both
HTTP and "netstrings" to wrap the basic JSON packets.

The _mode-options_ for HTTP mode (besides `-h`) are:

`--tls`
: Enable TLS (transport layer security, aka more-modern SSL) and run
  over HTTPS.
  Setting the environment variable `TLS_ENABLE` has the same effect.

`--session` _session-name_
: This option is recognized but not supported for HTTP.

`--host` _hostname_
: Set the listen hostname or interface address.
  On multihomed machines, listening on specific addresses allows
  accepting connections from some networks and not others.
  To listen for connections from anywhere, use `0.0.0.0` or `::`.
  To restrict connections to the same machine, use `127.0.0.1` or `::1`.
  The default is `0.0.0.0`.
  Note that this is different from socket mode.  

`--port` _port_
: Set the listen port number.
  If no explicit port is selected the default is 8080.

In HTTP mode one _mode-arg_ must be provided: the name of the HTTP
endpoint to serve the protocol on.
For example, `saw-remote-api http --host 127.0.0.1 /foo` will respond
to requests made to `http://127.0.0.1:8080/foo`.

## `saw-remote-api` Environment Variables

:::{warning}
This section is under construction!
:::
