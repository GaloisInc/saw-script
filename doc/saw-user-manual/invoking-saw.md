# Invoking SAW

There are two almost completely different top-level ways to run SAW, and
as hinted at in the previous sections they are even separate executables.

The default way to use SAW is with its native setup and tactic scripting
language called SAWScript.
For this approach you use the `saw` executable you installed or built in
the previous section.

The other way is to use Python as the scripting language.
This involves more moving parts; the Python bindings connect over a
JSON-based RPC protocol to a server process.
That server is the `saw-remote-api` executable you installed or built in
the previous section.
However, once set up SAW can then be used from your choice of Python
environments, allowing for example the use of notebooks and other
similar interfaces.

## Invoking `saw`

The most common way to run `saw` is by running it on a file of
SAWScript code:

```sh
saw myproofs.saw
```

If you leave the file name off, or give the `-I` option, SAW will
instead start an interactive read-eval-print loop ("REPL") that you
can use for experimentation.

Like many such interfaces, the SAW REPL contains, in addition to the
ordinary SAWScript operations, REPL-specific commands that are written
beginning with a colon (`:`).
If you have a file of REPL commands that you want to run, you can do
that with the `-B` ("batch") option.

### Invoking `saw` with Docker

<!--
XXX: write this
-->

### `saw` Options

Common options include:

`-h` or `--help`
: Show the command-line options summary.

`-V` or `--version`
: Print the SAW version and exit.

`-s` _file_ or `--summary=`_file`
: Write a verification summary to the given file.

`-f pretty` or `--summary-format=pretty`
: Generate a human-readable verification summary.
  (The default is JSON.)

`--detect-vacuity`
: Check for specifications whose precondition is unsatisfiable.
  This defaults to off because it can be expensive and is rarely needed,
  but can be very helpful if one becomes suspicious that some of one's
  specifications are wrong.
  
`--no-color`
: Disable terminal colors, non-ASCII output, and other terminal control codes.

`-i` _dirs_
: Add _dirs_ to the search path for SAWScript imports.
  _dirs_ may be multiple directory names.

Commonly used environment variables include:

`CRYPTOLPATH=`_dirs_
: Specify the search path used for Cryptol imports, as with Cryptol.

`SAW_SOLVER_CACHE_PATH=`_dir_
: Tells SAW to keep a cache of solver results in the specified directory.

Multiple directory names should be separated by colons on Unix and
semicolons on Windows, per standard usage on those platforms.

These options are used with Java verification:

`-b` _dirs_ or `--java-bin-dirs=`_dirs_
: Add _dirs_ to the search path used to find a Java executable.
  _dirs_ may be multiple directory names.

`-c` _dirs_ or `--classpath=`_dirs_
: Add _dirs_ to the Java class path.
  _dirs_ may be multiple directory names.

`-j` _dirs_ or `--jars=`_dirs_
: Add _dirs_ to the Java JAR list.
  _dirs_ may be multiple directory names.

This environment variable is used with Java verification.

`SAW_JDK_JAR`
: Specify the path of the `.jar` file containing the core Java libraries.
  Only needed if SAW cannot discover the location by finding a Java
  executable.

See [the REPL reference](./appendices/repl-reference) for the complete list
of supported options and environment variable settings.
<!--
XXX: the command-line reference shouldn't be stuffed in with the repl reference.
-->


## Invoking `saw-remote-api`

There are several ways to run the remote API server.

The simplest way is to just make sure `saw-remote-api` is on your
`$PATH` and run your Python scripts.
The Python bindings code will find and run it as a subprocess in each
script.
You can also set the environment variable `$SAW_SERVER` to point to the
executable.

You can, however, also run it as a standalone server.
Run the following:
```sh
saw-remote-api http --host 127.0.0.1 --port 8080 saw
```
then before running your Python run the following:
```sh
export SAW_SERVER_URL=http://localhost:8080/saw/
```
where you can set the port number (here 8080) and the endpoint name
(here `saw`) to anything you like within reason.

If you are using Docker, you might do this:
```sh
docker run --name=saw-remote-api -v somedir/myfiles:/home/saw/myfiles -p 8080:8080 galoisinc/saw-remote-api:nightly
```
and
```sh
export SAW_SERVER_URL=http://localhost:8080/
```
This runs the server in its Docker container, exports its socket to the host machine,
and shares the `myfiles` directory.

Note: the Docker container's port is wired to 8080, and the endpoint is `/`.

While in principle you can run either or both of these in the
background (with `&` in the shell, or the `-d` detach option in
Docker), currently there is a strong tendency for SAW errors and
messages to accidentally print to the `saw-remote-api` terminal
instead of being
sent across the RPC connection.
(Such cases are bugs; feel free to report any you encounter.)
<!--
XXX: (at some point that wording should be strengthened, but we aren't ready yet)
-->

Also, occasionally it has been known to abort on error, in which case being
able to restart it easily is helpful.
(Such cases are serious bugs; please report any you encounter.)

### `saw-remote-api` Options

<!-- XXX TBD -->
probably we want here
 - `--log`
 - `--read-only`
 - `--max-occupancy`
 - `--no-evict`
 - `html --tls`
 - `html --session`

<!--
XXX there should be a command-line options reference for saw-remote api in the appendixes
-->

