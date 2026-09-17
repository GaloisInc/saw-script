# Running SAW

There are two almost completely different top-level ways to run SAW, and
as hinted at in the previous sections they are even separate executables.

The default way to use SAW is with its native setup and tactic scripting
metalanguage called SAWScript.
For this approach you use the `saw` executable.

The other way is to use Python as the scripting language.
This involves more moving parts; the Python bindings connect over a
JSON-based RPC protocol to a server process.
This requires first starting the `saw-remote-api` executable.
Then your (separate) Python script talks to the running
`saw-remote-api` process.
SAW can then be used from your choice of Python
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

The most common colon-commands are `:help` (or `:h` or `:?`) which you
can use to retrieve the type and help text for a SAWScript command,
and `:search`, which lets you look for SAWScript commands by their
SAWScript types.

### Invoking `saw` with Docker

The Docker container for `saw` is a wrapper around the `saw`
executable, so `saw` is the default entry point.

The simplest way to run the docker container (on a file called
`myproofs.saw`) is like this:
```sh
docker run --rm -v .:/work -w /work \
   ghcr.io/galoisinc/saw:nightly myproofs.saw
```

This fetches the container image from GitHub, and runs it transiently
(with the `--rm` argument).
The `-v` and `-w` arguments bind your current working directory to the
directory `/work` within the container, and makes that the current
working directory inside.
This allows SAW to find your file `myproofs.saw`.

If you built the container locally and called it `saw`, you can run
that instead like this:
```sh
docker run --rm -v .:/work -w /work saw myproofs.saw
```

You can pass options to the `saw` executable by including them before
the filename, and you can pass environment variables by using the `-e`
option of `docker run`.

Like with the standalone `saw` executable, if you don't pass a
filename it will start the REPL.
If you want to do that, you'll also want the `-i` and `-t` flags
to `docker run` so you can type into it and so the line editing works.
Thus:
```
docker run -i -t --rm -v .:/work -w /work ghcr.io/galoisinc/saw:nightly
```
or
```
docker run -i -t --rm -v .:/work -w /work saw
```

If you want to start a shell inside the container to look around,
instead of running the SAW executable, you can use `--entrypoint
/bin/sh`.

You can also create and start a non-transient container image with
`docker run` and then run SAW from it using `docker exec`.
For more information about using Docker, consult its documentation or
one of the many tutorials available on the internet.

### `saw` Options

Common options include:

`-h` or `--help`
: Show the command-line options summary.

`-V` or `--version`
: Print the SAW version and exit.

`-s` _file_ or `--summary=`_file_
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
: Add _dirs_ to the search path for SAWScript includes.
  _dirs_ may be multiple directory names.

Commonly used environment variables include:

`CRYPTOLPATH=`_dirs_
: Specify the search path used for Cryptol imports, as with Cryptol.

`SAW_IMPORT_PATH=`_dirs_
: Specify the search path used for SAWScript includes.

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

These environment variables are used with Java verification:

`SAW_JDK_JAR`
: Specify the path of the `.jar` file containing the core Java libraries.
  Only needed if SAW cannot discover the location by finding a Java
  executable.

`CLASSPATH`
: Specify the search path for Java class files.
  Can include `.jar` files as well as directories.

See [the REPL reference](saw-repl-reference) for the complete list
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
(here `saw`) on both ends to anything you like within reason.

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

### Common `saw-remote-api` Options

`-h` or `--help`
: Show the command-line options summary.

`-v` or `--version`
: Print the SAW version and exit.

`--max-occupancy` _num_
: Set the maximum number of sessions allowed at once.
  The default is 1.

`--no-evict`
: Don't evict sessions if the server is full.

The following option can be given after the `http` verb on the command
line when running in HTTP mode.

`--tls`
: Enable HTTPS mode, that is, encrypt the network connection.

<!--
XXX there should be a command-line options reference for saw-remote api in the appendixes
-->

