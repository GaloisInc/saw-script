# SAW Python Client

In-development Python client for SAW. Currently tested on Linux and MacOS -- at present there may be some minor issues running the Python Client in a Windows environment that needs addressed (e.g., some Python process management methods are not cross-OS-compatible).

This SAW client depends on the [saw-remote-api](https://github.com/GaloisInc/saw-script/tree/master/saw-remote-api) server.

# TL;DR Steps to running SAW Python scripts

1. Clone the repo 
```
git clone https://github.com/GaloisInc/saw-script.git
```
2. Enter the repo
```
cd saw-script
```
3. Initialize git submodules 
```
git submodule update --init
```
4. Navigate to the python client
```
cd saw-python
```
5. Install and setup some version of the `saw-remote-api` server and update any
   relevant environment variables as needed (see `saw_client.connect()` documentation
   for the various ways a server can be connected to).
   E.g., here is how the docker image of the server might be used:
```
$ docker run --name=saw-remote-api -d \
  -v $PWD/tests/saw/test-files:/home/saw/tests/saw/test-files \
  -p 8080:8080 \
  galoisinc/saw-remote-api:nightly
$ export SAW_SERVER_URL="http://localhost:8080/"
```
6. Install the Python client (requires Python v3.8 or newer -- we recommend using [`poetry`](https://python-poetry.org/docs/#installation) to install the package):
```
$ poetry install 
```
7. Run tests or individual scripts:
```
$ poetry run python -m unittest discover tests/saw
$ poetry run python tests/saw/test_salsa20.py
```

(We're aware the tests currently emit some `ResourceWarning`s regarding
subprocesses when run via `unittest` even though they pass and successfully
verify the goals. It's on our to-do list.)

# Python Client Installation (via Poetry)

First, clone the repository and submodules.

```
$ git clone https://github.com/GaloisInc/saw-script.git
$ cd saw-script
$ git submodule update --init
```

Then, use [`poetry`](https://python-poetry.org/docs/#installation) to install
the python client from the `saw-python` directory:

```
$ cd saw-python
$ poetry install
```

# SAW server

To run the verification scripts a `saw-remote-api` server must be available,
either as a local executable or running in docker image listening on a port.

## Connecting with a server in a script

Connecting to a server in a Python script is accomplished via the `saw_client.connect`
method. Its accompanying Python doc strings describe the various ways it can be
used. Below is a brief summary:

`saw_client.connect()`, when provided no arguments, will attempt the following in order:

1. If the environment variable ``SAW_SERVER`` is set and refers to an
   executable, it is assumed to be a `saw-remote-api` executable and will be
   used for the duration of the script.
2. If the environment variable ``SAW_SERVER_URL`` is set, it is assumed to be
   the URL for a running SAW server in ``http`` mode and will be connected to.
   (N.B., this can be a local server or a server running in a docker image.)
3. If an executable ``saw-remote-api`` is available on the ``PATH`` it is
    assumed to be a SAW server and will be used for the duration of the script.

Additional arguments and options are documented with the function.

Notable, the `reset_server` keyword can be used to connect to a running server
and reset it, ensuring states from previous scrips have been cleared. E.g.,
`saw_client.connect(reset_server=True)`.


## Acquiring a SAW Server

There are several ways a server executable can be obtained.

### Server executables

An executable of the server is included in the SAW release/nightly tarballs.

If using a SAW [release](https://github.com/GaloisInc/saw-script/releases), it
is recommended to use `v0.8` or greater if possible. (`v0.7` _does_ include the
server and may work for individual use cases, but running repeated scripts
against the same persistent server will not work as intended.)

Nightly server builds can be found as `Artifacts` of the [Nightly
Builds](https://github.com/GaloisInc/saw-script/actions/workflows/nightly.yml)
github action. I.e., go to the `Nightly Builds` Github Action, click on a
successful build, scroll to the bottom and under `Artifacts` a Linux, Windows,
and MacOS tarball will be listed. (Apologies... we need to make these easier to
find...)

### Server docker images

Docker images for the SAW server are currently uploaded to
[DockerHub](https://hub.docker.com/r/galoisinc/saw-remote-api).

These images are set up to run as HTTP `saw-remote-api` servers, e.g.:

```
docker run --name=saw-remote-api -d \
  -p 8080:8080 \
  galoisinc/saw-remote-api:TAG
```

(where `TAG` is either `latest` or `nightly`) will launch a server listening at
`http://localhost:8080/`. (As of March 2020, `nightly` is recommended, as the
server in the last official release (i.e., the one accompanying SAW `v0.7`)
contains some non-trivial bugs that greatly limit its utility.)

The `-v` option to `docker run` can be used to load files into the docker
server's working directory so they can be loaded into the server at the request
of python scripts. E.g., `-v PATH_TO_FILES:/home/saw/files/` will upload the
contents of the host machine's directory `PATH_TO_FILES` to the
`/home/saw/files/` directory in the docker container, which corresponds to the
relative path `files/` for the SAW server. (If desired, it can be useful to
place files in a location in the Docker container such that the same relative
paths in scripts refer to the same files in the host machine and docker
container.)

### Building from Source

If this repository is checked out and the build directions are successfully run,
`cabal v2-exec which saw-remote-api` should indicate where the server executable has
been stored by `cabal`.

Alternatively `cabal v2-install saw-remote-api` should install the server
executable into the user's `~/.cabal/bin` directory (or similar), which (if
configured properly) should then appear as `saw-remote-api` in a user's `PATH`.


# Running Python SAW verification scripts

Once the server is setup and any path variables are setup as desired, the
Python (>= v3.8) client can be installed using
[`poetry`](https://python-poetry.org/docs/#installation) as follows:

```
$ cd saw-python
$ poetry install
```

Then the tests or individual scripts can be run as follows:
```
$ poetry run python -m unittest discover tests/saw
$ poetry run python tests/saw/test_salsa20.py
```

If leveraging environment variables is undesirable, the scripts themselves can
specify a command to launch the server, e.g.:

```
saw_client.connect(COMMAND)
```

where `COMMAND` is a command to launch a new SAW server in socket mode.

Or a server URL can be specified directly in the script, e.g.:

```
saw_client.connect(url=URL)
```

where `URL` is a URL for a running SAW server in HTTP mode.

## Running Verification Scripts from a clean state

To ensure any previous server state is cleared when running a SAW Python script
against a persistent server (e.g., one running in HTTP mode in a different process),
the `reset_server` keyword can be passed to `saw_client.connect()`. E.g.,

```
saw_client.connect(url="http://localhost:8080/", reset_server=True)
```

will connect to a SAW server running at `http://localhost:8080/` and will
guarantee any previous state on the server is cleared.


## Python Version Support

Currently, `saw-python` officially supports python `3.12`.
