from __future__ import annotations
import os
import signal
import sys
from shutil import which
from argo_client.connection import ServerConnection, DynamicSocketProcess, HttpProcess, ManagedProcess
from argo_client.interaction import Interaction, Command
from .commands import *
from .option import *
from typing import Optional, Union, Any, List, TextIO

# FIXME cryptol_path isn't always used...?
def connect(command: Union[str, ServerConnection, None] = None,
            *,
            cryptol_path: Optional[str] = None,
            persist: bool = False,
            url : Optional[str] = None,
            reset_server : bool = False,
            verify : Union[bool, str] = True,
            log_dest : Optional[TextIO] = None) -> SAWConnection:
    """
    Connect to a (possibly new) Saw server process.

    :param command: A command to launch a new Saw server in socket mode (if
    provided).

    :param url: A URL at which to connect to an already running SAW HTTP server.

    : param reset_server: If ``True``, the server that is connected to will be
    reset. (This ensures any states from previous server usages have been cleared.)

    If no parameters specifying how to connect to the server are provided, the
    following are attempted in order:

    1. If the environment variable ``SAW_SERVER`` is set and referse to an
       executable, it is assumed to be a SAW server and will be used for a new
       ``socket`` connection.

    2. If the environment variable ``SAW_SERVER_URL`` is set, it is assumed to
       be the URL for a running SAW server in ``http`` mode and will be
       connected to.

    3. If an executable ``saw-remote-api`` is available on the ``PATH`` it is
       assumed to be a SAW server and will be used for a new ``socket``
       connection.

    """
    c = None
    if command is not None:
        if url is not None:
            raise ValueError("A SAW server URL cannot be specified with a command currently.")
        c = SAWConnection(command, log_dest=log_dest)
    elif url is not None:
        c = SAWConnection(ServerConnection(HttpProcess(url, verify=verify)), log_dest=log_dest)
    elif (command := os.getenv('SAW_SERVER')) is not None and (command := which(command)) is not None:
        c = SAWConnection(command+" socket", log_dest=log_dest) # SAWConnection(ServerConnection(StdIOProcess(command+" stdio")))
    elif (url := os.getenv('SAW_SERVER_URL')) is not None:
        c = SAWConnection(ServerConnection(HttpProcess(url, verify=verify)), log_dest=log_dest)
    elif (command := which('saw-remote-api')) is not None:
        c = SAWConnection(command+" socket", log_dest=log_dest)
    else:
        raise ValueError(
            """saw.connection.connect requires one of the following:",
            1) a command to launch a SAW server is the first positional argument,
            2) a URL to connect to a running SAW server is provided via the `url` keyword argument,
            3) the environment variable `SAW_SERVER` must refer to a valid server executable, or
            4) the environment variable `SAW_SERVER_URL` must refer to the URL of a running SAW server.""")
    if reset_server:
        SAWResetServer(c)
    return c


class SAWConnection:
    """A representation of a current user state in a session with SAW."""

    most_recent_result: Optional[Interaction]
    server_connection: ServerConnection
    proc: Optional[ManagedProcess]

    def __init__(self,
                 command_or_connection: Union[str, ServerConnection],
                 *,
                 persist: bool = False,
                 log_dest : Optional[TextIO] = None) -> None:
        self.proc = None
        self.most_recent_result = None
        self.persist = persist
        if isinstance(command_or_connection, str):
            self.proc = DynamicSocketProcess(command_or_connection, persist=self.persist)
            self.server_connection = ServerConnection(self.proc)
        else:
            self.server_connection = command_or_connection

        if log_dest:
            self.logging(on=True,dest=log_dest)

    def reset(self) -> None:
        """Resets the connection, causing its unique state on the server to be freed (if applicable).

        After a reset a connection may be treated as if it were a fresh connection with the server if desired."""
        SAWReset(self)
        self.most_recent_result = None

    def reset_server(self) -> None:
        """Resets the server, causing all states on the server to be freed."""
        SAWResetServer(self)
        self.most_recent_result = None

    def disconnect(self) -> None:
        """Clears the state from the server and closes any underlying
        server/connection process launched by this object."""
        self.reset()
        if not self.persist and self.proc and (pid := self.proc.pid()):
            pgid = os.getpgid(pid)
            os.kill(pgid, signal.SIGKILL)
            self.proc = None

    def logging(self, on : bool, *, dest : TextIO = sys.stderr) -> None:
        """Whether to log received and transmitted JSON."""
        self.server_connection.logging(on=on,dest=dest)

    def __del__(self) -> None:
        # when being deleted, ensure we don't have a lingering state on the server
        if not self.persist:
            if self.proc and (pid := self.proc.pid()):
                os.killpg(os.getpgid(pid), signal.SIGKILL)


    def pid(self) -> Optional[int]:
        """Return the PID of the running server process."""
        if self.proc is not None:
            return self.proc.pid()
        else:
            return None

    def running(self) -> bool:
        """Return whether the underlying server process is still running."""
        if self.proc is not None:
            return self.proc.running()
        else:
            return False

    def protocol_state(self) -> Any:
        if self.most_recent_result is None:
            return None
        else:
            return self.most_recent_result.state()

    # Protocol messages
    def cryptol_load_file(self, filename: str, timeout : Optional[float] = None) -> Command:
        self.most_recent_result = CryptolLoadFile(self, filename, timeout)
        return self.most_recent_result

    def create_ghost_variable(self, name: str, server_name: str, timeout : Optional[float] = None) -> Command:
        """Create an instance of the `CreateGhostVariable` command. Documentation on
        the purpose and use of this command is associated with the top-level
        `create_ghost_variable` function.
        """
        self.most_recent_result = CreateGhostVariable(self, name, server_name, timeout)
        return self.most_recent_result

    def jvm_load_class(self, name: str, class_name: str, timeout : Optional[float] = None)  -> Command:
        """Create an instance of the `JVMLoadClass` command. Documentation on the purpose
        and use of this command is associated with the top-level `jvm_load_class`
        function.
        """
        self.most_recent_result = JVMLoadClass(self, name, class_name, timeout)
        return self.most_recent_result

    def jvm_verify(self,
                   class_name: str,
                   method_name: str,
                   lemmas: List[str],
                   check_sat: bool,
                   contract: Any,
                   script: ProofScript,
                   lemma_name: str,
                   timeout : Optional[float] = None) -> Command:
        """Create an instance of the `JVMVerify` command. Documentation on the purpose
        and use of this command is associated with the top-level `jvm_assume`
        function.
        """
        self.most_recent_result = \
            JVMVerify(self, class_name, method_name, lemmas, check_sat, contract, script, lemma_name, timeout)
        return self.most_recent_result

    def jvm_assume(self,
                   class_name: str,
                   method_name: str,
                   contract: Any,
                   lemma_name: str,
                   timeout : Optional[float] = None) -> Command:
        """Create an instance of the `JVMAssume` command. Documentation on the purpose
        and use of this command is associated with the top-level `jvm_assume`
        function.
        """
        self.most_recent_result = \
            JVMAssume(self, class_name, method_name, contract, lemma_name, timeout)
        return self.most_recent_result

    def llvm_load_module(self, name: str, bitcode_file: str, timeout : Optional[float] = None)  -> Command:
        self.most_recent_result = LLVMLoadModule(self, name, bitcode_file, timeout)
        return self.most_recent_result

    def llvm_verify(self,
                    module: str,
                    function: str,
                    lemmas: List[str],
                    check_sat: bool,
                    contract: Any,
                    script: ProofScript,
                    lemma_name: str,
                    timeout : Optional[float] = None) -> Command:
        self.most_recent_result = \
            LLVMVerify(self, module, function, lemmas, check_sat, contract, script, lemma_name, timeout)
        return self.most_recent_result

    def llvm_assume(self,
                    module: str,
                    function: str,
                    contract: Any,
                    lemma_name: str,
                    timeout : Optional[float] = None) -> Command:
        """Create an instance of the `LLVMAssume` command. Documentation on the purpose
        and use of this command is associated with the top-level `llvm_assume`
        function.
        """
        self.most_recent_result = \
            LLVMAssume(self, module, function, contract, lemma_name, timeout)
        return self.most_recent_result

    def mir_load_module(self, name: str, mir_json_file: str, timeout : Optional[float] = None)  -> Command:
        """Create an instance of the `MIRLoadClass` command. Documentation on the purpose
        and use of this command is associated with the top-level `mir_load_class`
        function.
        """
        self.most_recent_result = MIRLoadModule(self, name, mir_json_file, timeout)
        return self.most_recent_result

    def mir_verify(self,
                   module: str,
                   function: str,
                   lemmas: List[str],
                   check_sat: bool,
                   contract: Any,
                   script: ProofScript,
                   lemma_name: str,
                   timeout : Optional[float] = None) -> Command:
        """Create an instance of the `MIRVerify` command. Documentation on the purpose
        and use of this command is associated with the top-level `mir_verify`
        function.
        """
        self.most_recent_result = \
            MIRVerify(self, module, function, lemmas, check_sat, contract, script, lemma_name, timeout)
        return self.most_recent_result

    def mir_assume(self,
                   module: str,
                   function: str,
                   contract: Any,
                   lemma_name: str,
                   timeout : Optional[float] = None) -> Command:
        """Create an instance of the `MIRAssume` command. Documentation on the purpose
        and use of this command is associated with the top-level `mir_assume`
        function.
        """
        self.most_recent_result = \
            MIRAssume(self, module, function, contract, lemma_name, timeout)
        return self.most_recent_result

    def mir_find_adt(self,
                     module_server_name : str,
                     adt_orig_name : str,
                     tys : List[MIRType],
                     adt_server_name: str,
                     timeout : Optional[float] = None) -> Command:
        """Consult the given MIR module (``module_server_name``) to find an
           algebraic data type (ADT) with ``adt_orig_name`` as its identifier
           and ``tys`` as the types used to instantiate the type parameters. If
           such an ADT cannot be found in the module, this will raise an error.
        """
        self.most_recent_result = \
            MIRFindADT(self, module_server_name, adt_orig_name, tys, adt_server_name, timeout)
        return self.most_recent_result

    def yosys_import(self, name: str, path: str, timeout : Optional[float] = None) -> Command:
        self.most_recent_result = YosysImport(self, name, path, timeout)
        return self.most_recent_result

    def yosys_verify(self,
                     imp: str,
                     module: str,
                     preconds: List[str],
                     spec: str,
                     lemmas: List[str],
                     script: ProofScript,
                     lemma_name: str,
                     timeout : Optional[float] = None) -> Command:
        self.most_recent_result = \
            YosysVerify(self, imp, module, preconds, spec, lemmas, script, lemma_name, timeout)
        return self.most_recent_result

    def yosys_import_sequential(self, name: str, path: str, module: str, timeout : Optional[float] = None) -> Command:
        self.most_recent_result = YosysImportSequential(self, name, path, module, timeout)
        return self.most_recent_result

    def yosys_extract_sequential(self, name: str, module: str, cycles: int, timeout : Optional[float] = None) -> Command:
        self.most_recent_result = YosysExtractSequential(self, name, module, cycles, timeout)
        return self.most_recent_result

    def prove(self,
              goal: cryptoltypes.CryptolJSON,
              proof_script: ProofScript,
              timeout : Optional[float] = None) -> Command:
        """Create an instance of the `Prove` command. Documentation on the purpose and
        use of this command is associated with the top-level `prove` function.
        """
        self.most_recent_result = Prove(self, goal, proof_script, timeout)
        return self.most_recent_result

    def eval_int(self,
              expr: cryptoltypes.CryptolJSON,
              timeout : Optional[float] = None) -> Command:
        """Create an instance of the `EvalInt` command. Documentation on the purpose and
        use of this command is associated with the top-level `eval_int` function.
        """
        self.most_recent_result = EvalInt(self, expr, timeout)
        return self.most_recent_result

    def eval_bool(self,
              expr: cryptoltypes.CryptolJSON,
              timeout : Optional[float] = None) -> Command:
        """Create an instance of the `EvalBool` command. Documentation on the purpose and
        use of this command is associated with the top-level `eval_bool` function.
        """
        self.most_recent_result = EvalBool(self, expr, timeout)
        return self.most_recent_result

    def set_option(self,
                   option : SAWOption,
                   value : bool,
                   timeout : Optional[float] = None) -> Command:
        """Set a boolean-valued SAW option."""
        self.most_recent_result = SAWSetOption(self, option, value, timeout)
        return self.most_recent_result
