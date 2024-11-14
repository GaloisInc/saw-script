from abc import ABCMeta, abstractmethod
from dataclasses import dataclass
from typing import List, Optional, Set, Union, Tuple, Any, IO, TextIO
import uuid
import sys
import time
import atexit
from shutil import which

import cryptol

from cryptol import cryptoltypes
from . import connection
from argo_client.connection import ServerConnection
from . import llvm
from . import mir
from . import exceptions
from . import option
from . import proofscript

__designated_connection = None  # type: Optional[connection.SAWConnection]
__designated_views = []         # type: List[View]
__global_success = True         # type: bool

# Script-execution-global set of all results verified so far
__used_server_names = set([])      # type: Set[str]


def __fresh_server_name(hint: Optional[str] = None) -> str:
    if hint is None:
        hint = 'x'
    name = llvm.uniquify(hint, __used_server_names)
    __used_server_names.add(name)
    return name


def __get_designated_connection() -> connection.SAWConnection:
    global __designated_connection
    if __designated_connection is None:
        raise ValueError("There is not yet a designated connection.")
    else:
        return __designated_connection


def __set_designated_connection(conn: connection.SAWConnection) -> None:
    global __designated_connection
    __designated_connection = conn


class VerificationResult(metaclass=ABCMeta):
    server_name: str
    assumptions: List[Any]   # really, List[VerificationResult],
    contract: llvm.Contract  # but mypy doesn't allow recursive types
    _unique_id: uuid.UUID

    @abstractmethod
    def is_success(self) -> bool: ...

class ProofResult(metaclass=ABCMeta):
    goal: proofscript.ProofScript
    valid: bool
    counterexample: Optional[Any]

    def is_valid(self) -> bool:
        """Returns `True` in the case where the given proof goal is valid, or true for
        all possible values of any symbolic variables that it contains. Returns
        `False` if the goal can possibly be false for any value of symbolic
        variables it contains. In this latter case, the `get_counterexample`
        function will return the variable values for which the goal evaluates
        to false.
        """
        return self.valid

    def get_counterexample(self) -> Any:
        """In the case where `is_valid` returns `False`, this function returns the
        counterexample that provides the values for symbolic variables that
        lead to it being false. If `is_valid` returns `True`, returns `None`.
        """
        return self.counterexample

@dataclass
class VerificationSucceeded(VerificationResult):
    def __init__(self,
                 server_name: str,
                 assumptions: List[VerificationResult],
                 contract: llvm.Contract,
                 stdout: str,
                 stderr: str) -> None:
        self.server_name = server_name
        self.assumptions = assumptions
        self.contract = contract
        self._unique_id = uuid.uuid4()
        self.stdout = stdout
        self.stderr = stderr

    def is_success(self) -> bool:
        return True


@dataclass
class VerificationFailed(VerificationResult):
    exception: exceptions.VerificationError

    def __init__(self,
                 server_name: str,
                 assumptions: List[VerificationResult],
                 contract: llvm.Contract,
                 exception: exceptions.VerificationError) -> None:
        self.server_name = server_name
        self.assumptions = assumptions
        self.contract = contract
        self.exception = exception
        self._unique_id = uuid.uuid4()

    def is_success(self) -> bool:
        return False


@dataclass
class AssumptionSucceeded(VerificationSucceeded):
    def __init__(self,
                 server_name: str,
                 contract: llvm.Contract,
                 stdout: str,
                 stderr: str) -> None:
        super().__init__(server_name,
                         [],
                         contract,
                         stdout,
                         stderr)

@dataclass
class AssumptionFailed(VerificationFailed):
    def __init__(self,
                 server_name: str,
                 assumptions: List[VerificationResult],
                 contract: llvm.Contract,
                 exception: exceptions.VerificationError) -> None:
        super().__init__(server_name,
                         assumptions,
                         contract,
                         exception)

# FIXME cryptol_path isn't always used...?
def connect(command: Union[str, ServerConnection, None] = None,
            *,
            cryptol_path: Optional[str] = None,
            persist: bool = False,
            url : Optional[str] = None,
            reset_server : bool = False,
            verify : Union[bool, str] = True,
            log_dest : Optional[TextIO] = None) -> None:
    """
    Connect to a (possibly new) Saw server process.

    :param command: A command to launch a new Saw server in socket mode (if
    provided).

    :param url: A URL at which to connect to an already running SAW HTTP server.

    : param reset_server: If ``True``, the server that is connected to will be
    reset. (This ensures any states from previous server usages have been
    cleared.)

    If no parameters specifying how to connect to the server are provided, the
    following are attempted in order:

    1. If the environment variable ``SAW_SERVER`` is set and refers to an
       executable, it is assumed to be a SAW server and will be used for a new
       ``stdio`` connection.

    2. If the environment variable ``SAW_SERVER_URL`` is set, it is assumed to
       be the URL for a running SAW server in ``http`` mode and will be
       connected to.

    3. If an executable ``saw-remote-api`` is available on the ``PATH`` it is
       assumed to be a SAW server and will be used for a new ``stdio``
       connection.

    """
    global __designated_connection

    # Set the designated connection by starting a server process
    if __designated_connection is None:
        __designated_connection = connection.connect(
            command=command,
            cryptol_path=cryptol_path,
            persist=persist,
            url=url,
            verify=verify,
            log_dest=log_dest)
    elif reset_server:
        __designated_connection.reset_server()
    else:
        raise ValueError("There is already a designated connection."
                         " Did you call `connect()` more than once?")

    # After the script quits, print the server PID
    if persist:
        def print_if_still_running() -> None:
            if __designated_connection is not None:
                try:
                    pid = __designated_connection.pid()
                    if __designated_connection.running():
                        message = f"Created persistent server process: PID {pid}"
                        print(message)
                except ProcessLookupError:
                    pass
        atexit.register(print_if_still_running)
    time.sleep(0.1)


def reset() -> None:
    """Reset the current SAW connection to the initial state.

    If the connection is inactive, ``connect()`` is called to initialize it."""
    if __designated_connection is not None:
        __designated_connection.reset()
    else:
        connect()

def reset_server() -> None:
    """Reset the SAW server, clearing all states.

    If the connection is inactive, ``connect()`` is called to initialize it."""
    if __designated_connection is not None:
        __designated_connection.reset_server()
    else:
        connect()
        if __designated_connection is not None:
            __designated_connection.reset_server()

def disconnect() -> None:
    global __designated_connection
    if __designated_connection is not None:
        __designated_connection.disconnect()
    __designated_connection = None


def logging(on : bool, *, dest : TextIO = sys.stderr) -> None:
    """Whether to log received and transmitted JSON."""
    global __designated_connection
    if __designated_connection is not None:
        __designated_connection.logging(on=on,dest=dest)


class View:
    """An instance of View describes how to (potentially interactively) view
       or log the results of a verification script, in real-time."""

    def on_failure(self, failure: VerificationFailed) -> None:
        """When a verification attempt fails, do this."""
        pass

    def on_success(self, success: VerificationSucceeded) -> None:
        """When a verification attempt succeeds, do this."""
        pass

    def on_python_exception(self, exception: Exception) -> None:
        """When some Python exception occurs, do this."""
        pass

    def on_finish(self) -> None:
        """After all verifications are finished, do this."""
        pass

    def on_abort(self) -> None:
        """If the proof is aborted due to inability to assume a lemma, do
        this."""
        pass


class DebugLog(View):
    """A view on the verification results that logs the stdout/stderr of the
    method to stdout/stderr, or specified file handles."""

    def __init__(self, *, out: IO[str] = sys.stdout, err: IO[str] = sys.stderr) -> None:
        self.out = out
        self.err = err

    def on_failure(self, failure: VerificationFailed) -> None:
        if self.out is not None:
            print(failure.exception.stdout, file=self.out, end='')
        if self.err is not None:
            print(failure.exception.stderr, file=self.err, end='')

    def on_success(self, success: VerificationSucceeded) -> None:
        if self.out is not None:
            print(success.stdout, file=self.out, end='')
        if self.err is not None:
            print(success.stderr, file=self.err, end='')


class LogResults(View):
    """A view on the verification results that logs failures and successes in a
       human-readable text format to stdout, or a given file handle."""

    def __init__(self, file: IO[str] = sys.stdout, verbose_failure: bool = False):
        self.file = file
        self.verbose = verbose_failure
        self.successes: List[VerificationSucceeded] = []
        self.failures: List[VerificationFailed] = []

    def format_failure(self, failure: VerificationFailed) -> str:
        filename, lineno, lemma_name = self.__result_attributes(failure)
        message = f"⚠️  Failed to verify: {lemma_name}" + \
                  f" (defined at {filename}:{lineno}):\n{failure.exception}"
        if self.verbose:
            message += '\n\tstdout:\n' + '\n'.join(
                '\t\t' + line for line in failure.exception.stdout.split('\n')
            )
            # message += '\n\tstderr:\n' + '\n'.join(
            #     '\t\t' + line for line in failure.exception.stderr.split('\n')
            # )
        return message

    def format_success(self, success: VerificationSucceeded) -> str:
        filename, lineno, lemma_name = self.__result_attributes(success)
        return (f"✅  Verified: {lemma_name}"
                f" (defined at {filename}:{lineno})")

    @staticmethod
    def __result_attributes(result: VerificationResult) -> Tuple[str, Union[int, str], str]:
        lineno: Optional[Union[int, str]] = result.contract.definition_lineno()
        if lineno is None:
            lineno = "<unknown line>"
        filename = result.contract.definition_filename()
        if filename is None:
            filename = "<unknown file>"
        lemma_name = result.contract.lemma_name()
        return (filename, lineno, lemma_name)

    def on_failure(self, result: VerificationFailed) -> None:
        self.failures.append(result)
        print(self.format_failure(result), file=self.file)

    def on_success(self, result: VerificationSucceeded) -> None:
        self.successes.append(result)
        print(self.format_success(result), file=self.file)

    def on_finish(self) -> None:
        failures = len(self.failures)
        successes = len(self.successes)
        total = failures + successes
        if total == 0:
            print(f'🔶 No goal results logged.', file=self.file)
        elif failures > 0:
            if failures == 1 and total == 1:
                print(f'🛑  The goal failed to verify.', file=self.file)
            elif failures == total:
                print(f'🛑  All {total!r} goals failed to verify.', file=self.file)
            else:
                print(f'🛑  {failures!r} out of {total!r} goals failed to verify.', file=self.file)
        elif successes == 1:
            print(f'✅  The goal was verified!', file=self.file)
        else:
            print(f'✅  All {successes!r} goals verified!', file=self.file)

    def on_abort(self) -> None:
        print("🛑  Aborting proof script.", file=self.file)


def view(v: View) -> None:
    """Add a view to the global list of views. Future verification results will
       be handed to this view, and its on_finish() handler will be called at
       the end of the script."""
    global __designated_views
    __designated_views.append(v)


def cryptol_load_file(filename: str) -> None:
    __get_designated_connection().cryptol_load_file(filename).result()
    return None

def create_ghost_variable(name: str) -> llvm.GhostVariable:
    """Create a ghost variable that can be used to invent state useful to
    verification but that doesn't exist in the concrete state of the program.
    This state can be referred to using the `c.ghost_value` method for some
    `Contract` object `c`.
    """
    server_name = __fresh_server_name(name)
    __get_designated_connection().create_ghost_variable(name, server_name)
    return llvm.GhostVariable(name, server_name)


@dataclass
class JVMClass:
    class_name: str
    server_name: str


def jvm_load_class(class_name: str) -> JVMClass:
    name = __fresh_server_name(class_name)
    __get_designated_connection().jvm_load_class(name, class_name).result()
    return JVMClass(class_name, name)

# TODO: this is almost identical to llvm_assume and mir_assume. Can we reduce duplication?
def jvm_assume(cls: JVMClass,
               method_name: str,
               contract: llvm.Contract,
               lemma_name_hint: Optional[str] = None) -> VerificationResult:
    """Assume that the given method satisfies the given contract. Returns an
    override linking the method and contract that can be passed as an
    argument in calls to `jvm_verify`
    """
    if lemma_name_hint is None:
        lemma_name_hint = contract.__class__.__name__ + "_" + method_name
    name = __fresh_server_name(lemma_name_hint)

    result: VerificationResult
    try:
        conn = __get_designated_connection()
        res = conn.jvm_assume(cls.class_name,
                              method_name,
                              contract.to_json(),
                              name)
        result = AssumptionSucceeded(server_name=name,
                                     contract=contract,
                                     stdout=res.stdout(),
                                     stderr=res.stderr())
        __global_success = True
        # If something stopped us from even **assuming**...
    except exceptions.VerificationError as err:
        __global_success = False
        result = AssumptionFailed(server_name=name,
                                  assumptions=[],
                                  contract=contract,
                                  exception=err)
    except Exception as err:
        __global_success = False
        for view in __designated_views:
            view.on_python_exception(err)
        raise err from None

    return result

# TODO: this is almost identical to llvm_verify and mir_verify. Can we reduce duplication?
def jvm_verify(cls: JVMClass,
               method_name: str,
               contract: llvm.Contract,
               lemmas: List[VerificationResult] = [],
               check_sat: bool = False,
               script: Optional[proofscript.ProofScript] = None,
               lemma_name_hint: Optional[str] = None) -> VerificationResult:
    """Verify that the given method satisfies the given contract. Returns an
    override linking the method and contract that can be passed as an
    argument in further calls to `jvm_verify`
    """

    if script is None:
        script = proofscript.ProofScript([proofscript.z3([])])
    if lemma_name_hint is None:
        lemma_name_hint = contract.__class__.__name__ + "_" + method_name

    name = __fresh_server_name(lemma_name_hint)

    result: VerificationResult
    conn = __get_designated_connection()

    global __global_success
    global __designated_views

    try:
        res = conn.jvm_verify(cls.class_name,
                              method_name,
                              [l.server_name for l in lemmas],
                              check_sat,
                              contract.to_json(),
                              script.to_json(),
                              name)

        stdout = res.stdout()
        stderr = res.stderr()
        result = VerificationSucceeded(server_name=name,
                                       assumptions=lemmas,
                                       contract=contract,
                                       stdout=stdout,
                                       stderr=stderr)
    # If the verification did not succeed...
    except exceptions.VerificationError as err:
        # FIXME add the goal as an assumption if it failed...?
        result = VerificationFailed(server_name=name,
                                    assumptions=lemmas,
                                    contract=contract,
                                    exception=err)
    # If something else went wrong...
    except Exception as err:
        __global_success = False
        for view in __designated_views:
            view.on_python_exception(err)
        raise err from None

    # Log or otherwise process the verification result
    for view in __designated_views:
        if isinstance(result, VerificationSucceeded):
            view.on_success(result)
        elif isinstance(result, VerificationFailed):
            view.on_failure(result)

    # Note when any failure occurs
    __global_success = __global_success and result.is_success()

    # Abort the proof if we failed to assume a failed verification, otherwise
    # return the result of the verification
    if isinstance(result, AssumptionFailed):
        raise result.exception from None

    return result

@dataclass
class LLVMModule:
    bitcode_file: str
    server_name: str


def llvm_load_module(bitcode_file: str) -> LLVMModule:
    name = __fresh_server_name(bitcode_file)
    __get_designated_connection().llvm_load_module(name, bitcode_file).result()
    return LLVMModule(bitcode_file, name)


def llvm_assume(module: LLVMModule,
                function: str,
                contract: llvm.Contract,
                lemma_name_hint: Optional[str] = None) -> VerificationResult:
    """Assume that the given function satisfies the given contract. Returns an
    override linking the function and contract that can be passed as an
    argument in calls to `llvm_verify`
    """
    if lemma_name_hint is None:
        lemma_name_hint = contract.__class__.__name__ + "_" + function
    name = __fresh_server_name(lemma_name_hint)

    result: VerificationResult
    try:
        conn = __get_designated_connection()
        res = conn.llvm_assume(module.server_name,
                               function,
                               contract.to_json(),
                               name)
        result = AssumptionSucceeded(server_name=name,
                                     contract=contract,
                                     stdout=res.stdout(),
                                     stderr=res.stderr())
        __global_success = True
        # If something stopped us from even **assuming**...
    except exceptions.VerificationError as err:
        __global_success = False
        result = AssumptionFailed(server_name=name,
                                  assumptions=[],
                                  contract=contract,
                                  exception=err)
    except Exception as err:
        __global_success = False
        for view in __designated_views:
            view.on_python_exception(err)
        raise err from None

    return result

def llvm_verify(module: LLVMModule,
                function: str,
                contract: llvm.Contract,
                lemmas: List[VerificationResult] = [],
                check_sat: bool = False,
                script: Optional[proofscript.ProofScript] = None,
                lemma_name_hint: Optional[str] = None) -> VerificationResult:

    if script is None:
        script = proofscript.ProofScript([proofscript.z3([])])
    if lemma_name_hint is None:
        lemma_name_hint = contract.__class__.__name__ + "_" + function

    name = __fresh_server_name(lemma_name_hint)

    result: VerificationResult
    conn = __get_designated_connection()

    global __global_success
    global __designated_views

    try:
        res = conn.llvm_verify(module.server_name,
                               function,
                               [l.server_name for l in lemmas],
                               check_sat,
                               contract.to_json(),
                               script.to_json(),
                               name)

        stdout = res.stdout()
        stderr = res.stderr()
        result = VerificationSucceeded(server_name=name,
                                       assumptions=lemmas,
                                       contract=contract,
                                       stdout=stdout,
                                       stderr=stderr)
    # If the verification did not succeed...
    except exceptions.VerificationError as err:
        # FIXME add the goal as an assumption if it failed...?
        result = VerificationFailed(server_name=name,
                                    assumptions=lemmas,
                                    contract=contract,
                                    exception=err)
    # If something else went wrong...
    except Exception as err:
        __global_success = False
        for view in __designated_views:
            view.on_python_exception(err)
        raise err from None

    # Log or otherwise process the verification result
    for view in __designated_views:
        if isinstance(result, VerificationSucceeded):
            view.on_success(result)
        elif isinstance(result, VerificationFailed):
            view.on_failure(result)

    # Note when any failure occurs
    __global_success = __global_success and result.is_success()

    # Abort the proof if we failed to assume a failed verification, otherwise
    # return the result of the verification
    if isinstance(result, AssumptionFailed):
        raise result.exception from None

    return result


@dataclass
class MIRModule:
    json_file: str
    server_name: str


def mir_load_module(json_file: str) -> MIRModule:
    name = __fresh_server_name(json_file)
    __get_designated_connection().mir_load_module(name, json_file).result()
    return MIRModule(json_file, name)


# TODO: this is almost identical to llvm_assume and jvm_assume. Can we reduce duplication?
def mir_assume(module: MIRModule,
               function: str,
               contract: llvm.Contract,
               lemma_name_hint: Optional[str] = None) -> VerificationResult:
    """Assume that the given function satisfies the given contract. Returns an
    override linking the function and contract that can be passed as an
    argument in calls to `mir_verify`
    """
    if lemma_name_hint is None:
        lemma_name_hint = contract.__class__.__name__ + "_" + function
    name = __fresh_server_name(lemma_name_hint)

    result: VerificationResult
    try:
        conn = __get_designated_connection()
        res = conn.mir_assume(module.server_name,
                              function,
                              contract.to_json(),
                              name)
        result = AssumptionSucceeded(server_name=name,
                                     contract=contract,
                                     stdout=res.stdout(),
                                     stderr=res.stderr())
        __global_success = True
        # If something stopped us from even **assuming**...
    except exceptions.VerificationError as err:
        __global_success = False
        result = AssumptionFailed(server_name=name,
                                  assumptions=[],
                                  contract=contract,
                                  exception=err)
    except Exception as err:
        __global_success = False
        for view in __designated_views:
            view.on_python_exception(err)
        raise err from None

    return result


# TODO: this is almost identical to llvm_verify and jvm_verify. Can we reduce duplication?
def mir_verify(module: MIRModule,
               function: str,
               contract: llvm.Contract,
               lemmas: List[VerificationResult] = [],
               check_sat: bool = False,
               script: Optional[proofscript.ProofScript] = None,
               lemma_name_hint: Optional[str] = None) -> VerificationResult:
    """Verify that the given function satisfies the given contract. Returns an
    override linking the function and contract that can be passed as an
    argument in further calls to `mir_verify`
    """

    if script is None:
        script = proofscript.ProofScript([proofscript.z3([])])
    if lemma_name_hint is None:
        lemma_name_hint = contract.__class__.__name__ + "_" + function

    name = __fresh_server_name(lemma_name_hint)

    result: VerificationResult
    conn = __get_designated_connection()

    global __global_success
    global __designated_views

    try:
        res = conn.mir_verify(module.server_name,
                              function,
                              [l.server_name for l in lemmas],
                              check_sat,
                              contract.to_json(),
                              script.to_json(),
                              name)

        stdout = res.stdout()
        stderr = res.stderr()
        result = VerificationSucceeded(server_name=name,
                                       assumptions=lemmas,
                                       contract=contract,
                                       stdout=stdout,
                                       stderr=stderr)
    # If the verification did not succeed...
    except exceptions.VerificationError as err:
        # FIXME add the goal as an assumption if it failed...?
        result = VerificationFailed(server_name=name,
                                    assumptions=lemmas,
                                    contract=contract,
                                    exception=err)
    # If something else went wrong...
    except Exception as err:
        __global_success = False
        for view in __designated_views:
            view.on_python_exception(err)
        raise err from None

    # Log or otherwise process the verification result
    for view in __designated_views:
        if isinstance(result, VerificationSucceeded):
            view.on_success(result)
        elif isinstance(result, VerificationFailed):
            view.on_failure(result)

    # Note when any failure occurs
    __global_success = __global_success and result.is_success()

    # Abort the proof if we failed to assume a failed verification, otherwise
    # return the result of the verification
    if isinstance(result, AssumptionFailed):
        raise result.exception from None

    return result


def mir_find_adt(module: MIRModule,
                 adt_orig_name: str,
                 *tys: mir.MIRType,
                 adt_server_name_hint: Optional[str] = None) -> mir.MIRAdt:
    """Consult the given MIR module (``module_server_name``) to find an
       algebraic data type (ADT) with ``adt_orig_name`` as its identifier and
       ``tys`` as the types used to instantiate the type parameters. If such an
       ADT cannot be found in the module, this will raise an error.
    """
    if adt_server_name_hint is None:
        adt_server_name_hint = adt_orig_name
    adt_server_name = __fresh_server_name(adt_server_name_hint)
    __get_designated_connection().mir_find_adt(module.server_name, adt_orig_name, list(tys), adt_server_name).result()
    return mir.MIRAdt(adt_orig_name, adt_server_name)


def prove(goal: cryptoltypes.CryptolJSON,
          proof_script: proofscript.ProofScript) -> ProofResult:
    """Atempts to prove that the expression given as the first argument, `goal`, is
    true for all possible values of free symbolic variables. Uses the proof
    script (potentially specifying an automated prover) provided by the second
    argument.
    """
    conn = __get_designated_connection()
    res = conn.prove(goal, proof_script.to_json()).result()
    pr = ProofResult()
    if res['status'] == 'valid':
        pr.valid = True
    elif res['status'] == 'invalid':
        pr.valid = False
    else:
        raise ValueError("Unknown proof result " + str(res))
    if 'counterexample' in res:
        pr.counterexample = [ (arg['name'], cryptol.from_cryptol_arg(arg['value']))
                              for arg in res['counterexample'] ]
    else:
        pr.counterexample = None
    return pr

def eval_int(expr: cryptoltypes.CryptolJSON) -> int:
    """Atempts to evaluate the given expression as a concrete integer.
    """
    conn = __get_designated_connection()
    res = conn.eval_int(expr).result()
    v = res['value']
    if not isinstance(v, int):
        raise ValueError(str(v) + " is not an integer")
    return v

def eval_bool(expr: cryptoltypes.CryptolJSON) -> bool:
    """Atempts to evaluate the given expression as a concrete boolean.
    """
    conn = __get_designated_connection()
    res = conn.eval_bool(expr).result()
    v = res['value']
    if not isinstance(v, bool):
        raise ValueError(str(v) + " is not a boolean")
    return v

def set_option(option : option.SAWOption, value : bool) -> None:
    """Set a boolean-valued SAW option."""
    global __designated_connection
    if __designated_connection is not None:
        __designated_connection.set_option(option=option,value=value)

@atexit.register
def script_exit() -> None:
    global __designated_views
    for view in __designated_views:
        view.on_finish()
