import argo_client.interaction as argo
from typing import Any, Dict, List, Optional, Set, Union, overload

from cryptol import cryptoltypes
from . import exceptions
from .mir_type import *
from .proofscript import *
from .option import *

from typing import Any, List

class SAWCommand(argo.Command):
    def process_error(self, ae : argo.ArgoException) -> Exception:
        return exceptions.make_saw_exception(ae)

class YosysImport(SAWCommand):
    def __init__(self,
                 connection : argo.HasProtocolState,
                 name : str,
                 path : str,
                 timeout : Optional[float]) -> None:
        super(YosysImport, self).__init__(
            'SAW/Yosys/import',
            {'name': name, 'path': path},
            connection,
            timeout=timeout
        )

    def process_result(self, res : Any) -> Any:
        return res

class YosysVerify(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            imp: str,
            module : str,
            preconds: List[str],
            spec : str,
            lemmas : List[str],
            script : ProofScript,
            lemma_name : str,
            timeout : Optional[float]) -> None:
        params = {
            'import': imp,
            'module': module,
            'preconds': preconds,
            'spec': spec,
            'lemmas': lemmas,
            'script': script,
            'lemma name': lemma_name
        }
        super(YosysVerify, self).__init__(
            'SAW/Yosys/verify',
            params,
            connection,
            timeout=timeout
        )

    def process_result(self, res : Any) -> Any:
        return res

class YosysImportSequential(SAWCommand):
    def __init__(self,
                 connection : argo.HasProtocolState,
                 name : str,
                 path : str,
                 module : str,
                 timeout : Optional[float]) -> None:
        super(YosysImportSequential, self).__init__(
            'SAW/Yosys/import sequential',
            {'name': name, 'path': path, 'module': module},
            connection,
            timeout=timeout
        )

    def process_result(self, res : Any) -> Any:
        return res

class YosysExtractSequential(SAWCommand):
    def __init__(self,
                 connection : argo.HasProtocolState,
                 name : str,
                 module : str,
                 cycles : int,
                 timeout : Optional[float]) -> None:
        super(YosysExtractSequential, self).__init__(
            'SAW/Yosys/extract sequential',
            {'name': name, 'cycles': cycles, 'module': module},
            connection,
            timeout=timeout
        )

    def process_result(self, res : Any) -> Any:
        return res

class CryptolLoadFile(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState,
                 filename : str,
                 timeout : Optional[float]) -> None:
        super(CryptolLoadFile, self).__init__(
            'SAW/Cryptol/load file',
            {'file': filename},
            connection,
            timeout=timeout
        )

    def process_result(self, _res : Any) -> Any:
        return None

class CryptolLoadModule(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState,
                 module_name : str,
                 timeout : Optional[float]) -> None:
        super(CryptolLoadModule, self).__init__(
            'SAW/Cryptol/load module',
            {'module': module_name},
            connection,
            timeout=timeout
        )

    def process_result(self, _res : Any) -> Any:
        return None

class CreateGhostVariable(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState,
                 name : str,
                 server_name : str,
                 timeout : Optional[float]) -> None:
        super(CreateGhostVariable, self).__init__(
            'SAW/create ghost variable',
            {'display name': name,
             'server name': server_name},
            connection,
            timeout=timeout
        )

    def process_result(self, _res : Any) -> Any:
        return None

class LLVMLoadModule(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState,
                 name : str,
                 bitcode_file : str,
                 timeout : Optional[float]) -> None:
        super(LLVMLoadModule, self).__init__(
            'SAW/LLVM/load module',
            {'name': name, 'bitcode file': bitcode_file},
            connection,
            timeout=timeout
        )

    def process_result(self, res : Any) -> Any:
        return res

class LLVMAssume(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            module : str,
            function : str,
            setup : Any,
            lemma_name : str,
            timeout : Optional[float]) -> None:
        params = {'module': module,
                  'function': function,
                  'contract': setup,
                  'lemma name': lemma_name}
        super(LLVMAssume, self).__init__('SAW/LLVM/assume', params, connection, timeout=timeout)

    def process_result(self, _res : Any) -> Any:
        return None

class LLVMVerify(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            module : str,
            function : str,
            lemmas : List[str],
            check_sat : bool,
            setup : Any,
            script : ProofScript,
            lemma_name : str,
            timeout : Optional[float]) -> None:
        params = {'module': module,
                  'function': function,
                  'lemmas': lemmas,
                  'check sat': check_sat,
                  'contract': setup,
                  'script': script,
                  'lemma name': lemma_name}
        super(LLVMVerify, self).__init__('SAW/LLVM/verify', params, connection, timeout=timeout)

    def process_result(self, res : Any) -> Any:
        return res

class JVMLoadClass(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState,
                 name : str,
                 class_name : str,
                 timeout : Optional[float]) -> None:
        super(JVMLoadClass, self).__init__(
            'SAW/JVM/load class',
            {'name': name, 'class name': class_name},
            connection,
            timeout=timeout
        )

    def process_result(self, res : Any) -> Any:
        return res

class JVMAssume(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            module : str,
            function : str,
            setup : Any,
            lemma_name : str,
            timeout : Optional[float]) -> None:
        params = {'module': module,
                  'function': function,
                  'contract': setup,
                  'lemma name': lemma_name}
        super(JVMAssume, self).__init__('SAW/JVM/assume', params, connection, timeout=timeout)

    def process_result(self, _res : Any) -> Any:
        return None

class JVMVerify(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            class_name : str,
            method_name : str,
            lemmas : List[str],
            check_sat : bool,
            setup : Any,
            script : ProofScript,
            lemma_name : str,
            timeout : Optional[float]) -> None:
        params = {'module': class_name,
                  'function': method_name,
                  'lemmas': lemmas,
                  'check sat': check_sat,
                  'contract': setup,
                  'script': script,
                  'lemma name': lemma_name}
        super(JVMVerify, self).__init__('SAW/JVM/verify', params, connection, timeout=timeout)

    def process_result(self, res : Any) -> Any:
        return res

class MIRLoadModule(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState,
                 name : str,
                 json_file : str,
                 timeout : Optional[float]) -> None:
        super(MIRLoadModule, self).__init__(
            'SAW/MIR/load module',
            {'name': name, 'JSON file': json_file},
            connection,
            timeout=timeout
        )

    def process_result(self, res : Any) -> Any:
        return res

class MIRAssume(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            module : str,
            function : str,
            setup : Any,
            lemma_name : str,
            timeout : Optional[float]) -> None:
        params = {'module': module,
                  'function': function,
                  'contract': setup,
                  'lemma name': lemma_name}
        super(MIRAssume, self).__init__('SAW/MIR/assume', params, connection, timeout=timeout)

    def process_result(self, _res : Any) -> Any:
        return None

class MIRVerify(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            module : str,
            function : str,
            lemmas : List[str],
            check_sat : bool,
            setup : Any,
            script : ProofScript,
            lemma_name : str,
            timeout : Optional[float]) -> None:
        params = {'module': module,
                  'function': function,
                  'lemmas': lemmas,
                  'check sat': check_sat,
                  'contract': setup,
                  'script': script,
                  'lemma name': lemma_name}
        super(MIRVerify, self).__init__('SAW/MIR/verify', params, connection, timeout=timeout)

    def process_result(self, res : Any) -> Any:
        return res

class MIRFindADT(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            module_server_name : str,
            adt_orig_name : str,
            tys : List[MIRType],
            adt_server_name : str,
            timeout : Optional[float]) -> None:
        params = {'module': module_server_name,
                  'ADT original name': adt_orig_name,
                  'type substitutions': [ty.to_json() for ty in tys],
                  'ADT server name': adt_server_name}
        super(MIRFindADT, self).__init__('SAW/MIR/find ADT', params, connection, timeout=timeout)

    def process_result(self, res : Any) -> Any:
        return res

class Prove(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            goal : cryptoltypes.CryptolJSON,
            script : ProofScript,
            timeout : Optional[float]) -> None:
        params = {'goal': cryptoltypes.to_cryptol(goal),
                  'script': script}
        super(Prove, self).__init__('SAW/prove', params, connection, timeout=timeout)

    def process_result(self, res : Any) -> Any:
        return res

class EvalInt(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            expr : cryptoltypes.CryptolJSON,
            timeout : Optional[float]) -> None:
        params = {'expr': cryptoltypes.to_cryptol(expr)}
        super(EvalInt, self).__init__('SAW/eval int', params, connection, timeout=timeout)

    def process_result(self, res : Any) -> Any:
        return res

class EvalBool(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            expr : cryptoltypes.CryptolJSON,
            timeout : Optional[float]) -> None:
        params = {'expr': cryptoltypes.to_cryptol(expr)}
        super(EvalBool, self).__init__('SAW/eval bool', params, connection, timeout=timeout)

    def process_result(self, res : Any) -> Any:
        return res

class SAWReset(argo.Notification):
    def __init__(self, connection : argo.HasProtocolState) -> None:
        super(SAWReset, self).__init__(
            'SAW/clear state',
            {'state to clear': connection.protocol_state()},
            connection
        )


class SAWResetServer(argo.Notification):
    def __init__(self, connection : argo.HasProtocolState) -> None:
        super(SAWResetServer, self).__init__(
            'SAW/clear all states',
            {},
            connection
        )


class SAWSetOption(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState,
                 option : SAWOption, value : bool,
                 timeout : Optional[float]) -> None:
        params = {'option': str(option),
                  'value': value}
        super(SAWSetOption, self).__init__('SAW/set option', params, connection, timeout=timeout)

    def process_result(self, _res : Any) -> Any:
        return None
