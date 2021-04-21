import argo_client.interaction as argo
from typing import Any, Dict, List, Optional, Set, Union, overload

from cryptol import cryptoltypes
from . import exceptions
from .proofscript import *

from typing import Any, List

class SAWCommand(argo.Command):
    def process_error(self, ae : argo.ArgoException) -> Exception:
        return exceptions.make_saw_exception(ae)

class CryptolLoadFile(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState, filename : str) -> None:
        super(CryptolLoadFile, self).__init__(
            'SAW/Cryptol/load file',
            {'file': filename},
            connection
        )

    def process_result(self, _res : Any) -> Any:
        return None

class CryptolLoadModule(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState, module_name : str) -> None:
        super(CryptolLoadModule, self).__init__(
            'SAW/Cryptol/load module',
            {'module': module_name},
            connection
        )

    def process_result(self, _res : Any) -> Any:
        return None

class CreateGhostVariable(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState, name : str, server_name : str) -> None:
        super(CreateGhostVariable, self).__init__(
            'SAW/create ghost variable',
            {'display name': name,
             'server name': server_name},
            connection
        )

    def process_result(self, _res : Any) -> Any:
        return None

class LLVMLoadModule(SAWCommand):
    def __init__(self, connection : argo.HasProtocolState,
                 name : str,
                 bitcode_file : str) -> None:
        super(LLVMLoadModule, self).__init__(
            'SAW/LLVM/load module',
            {'name': name, 'bitcode file': bitcode_file},
            connection
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
            lemma_name : str) -> None:
        params = {'module': module,
                  'function': function,
                  'contract': setup,
                  'lemma name': lemma_name}
        super(LLVMAssume, self).__init__('SAW/LLVM/assume', params, connection)

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
            lemma_name : str) -> None:
        params = {'module': module,
                  'function': function,
                  'lemmas': lemmas,
                  'check sat': check_sat,
                  'contract': setup,
                  'script': script,
                  'lemma name': lemma_name}
        super(LLVMVerify, self).__init__('SAW/LLVM/verify', params, connection)

    def process_result(self, res : Any) -> Any:
        return res

class Prove(SAWCommand):
    def __init__(
            self,
            connection : argo.HasProtocolState,
            goal : cryptoltypes.CryptolJSON,
            script : ProofScript) -> None:
        params = {'goal': goal,
                  'script': script}
        super(Prove, self).__init__('SAW/prove', params, connection)

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
