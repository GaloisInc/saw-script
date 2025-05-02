from itertools import chain
from typing import Dict, Any, List, Iterable, Type
from argo_client.interaction import ArgoException


class SAWException(Exception):
    data: Dict[str, Any]
    code: int
    stdout: str
    stderr: str

    def __init__(self, ae: ArgoException) -> None:
        super().__init__(ae.message)
        self.data = ae.data
        self.code = ae.code
        self.stdout = ae.stdout
        self.stderr = ae.stderr

    # The exception gets fields for each data field in the ArgoException
    def __getattr__(self, attr: str) -> Any:
        self.data.get(attr)

    def __dir__(self) -> Iterable[str]:
        return chain(super().__dir__(), [str(k) for k in self.data.keys()])

    def __str__(self) -> str:
        lines: List[str] = []
        for k, v in self.data.items():
            lines.append(f"{k}: {v}")
        return '\n'.join(lines)

    
def make_saw_exception(ae: ArgoException) -> SAWException:
    """Convert an ArgoException to its corresponding SAWException, failing with
    the original ArgoException if the code for this ArgoException does not
    correspond to a SAWException.
    """
    specific_exception_class = error_code_table.get(ae.code)
    if specific_exception_class is not None:
        return specific_exception_class(ae)
    else:
        raise ae

# Server value errors:
class ServerValueError(SAWException): pass
class NoServerValue(ServerValueError): pass
class NotACryptolEnvironment(ServerValueError): pass
class NotAnLLVMModule(ServerValueError): pass
class NotAnLLVMSetupScript(ServerValueError): pass
class NotAnLLVMSetupValue(ServerValueError): pass
class NotAnLLVMMethodSpecification(ServerValueError): pass
class NotAnLLVMMethodSpecIR(ServerValueError): pass
class NotAJVMClass(ServerValueError): pass
class NotAJVMMethodSpecIR(ServerValueError): pass
class NotASimpset(ServerValueError): pass
class NotATerm(ServerValueError): pass
class NotAYosysTheorem(ServerValueError): pass

# Setup errors:
class SetupError(SAWException): pass
class NotSettingUpCryptol(SetupError): pass
class NotSettingUpCrucibleLLVM(SetupError): pass
class NotAtTopLevel(SetupError): pass

# Loading errors:
class LoadingError(SAWException): pass
class CantLoadLLVMModule(LoadingError): pass

# Verification errors:
class VerificationError(SAWException): pass

# Cryptol errors:
class CryptolError(SAWException): pass

# The canonical mapping from Argo error codes to SAW exceptions:
error_code_table : Dict[int, Type[SAWException]] = {
    # Server value errors:
    10000: NoServerValue,
    10010: NotACryptolEnvironment,
    10020: NotAnLLVMModule,
    10030: NotAnLLVMSetupScript,
    10040: NotAnLLVMSetupValue,
    10040: NotAnLLVMMethodSpecification,
    10050: NotAnLLVMMethodSpecIR,
    10060: NotASimpset,
    10070: NotATerm,
    10080: NotAJVMClass,
    10090: NotAJVMMethodSpecIR,
    10130: NotAYosysTheorem,
    # Setup errors:
    10100: NotSettingUpCryptol,
    10110: NotSettingUpCrucibleLLVM,
    10120: NotAtTopLevel,
    # Loading errors:
    10200: CantLoadLLVMModule,
    # Verification errors:
    10300: VerificationError,
    # Cryptol errors:
    11000: CryptolError,
}
