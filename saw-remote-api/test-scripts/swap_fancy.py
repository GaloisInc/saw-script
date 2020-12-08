import os
import os.path
import saw.connection as saw
from saw.llvm import uint32_t, Contract, void
from saw.proofscript import *
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))

c = env_connect()

swap_bc = os.path.join(dir_path, 'swap.bc')

c.llvm_load_module('m', swap_bc).result()

class Swap(Contract):
    def __init__(self) -> None:
        super().__init__()
        self.ty = uint32_t

    def specification(self) -> None:
        x = self.declare_var(self.ty)
        y = self.declare_var(self.ty)
        x_ptr = self.declare_pointer(self.ty)
        y_ptr = self.declare_pointer(self.ty)
        self.points_to(x_ptr, x)
        self.points_to(y_ptr, y)

        self.execute_func(x_ptr, y_ptr)

        self.points_to(x_ptr, y)
        self.points_to(y_ptr, x)
        self.returns(void)

contract = Swap()

prover = ProofScript([abc]).to_json()
print(c.llvm_verify('m', 'swap', [], False, contract.to_json(), prover, 'ok').result())
