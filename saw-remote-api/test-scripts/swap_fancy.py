import os
import os.path
import saw.connection as saw
from saw.llvm import Contract, void
from saw.llvm_types import i32
from saw.proofscript import *
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))

c = env_connect()

swap_bc = os.path.join(dir_path, 'swap.bc')

c.llvm_load_module('m', swap_bc).result()

class Swap(Contract):
    def __init__(self) -> None:
        super().__init__()
        self.ty = i32

    def specification(self) -> None:
        x = self.fresh_var(self.ty)
        y = self.fresh_var(self.ty)
        x_ptr = self.alloc(self.ty, points_to=x)
        y_ptr = self.alloc(self.ty, points_to=y)

        self.execute_func(x_ptr, y_ptr)

        self.points_to(x_ptr, y)
        self.points_to(y_ptr, x)
        self.returns(void)

contract = Swap()

prover = ProofScript([abc]).to_json()
print(c.llvm_verify('m', 'swap', [], False, contract.to_json(), prover, 'ok').result())
