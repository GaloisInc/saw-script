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
        self.t = uint32_t

    def pre(self) -> None:
        self.x = self.declare(self.t)
        self.y = self.declare(self.t)
        self.x_pointer = self.declare_pointer(self.t)
        self.y_pointer = self.declare_pointer(self.t)
        self.points_to(self.x_pointer, self.x)
        self.points_to(self.y_pointer, self.y)

    def call(self) -> None:
        self.arguments(self.x_pointer, self.y_pointer)

    def post(self) -> None:
        self.points_to(self.x_pointer, self.y)
        self.points_to(self.y_pointer, self.x)
        self.returns(void)

contract = Swap()

prover = ProofScript([abc]).to_json()
print(c.llvm_verify('m', 'swap', [], False, contract.to_json(), prover, 'ok').result())
