from saw import *
from saw.llvm import uint32_t, Contract, void

import os
import os.path
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))
swap_bc = os.path.join(dir_path, 'swap.bc')

class Swap(Contract):
    def __init__(self) -> None:
        super().__init__()
        self.ty = uint32_t

    def specification(self) -> None:
        x = self.declare_var(self.ty, "x")
        y = self.declare_var(self.ty, "y")
        x_ptr = self.declare_pointer(self.ty)
        y_ptr = self.declare_pointer(self.ty)
        self.points_to(x_ptr, x)
        self.points_to(y_ptr, y)

        self.execute_func(x_ptr, y_ptr)

        self.points_to(x_ptr, y)
        self.points_to(y_ptr, x)
        self.returns(void)

env_connect_global()

mod = llvm_load_module(swap_bc)

result = llvm_verify(mod, 'swap', Swap())
