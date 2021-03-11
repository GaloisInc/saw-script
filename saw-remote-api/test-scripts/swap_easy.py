from saw import *
from saw.llvm import Contract, void
from saw.llvm_types import i32

import os
import os.path
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))
swap_bc = os.path.join(dir_path, 'swap.bc')

class Swap(Contract):
    def __init__(self) -> None:
        super().__init__()
        self.ty = i32

    def specification(self) -> None:
        x = self.fresh_var(self.ty, "x")
        y = self.fresh_var(self.ty, "y")
        x_ptr = self.alloc(self.ty, points_to=x)
        y_ptr = self.alloc(self.ty, points_to=y)

        self.execute_func(x_ptr, y_ptr)

        self.points_to(x_ptr, y)
        self.points_to(y_ptr, x)
        self.returns(void)

env_connect_global()

mod = llvm_load_module(swap_bc)

result = llvm_verify(mod, 'swap', Swap())
