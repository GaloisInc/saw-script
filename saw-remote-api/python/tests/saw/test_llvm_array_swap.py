from pathlib import Path
import unittest
from saw_client import *
from saw_client.llvm import Contract, array, array_ty, void, i32


class ArraySwapContract(Contract):
    def specification(self):
        a0 = self.fresh_var(i32, "a0")
        a1 = self.fresh_var(i32, "a1")
        a  = self.alloc(array_ty(2, i32),
                        points_to=array(a0, a1))

        self.execute_func(a)

        self.points_to(a[0], a1)
        self.points_to(a[1], a0)
        self.returns(void)


class LLVMArraySwapTest(unittest.TestCase):
    def test_llvm_array_swap(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_array_swap.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'array_swap', ArraySwapContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
