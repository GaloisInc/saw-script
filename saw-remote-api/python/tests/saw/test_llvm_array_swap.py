from pathlib import Path
import unittest
from saw import *
from saw.llvm import Contract, array_val, elem, void
import saw.llvm_types as ty


class ArraySwapContract(Contract):
    def specification(self):
        a0 = self.fresh_var(ty.i32, "a0")
        a1 = self.fresh_var(ty.i32, "a1")
        a  = self.alloc(ty.array(2, ty.i32),
                        points_to=array_val(a0, a1))

        self.execute_func(a)

        self.points_to(elem(a, 0), a1)
        self.points_to(elem(a, 1), a0)
        self.returns(void)


class LLVMArraySwapTest(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(reset_server=True)

    @classmethod
    def tearDownClass(self):
        disconnect()

    def test_llvm_array_swap(self):
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_array_swap.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'array_swap', ArraySwapContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
