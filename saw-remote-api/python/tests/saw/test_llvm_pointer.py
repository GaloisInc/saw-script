from pathlib import Path
import unittest
from saw import *
from saw.llvm import Contract, cryptol, void
import saw.llvm_types as ty


class FContract(Contract):
    def specification(self):
        x = self.alloc(ty.ptr(ty.i8))

        self.execute_func(x)

        p = self.alloc(ty.i8)
        self.points_to(x, p)
        self.points_to(p, cryptol("42 : [8]"))
        self.returns(void)


class LLVMPointerTest(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(reset_server=True)

    @classmethod
    def tearDownClass(self):
        disconnect()

    def test_llvm_pointer(self):
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_pointer.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
