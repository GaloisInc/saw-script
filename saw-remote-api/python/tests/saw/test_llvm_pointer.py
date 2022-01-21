from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, void, i8, ptr_ty


class FContract(Contract):
    def specification(self):
        x = self.alloc(ptr_ty(i8))

        self.execute_func(x)

        p = self.alloc(i8)
        self.points_to(x, p)
        self.points_to(p, cry("42 : [8]"))
        self.returns(void)


class LLVMPointerTest(unittest.TestCase):

    def test_llvm_pointer(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_pointer.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
