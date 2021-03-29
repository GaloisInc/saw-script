from pathlib import Path
import unittest
from saw import *
from saw.llvm import Contract, cryptol, null
import saw.llvm_types as ty


class FContract1(Contract):
    def specification(self):
        p = self.alloc(ty.i32)

        self.execute_func(p)

        self.returns(cryptol("0 : [32]"))


class FContract2(Contract):
    def specification(self):
        self.execute_func(null())

        self.returns(cryptol("1 : [32]"))


class LLVMAssertNullTest(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(reset_server=True)

    @classmethod
    def tearDownClass(self):
        disconnect()

    def test_llvm_assert_null(self):
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_assert_null.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract1())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'f', FContract2())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
