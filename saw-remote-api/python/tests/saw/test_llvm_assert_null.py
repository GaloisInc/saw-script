from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, null, i32


class FContract1(Contract):
    def specification(self):
        p = self.alloc(i32)

        self.execute_func(p)

        self.returns(cry("0 : [32]"))


class FContract2(Contract):
    def specification(self):
        self.execute_func(null())

        self.returns(cry("1 : [32]"))


class LLVMAssertNullTest(unittest.TestCase):
    def test_llvm_assert_null(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_assert_null.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract1())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'f', FContract2())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
