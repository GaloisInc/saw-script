from pathlib import Path
import unittest
from saw import *
from saw.llvm import Contract, elem, field
import saw.llvm_types as ty

class FContract1(Contract):
    def specification(self):
        tp = self.alloc(ty.alias('struct.t'))
        b = self.fresh_var(ty.i32, "b")
        self.points_to(field(field(tp, "n"), "b"), b)

        self.execute_func(tp)

        self.returns(b)

class FContract2(Contract):
    def specification(self):
        tp = self.alloc(ty.alias('struct.t'))
        b = self.fresh_var(ty.i32, "b")
        self.points_to(elem(elem(tp, 1), 1), b)

        self.execute_func(tp)

        self.returns(b)

class LLVMNestedStructTest(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(reset_server=True)

    @classmethod
    def tearDownClass(self):
        disconnect()

    def test_llvm_struct(self):
        if __name__ == "__main__": view(LogResults())

        bcname = str(Path('tests','saw','test-files', 'nested_struct.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract1())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'f', FContract2())
        self.assertIs(result.is_success(), True)

if __name__ == "__main__":
    unittest.main()
