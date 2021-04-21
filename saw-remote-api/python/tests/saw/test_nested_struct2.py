from pathlib import Path
import unittest
from saw_client import *
from saw_client.llvm import Contract, elem, field, i32, alias_ty

# like test_nested_struct.py but using cute __getitem__ indexing on SetupVals

class FContract1(Contract):
    def specification(self):
        tp = self.alloc(alias_ty('struct.t'))
        b = self.fresh_var(i32, "b")
        self.points_to(tp['n']['b'], b)

        self.execute_func(tp)

        self.returns(b)

class FContract2(Contract):
    def specification(self):
        tp = self.alloc(alias_ty('struct.t'))
        b = self.fresh_var(i32, "b")
        self.points_to(tp[1][1], b)

        self.execute_func(tp)

        self.returns(b)

class LLVMNestedStructTest(unittest.TestCase):
    def test_llvm_struct(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())

        bcname = str(Path('tests','saw','test-files', 'nested_struct.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract1())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'f', FContract2())
        self.assertIs(result.is_success(), True)

if __name__ == "__main__":
    unittest.main()
