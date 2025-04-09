from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry_f
from saw_client.llvm import Contract, global_var, void, i32


class ClearContract(Contract):
    def specification(self):
        self.alloc_global("g")

        self.execute_func()

        self.points_to(global_var("g"), cry_f("0 : [32]"))
        self.returns(void)

class SetContract(Contract):
    def specification(self):
        self.alloc_global("g")
        x  = self.fresh_var(i32, "x")

        self.execute_func(x)

        self.points_to(global_var("g"), x)
        self.returns(void)

class GetContract(Contract):
    def specification(self):
        self.alloc_global("g")
        g = global_var("g")
        x = self.fresh_var(i32, "x")
        self.points_to(g, x)

        self.execute_func(x)

        self.points_to(g, x)
        self.returns(x)

class LLVMGlobalTest(unittest.TestCase):
    def test_llvm_global(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'global.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'set', SetContract())
        self.assertIs(result.is_success(), True)
        result = llvm_verify(mod, 'clear', ClearContract())
        self.assertIs(result.is_success(), True)
        result = llvm_verify(mod, 'get', GetContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
