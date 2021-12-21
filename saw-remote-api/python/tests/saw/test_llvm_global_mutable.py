from pathlib import Path
import unittest
from saw_client import *
from saw_client.llvm import Contract, cryptol, global_var, void, i32


class ClearContract(Contract):
    def specification(self):
        self.alloc_global("g")

        self.execute_func()

        self.points_to(global_var("g"), cryptol("0 : [32]"))
        self.returns(void)

class SetContract(Contract):
    def specification(self):
        self.alloc_global("g")
        x  = self.fresh_var(i32, "x")

        self.execute_func(x)

        self.points_to(global_var("g"), x)
        self.returns(void)

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


if __name__ == "__main__":
    unittest.main()
