from pathlib import Path
import unittest
from saw_client import *
from saw_client.llvm import Contract, global_initializer, global_var


class FContract(Contract):
    def specification(self):
        x_init = global_initializer("x")
        self.points_to(global_var("x"), x_init)

        self.execute_func()

        self.returns(x_init)


class LLVMGlobalTest(unittest.TestCase):
    def test_llvm_global(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_global.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
