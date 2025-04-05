from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, struct, void, i32, array_ty, struct_ty


class FContract(Contract):
    def specification(self):
        ty = array_ty(2, array_ty(4, i32))
        i  = self.fresh_var(ty, "w.i")
        pw = self.alloc(struct_ty(ty), points_to = struct(i))

        self.execute_func(pw)

        self.points_to(pw, struct(cry('zero:[2][4][32]')))
        self.returns(void)


class LLVMStructTest(unittest.TestCase):
    def test_llvm_struct(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_struct_type.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
