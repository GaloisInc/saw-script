from pathlib import Path
import unittest
from saw import *
from saw.llvm import Contract, cryptol, struct, void
import saw.llvm_types as ty


class FContract(Contract):
    def specification(self):
        array_ty = ty.array(2, ty.array(4, ty.i32))
        i  = self.fresh_var(array_ty, "w.i")
        pw = self.alloc(ty.struct_type(array_ty), points_to = struct(i))

        self.execute_func(pw)

        self.points_to(pw, struct(cryptol('zero:[2][4][32]')))
        self.returns(void)


class LLVMStructTest(unittest.TestCase):
    def test_llvm_struct(self):
        connect()
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_struct_type.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'f', FContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
