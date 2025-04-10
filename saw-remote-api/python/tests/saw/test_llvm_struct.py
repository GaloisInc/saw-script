from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, SetupVal, FreshVar, struct, LLVMType, void, array_ty, i32, alias_ty


def ptr_to_fresh(c : Contract, ty : LLVMType, name : Optional[str] = None) -> Tuple[FreshVar, SetupVal]:
    """Add to``Contract`` ``c`` an allocation of a pointer of type ``ty`` initialized to an unknown fresh value.
    
    :returns A fresh variable bound to the pointers initial value and the newly allocated pointer. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.fresh_var(ty, name)
    ptr = c.alloc(ty, points_to = var)
    return (var, ptr)


class SetContract(Contract):
    def specification(self):
        (_, x_p) = ptr_to_fresh(self, array_ty(2, i32), "x")
        p = self.alloc(alias_ty('struct.s'), points_to=struct(x_p))

        self.execute_func(p)

        self.points_to(p, struct(x_p))
        self.points_to(x_p, cry('[0, 0] : [2][32]'))
        self.returns(void)


class AddContract(Contract):
    def specification(self):
        (x, x_p) = ptr_to_fresh(self, array_ty(2, i32), "x")
        p = self.alloc(alias_ty('struct.s'), points_to=struct(x_p))

        self.execute_func(p)

        self.returns_f('{x}@0 + {x}@1')


class IdContract(Contract):
    def specification(self):
        (x, x_p) = ptr_to_fresh(self, array_ty(2, i32), "x")
        p = self.alloc(alias_ty('struct.s'), points_to=struct(x_p))

        self.execute_func(p)

        self.returns(p)


class LLVMStructTest(unittest.TestCase):
    def test_llvm_struct(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_struct.bc'))
        mod = llvm_load_module(bcname)

        # crucible_llvm_verify m "set_indirect" [] false set_spec abc;
        result = llvm_verify(mod, 'set_indirect', SetContract())
        self.assertIs(result.is_success(), True)
        # crucible_llvm_verify m "add_indirect" [] false add_spec abc;
        result = llvm_verify(mod, 'add_indirect', AddContract())
        self.assertIs(result.is_success(), True)
        # crucible_llvm_verify m "s_id" [] false id_spec abc;
        result = llvm_verify(mod, 's_id', IdContract())
        self.assertIs(result.is_success(), True)

if __name__ == "__main__":
    unittest.main()
