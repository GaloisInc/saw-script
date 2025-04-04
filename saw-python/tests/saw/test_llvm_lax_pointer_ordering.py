from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, FreshVar, LLVMType, SetupVal, array_ty, i64, void
from saw_client.option import LaxPointerOrdering


LEN = 42


def ptr_to_fresh(c : Contract, ty : LLVMType, name : Optional[str] = None,
                read_only : bool = False) -> Tuple[FreshVar, SetupVal]:
    """Add to ``Contract`` ``c`` an allocation of a pointer of type ``ty`` initialized to an unknown fresh value.
    If ``read_only == True`` then the allocated memory is immutable.

    :returns A fresh variable bound to the pointers initial value and the newly allocated pointer. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.fresh_var(ty, name)
    ptr = c.alloc(ty, points_to = var, read_only = read_only)
    return (var, ptr)


class ZipWithAddContract(Contract):
    def specification(self):
        array_t = array_ty(LEN, i64)
        c_ptr = self.alloc(array_t)
        (a, a_ptr) = ptr_to_fresh(self, name='a', ty=array_t, read_only=True)
        (b, b_ptr) = ptr_to_fresh(self, name='b', ty=array_t, read_only=True)

        self.execute_func(c_ptr, a_ptr, b_ptr)

        self.points_to(c_ptr, cry_f('zipWith`{{ {LEN} }} (+) {a} {b}'))
        self.returns(void)


class LLVMPointerTest(unittest.TestCase):

    def test_llvm_pointer(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'llvm_lax_pointer_ordering.bc'))
        mod = llvm_load_module(bcname)

        set_option(LaxPointerOrdering(), True)

        result = llvm_verify(mod, 'zip_with_add', ZipWithAddContract())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
