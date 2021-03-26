from pathlib import Path
import unittest
from cryptol.cryptoltypes import to_cryptol
from saw import *
from saw.llvm import Contract, void, SetupVal, FreshVar, cryptol
from saw.llvm_types import i8, i32, LLVMType, LLVMArrayType



def ptr_to_fresh(c : Contract, ty : LLVMType, name : Optional[str] = None) -> Tuple[FreshVar, SetupVal]:
    """Add to``Contract`` ``c`` an allocation of a pointer of type ``ty`` initialized to an unknown fresh value.
    
    :returns A fresh variable bound to the pointers initial value and the newly allocated pointer. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.fresh_var(ty, name)
    ptr = c.alloc(ty, points_to = var)
    return (var, ptr)

def oneptr_update_func(c : Contract, ty : LLVMType, fn_name : str) -> None:
    """Upcates contract ``c`` to declare calling it with a pointer of type ``ty``
    updates that pointer with the result, which is equal to calling the
    Cryptol function ``fn_name``."""
    (x, x_p) = ptr_to_fresh(c, ty)

    c.execute_func(x_p)

    c.points_to(x_p, cryptol(fn_name)(x))
    c.returns(void)
    return None


class RotlContract(Contract):
    def specification(self) -> None:
        value = self.fresh_var(i32, "value")
        shift = self.fresh_var(i32, "shift")
        self.precondition(shift > cryptol("0"))
        self.precondition(shift < cryptol("32"))

        self.execute_func(value, shift)

        self.returns(cryptol("(<<<)")(value, shift))



class QuarterRoundContract(Contract):
    def specification(self) -> None:
        y0 = self.fresh_var(i32, "y0")
        y1 = self.fresh_var(i32, "y1")
        y2 = self.fresh_var(i32, "y2")
        y3 = self.fresh_var(i32, "y3")

        y0_p = self.alloc(i32, points_to=y0)
        y1_p = self.alloc(i32, points_to=y1)
        y2_p = self.alloc(i32, points_to=y2)
        y3_p = self.alloc(i32, points_to=y3)

        self.execute_func(y0_p, y1_p, y2_p, y3_p)

        res = cryptol("quarterround")([y0, y1, y2, y3])
        self.points_to(y0_p, cryptol("(@)")(res, cryptol("0")))
        self.points_to(y1_p, cryptol("(@)")(res, cryptol("1")))
        self.points_to(y2_p, cryptol("(@)")(res, cryptol("2")))
        self.points_to(y3_p, cryptol("(@)")(res, cryptol("3")))
        self.returns(void)



class RowRoundContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, LLVMArrayType(i32, 16), "rowround")



class ColumnRoundContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, LLVMArrayType(i32, 16), "columnround")



class DoubleRoundContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, LLVMArrayType(i32, 16), "doubleround")



class HashContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, LLVMArrayType(i8, 64), "Salsa20")




class ExpandContract(Contract):
    def specification(self):
        k = self.fresh_var(LLVMArrayType(i8, 32))
        n = self.fresh_var(LLVMArrayType(i8, 16))
        k_p = self.alloc(LLVMArrayType(i8, 32))
        n_p = self.alloc(LLVMArrayType(i8, 16))
        ks_p = self.alloc(LLVMArrayType(i8, 64))
        self.points_to(k_p, k)
        self.points_to(n_p, n)

        self.execute_func(k_p, n_p, ks_p)

        self.returns(void)
        self.points_to(ks_p, cryptol("Salsa20_expansion`{a=2}")((k, n)))



class Salsa20CryptContract(Contract):
    def __init__(self, size):
        super().__init__()
        self.size = size

    def specification(self):
        (k, k_p) = ptr_to_fresh(self, LLVMArrayType(i8, 32))
        (v, v_p) = ptr_to_fresh(self, LLVMArrayType(i8, 8))
        (m, m_p) = ptr_to_fresh(self, LLVMArrayType(i8, self.size))

        self.execute_func(k_p, v_p, cryptol('0 : [32]'), m_p, cryptol(f'{self.size!r} : [32]'))

        self.returns(cryptol('0 : [32]'))
        self.points_to(m_p, cryptol("Salsa20_encrypt")((k, v, m)))

class Salsa20EasyTest(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        connect(reset_server=True)

    @classmethod
    def tearDownClass(self):
        disconnect()

    def test_salsa20(self):
        if __name__ == "__main__": view(LogResults())

        bcname = str(Path('tests','saw','test-files', 'salsa20.bc'))
        cryname = str(Path('tests','saw','test-files', 'Salsa20.cry'))

        cryptol_load_file(cryname)

        mod = llvm_load_module(bcname)

        rotl_result = llvm_verify(mod, 'rotl', RotlContract())

        qr_result = llvm_verify(mod, 's20_quarterround', QuarterRoundContract(), lemmas=[rotl_result])
        self.assertIs(qr_result.is_success(), True)
        rr_result = llvm_verify(mod, 's20_rowround', RowRoundContract(), lemmas=[qr_result])
        self.assertIs(rr_result.is_success(), True)
        cr_result = llvm_verify(mod, 's20_columnround', ColumnRoundContract(), lemmas=[rr_result])
        self.assertIs(cr_result.is_success(), True)
        dr_result = llvm_verify(mod, 's20_doubleround', DoubleRoundContract(), lemmas=[cr_result, rr_result])
        self.assertIs(dr_result.is_success(), True)
        hash_result = llvm_verify(mod, 's20_hash', HashContract(), lemmas=[dr_result])
        self.assertIs(hash_result.is_success(), True)
        expand_result = llvm_verify(mod, 's20_expand32', ExpandContract(), lemmas=[hash_result])
        self.assertIs(expand_result.is_success(), True)
        crypt_result = llvm_verify(mod, 's20_crypt32', Salsa20CryptContract(63), lemmas=[expand_result])
        self.assertIs(crypt_result.is_success(), True)

if __name__ == "__main__":
    unittest.main()
