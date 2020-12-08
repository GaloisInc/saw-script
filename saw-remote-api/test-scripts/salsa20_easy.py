import os
import os.path
from cryptol.cryptoltypes import to_cryptol
from saw import *
from saw.llvm import Contract, LLVMType, LLVMArrayType, uint8_t, uint32_t, void, SetupVal, FreshVar, cryptol
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))

env_connect_global()
view(LogResults())

bcname = os.path.join(dir_path, 'salsa20.bc')
cryname = os.path.join(dir_path, 'Salsa20.cry')

cryptol_load_file(cryname)

mod = llvm_load_module(bcname)


def alloc_init(c : Contract, ty : LLVMType, val : SetupVal) -> SetupVal:
    """Add to``Contract`` ``c`` an allocation of a pointer to a value of type ``ty`` initialized to ``val``."""
    p = c.declare_pointer(ty)
    c.points_to(p, val)
    return p

def ptr_to_fresh(c : Contract, ty : LLVMType, name : Optional[str] = None) -> Tuple[FreshVar, SetupVal]:
    """Add to``Contract`` ``c`` an allocation of a pointer of type ``ty`` initialized to an unknown fresh value.
    
    :returns A fresh variable bound to the pointers initial value and the newly allocated pointer. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.declare_var(ty, name)
    ptr = alloc_init(c, ty, var)
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
        value = self.declare_var(uint32_t, "value")
        shift = self.declare_var(uint32_t, "shift")
        self.proclaim(shift > cryptol("0"))
        self.proclaim(shift < cryptol("32"))

        self.execute_func(value, shift)

        self.returns(cryptol("(<<<)")(value, shift))


rotl_result = llvm_verify(mod, 'rotl', RotlContract())

class QuarterRoundContract(Contract):
    def specification(self) -> None:
        y0 = self.declare_var(uint32_t, "y0")
        y1 = self.declare_var(uint32_t, "y1")
        y2 = self.declare_var(uint32_t, "y2")
        y3 = self.declare_var(uint32_t, "y3")

        y0_p = alloc_init(self, uint32_t, y0)
        y1_p = alloc_init(self, uint32_t, y1)
        y2_p = alloc_init(self, uint32_t, y2)
        y3_p = alloc_init(self, uint32_t, y3)

        self.execute_func(y0_p, y1_p, y2_p, y3_p)

        res = cryptol("quarterround")([y0, y1, y2, y3])
        self.points_to(y0_p, cryptol("(@)")(res, cryptol("0")))
        self.points_to(y1_p, cryptol("(@)")(res, cryptol("1")))
        self.points_to(y2_p, cryptol("(@)")(res, cryptol("2")))
        self.points_to(y3_p, cryptol("(@)")(res, cryptol("3")))
        self.returns(void)


qr_result = llvm_verify(mod, 's20_quarterround', QuarterRoundContract(), lemmas=[rotl_result])


class RowRoundContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, LLVMArrayType(uint32_t, 16), "rowround")

rr_result = llvm_verify(mod, 's20_rowround', RowRoundContract(), lemmas=[qr_result])


class ColumnRoundContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, LLVMArrayType(uint32_t, 16), "columnround")

cr_result = llvm_verify(mod, 's20_columnround', ColumnRoundContract(), lemmas=[rr_result])


class DoubleRoundContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, LLVMArrayType(uint32_t, 16), "doubleround")

dr_result = llvm_verify(mod, 's20_doubleround', DoubleRoundContract(), lemmas=[cr_result, rr_result])


class HashContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, LLVMArrayType(uint8_t, 64), "Salsa20")

hash_result = llvm_verify(mod, 's20_hash', HashContract(), lemmas=[dr_result])



class ExpandContract(Contract):
    def specification(self):
        k = self.declare_var(LLVMArrayType(uint8_t, 32))
        n = self.declare_var(LLVMArrayType(uint8_t, 16))
        k_p = self.declare_pointer(LLVMArrayType(uint8_t, 32))
        n_p = self.declare_pointer(LLVMArrayType(uint8_t, 16))
        ks_p = self.declare_pointer(LLVMArrayType(uint8_t, 64))
        self.points_to(k_p, k)
        self.points_to(n_p, n)

        self.execute_func(k_p, n_p, ks_p)

        self.returns(void)
        self.points_to(ks_p, cryptol("Salsa20_expansion`{a=2}")((k, n)))

expand_result = llvm_verify(mod, 's20_expand32', ExpandContract(), lemmas=[hash_result])


class Salsa20CryptContract(Contract):
    def __init__(self, size):
        super().__init__()
        self.size = size

    def specification(self):
        (k, k_p) = ptr_to_fresh(self, LLVMArrayType(uint8_t, 32))
        (v, v_p) = ptr_to_fresh(self, LLVMArrayType(uint8_t, 8))
        (m, m_p) = ptr_to_fresh(self, LLVMArrayType(uint8_t, self.size))

        self.execute_func(k_p, v_p, cryptol('0 : [32]'), m_p, cryptol(f'{self.size!r} : [32]'))

        self.returns(cryptol('0 : [32]'))
        self.points_to(m_p, cryptol("Salsa20_encrypt")((k, v, m)))

crypt_result = llvm_verify(mod, 's20_crypt32', Salsa20CryptContract(63), lemmas=[expand_result])
