import os
import os.path
from cryptol.cryptoltypes import to_cryptol
from saw import *
from saw.llvm import Contract, void, SetupVal, FreshVar, cryptol
from saw.llvm_types import i8, i32, LLVMType, LLVMArrayType
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))

env_connect_global()
view(LogResults())

bcname = os.path.join(dir_path, 'salsa20.bc')
cryname = os.path.join(dir_path, 'Salsa20.cry')

cryptol_load_file(cryname)

mod = llvm_load_module(bcname)

def ptr_to_fresh(c : Contract, ty : LLVMType, name : Optional[str] = None) -> Tuple[FreshVar, SetupVal]:
    """Add to``Contract`` ``c`` an allocation of a pointer of type ``ty`` initialized to an unknown fresh value.

    :returns A fresh variable bound to the pointers initial value and the newly allocated pointer. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.fresh_var(ty, name)
    ptr = c.alloc(ty, points_to = var)
    return (var, ptr)

def oneptr_update_func(c : Contract, ty : LLVMType, fn_name : str) -> None:
    """Updates contract ``c`` to declare calling it with a pointer of type ``ty``
    updates that pointer with the result, which is equal to calling the
    Cryptol function ``fn_name``."""
    (x, x_p) = ptr_to_fresh(c, ty)

    c.execute_func(x_p)

    c.points_to(x_p, cryptol(fn_name)(x))
    c.returns(void)
    return None

def bytes_type(n):
    return LLVMArrayType(i8, n)

def words_type(n):
    return LLVMArrayType(i32, n)

def fresh_bytes(c, sz, nm):
    return ptr_to_fresh(c, bytes_type(sz), nm)

def fresh_words(c, sz, nm):
    return ptr_to_fresh(c, words_type(sz), nm)

class RotlContract(Contract):
    def specification(self) -> None:
        value = self.fresh_var(i32, "value")
        shift = self.fresh_var(i32, "shift")
        self.proclaim(shift > cryptol("0"))
        self.proclaim(shift < cryptol("32"))

        self.execute_func(value, shift)

        self.returns(cryptol("(<<<)")(value, shift))

rotl_result = llvm_verify(mod, 'rotl', RotlContract())

class QuarterRoundContract(Contract):
    def specification(self) -> None:
        (y0, y0_p) = ptr_to_fresh(self, i32, "y0")
        (y1, y1_p) = ptr_to_fresh(self, i32, "y1")
        (y2, y2_p) = ptr_to_fresh(self, i32, "y2")
        (y3, y3_p) = ptr_to_fresh(self, i32, "y3")

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
        oneptr_update_func(self, words_type(16), "rowround")

rr_result = llvm_verify(mod, 's20_rowround', RowRoundContract(), lemmas=[qr_result])

class ColumnRoundContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, words_type(16), "columnround")

cr_result = llvm_verify(mod, 's20_columnround', ColumnRoundContract(), lemmas=[rr_result])

class DoubleRoundContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, words_type(16), "doubleround")

dr_result = llvm_verify(mod, 's20_doubleround', DoubleRoundContract(), lemmas=[cr_result, rr_result])

class HashContract(Contract):
    def specification(self) -> None:
        oneptr_update_func(self, bytes_type(64), "Salsa20")

hash_result = llvm_verify(mod, 's20_hash', HashContract(), lemmas=[dr_result])

class ExpandContract(Contract):
    def specification(self):
        (k, k_p) = fresh_bytes(self, 32, "k")
        (n, n_p) = fresh_bytes(self, 16, "n")
        ks_p = self.alloc(bytes_type(64))

        self.execute_func(k_p, n_p, ks_p)

        self.returns(void)
        self.points_to(ks_p, cryptol("Salsa20_expansion`{a=2}")((k, n)))

expand_result = llvm_verify(mod, 's20_expand32', ExpandContract(), lemmas=[hash_result])

class Salsa20CryptContract(Contract):
    def __init__(self, size):
        super().__init__()
        self.size = size

    def specification(self):
        (k, k_p) = fresh_bytes(self, 32, "k")
        (v, v_p) = fresh_bytes(self, 8, "v")
        (m, m_p) = fresh_bytes(self, self.size, "m")

        self.execute_func(k_p, v_p, cryptol('0 : [32]'), m_p, cryptol(f'{self.size!r} : [32]'))

        self.returns(cryptol('0 : [32]'))
        self.points_to(m_p, cryptol("Salsa20_encrypt")((k, v, m)))

crypt_result = llvm_verify(mod, 's20_crypt32', Salsa20CryptContract(63), lemmas=[expand_result])
