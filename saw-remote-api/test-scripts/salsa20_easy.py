import os
import os.path
from cryptol.cryptoltypes import to_cryptol
from saw import *
from saw.llvm import Contract, LLVMArrayType, uint8_t, uint32_t, void
from env_server import *

dir_path = os.path.dirname(os.path.realpath(__file__))

env_connect_global()
view(LogResults())

bcname = os.path.join(dir_path, 'salsa20.bc')
cryname = os.path.join(dir_path, 'Salsa20.cry')

cryptol_load_file(cryname)

mod = llvm_load_module(bcname)

class RotlContract(Contract):
    def pre(self):
        self.value = self.declare(uint32_t)
        self.shift = self.declare(uint32_t)
        self.proclaim(self.shift > self.cryptol("0"))
        self.proclaim(self.shift < self.cryptol("32"))
    def call(self):
        self.arguments(self.value, self.shift)
    def post(self):
        self.returns(self.cryptol("(<<<)")(self.value, self.shift))


rotl_result = llvm_verify(mod, 'rotl', RotlContract())

class TrivialContract(Contract):
    def post(self): self.returns(void)

class QuarterRoundContract(Contract):
    def pre(self):
        self.y0 = self.declare(uint32_t)
        self.y1 = self.declare(uint32_t)
        self.y2 = self.declare(uint32_t)
        self.y3 = self.declare(uint32_t)

        self.y0_p = self.declare_pointer(uint32_t)
        self.y1_p = self.declare_pointer(uint32_t)
        self.y2_p = self.declare_pointer(uint32_t)
        self.y3_p = self.declare_pointer(uint32_t)

        self.points_to(self.y0_p, self.y0)
        self.points_to(self.y1_p, self.y1)
        self.points_to(self.y2_p, self.y2)
        self.points_to(self.y3_p, self.y3)

    def call(self):
        self.arguments(self.y0_p, self.y1_p, self.y2_p, self.y3_p)

    def post(self):
        self.points_to(self.y0_p,
                       self.cryptol("(@)")(self.cryptol("quarterround")([self.y0, self.y1, self.y2, self.y3]),
                                           self.cryptol("0")))
        self.points_to(self.y1_p,
                       self.cryptol("(@)")(self.cryptol("quarterround")([self.y0, self.y1, self.y2, self.y3]),
                                           self.cryptol("1")))
        self.points_to(self.y2_p,
                       self.cryptol("(@)")(self.cryptol("quarterround")([self.y0, self.y1, self.y2, self.y3]),
                                           self.cryptol("2")))
        self.points_to(self.y3_p,
                       self.cryptol("(@)")(self.cryptol("quarterround")([self.y0, self.y1, self.y2, self.y3]),
                                           self.cryptol("3")))
        self.returns(void)


qr_result = llvm_verify(mod, 's20_quarterround', QuarterRoundContract(), lemmas=[rotl_result])


class OnePointerUpdateContract(Contract):
    def __init__(self, the_type):
        super().__init__()
        self.t = the_type


    def pre(self):
        self.y = self.declare(self.t)
        self.y_p = self.declare_pointer(self.t)
        self.points_to(self.y_p, self.y)

    def call(self):
        self.arguments(self.y_p)

    def post(self):

        self.returns(void)


class RowRoundContract(OnePointerUpdateContract):
    def __init__(self):
        super().__init__(LLVMArrayType(uint32_t, 16))

    def post(self):
        super().post()
        self.points_to(self.y_p, self.cryptol("rowround")(self.y))

rr_result = llvm_verify(mod, 's20_rowround', RowRoundContract(), lemmas=[qr_result])


class ColumnRoundContract(OnePointerUpdateContract):
    def __init__(self):
        super().__init__(LLVMArrayType(uint32_t, 16))

    def post(self):
        super().post()
        self.points_to(self.y_p, self.cryptol("columnround")(self.y))

cr_result = llvm_verify(mod, 's20_columnround', ColumnRoundContract(), lemmas=[rr_result])


class DoubleRoundContract(OnePointerUpdateContract):
    def __init__(self):
        super().__init__(LLVMArrayType(uint32_t, 16))

    def post(self):
        super().post()
        self.points_to(self.y_p, self.cryptol("doubleround")(self.y))

dr_result = llvm_verify(mod, 's20_doubleround', DoubleRoundContract(), lemmas=[cr_result, rr_result])


class HashContract(OnePointerUpdateContract):
    def __init__(self):
        super().__init__(LLVMArrayType(uint8_t, 64))

    def post(self):
        super().post()
        self.points_to(self.y_p, self.cryptol("Salsa20")(self.y))

hash_result = llvm_verify(mod, 's20_hash', HashContract(), lemmas=[dr_result])


class ExpandContract(Contract):
    def pre(self):
        self.k = self.declare(LLVMArrayType(uint8_t, 32))
        self.n = self.declare(LLVMArrayType(uint8_t, 16))

        self.k_p = self.declare_pointer(LLVMArrayType(uint8_t, 32))
        self.n_p = self.declare_pointer(LLVMArrayType(uint8_t, 16))
        self.ks_p = self.declare_pointer(LLVMArrayType(uint8_t, 64))

        self.points_to(self.k_p, self.k)
        self.points_to(self.n_p, self.n)

    def call(self):
        self.arguments(self.k_p, self.n_p, self.ks_p)

    def post(self):
        self.returns(void)
        self.points_to(self.ks_p, self.cryptol("Salsa20_expansion`{a=2}")((self.k, self.n)))

expand_result = llvm_verify(mod, 's20_expand32', ExpandContract(), lemmas=[hash_result])


class Salsa20CryptContract(Contract):
    def __init__(self, size):
        super().__init__()
        self.size = size
        self.zero = self.cryptol("0 : [32]")

    def val_and_pointer(self, t):
        v = self.declare(t)
        p = self.declare_pointer(t)
        self.points_to(p, v)
        return (v, p)

    def pre(self):
        (self.k, self.k_p) = self.val_and_pointer(LLVMArrayType(uint8_t, 32))
        (self.v, self.v_p) = self.val_and_pointer(LLVMArrayType(uint8_t, 8))
        (self.m, self.m_p) = self.val_and_pointer(LLVMArrayType(uint8_t, self.size))

    def call(self):
        self.arguments(self.k_p, self.v_p, self.zero, self.m_p, self.cryptol(str(self.size) + " : [32]"))

    def post(self):
        self.returns(self.zero)
        self.points_to(self.m_p, self.cryptol("Salsa20_encrypt")((self.k, self.v, self.m)))

crypt_result = llvm_verify(mod, 's20_crypt32', Salsa20CryptContract(63), lemmas=[expand_result])
