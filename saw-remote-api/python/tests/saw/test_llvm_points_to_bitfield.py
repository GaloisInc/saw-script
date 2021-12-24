from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, LLVMIntType, alias_ty, i8, void
from saw_client.option import LaxLoadsAndStores


i1 = LLVMIntType(1)
i2 = LLVMIntType(2)


class GetX2Contract(Contract):
    def specification(self):
        ss = self.alloc(alias_ty('struct.s'))
        z = self.fresh_var(i2, 'z')
        self.points_to_bitfield(ss, 'x2', z)

        self.execute_func(ss)

        self.returns_f('zext {z} : [8]')


class GetYContract(Contract):
    def specification(self):
        ss = self.alloc(alias_ty('struct.s'))
        z = self.fresh_var(i1, 'z')
        self.points_to_bitfield(ss, 'y', z)

        self.execute_func(ss)

        self.returns(z)


class SetX2Contract(Contract):
    def specification(self):
        ss = self.alloc(alias_ty('struct.s'))
        z = self.fresh_var(i8, 'z')

        self.execute_func(ss, z)

        self.points_to_bitfield(ss, 'x2', cry_f('drop {z} : [2]'))
        self.returns(void)


class SetX2AltContract(Contract):
    def specification(self):
        ss = self.alloc(alias_ty('struct.s'))
        z = self.fresh_var(i2, 'z')

        self.execute_func(ss, cry_f('zext {z} : [8]'))

        self.points_to_bitfield(ss, 'x2', z)
        self.returns(void)


def y_spec(c : Contract) -> None:
    ss = c.alloc(alias_ty('struct.s'))
    z = c.fresh_var(i1, 'z')

    c.execute_func(ss, z)

    c.points_to_bitfield(ss, 'y', z)
    c.returns(void)


class SetYContract(Contract):
    def specification(self):
        y_spec(self)


class SetYAltContract(Contract):
    def specification(self):
        y_spec(self)


class LLVMNestedStructTest(unittest.TestCase):
    def test_llvm_struct(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())

        bcname = str(Path('tests','saw','test-files', 'llvm_points_to_bitfield.bc'))
        mod = llvm_load_module(bcname)

        set_option(LaxLoadsAndStores(), True)

        result = llvm_verify(mod, 'get_x2', GetX2Contract())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'get_y', GetYContract())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'set_x2', SetX2Contract())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'set_x2_alt', SetX2AltContract())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'set_y', SetYContract())
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, 'set_y_alt', SetYAltContract())
        self.assertIs(result.is_success(), True)

        set_x2_ov = llvm_assume(mod, 'set_x2', SetX2Contract())
        result = llvm_verify(mod, 'set_x2_alt', SetX2AltContract(), lemmas=[set_x2_ov])
        self.assertIs(result.is_success(), True)

        set_y_ov = llvm_assume(mod, 'set_y', SetYContract())
        result = llvm_verify(mod, 'set_y_alt', SetYAltContract(), lemmas=[set_x2_ov])
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
