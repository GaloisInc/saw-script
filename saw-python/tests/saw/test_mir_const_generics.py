import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry_f, struct
from saw_client.mir import *


class FGContract(Contract):
    mod: MIRModule
    n: int

    def __init__(self, mod: MIRModule, n: int):
        super().__init__()
        self.mod = mod
        self.n = n

    def specification(self) -> None:
        y = self.fresh_var(array_ty(self.n, u32), "y")

        self.execute_func(y)

        s_adt = mir_find_adt(
            self.mod,
            "mir_const_generics::S",
            const_ty(usize, cry_f('{self.n} : [64]')),
        )
        self.returns(struct(y, mir_adt = s_adt))


class HContract(Contract):
    mod: MIRModule

    def __init__(self, mod: MIRModule):
        super().__init__()
        self.mod = mod

    def specification(self) -> None:
        self.execute_func()

        t_adt = mir_find_adt(
            self.mod,
            "mir_const_generics::T",
            const_ty(i8, cry_f('0 : [8]')),
            const_ty(i16, cry_f('0 : [16]')),
            const_ty(i32, cry_f('0 : [32]')),
            const_ty(i64, cry_f('0 : [64]')),
            const_ty(i128, cry_f('0 : [128]')),
            const_ty(isize, cry_f('0 : [64]')),
            const_ty(u8, cry_f('0 : [8]')),
            const_ty(u16, cry_f('0 : [16]')),
            const_ty(u32, cry_f('0 : [32]')),
            const_ty(u64, cry_f('0 : [64]')),
            const_ty(u128, cry_f('0 : [128]')),
            const_ty(usize, cry_f('0 : [64]')),
            const_ty(bool_ty, cry_f('True')),
            const_ty(char_ty, cry_f('zext \'a\' : [32]')),
        )
        self.returns(struct(mir_adt = t_adt))


class MIRConstGenericsTest(unittest.TestCase):
    def test_mir_const_generics_adt(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_const_generics.linked-mir.json'))
        mod = mir_load_module(json_name)

        f_result = mir_verify(mod, 'mir_const_generics::f', FGContract(mod, 1))
        self.assertIs(f_result.is_success(), True)

        g_result = mir_verify(mod, 'mir_const_generics::g', FGContract(mod, 2))
        self.assertIs(g_result.is_success(), True)

        h_result = mir_verify(mod, 'mir_const_generics::h', HContract(mod))
        self.assertIs(h_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
