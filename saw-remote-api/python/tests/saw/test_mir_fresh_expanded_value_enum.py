import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import fresh_expanded
from saw_client.mir import Contract, MIRAdt, adt_ty, enum, u32, void


class FNoneContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        x = enum(self.adt, 'None')

        self.execute_func(x)

        self.returns_f('27 : [32]')


class FSomeContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        ret = self.fresh_var(u32, 'ret')
        x = enum(self.adt, 'Some', ret)

        self.execute_func(x)

        self.returns(ret)


class GContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        x = fresh_expanded('x', adt_ty(self.adt))

        self.execute_func(x)

        self.returns(void)


class GGContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        x = fresh_expanded('x', adt_ty(self.adt))

        self.execute_func(x)

        self.returns(void)


class MIRFreshExpandedValueTest(unittest.TestCase):
    def test_mir_fresh_expanded_value(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_fresh_expanded_value_enum.linked-mir.json'))
        mod = mir_load_module(json_name)

        option_u32_adt = mir_find_adt(mod, 'core::option::Option', u32)

        f_none_ov = mir_verify(mod, 'mir_fresh_expanded_value_enum::f', FNoneContract(option_u32_adt))
        self.assertIs(f_none_ov.is_success(), True)

        f_some_ov = mir_verify(mod, 'mir_fresh_expanded_value_enum::f', FSomeContract(option_u32_adt))
        self.assertIs(f_some_ov.is_success(), True)

        g_ov_1 = mir_verify(mod, 'mir_fresh_expanded_value_enum::g', GContract(option_u32_adt))
        self.assertIs(g_ov_1.is_success(), True)

        g_ov_2 = mir_verify(mod, 'mir_fresh_expanded_value_enum::g', GContract(option_u32_adt), lemmas=[f_none_ov, f_some_ov])
        self.assertIs(g_ov_2.is_success(), True)

        gg_ov_1 = mir_verify(mod, 'mir_fresh_expanded_value_enum::gg', GGContract(option_u32_adt))
        self.assertIs(gg_ov_1.is_success(), True)

        gg_ov_2 = mir_verify(mod, 'mir_fresh_expanded_value_enum::gg', GGContract(option_u32_adt), lemmas=[g_ov_2])
        self.assertIs(gg_ov_2.is_success(), True)


if __name__ == "__main__":
    unittest.main()
