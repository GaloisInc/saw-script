import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry_f, enum
from saw_client.mir import Contract, MIRAdt, adt_ty, bool_ty, u32


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
        ret = cry_f('42 : [32]')
        x = enum(self.adt, 'Some', ret)

        self.execute_func(x)

        self.returns(ret)


class GContract(Contract):
    def specification(self) -> None:
        b = self.fresh_var(bool_ty, 'b')

        self.execute_func(b)

        self.returns_f('if {b} then 27 else 42 : [32]')


class HNoneContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        self.execute_func()

        self.returns(enum(self.adt, 'None'))


class HSomeContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        x = self.fresh_var(u32, 'x')

        self.execute_func(x)

        self.returns(enum(self.adt, 'Some', x))


class I42Contract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        self.execute_func()

        self.returns(enum(self.adt, 'I42'))


class I43Contract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        self.execute_func()

        self.returns(enum(self.adt, 'I43'))


class MIRStructsTest(unittest.TestCase):
    def test_mir_points_to(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_enums.linked-mir.json'))
        mod = mir_load_module(json_name)

        option_adt = mir_find_adt(mod, 'core::option::Option', u32)
        i_adt = mir_find_adt(mod, "mir_enums::I")

        f_none_ov = mir_verify(mod, 'mir_enums::f', FNoneContract(option_adt))
        self.assertIs(f_none_ov.is_success(), True)

        f_some_ov = mir_verify(mod, 'mir_enums::f', FSomeContract(option_adt))
        self.assertIs(f_some_ov.is_success(), True)

        g_result = mir_verify(mod, 'mir_enums::g', GContract(), lemmas=[f_none_ov, f_some_ov])
        self.assertIs(g_result.is_success(), True)

        h_none_result = mir_verify(mod, 'mir_enums::h_none', HNoneContract(option_adt))
        self.assertIs(h_none_result.is_success(), True)

        h_some_result = mir_verify(mod, 'mir_enums::h_some', HSomeContract(option_adt))
        self.assertIs(h_some_result.is_success(), True)

        i42_result = mir_verify(mod, 'mir_enums::i42', I42Contract(i_adt))
        self.assertIs(i42_result.is_success(), True)

        i43_result = mir_verify(mod, 'mir_enums::i43', I43Contract(i_adt))
        self.assertIs(i43_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
