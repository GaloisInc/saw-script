import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry_f, tuple_value
from saw_client.mir import Contract, tuple_ty, u32, void


class FContract(Contract):
    def specification(self) -> None:
        x = self.fresh_var(u32, "x")
        y = self.fresh_var(u32, "y")
        s = tuple_value(x, y)

        self.execute_func(s)

        s_ = tuple_value(cry_f('{y} + 1'), cry_f('{x} + 2'))
        self.returns(s_)


class GContract(Contract):
    def specification(self) -> None:
        x = self.fresh_var(u32, "x")
        y = self.fresh_var(u32, "y")
        s = tuple_value(x, y)
        s_ptr = self.alloc(tuple_ty(u32, u32), points_to = s, read_only = True)

        self.execute_func(s_ptr)

        s_ = tuple_value(cry_f('{y} + 1'), cry_f('{x} + 2'))
        self.returns(s_)


class HContract(Contract):
    def specification(self) -> None:
        x = self.fresh_var(u32, "x")
        y = self.fresh_var(u32, "y")
        s = tuple_value(x, y)
        s_ptr = self.alloc(tuple_ty(u32, u32), points_to = s)

        self.execute_func(s_ptr)

        s_ = tuple_value(cry_f('{y} + 1'), cry_f('{x} + 2'))
        self.points_to(s_ptr, s_)
        self.returns(void)


class MIRStructsTest(unittest.TestCase):
    def test_mir_points_to(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_tuples.linked-mir.json'))
        mod = mir_load_module(json_name)

        f_result = mir_verify(mod, 'mir_tuples::f', FContract())
        self.assertIs(f_result.is_success(), True)

        g_result = mir_verify(mod, 'mir_tuples::g', GContract())
        self.assertIs(g_result.is_success(), True)

        h_result = mir_verify(mod, 'mir_tuples::h', HContract())
        self.assertIs(h_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
