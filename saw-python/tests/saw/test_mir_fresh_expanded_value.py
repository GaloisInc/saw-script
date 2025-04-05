import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import fresh_expanded
from saw_client.mir import Contract, MIRAdt, adt_ty, array_ty, tuple_ty, u32, void


class FContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        s = fresh_expanded('s', adt_ty(self.adt))

        self.execute_func(s)

        self.returns(void)


class GContract(Contract):
    def specification(self) -> None:
        a = fresh_expanded('a', array_ty(2, u32))

        self.execute_func(a)

        self.returns(void)


class HContract(Contract):
    def specification(self) -> None:
        t = fresh_expanded('t', tuple_ty(u32, u32))

        self.execute_func(t)

        self.returns(void)


class MIRFreshExpandedValueTest(unittest.TestCase):
    def test_mir_fresh_expanded_value(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_fresh_expanded_value.linked-mir.json'))
        mod = mir_load_module(json_name)

        s1_adt = mir_find_adt(mod, 'mir_fresh_expanded_value::S1')
        f_result = mir_verify(mod, 'mir_fresh_expanded_value::f', FContract(s1_adt))
        self.assertIs(f_result.is_success(), True)

        g_result = mir_verify(mod, 'mir_fresh_expanded_value::g', GContract())
        self.assertIs(g_result.is_success(), True)

        h_result = mir_verify(mod, 'mir_fresh_expanded_value::h', HContract())
        self.assertIs(h_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
