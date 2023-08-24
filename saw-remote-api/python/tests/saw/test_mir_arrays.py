import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import array, cry, cry_f
from saw_client.mir import Contract, FreshVar, MIRType, SetupVal, u32, u64, void


def ref_to_fresh(c : Contract, ty : MIRType, name : Optional[str] = None,
                 read_only : bool = False) -> Tuple[FreshVar, SetupVal]:
    """Add to ``Contract`` ``c`` an allocation of a reference of type ``ty`` initialized to an unknown fresh value.
    If ``read_only == True`` then the allocated memory is immutable.

    :returns A fresh variable bound to the reference's initial value and the newly allocated reference. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.fresh_var(ty, name)
    ptr = c.alloc(ty, points_to = var, read_only = read_only)
    return (var, ptr)


class FContract(Contract):
    def specification(self) -> None:
        (x0, x0_p) = ref_to_fresh(self, u32, "x0", read_only = True)
        (x1, x1_p) = ref_to_fresh(self, u32, "x1", read_only = True)
        x = array(x0_p, x1_p)

        self.execute_func(x)

        self.returns_f('{x0} + {x1}')


class GContract(Contract):
    def specification(self) -> None:
        x0_p = self.alloc(u32)
        (x1, x1_p) = ref_to_fresh(self, u32, "x1")
        x = array(x0_p, x1_p)

        self.execute_func(x)

        self.points_to(x0_p, cry_f('42 : [32]'))
        self.points_to(x1_p, cry_f('{x1} + 1'))
        self.returns(void)


class HContract(Contract):
    def specification(self) -> None:
        self.execute_func()

        x0_ptr = self.alloc(u32, points_to = cry_f('27 : [32]'), read_only = True)
        x1_ptr = self.alloc(u32, points_to = cry_f('42 : [32]'), read_only = True)
        self.returns(array(x0_ptr, x1_ptr))


class IContract(Contract):
    def specification(self) -> None:
        self.execute_func(cry_f('[] : [0][32]'))

        self.returns(array(element_type = u64))


class MIRArraysTest(unittest.TestCase):
    def test_mir_points_to(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_arrays.linked-mir.json'))
        mod = mir_load_module(json_name)

        f_result = mir_verify(mod, 'mir_arrays::f', FContract())
        self.assertIs(f_result.is_success(), True)

        g_result = mir_verify(mod, 'mir_arrays::g', GContract())
        self.assertIs(g_result.is_success(), True)

        h_result = mir_verify(mod, 'mir_arrays::h', HContract())
        self.assertIs(h_result.is_success(), True)

        i_result = mir_verify(mod, 'mir_arrays::i', IContract())
        self.assertIs(i_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
