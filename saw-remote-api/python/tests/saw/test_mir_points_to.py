import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.mir import Contract, FreshVar, MIRType, SetupVal, u32, void


def ref_to_fresh(c : Contract, ty : MIRType, name : Optional[str] = None,
                 read_only : bool = False) -> Tuple[FreshVar, SetupVal]:
    """Add to ``Contract`` ``c`` an allocation of a reference of type ``ty`` initialized to an unknown fresh value.
    If ``read_only == True`` then the allocated memory is immutable.

    :returns A fresh variable bound to the reference's initial value and the newly allocated reference. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.fresh_var(ty, name)
    ptr = c.alloc(ty, points_to = var, read_only = read_only)
    return (var, ptr)


class ReadFromRefContract(Contract):
    def specification(self) -> None:
        (x, x_p) = ref_to_fresh(self, u32, "x", read_only = True)

        self.execute_func(x_p)

        self.returns_f('{x}')


class WriteToRefContract(Contract):
    def specification(self) -> None:
        ptr = self.alloc(u32, read_only = False)
        y = self.fresh_var(u32, 'y')

        self.execute_func(ptr, y)

        self.points_to(ptr, y)
        self.returns(void)


class MIRPointsToTest(unittest.TestCase):
    def test_mir_points_to(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_points_to.linked-mir.json'))
        mod = mir_load_module(json_name)

        read_from_ref_result = mir_verify(mod, 'mir_points_to::read_from_ref', ReadFromRefContract())
        self.assertIs(read_from_ref_result.is_success(), True)

        write_to_ref_result = mir_verify(mod, 'mir_points_to::write_to_ref', WriteToRefContract())
        self.assertIs(write_to_ref_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
