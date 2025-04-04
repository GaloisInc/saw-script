import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import struct
from saw_client.mir import Contract, FreshVar, MIRAdt, MIRType, SetupVal, lifetime, u32


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
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        (_, y) = ref_to_fresh(self, u32, read_only = True)

        self.execute_func(y)

        s = struct(y, mir_adt = self.adt)
        self.returns(s)


class MIRLifetimeTest(unittest.TestCase):
    def test_mir_lifetime(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_lifetime.linked-mir.json'))
        mod = mir_load_module(json_name)

        s_adt = mir_find_adt(mod, "mir_lifetime::S", lifetime)
        f_result = mir_verify(mod, 'mir_lifetime::f', FContract(s_adt))
        self.assertIs(f_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
