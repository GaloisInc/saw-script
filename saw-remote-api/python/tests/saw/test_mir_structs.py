import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry, cry_f, struct
from saw_client.mir import Contract, FreshVar, MIRAdt, MIRType, SetupVal, adt_ty, u32, void


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
        x1 = self.fresh_var(u32, "x1")
        y1 = self.fresh_var(u32, "y1")
        s = struct(x1, y1, mir_adt = self.adt)

        self.execute_func(s)

        s_ = struct(cry_f('{y1} + 1'), cry_f('{x1} + 2'), mir_adt = self.adt)
        self.returns(s_)


class F4Contract(Contract):
    mod: MIRModule

    def __init__(self, mod: MIRModule):
        super().__init__()
        self.mod = mod

    def specification(self) -> None:
        x4 = self.fresh_var(u32, "x4")
        s4_adt = mir_find_adt(self.mod, "mir_structs::S4")
        s = struct(x4, mir_adt = s4_adt)

        self.execute_func(s)

        s_ = struct(cry_f('{x4} + 2'), mir_adt = s4_adt)
        self.returns(s_)


class GContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        x1 = self.fresh_var(u32, "x1")
        y1 = self.fresh_var(u32, "y1")
        s = struct(x1, y1, mir_adt = self.adt)
        s_ptr = self.alloc(adt_ty(self.adt), points_to = s, read_only = True)

        self.execute_func(s_ptr)

        s_ = struct(cry_f('{y1} + 1'), cry_f('{x1} + 2'), mir_adt = self.adt)
        self.returns(s_)


class HContract(Contract):
    adt: MIRAdt

    def __init__(self, adt: MIRAdt):
        super().__init__()
        self.adt = adt

    def specification(self) -> None:
        x1 = self.fresh_var(u32, "x1")
        y1 = self.fresh_var(u32, "y1")
        s = struct(x1, y1, mir_adt = self.adt)
        s_ptr = self.alloc(adt_ty(self.adt), points_to = s)

        self.execute_func(s_ptr)

        s_ = struct(cry_f('{y1} + 1'), cry_f('{x1} + 2'), mir_adt = self.adt)
        self.points_to(s_ptr, s_)
        self.returns(void)


class MIRStructsTest(unittest.TestCase):
    def test_mir_points_to(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_structs.linked-mir.json'))
        mod = mir_load_module(json_name)

        s1_adt = mir_find_adt(mod, "mir_structs::S1")
        f1_result = mir_verify(mod, 'mir_structs::f1', FContract(s1_adt))
        self.assertIs(f1_result.is_success(), True)

        s2_adt = mir_find_adt(mod, "mir_structs::S2", u32, u32)
        f2_result = mir_verify(mod, 'mir_structs::f2', FContract(s2_adt))
        self.assertIs(f2_result.is_success(), True)

        s3_adt = mir_find_adt(mod, "mir_structs::S3")
        f3_result = mir_verify(mod, 'mir_structs::f3', FContract(s3_adt))
        self.assertIs(f3_result.is_success(), True)

        f4_result = mir_verify(mod, 'mir_structs::f4', F4Contract(mod))
        self.assertIs(f4_result.is_success(), True)

        g_result = mir_verify(mod, 'mir_structs::g', GContract(s1_adt))
        self.assertIs(g_result.is_success(), True)

        h_result = mir_verify(mod, 'mir_structs::h', HContract(s1_adt))
        self.assertIs(h_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
