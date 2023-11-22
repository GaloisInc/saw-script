import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry_f
from saw_client.mir import Contract, FreshVar, MIRType, SetupVal, u32


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
        x = self.fresh_var(u32, 'x')

        self.execute_func(x)

        self.returns(x)


class F2Contract(Contract):
    def specification(self) -> None:
        x = cry_f('2 : [32]')

        self.execute_func(x)

        self.returns(x)


class GContract(Contract):
    def specification(self) -> None:
        x = self.fresh_var(u32, 'x')

        self.execute_func(x)

        self.returns(cry_f('{x} + 1'))


class G2Contract(Contract):
    def specification(self) -> None:
        self.execute_func()

        self.returns(cry_f('3 : [32]'))


class HContract(Contract):
    def specification(self) -> None:
        x = self.fresh_var(u32, 'x')

        self.execute_func(x)

        self.returns(cry_f('{x} + 1'))


class PContract(Contract):
    def specification(self) -> None:
        (x, x_ref) = ref_to_fresh(self, u32, "x", read_only = True)
        (y, y_ref) = ref_to_fresh(self, u32, "y", read_only = True)

        self.execute_func(x_ref, y_ref)

        self.returns(cry_f('{x} + {y}'))


class QContract(Contract):
    def specification(self) -> None:
        (x, x_ref) = ref_to_fresh(self, u32, "x", read_only = True)
        (y, y_ref) = ref_to_fresh(self, u32, "y", read_only = True)

        self.execute_func(x_ref, y_ref)

        self.returns(cry_f('{x} + {y}'))


class MIRUnsafeAssumeSpecTest(unittest.TestCase):
    def test_mir_unsafe_assume_spec(self):
        connect(reset_server=True)
        # if __name__ == "__main__": view(LogResults())
        if __name__ == "__main__": view(LogResults(verbose_failure=True))
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_unsafe_assume_spec.linked-mir.json'))
        mod = mir_load_module(json_name)

        f_ov  = mir_assume(mod, 'mir_unsafe_assume_spec::f', FContract())
        f2_ov = mir_assume(mod, 'mir_unsafe_assume_spec::f', F2Contract())
        p_ov  = mir_assume(mod, 'mir_unsafe_assume_spec::p', PContract())

        g_result = mir_verify(mod, 'mir_unsafe_assume_spec::g', GContract(), lemmas=[f_ov])
        self.assertIs(g_result.is_success(), True)

        h_result = mir_verify(mod, 'mir_unsafe_assume_spec::h', HContract(), lemmas=[f_ov])
        self.assertIs(h_result.is_success(), True)

        g2_result1 = mir_verify(mod, 'mir_unsafe_assume_spec::g2', G2Contract(), lemmas=[f_ov])
        self.assertIs(g2_result1.is_success(), True)

        g2_result2 = mir_verify(mod, 'mir_unsafe_assume_spec::g2', G2Contract(), lemmas=[f2_ov])
        self.assertIs(g2_result2.is_success(), True)

        g2_result3 = mir_verify(mod, 'mir_unsafe_assume_spec::g2', G2Contract(), lemmas=[f_ov, f2_ov])
        self.assertIs(g2_result3.is_success(), True)

        q_result = mir_verify(mod, 'mir_unsafe_assume_spec::q', QContract(), lemmas=[p_ov])
        self.assertIs(q_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
