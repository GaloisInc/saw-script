import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry_f, slice_range, slice_value
from saw_client.mir import Contract, array_ty, u32


one_through_five = cry_f('[1, 2, 3, 4, 5] : [5][32]')


class F1Contract(Contract):
    def specification(self) -> None:
        a = self.alloc(array_ty(5, u32), points_to=one_through_five, read_only=True)

        self.execute_func(slice_value(a))

        self.returns(cry_f('3 : [32]'))


class F2Contract(Contract):
    def specification(self) -> None:
        a = self.alloc(array_ty(5, u32), points_to=one_through_five, read_only=True)

        self.execute_func(slice_range(a, 1, 3))

        self.returns(cry_f('5 : [32]'))


class MIRSlicesTest(unittest.TestCase):
    def test_mir_slices(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_slices.linked-mir.json'))
        mod = mir_load_module(json_name)

        f1_result = mir_verify(mod, 'mir_slices::f', F1Contract())
        self.assertIs(f1_result.is_success(), True)

        f2_result = mir_verify(mod, 'mir_slices::f', F2Contract())
        self.assertIs(f2_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
