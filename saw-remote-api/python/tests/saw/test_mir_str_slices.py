import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry_f, str_slice, str_slice_range
from saw_client.mir import Contract, array_ty, u8


hello = cry_f('"hello" : [5][8]')


class F1Contract(Contract):
    def specification(self) -> None:
        a = self.alloc(array_ty(5, u8), points_to=hello, read_only=True)

        self.execute_func(str_slice(a))

        self.returns(cry_f('205 : [8]'))


class F2Contract(Contract):
    def specification(self) -> None:
        a = self.alloc(array_ty(5, u8), points_to=hello, read_only=True)

        self.execute_func(str_slice_range(a, 1, 3))

        self.returns(cry_f('209 : [8]'))


class MIRStrSlicesTest(unittest.TestCase):
    def test_mir_str_slices(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_str_slices.linked-mir.json'))
        mod = mir_load_module(json_name)

        f1_result = mir_verify(mod, 'mir_str_slices::f', F1Contract())
        self.assertIs(f1_result.is_success(), True)

        f2_result = mir_verify(mod, 'mir_str_slices::f', F2Contract())
        self.assertIs(f2_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
