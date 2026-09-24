import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import struct
from saw_client.mir import Contract, MIRType, u8, u16


class FContract(Contract):
    ty: MIRType

    def __init__(self, ty: MIRType):
        super().__init__()
        self.ty = ty

    def specification(self) -> None:
        x = self.fresh_var(self.ty, "x")
        self.execute_func(x)
        self.returns(x)


class MIRFindNameTest(unittest.TestCase):
    def test_mir_find_name(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_find_name.linked-mir.json'))
        mod = mir_load_module(json_name)

        f_u8 = mir_find_name(mod, "mir_find_name::f", u8)
        f_u8_result = mir_verify(mod, f_u8, FContract(u8))
        self.assertIs(f_u8_result.is_success(), True)

        f_u16 = mir_find_name(mod, "mir_find_name::f", u16)
        f_u16_result = mir_verify(mod, f_u16, FContract(u16))
        self.assertIs(f_u16_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
