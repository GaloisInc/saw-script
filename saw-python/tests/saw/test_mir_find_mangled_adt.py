import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import struct
from saw_client.mir import Contract, MIRAdt, adt_ty, array_ty, u8


class HContract(Contract):
    adt: MIRAdt
    n: int

    def __init__(self, adt: MIRAdt, n: int):
        super().__init__()
        self.adt = adt
        self.n = n

    def specification(self) -> None:
        a_arr = self.fresh_var(array_ty(self.n, u8), "a_arr")
        a = struct(a_arr, mir_adt = self.adt)

        self.execute_func(a)

        self.returns(a_arr)


class MIRFindMangledAdtTest(unittest.TestCase):
    def test_mir_find_mangled_adt(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_find_mangled_adt.linked-mir.json'))
        mod = mir_load_module(json_name)

        # SAW doesn't have a way to look up instantiations of ADTs that use
        # const generics, so as a workaround, we look up the mangled
        # identifiers instead.
        words4_adt = mir_find_mangled_adt(mod, "mir_find_mangled_adt::Words::_adta4a904df508e9aad")
        words7_adt = mir_find_mangled_adt(mod, "mir_find_mangled_adt::Words::_adt96fbb9234cd1add7")

        h4_result = mir_verify(mod, 'mir_find_mangled_adt::h4', HContract(words4_adt, 4))
        self.assertIs(h4_result.is_success(), True)

        h7_result = mir_verify(mod, 'mir_find_mangled_adt::h7', HContract(words7_adt, 7))
        self.assertIs(h7_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
