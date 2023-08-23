import unittest
from pathlib import Path

import saw_client as saw

from saw_client.crucible import cry, cry_f
from saw_client.mir import Contract, u32

class Basic(Contract):
    def __init__(self) -> None:
        super().__init__()

    def specification(self) -> None:
        x = self.fresh_var(u32, "x")

        self.execute_func(x)

        self.returns_f("{x}")

class BasicTest(unittest.TestCase):
    def test_basic(self):
        saw.connect(reset_server=True)
        if __name__ == "__main__": saw.view(saw.LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'basic_mir.linked-mir.json'))
        mod = saw.mir_load_module(json_name)

        basic_result = saw.mir_verify(mod, 'basic_mir::basic', Basic())
        self.assertIs(basic_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
