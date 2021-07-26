import unittest
from pathlib import Path

import saw_client as saw

from saw_client.jvm import Contract, java_int, cryptol

class Add(Contract):
    def __init__(self) -> None:
        super().__init__()

    def specification(self) -> None:
        x = self.fresh_var(java_int, "x")
        y = self.fresh_var(java_int, "y")

        self.execute_func(x, y)

        self.returns(cryptol("(+)")(x,y))

class AddTest(unittest.TestCase):
    def test_add(self):
        saw.connect(reset_server=True)

        if __name__ == "__main__": saw.view(saw.LogResults())

        cls = saw.jvm_load_class("Add")

        result = saw.jvm_verify(cls, 'add', Add())
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
