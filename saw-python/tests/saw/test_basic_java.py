import unittest
from pathlib import Path

import saw_client as saw

from saw_client.crucible import cry, cry_f
from saw_client.jvm import Contract, java_int

class Add(Contract):
    def __init__(self) -> None:
        super().__init__()

    def specification(self) -> None:
        x = self.fresh_var(java_int, "x")
        y = self.fresh_var(java_int, "y")

        self.execute_func(x, y)

        self.returns_f("{x} + {y}")

class Double(Contract):
    def __init__(self) -> None:
        super().__init__()

    def specification(self) -> None:
        x = self.fresh_var(java_int, "x")

        self.execute_func(x)

        self.returns_f("{x} + {x}")

class AddTest(unittest.TestCase):
    def test_add(self):
        saw.connect(reset_server=True)

        if __name__ == "__main__": saw.view(saw.LogResults())

        cls = saw.jvm_load_class("Add")

        add_result1 = saw.jvm_verify(cls, 'add', Add())
        self.assertIs(add_result1.is_success(), True)
        add_result2 = saw.jvm_assume(cls, 'add', Add())
        self.assertIs(add_result2.is_success(), True)

        dbl_result1 = saw.jvm_verify(cls, 'dbl', Double(), lemmas=[add_result1])
        self.assertIs(dbl_result1.is_success(), True)
        dbl_result2 = saw.jvm_verify(cls, 'dbl', Double(), lemmas=[add_result2])
        self.assertIs(dbl_result2.is_success(), True)


if __name__ == "__main__":
    unittest.main()
