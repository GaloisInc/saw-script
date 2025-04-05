from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.mir import Contract, i32


class FContract1(Contract):
    def specification(self):
        x = self.fresh_var(i32, 'x')
        self.proclaim(cry_f('{x} < 0x7fffffff'))

        self.execute_func(x)

        r = self.fresh_var(i32, 'r')
        self.proclaim(cry_f('{r} == {x} + 1'))
        self.proclaim(cry_f('{r} <= 0x7fffffff'))
        self.returns(r)


# Like FContract1, but using `proclaim_f` instead of `proclaim`.
class FContract2(Contract):
    def specification(self):
        x = self.fresh_var(i32, 'x')
        self.proclaim_f('{x} < 0x7fffffff')

        self.execute_func(x)

        r = self.fresh_var(i32, 'r')
        self.proclaim_f('{r} == {x} + 1')
        self.proclaim_f('{r} <= 0x7fffffff')
        self.returns(r)


class ProclaimTest(unittest.TestCase):
    def test_proclaim(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'mir_proclaim.linked-mir.json'))
        mod = mir_load_module(bcname)

        result1 = mir_verify(mod, 'mir_proclaim::f', FContract1())
        self.assertIs(result1.is_success(), True)

        result2 = mir_verify(mod, 'mir_proclaim::f', FContract2())
        self.assertIs(result2.is_success(), True)


if __name__ == "__main__":
    unittest.main()
