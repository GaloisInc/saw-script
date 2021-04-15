import saw
from saw.llvm import Contract, CryptolTerm, cryptol, void, i32, GhostVariable

import unittest
from pathlib import Path

def pre_counter(contract: Contract, counter: GhostVariable):
    n = contract.fresh_var(i32, "n")
    contract.precondition(n < cryptol("128"))
    contract.ghost_value(counter, n)
    return n

def post_counter(contract: Contract, counter: GhostVariable, n: CryptolTerm):
    contract.ghost_value(counter, cryptol("(+)")(n, cryptol("1")))

class GetAndIncrementContract(Contract):
    def __init__(self, counter: str) -> None:
        super().__init__()
        self.counter = counter

    def specification(self) -> None:
        n = pre_counter(self, self.counter)
        self.execute_func()
        post_counter(self, self.counter, n)
        self.returns(n)

class FContract(Contract):
    def __init__(self, counter: str) -> None:
        super().__init__()
        self.counter = counter

    def specification(self) -> None:
        n = pre_counter(self, self.counter)
        i = self.fresh_var(i32, "i")
        self.precondition(i < cryptol("512"))
        self.execute_func(i)
        post_counter(self, self.counter, n)
        self.returns(cryptol("(*)")(i, n))

class GhostTest(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        saw.connect(reset_server=True)

    @classmethod
    def tearDownClass(self):
        saw.reset_server()
        saw.disconnect()

    def test_ghost(self):

        if __name__ == "__main__": saw.view(saw.LogResults())
        ghost_bc = str(Path('tests','saw','test-files', 'ghost.bc'))

        mod = saw.llvm_load_module(ghost_bc)

        counter = saw.create_ghost_variable('counter');
        get_and_increment_ov = saw.llvm_assume(mod, 'get_and_increment', GetAndIncrementContract(counter))
        self.assertIs(get_and_increment_ov.is_success(), True)
        f_ov = saw.llvm_verify(mod, 'f', FContract(counter), lemmas=[get_and_increment_ov])
        self.assertIs(f_ov.is_success(), True)

if __name__ == "__main__":
    unittest.main()
