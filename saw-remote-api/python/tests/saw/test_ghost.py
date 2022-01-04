import saw_client as saw
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, CryptolTerm, void, i32, GhostVariable

import unittest
from pathlib import Path

def pre_counter(contract: Contract, counter: GhostVariable):
    n = contract.fresh_var(i32, "n")
    contract.precondition_f("{n} < 128")
    contract.ghost_value(counter, n)
    return n

def post_counter(contract: Contract, counter: GhostVariable, n: CryptolTerm):
    contract.ghost_value(counter, cry_f("{n} + 1"))

class GetAndIncrementContract(Contract):
    def __init__(self, counter: GhostVariable) -> None:
        super().__init__()
        self.counter = counter

    def specification(self) -> None:
        n = pre_counter(self, self.counter)
        self.execute_func()
        post_counter(self, self.counter, n)
        self.returns(n)

class FContract(Contract):
    def __init__(self, counter: GhostVariable) -> None:
        super().__init__()
        self.counter = counter

    def specification(self) -> None:
        n = pre_counter(self, self.counter)
        i = self.fresh_var(i32, "i")
        self.precondition_f("{i} < 512")
        self.execute_func(i)
        post_counter(self, self.counter, n)
        self.returns_f("{i} * {n}")

class GhostTest(unittest.TestCase):

    def test_ghost(self):

        saw.connect(reset_server=True)
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
