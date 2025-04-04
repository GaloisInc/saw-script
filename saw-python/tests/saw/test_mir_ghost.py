import unittest
from pathlib import Path

from saw_client import *
from saw_client.crucible import cry_f
from saw_client.mir import Contract, GhostVariable, u32


class NextContract(Contract):
    def __init__(self, counter: GhostVariable) -> None:
        super().__init__()
        self.counter = counter

    def specification(self) -> None:
        n = self.fresh_var(u32, 'n')
        self.ghost_value(self.counter, n)

        self.execute_func()

        self.ghost_value(self.counter, cry_f('{n} + 1'))
        self.returns(n)


class ExampleContract(Contract):
    def __init__(self, counter: GhostVariable) -> None:
        super().__init__()
        self.counter = counter

    def specification(self) -> None:
        n = self.fresh_var(u32, 'n')
        self.precondition_f('{n} < 2')
        self.ghost_value(self.counter, n)

        self.execute_func()
        self.ghost_value(self.counter, cry_f('{n} + 3'))
        self.returns_f('{n} + 2')


class MIRGhostTest(unittest.TestCase):
    def test_mir_ghost(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        json_name = str(Path('tests', 'saw', 'test-files', 'mir_ghost.linked-mir.json'))
        mod = mir_load_module(json_name)

        counter = create_ghost_variable('ctr');
        next_ov = mir_assume(mod, 'mir_ghost::next', NextContract(counter))
        example_result = mir_verify(mod, 'mir_ghost::example', ExampleContract(counter), lemmas=[next_ov])
        self.assertIs(example_result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
