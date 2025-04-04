from pathlib import Path
import unittest
import saw_client as saw
from saw_client.proofscript import *


class TrivialTest(unittest.TestCase):
    def test_trivial(self):
        c = saw.connection.connect(reset_server=True)
        if __name__ == "__main__": saw.view(saw.LogResults())

        cry_file = str(Path('tests','saw','test-files', 'Foo.cry'))
        c.cryptol_load_file(cry_file)


        null_bc = str(Path('tests','saw','test-files', 'null.bc'))

        c.llvm_load_module('m', null_bc).result()

        contract = {
            "mutable globals": [],
            "pre vars": [],
            "pre conds": [],
            "pre allocated": [],
            "pre points tos": [],
            "argument vals": [],
            "post vars": [],
            "post conds": [],
            "post allocated": [],
            "post points tos": [],
            "return val": {"setup value": "null"}
        }

        prover = ProofScript([abc]).to_json()
        c.llvm_verify('m', 'always_null', [], False, contract, prover, 'ok').result()


if __name__ == "__main__":
    unittest.main()
