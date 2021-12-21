from pathlib import Path
import unittest
import saw_client as saw
from saw_client.proofscript import *

class SevenTest(unittest.TestCase):
    def test_seven(self):
        c = saw.connection.connect(reset_server=True)
        if __name__ == "__main__": saw.view(saw.LogResults())

        seven_bc = str(Path('tests','saw','test-files', 'seven.bc'))

        c.llvm_load_module('m', seven_bc).result()

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
            "return val": {"setup value": "Cryptol", "expression": "7 : [32]"}
        }

        prover = ProofScript([abc]).to_json()
        c.llvm_verify('m', 'seven', [], False, contract, prover, 'ok').result()

if __name__ == "__main__":
    unittest.main()
