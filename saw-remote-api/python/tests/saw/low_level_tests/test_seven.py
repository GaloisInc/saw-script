import os
import os.path
import unittest
import saw
from saw.proofscript import *

class SevenTest(unittest.TestCase):
    def test_seven(self):
        dir_path = os.path.dirname(os.path.realpath(__file__))

        c = saw.connection.connect(saw.find_saw_server() + " socket")
        if __name__ == "__main__": saw.view(saw.LogResults())

        seven_bc = os.path.join(dir_path, '../seven.bc')

        c.llvm_load_module('m', seven_bc).result()

        contract = {
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
        c.disconnect()

if __name__ == "__main__":
    unittest.main()
