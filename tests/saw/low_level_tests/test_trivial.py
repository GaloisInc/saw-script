import os
import os.path
import unittest
import saw
from saw.proofscript import *


class TrivialTest(unittest.TestCase):
    def test_trivial(self):
        dir_path = os.path.dirname(os.path.realpath(__file__))

        c = saw.connection.connect(saw.find_saw_server() + " socket")
        if __name__ == "__main__": saw.view(saw.LogResults())

        cry_file = os.path.join(dir_path, '../Foo.cry')
        c.cryptol_load_file(cry_file)


        null_bc = os.path.join(dir_path, '../null.bc')

        c.llvm_load_module('m', null_bc).result()

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
            "return val": {"setup value": "null"}
        }

        prover = ProofScript([abc]).to_json()
        c.llvm_verify('m', 'always_null', [], False, contract, prover, 'ok').result()
        c.disconnect()

if __name__ == "__main__":
    unittest.main()
