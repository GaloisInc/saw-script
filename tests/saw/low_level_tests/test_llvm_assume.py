import os
import os.path
import saw
from saw.proofscript import *
import unittest


class LLVMAssumeTest(unittest.TestCase):

    def test_llvm_assume(self):
        c = saw.connection.connect(saw.find_saw_server() + " socket")
        if __name__ == "__main__": saw.view(saw.LogResults())

        dir_path = os.path.dirname(os.path.realpath(__file__))
        assume_bc = os.path.join(dir_path, '../assume.bc')

        c.llvm_load_module('m', assume_bc).result()

        seven_contract = {
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

        addone_contract = {
            "pre vars": [],
            "pre conds": [],
            "pre allocated": [],
            "pre points tos": [],
            "argument vals": [],
            "post vars": [],
            "post conds": [],
            "post allocated": [],
            "post points tos": [],
            "return val": {"setup value": "Cryptol", "expression": "8 : [32]"}
        }

        prover = ProofScript([abc]).to_json()
        c.llvm_assume('m', 'seven', seven_contract, 'seven_ov').result()
        c.llvm_verify('m', 'addone', ['seven_ov'], False, addone_contract, prover, 'addone_ov').result()
        c.disconnect()

if __name__ == "__main__":
    unittest.main()
