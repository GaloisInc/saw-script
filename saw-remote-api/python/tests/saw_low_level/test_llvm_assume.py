from pathlib import Path
import saw_client as saw
from saw_client.proofscript import *
import unittest
import sys


class LLVMAssumeTest(unittest.TestCase):
    def test_llvm_assume(self):
        c = saw.connection.connect(reset_server=True)
        if __name__ == "__main__": saw.view(saw.LogResults())

        assume_bc = str(Path('tests','saw','test-files', 'assume.bc'))

        c.llvm_load_module('m', assume_bc).result()

        seven_contract = {
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

        addone_contract = {
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
            "return val": {"setup value": "Cryptol", "expression": "8 : [32]"}
        }

        prover = ProofScript([abc]).to_json()
        c.llvm_assume('m', 'seven', seven_contract, 'seven_ov').result()
        c.llvm_verify('m', 'addone', ['seven_ov'], False, addone_contract, prover, 'addone_ov').result()


if __name__ == "__main__":
    unittest.main()
