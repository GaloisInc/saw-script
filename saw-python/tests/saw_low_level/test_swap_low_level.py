from pathlib import Path
import unittest
import saw_client as saw
from saw_client.proofscript import *


class SwapLowLevelTest(unittest.TestCase):
    def test_swap(self):
        c = saw.connection.connect(reset_server=True)
        if __name__ == "__main__": saw.view(saw.LogResults())

        swap_bc = str(Path('tests','saw','test-files', 'swap.bc'))

        c.llvm_load_module('m', swap_bc).result()

        i32 = {"type": "primitive type", "primitive": "integer", "size": 32}

        # ServerNames
        xp_name = {"name": "xp"}
        yp_name = {"name": "yp"}

        # SetupVals
        xp = {"setup value": "named", "name": "xp"}
        yp = {"setup value": "named", "name": "yp"}
        x = {"setup value": "Cryptol", "expression": "x" }
        y = {"setup value": "Cryptol", "expression": "x" }

        contract = {
            "mutable globals": [],
            "pre vars": [
                {"server name": "x", "name": "x", "type": i32},
                {"server name": "y", "name": "y", "type": i32}
            ],
            "pre conds": [],
            "pre allocated": [
                {"server name": "xp",
                "type": i32,
                "mutable": True,
                "alignment": None},
                {"server name": "yp",
                "type": i32,
                "mutable": True,
                "alignment": None}
            ],
            "pre points tos": [{"pointer": xp, "points to": x},
                            {"pointer": yp, "points to": y}],
            "argument vals": [xp, yp],
            "post vars": [],
            "post conds": [],
            "post allocated": [],
            "post points tos": [{"pointer": xp, "points to": y},
                                {"pointer": yp, "points to": x}],
            "return val": None
        }

        prover = ProofScript([abc]).to_json()
        c.llvm_verify('m', 'swap', [], False, contract, prover, 'ok').result()


if __name__ == "__main__":
    unittest.main()
