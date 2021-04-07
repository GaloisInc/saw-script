from cryptol import cryptoltypes
import saw
from saw.proofscript import *

import unittest
from pathlib import Path


def cry(exp):
    return cryptoltypes.CryptolLiteral(exp)

class ProverTest(unittest.TestCase):

    @classmethod
    def setUpClass(self):
        saw.connect(reset_server=True)

    @classmethod
    def tearDownClass(self):
        saw.reset_server()
        saw.disconnect()

    def test_provers(self):

        if __name__ == "__main__": saw.view(saw.LogResults())

        simple_thm = cry('\(x:[8]) -> x != x+1')
        self.assertTrue(saw.prove(simple_thm, ProofScript([abc])))
        self.assertTrue(saw.prove(simple_thm, ProofScript([yices([])])))
        self.assertTrue(saw.prove(simple_thm, ProofScript([z3([])])))

        self.assertTrue(saw.prove(simple_thm, ProofScript([Admit()])))
        self.assertTrue(saw.prove(cry('True'), ProofScript([Trivial()])))

        simple_non_thm = cry('\(x:[8]) -> x == x+1')
        self.assertFalse(saw.prove(simple_non_thm, ProofScript([z3([])])))


if __name__ == "__main__":
    unittest.main()
