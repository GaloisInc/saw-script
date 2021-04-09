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

    def test_provers_low_level(self):

        if __name__ == "__main__": saw.view(saw.LogResults())

        simple_thm = cry('\(x:[8]) -> x != x+1')
        self.assertTrue(saw.prove(simple_thm, ProofScript([UseProver(ABC())])).is_valid())
        self.assertTrue(saw.prove(simple_thm, ProofScript([UseProver(Yices([]))])).is_valid())
        self.assertTrue(saw.prove(simple_thm, ProofScript([UseProver(Z3([]))])).is_valid())

        self.assertTrue(saw.prove(simple_thm, ProofScript([Admit()])).is_valid())
        self.assertTrue(saw.prove(cry('True'), ProofScript([Trivial()])).is_valid())

        simple_non_thm = cry('\(x:[8]) -> x != 5')
        pr = saw.prove(simple_non_thm, ProofScript([UseProver(Z3([]))]))
        self.assertFalse(pr.is_valid())
        cex = pr.get_counterexample()
        self.assertEqual(cex[0]['value']['data'], '5')


if __name__ == "__main__":
    unittest.main()
