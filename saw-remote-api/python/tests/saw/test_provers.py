from cryptol import cryptoltypes
import saw
from saw.proofscript import *

import unittest
from pathlib import Path


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

        self.assertTrue(saw.prove(cryptoltypes.CryptolLiteral('True'), ProofScript([abc])))
        self.assertTrue(saw.prove(cryptoltypes.CryptolLiteral('True'), ProofScript([yices([])])))
        self.assertTrue(saw.prove(cryptoltypes.CryptolLiteral('True'), ProofScript([z3([])])))

        self.assertTrue(saw.prove(cryptoltypes.CryptolLiteral('True'), ProofScript([Admit()])))

        self.assertFalse(saw.prove(cryptoltypes.CryptolLiteral('False'), ProofScript([z3([])])))


if __name__ == "__main__":
    unittest.main()
