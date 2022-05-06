from cryptol import cryptoltypes
import saw_client as saw

import unittest
from pathlib import Path


def cry(exp):
    return cryptoltypes.CryptolLiteral(exp)

class ProverTest(unittest.TestCase):

    def test_provers(self):
        saw.connect(reset_server=True)

        if __name__ == "__main__": saw.view(saw.LogResults())

        expr = cry('(6 : [8]) * 7')
        self.assertEqual(saw.eval_int(expr), 42)


if __name__ == "__main__":
    unittest.main()
