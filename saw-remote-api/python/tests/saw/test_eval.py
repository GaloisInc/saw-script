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

        expr1 = cry('(6 : [8]) * 7')
        self.assertEqual(saw.eval_int(expr1), 42)

        expr2 = cry('(1 < 2) : Bit')
        self.assertTrue(saw.eval_bool(expr2))


if __name__ == "__main__":
    unittest.main()
