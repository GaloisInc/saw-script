from io import StringIO
import os
from pathlib import Path
import shlex
from shutil import which
import unittest
from unittest.mock import patch

from argo_client.interaction import ArgoException
import saw_client as saw
from saw_client import connection, exceptions
from saw_client.llvm import Contract, i32


class RotatelContract(Contract):
    def specification(self):
        x = self.fresh_var(i32, "x")
        a = self.fresh_var(i32, "a")
        self.execute_func(x, a)
        self.returns_f("{x} <<< {a}")


class LogResultsTest(unittest.TestCase):
    def test_verbose_failure_without_stdout(self):
        server = os.environ.get("SAW_SERVER") or which("saw-remote-api")
        if server is None:
            self.skipTest("A local SAW server is needed for read-only mode")
        output = StringIO()
        logger = saw.LogResults(file=output, verbose_failure=True)
        conn = connection.connect(shlex.quote(server) + " --read-only socket")
        try:
            with patch.object(saw, "__designated_connection", conn), \
                 patch.object(saw, "__designated_views", []), \
                 patch.object(saw, "__global_success", True):
                saw.view(logger)
                bitcode = Path(__file__).parent / "test-files" / "rotatel.bc"
                module = saw.llvm_load_module(str(bitcode))
                result = saw.llvm_verify(module, "rotatel", RotatelContract())
                self.assertFalse(result.is_success())
                self.assertIsNone(result.exception.stdout)
                self.assertEqual(logger.failures, [result])
                self.assertIn("Proof failed", output.getvalue())
                self.assertNotIn("\tstdout:", output.getvalue())
        finally:
            conn.disconnect()

    def test_verbose_failure_with_stdout(self):
        for stdout in ["", "first line\nsecond line"]:
            with self.subTest(stdout=stdout):
                error = exceptions.VerificationError(
                    ArgoException(10300, "Proof failed", {}, stdout, ""))
                result = saw.VerificationFailed("rotatel", [], RotatelContract(), error)
                logger = saw.LogResults(verbose_failure=True)
                message = logger.format_failure(result)
                expected = "\n\tstdout:\n" + "\n".join(
                    "\t\t" + line for line in stdout.split("\n"))
                self.assertIn(expected, message)


if __name__ == "__main__":
    unittest.main()
