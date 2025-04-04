from pathlib import Path
import unittest
from saw_client import *
from saw_client.exceptions import VerificationError
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, LLVMType, PointerType, void, i32, array_ty
from typing import Union


class FPointsToContract(Contract):
    def __init__(self, check_x_type : Union[PointerType, LLVMType, None]) -> None:
        super().__init__()
        self.check_x_type = check_x_type

    def specification(self) -> None:
        x = self.fresh_var(array_ty(2, i32), "x")
        p = self.alloc(array_ty(4, i32))
        self.points_to(p, x, check_target_type = self.check_x_type)

        self.execute_func(p)

        self.points_to(p, cry_f("{x} # {x}"))
        self.returns(void)


class PointsToAtTypeTest(unittest.TestCase):
    def test_points_to_at_type(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'points_to_at_type.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, "f", FPointsToContract(None))
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, "f", FPointsToContract(array_ty(2, i32)))
        self.assertIs(result.is_success(), True)

        # with self.assertRaises(VerificationError):
        #     llvm_verify(mod, "f", FPointsToContract(PointerType()))

        # with self.assertRaises(VerificationError):
        #     llvm_verify(mod, "f", FPointsToContract(ty.array(3, ty.i32)))

if __name__ == "__main__":
    unittest.main()
