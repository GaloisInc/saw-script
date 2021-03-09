from pathlib import Path
import unittest
from saw import *
from saw.exceptions import VerificationError
from saw.llvm import Contract, LLVMType, PointerType, cryptol, void
from typing import Union
import saw.llvm_types as ty


class FPointsToContract(Contract):
    def __init__(self, check_x_type : Union[PointerType, LLVMType, None]) -> None:
        super().__init__()
        self.check_x_type = check_x_type

    def specification(self) -> None:
        x = self.fresh_var(ty.array(2, ty.i32), "x")
        p = self.alloc(ty.array(4, ty.i32))
        self.points_to(p, x, check_target_type = self.check_x_type)

        self.execute_func(p)

        self.points_to(p, cryptol("{x} # {x}".format(x=x.name())))
        self.returns(void)


class PointsToAtTypeTest(unittest.TestCase):
    def test_points_to_at_type(self):
        connect()
        if __name__ == "__main__": view(LogResults())
        bcname = str(Path('tests','saw','test-files', 'points_to_at_type.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, "f", FPointsToContract(None))
        self.assertIs(result.is_success(), True)

        result = llvm_verify(mod, "f", FPointsToContract(ty.array(2, ty.i32)))
        self.assertIs(result.is_success(), True)

        with self.assertRaises(VerificationError):
            llvm_verify(mod, "f", FPointsToContract(PointerType()))

        with self.assertRaises(VerificationError):
            llvm_verify(mod, "f", FPointsToContract(ty.array(3, ty.i32)))


if __name__ == "__main__":
    unittest.main()
