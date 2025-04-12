from pathlib import Path
import unittest
from saw_client import *
from saw_client.crucible import cry, cry_f
from saw_client.llvm import Contract, FreshVar, SetupVal, struct, LLVMType, array_ty, i8, i64
from typing import Tuple


def ptr_to_fresh(c : Contract, ty : LLVMType, name : Optional[str] = None) -> Tuple[FreshVar, SetupVal]:
    """Add to``Contract`` ``c`` an allocation of a pointer of type ``ty`` initialized to an unknown fresh value.

    :returns A fresh variable bound to the pointers initial value and the newly allocated pointer. (The fresh
             variable will be assigned ``name`` if provided/available.)"""
    var = c.fresh_var(ty, name)
    ptr = c.alloc(ty, points_to = var)
    return (var, ptr)


def int_to_64_cryptol(length: int):
    return cry_f("`{length}:[64]")


def buffer_type(length: int) -> LLVMType:
    return array_ty(8 + length, i8)


def alloc_buffer_aligned(spec: Contract, length: int) -> SetupVal:
    return spec.alloc(buffer_type(length), alignment = 16)


def alloc_buffer_aligned_readonly(spec: Contract, length: int) -> SetupVal:
    return spec.alloc(buffer_type(length), alignment = 16, read_only = True)


def alloc_pointsto_buffer(spec: Contract, length: int, data: SetupVal) -> SetupVal:
    buf = alloc_buffer_aligned(spec, length)
    spec.points_to(buf, struct(int_to_64_cryptol(length)), check_target_type = None)
    return buf


def alloc_pointsto_buffer_readonly(spec: Contract, length: int, data: SetupVal) -> SetupVal:
    buf = alloc_buffer_aligned_readonly(spec, length)
    spec.points_to(buf, struct(int_to_64_cryptol(length)), check_target_type = None)
    return buf


class BufferCopySpec(Contract):
    length: int

    def __init__(self, length: int):
        super().__init__()
        self.length = length

    def specification(self) -> None:
        data = self.fresh_var(array_ty(self.length, i8), "data")
        buf  = alloc_pointsto_buffer_readonly(self, self.length, data)

        self.execute_func(buf)

        new_buf = alloc_pointsto_buffer(self, self.length, data)
        self.returns(new_buf)


class LLVMNestedStructTest(unittest.TestCase):
    def test_llvm_struct(self):
        connect(reset_server=True)
        if __name__ == "__main__": view(LogResults())

        bcname = str(Path('tests','saw','test-files', 'alloc_aligned.bc'))
        mod = llvm_load_module(bcname)

        result = llvm_verify(mod, 'buffer_copy', BufferCopySpec(63))
        self.assertIs(result.is_success(), True)


if __name__ == "__main__":
    unittest.main()
