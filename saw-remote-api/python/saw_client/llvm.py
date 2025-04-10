from abc import ABCMeta, abstractmethod
from cryptol import cryptoltypes
from .utils import deprecated
from dataclasses import dataclass
import dataclasses
import re
from typing import Any, Dict, List, Optional, Set, Union, overload
from typing_extensions import Literal
import inspect
import uuid


from .llvm_type import *
from .crucible import *

##################################################
# Helpers for type construction
##################################################

i8  = LLVMIntType(8)
i16 = LLVMIntType(16)
i32 = LLVMIntType(32)
i64 = LLVMIntType(64)

def array_ty(size : int, ty : 'LLVMType') -> 'LLVMArrayType':
    """``[size x ty]``, i.e. an array of ``size`` elements of type ``ty``."""
    return LLVMArrayType(ty, size)

def ptr_ty(ty : 'LLVMType') -> 'LLVMPointerType':
    """``ty*``, i.e. a pointer to a value of type ``ty``."""
    return LLVMPointerType(ty)

def alias_ty(name : str) -> 'LLVMAliasType':
    """An LLVM type alias (i.e., ``name``)."""
    return LLVMAliasType(name)

def struct_ty(*field_types : LLVMType) -> 'LLVMStructType':
    """An LLVM struct type with fields of type ``field_types``."""
    return LLVMStructType(list(field_types))

def packed_struct_ty(*field_types : LLVMType) -> 'LLVMPackedStructType':
    """An LLVM packed struct type with fields of type ``field_types``."""
    return LLVMPackedStructType(list(field_types))
