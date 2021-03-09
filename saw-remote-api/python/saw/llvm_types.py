from abc import ABCMeta, abstractmethod
from typing import Any, List

class LLVMType(metaclass=ABCMeta):
    @abstractmethod
    def to_json(self) -> Any: pass

class LLVMIntType(LLVMType):
    def __init__(self, width : int) -> None:
        self.width = width

    def to_json(self) -> Any:
        return {'type': 'primitive type', 'primitive': 'integer', 'size': self.width}

class LLVMArrayType(LLVMType):
    def __init__(self, elemtype : 'LLVMType', size : int) -> None:
        self.size = size
        self.elemtype = elemtype

    def to_json(self) -> Any:
        return { 'type': 'array',
                 'element type': self.elemtype.to_json(),
                 'size': self.size }

class LLVMPointerType(LLVMType):
    def __init__(self, points_to : 'LLVMType') -> None:
        self.points_to = points_to

    def to_json(self) -> Any:
        return {'type': 'pointer', 'points to': self.points_to.to_json()}

class LLVMAliasType(LLVMType):
    def __init__(self, name : str) -> None:
        self.name = name

    def to_json(self) -> Any:
        return {'type': 'type alias',
                'alias of': self.name}

class LLVMStructType(LLVMType):
    def __init__(self, field_types : List[LLVMType]) -> None:
        self.field_types = field_types

    def to_json(self) -> Any:
        return {'type': 'struct',
                'fields': [fld_ty.to_json() for fld_ty in self.field_types]}

class LLVMPackedStructType(LLVMType):
    def __init__(self, field_types : List[LLVMType]) -> None:
        self.field_types = field_types

    def to_json(self) -> Any:
        return {'type': 'packed struct',
                'fields': [fld_ty.to_json() for fld_ty in self.field_types]}

##################################################
# Convenient helpers with intuitive/short names #
##################################################

i8  = LLVMIntType(8)
i16 = LLVMIntType(16)
i32 = LLVMIntType(32)
i64 = LLVMIntType(64)

def array(size : int, ty : 'LLVMType') -> 'LLVMArrayType':
    """``[size x ty]``, i.e. an array of ``size`` elements of type ``ty``."""
    return LLVMArrayType(ty, size)

def ptr(ty : 'LLVMType') -> 'LLVMPointerType':
    """``ty*``, i.e. a pointer to a value of type ``ty``."""
    return LLVMPointerType(ty)

def alias(name : str) -> 'LLVMAliasType':
    """An LLVM type alias (i.e., name)."""
    return LLVMAliasType(name)

def struct_type(*field_types : LLVMType) -> 'LLVMStructType':
    """An LLVM struct type."""
    return LLVMStructType(list(field_types))

def packed_struct_type(*field_types : LLVMType) -> 'LLVMPackedStructType':
    """An LLVM packed struct type."""
    return LLVMPackedStructType(list(field_types))
