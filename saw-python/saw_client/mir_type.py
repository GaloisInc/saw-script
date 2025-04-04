from abc import ABCMeta, abstractmethod
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Set, Union, overload

class MIRType(metaclass=ABCMeta):
    @abstractmethod
    def to_json(self) -> Any: pass

@dataclass
class MIRAdt:
    orig_name: str
    server_name: str

class MIRAdtType(MIRType):
    def __init__(self, adt : 'MIRAdt') -> None:
        self.adt = adt

    def to_json(self) -> Any:
        return { 'type': 'adt',
                 'ADT server name': self.adt.server_name }

class MIRArrayType(MIRType):
    def __init__(self, element_type : 'MIRType', size : int) -> None:
        self.size = size
        self.element_type = element_type

    def to_json(self) -> Any:
        return { 'type': 'array',
                 'element type': self.element_type.to_json(),
                 'size': self.size }

class MIRBoolType(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'bool' }

class MIRCharType(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'char' }

class MIRI8Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'i8' }

class MIRI16Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'i16' }

class MIRI32Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'i32' }

class MIRI64Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'i64' }

class MIRI128Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'i128' }

class MIRF32Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'f32' }

class MIRF64Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'f64' }

class MIRIsizeType(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'isize' }

class MIRLifetimeType(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'lifetime' }

class MIRRefType(MIRType):
    def __init__(self, referent_type : 'MIRType') -> None:
        self.referent_type = referent_type

    def to_json(self) -> Any:
        return { 'type': 'ref',
                 'referent type': self.referent_type.to_json() }

class MIRRefMutType(MIRType):
    def __init__(self, referent_type : 'MIRType') -> None:
        self.referent_type = referent_type

    def to_json(self) -> Any:
        return { 'type': 'ref mut',
                 'referent type': self.referent_type.to_json() }

class MIRSliceType(MIRType):
    def __init__(self, slice_type : 'MIRType') -> None:
        self.slice_type = slice_type

    def to_json(self) -> Any:
        return { 'type': 'slice',
                 'slice type': self.slice_type.to_json() }

class MIRStrType(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'str' }

class MIRTupleType(MIRType):
    def __init__(self, tuple_types : List['MIRType']) -> None:
        self.tuple_types = tuple_types

    def to_json(self) -> Any:
        return { 'type': 'tuple',
                 'tuple types': [ty.to_json() for ty in self.tuple_types] }

class MIRU8Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'u8' }

class MIRU16Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'u16' }

class MIRU32Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'u32' }

class MIRU64Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'u64' }

class MIRU128Type(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'u128' }

class MIRUsizeType(MIRType):
    def to_json(self) -> Any:
        return { 'type': 'usize' }
