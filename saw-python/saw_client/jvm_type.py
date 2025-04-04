from abc import ABCMeta, abstractmethod
from typing import Any, Dict, List, Optional, Set, Union, overload

class JVMType(metaclass=ABCMeta):
    @abstractmethod
    def to_json(self) -> Any: pass

class JVMPrimType(JVMType):
    def __init__(self, prim: str):
        self.prim = prim

    def to_json(self) -> Any:
        return {'type': 'primitive type', 'primitive': self.prim}

class JVMBooleanType(JVMPrimType):
    def __init__(self): super().__init__('boolean')

class JVMByteType(JVMPrimType):
    def __init__(self): super().__init__('byte')

class JVMCharType(JVMPrimType):
    def __init__(self): super().__init__('char')

class JVMDoubleType(JVMPrimType):
    def __init__(self): super().__init__('double')

class JVMFloatType(JVMPrimType):
    def __init__(self): super().__init__('float')

class JVMIntType(JVMPrimType):
    def __init__(self): super().__init__('int')

class JVMLongType(JVMPrimType):
    def __init__(self): super().__init__('long')

class JVMShortType(JVMPrimType):
    def __init__(self): super().__init__('short')

class JVMArrayType(JVMType):
    def __init__(self, elemtype : 'JVMType', size : int) -> None:
        self.size = size
        self.elemtype = elemtype

    def to_json(self) -> Any:
        return { 'type': 'array type',
                 'element type': self.elemtype.to_json(),
                 'size': self.size }

class JVMClassType(JVMType):
    def __init__(self, name: str) -> None:
        self.name = name

    def to_json(self) -> Any:
        return { 'type': 'class type',
                 'class name': self.name }

java_bool = JVMBooleanType()
java_byte = JVMByteType()
java_char = JVMCharType()
java_double = JVMDoubleType()
java_float = JVMFloatType()
java_int = JVMIntType()
java_long = JVMLongType()
java_short = JVMShortType()

def java_array(size : int, element_type: 'JVMType'):
    return JVMArrayType(element_type, size)

def java_class(name: str):
    return JVMClassType(name)
