from abc import ABCMeta, abstractmethod
from dataclasses import dataclass
from typing import Any

class SAWOption(metaclass=ABCMeta):
    @abstractmethod
    def __str__(self) -> str: pass

# typing wrapper
@dataclass
class BoolSAWOption(SAWOption):
    @abstractmethod
    def __str__(self) -> str: pass

# typing wrapper
@dataclass
class IntSAWOption(SAWOption):
    @abstractmethod
    def __str__(self) -> str: pass

@dataclass
class LaxArithmetic(BoolSAWOption):
    def __str__(self) -> str:
        return "lax arithmetic"


@dataclass
class LaxPointerOrdering(BoolSAWOption):
    def __str__(self) -> str:
        return "lax pointer ordering"


@dataclass
class LaxLoadsAndStores(BoolSAWOption):
    def __str__(self) -> str:
        return "lax loads and stores"


@dataclass
class DebugIntrinsics(BoolSAWOption):
    def __str__(self) -> str:
        return "debug intrinsics"


@dataclass
class SMTArrayMemoryModel(BoolSAWOption):
    def __str__(self) -> str:
        return "SMT array memory model"


@dataclass
class What4HashConsing(BoolSAWOption):
    def __str__(self) -> str:
        return "What4 hash consing"


@dataclass
class What4Eval(BoolSAWOption):
    def __str__(self) -> str:
        return "What4 eval"


@dataclass
class CryptolTypecheckerTimeout(IntSAWOption):
    def __str__(self) -> str:
        return "Cryptol typechecker timeout"
