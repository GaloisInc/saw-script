from abc import ABCMeta, abstractmethod
from dataclasses import dataclass
from typing import Any

class SAWOption(metaclass=ABCMeta):
    @abstractmethod
    def __str__(self) -> str: pass


@dataclass
class LaxArithmetic(SAWOption):
    def __str__(self) -> str:
        return "lax arithmetic"


@dataclass
class LaxPointerOrdering(SAWOption):
    def __str__(self) -> str:
        return "lax pointer ordering"


@dataclass
class LaxLoadsAndStores(SAWOption):
    def __str__(self) -> str:
        return "lax loads and stores"


@dataclass
class DebugIntrinsics(SAWOption):
    def __str__(self) -> str:
        return "debug intrinsics"


@dataclass
class SMTArrayMemoryModel(SAWOption):
    def __str__(self) -> str:
        return "SMT array memory model"


@dataclass
class What4HashConsing(SAWOption):
    def __str__(self) -> str:
        return "What4 hash consing"


@dataclass
class What4Eval(SAWOption):
    def __str__(self) -> str:
        return "What4 eval"
