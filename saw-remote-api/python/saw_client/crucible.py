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
from .jvm_type import *

class SetupVal(metaclass=ABCMeta):
    """Represent a ``SetupValue`` in SawScript, which "corresponds to
    values that can occur during symbolic execution, which includes both 'Term'
    values, pointers, and composite types consisting of either of these
    (both structures and arrays)."
    """
    @abstractmethod
    def to_json(self) -> Any:
        """JSON representation for this ``SetupVal`` (i.e., how it is represented in expressions, etc).

        N.B., should be a JSON object with a ``'setup value'`` field with a unique tag which the
        server will dispatch on to then interpret the rest of the JSON object.``"""
        pass

    @overload
    def __getitem__(self, key : int) -> 'ElemVal':
        pass
    @overload
    def __getitem__(self, key : str) -> 'FieldVal':
        pass
    def __getitem__(self, key : Union[int,str]) -> 'SetupVal':
        """``SetupVal`` element indexing and field access.
        :param key: If ``key`` is an integer, a ``SetupVal`` corresponding to accessing the element
                    at that index is returned. If ``key`` is a string, a ``SetupVal`` corresponding
                    to accessing a field with that name is returned.
        """
        if isinstance(key, int):
            return elem(self, key)
        elif isinstance(key, str):
            return field(self, key)
        else:
            raise ValueError(f'{key!r} is not a valid element index or field name.')


class NamedSetupVal(SetupVal):
    """Represents those ``SetupVal``s which are a named reference to some value, e.e., a variable
    or reference to allocated memory."""
    @abstractmethod
    def to_init_json(self) -> Any:
        """JSON representation with the information for those ``SetupVal``s which require additional
        information to initialize/allocate them vs that which is required later to reference them.

        I.e., ``.to_json()`` will be used to refer to such ``SetupVal``s in expressions, and
        ``.to_init_json() is used to initialize/allocate them.``
        """
        pass

class CryptolTerm(SetupVal):
    expression : cryptoltypes.CryptolJSON

    def __init__(self, code : Union[str, cryptoltypes.CryptolJSON]):
        if isinstance(code, str):
            self.expression = cryptoltypes.CryptolLiteral(code)
        else:
            self.expression = code

    def __call__(self, *args : cryptoltypes.CryptolJSON) -> 'CryptolTerm':
        out_term = self.expression
        for a in args:
            out_term = cryptoltypes.CryptolApplication(out_term, a)

        return CryptolTerm(out_term)

    def __repr__(self) -> str:
        return f"CryptolTerm({self.expression!r})"

    def to_json(self) -> Any:
        return {'setup value': 'Cryptol', 'expression': cryptoltypes.to_cryptol(self.expression)}

    def __to_cryptol__(self, ty : Any) -> Any:
        return self.expression.__to_cryptol__(ty)

class FreshVar(NamedSetupVal):
    __name : Optional[str]

    def __init__(self, spec : 'Contract', type : Union['LLVMType', 'JVMType'], suggested_name : Optional[str] = None) -> None:
        self.__name = suggested_name
        self.spec = spec
        self.type = type

    def __to_cryptol__(self, ty : Any) -> Any:
        return cryptoltypes.CryptolLiteral(self.name()).__to_cryptol__(ty)

    def to_init_json(self) -> Any:
        #FIXME it seems we don't actually use two names ever... just the one...do we actually need both?
        name = self.name()
        return {"server name": name,
                "name": name,
                "type": self.type.to_json()}

    def name(self) -> str:
        if self.__name is None:
            self.__name = self.spec.get_fresh_name()
        return self.__name

    def to_json(self) -> Any:
        return {'setup value': 'named', 'name': self.name()}

    def __gt__(self, other : cryptoltypes.CryptolJSON) -> CryptolTerm:
        gt = CryptolTerm("(>)")
        return gt(self, other)

    def __lt__(self, other : cryptoltypes.CryptolJSON) -> CryptolTerm:
        lt = CryptolTerm("(<)")
        return lt(self, other)


class Allocated(NamedSetupVal):
    name : Optional[str]

    def __init__(self, spec : 'Contract', type : Union['LLVMType','JVMType'], *,
                 mutable : bool = True, alignment : Optional[int] = None) -> None:
        self.name = None
        self.spec = spec
        self.type = type
        self.mutable = mutable
        self.alignment = alignment

    def to_init_json(self) -> Any:
        if self.name is None:
            self.name = self.spec.get_fresh_name()
        return {"server name": self.name,
                "type": self.type.to_json(),
                "mutable": self.mutable,
                "alignment": self.alignment}

    def to_json(self) -> Any:
        if self.name is None:
            self.name = self.spec.get_fresh_name()
        return {'setup value': 'named', 'name': self.name}

class StructVal(SetupVal):
    fields : List[SetupVal]

    def __init__(self, fields : List[SetupVal]) -> None:
        self.fields = fields

    def to_json(self) -> Any:
        return {'setup value': 'tuple', 'elements': [fld.to_json() for fld in self.fields]}

class ElemVal(SetupVal):
    base : SetupVal
    index : int

    def __init__(self, base : SetupVal, index : int) -> None:
        self.base = base
        self.index = index

    def to_json(self) -> Any:
        return {'setup value': 'element lvalue',
                'base': self.base.to_json(), 'index': self.index}

class FieldVal(SetupVal):
    base : SetupVal
    field_name : str

    def __init__(self, base : SetupVal, field_name : str) -> None:
        self.base = base
        self.field_name = field_name

    def to_json(self) -> Any:
        return {'setup value': 'field',
                'base': self.base.to_json(), 'field': self.field_name}

class GlobalInitializerVal(SetupVal):
    name : str

    def __init__(self, name : str) -> None:
        self.name = name

    def to_json(self) -> Any:
        return {'setup value': 'global initializer', 'name': self.name}

class GlobalVarVal(SetupVal):
    name : str

    def __init__(self, name : str) -> None:
        self.name = name

    def to_json(self) -> Any:
        return {'setup value': 'global lvalue', 'name': self.name}

class NullVal(SetupVal):
    def to_json(self) -> Any:
        return {'setup value': 'null'}

class ArrayVal(SetupVal):
    elements : List[SetupVal]

    def __init__(self, elements : List[SetupVal]) -> None:
        self.elements = elements

    def to_json(self) -> Any:
        return {'setup value': 'array',
                'elements': [element.to_json() for element in self.elements]}

name_regexp = re.compile('^(?P<prefix>.*[^0-9])?(?P<number>[0-9]+)?$')

def next_name(x : str) -> str:
    match = name_regexp.match(x)
    if match is None:
        return 'x'
    prefix, number = match.group('prefix', 'number')

    if prefix is None:
        prefix = 'x'
    if number is None:
        next_number = 0
    else:
        next_number = int(number) + 1
    return f'{prefix}{next_number}'


def uniquify(x : str, used : Set[str]) -> str:
    while x in used:
        x = next_name(x)
    return x


class PointerType:
    """A trivial class indicating that PointsTo should check ``target``'s type
    against the type that ``pointer``'s type points to.
    """
    pass


class Condition:
    def __init__(self, condition : CryptolTerm) -> None:
        self.cryptol_term = condition

    def to_json(self) -> Any:
        return cryptoltypes.to_cryptol(self.cryptol_term)


class PointsTo:
    """The workhorse for ``points_to``.
    """
    def __init__(self, pointer : SetupVal, target : SetupVal, *,
                 check_target_type : Union[PointerType, 'LLVMType', 'JVMType', None] = PointerType(),
                 condition : Optional[Condition] = None) -> None:
        self.pointer = pointer
        self.target = target
        self.check_target_type = check_target_type
        self.condition = condition

    def to_json(self) -> Any:
        check_target_type_json: Optional[Dict[str, Any]]
        if self.check_target_type is None:
            check_target_type_json = None
        elif isinstance(self.check_target_type, PointerType):
            check_target_type_json = { "check against": "pointer type" }
        elif isinstance(self.check_target_type, LLVMType):
            check_target_type_json = { "check against": "casted type"
                                     , "type": self.check_target_type.to_json() }
        return {"pointer": self.pointer.to_json(),
                "points to": self.target.to_json(),
                "check points to type": check_target_type_json,
                "condition": self.condition.to_json() if self.condition is not None else self.condition}

@dataclass
class GhostVariable:
    name: str
    server_name: str

class GhostValue:
    """A class containing the statement that a given ghost variable should have the
    value given by a Cryptol expression.
    """
    def __init__(self, name: str, value: CryptolTerm) -> None:
        self.name = name
        self.value = value

    def to_json(self) -> Any:
        return {"server name": self.name,
                "value": cryptoltypes.to_cryptol(self.value)}

@dataclass
class State:
    contract : 'Contract'
    fresh : List[FreshVar] = dataclasses.field(default_factory=list)
    conditions : List[Condition] = dataclasses.field(default_factory=list)
    allocated : List[Allocated] = dataclasses.field(default_factory=list)
    points_to : List[PointsTo] = dataclasses.field(default_factory=list)
    ghost_values : List[GhostValue] = dataclasses.field(default_factory=list)

    def to_json(self) -> Any:
        return {'variables': [v.to_init_json() for v in self.fresh],
                'conditions': [c.to_json() for c in self.conditions],
                'allocated': [a.to_init_json() for a in self.allocated],
                'points to': [p.to_json() for p in self.points_to],
                'ghost values': [g.to_json() for g in self.ghost_values]
               }

ContractState = \
  Union[Literal['pre'],
        Literal['post'],
        Literal['done']]

@dataclass
class Void:
    def to_json(self) -> Any:
        return None

void = Void()

@dataclass
class VerifyResult:
    contract : 'Contract'
    lemma_name : str

# Lemma names are generated deterministically with respect to a
# particular Python execution trace. This means that re-running the
# same script will be fast when using caching, but REPL-style usage
# will be slow, invalidating the cache at each step. We should be
# smarter about this.
used_lemma_names = set([]) # type: Set[str]

class Contract:
    __used_names : Set[str]

    __state : ContractState = 'pre'

    __mutable_globals : List[str]
    __pre_state : State
    __post_state : State

    __returns : Optional[Union[SetupVal, Void]]

    __arguments : Optional[List[SetupVal]]

    __definition_lineno : Optional[int]
    __definition_filename : Optional[str]
    __unique_id : uuid.UUID
    __cached_json : Optional[Any]

    def __init__(self) -> None:
        self.__mutable_globals = []
        self.__pre_state = State(self)
        self.__post_state = State(self)
        self.__used_names = set()
        self.__arguments = None
        self.__returns = None
        self.__unique_id = uuid.uuid4()
        self.__cached_json = None
        frame = inspect.currentframe()
        if frame is not None and frame.f_back is not None:
            self.__definition_lineno = frame.f_back.f_lineno
            self.__definition_filename = frame.f_back.f_code.co_filename
        else:
            self.__definition_lineno = None
            self.__definition_filename = None

    # To be overridden by users
    def specification(self) -> None:
        pass

    def execute_func(self, *args : SetupVal) -> None:
        """Denotes the end of the precondition specification portion of this ``Contract``, records that
        the function is executed with arguments ``args``, and denotes the beginning of the postcondition
        portion of this ``Contract``."""
        if self.__arguments is not None:
            raise ValueError("The function has already been called once during the specification.")
        elif self.__state != 'pre':
            raise ValueError("Contract state expected to be 'pre', but found {self.__state!r} (has `execute_func` already been called for this contract?).")
        else:
            self.__arguments = [arg for arg in args]
        self.__state = 'post'

    def get_fresh_name(self, hint : str = 'x') -> str:
        new_name = uniquify(hint, self.__used_names)
        self.__used_names.add(new_name)
        return new_name

    def fresh_var(self, type : Union['LLVMType','JVMType'], suggested_name : Optional[str] = None) -> FreshVar:
        """Declares a fresh variable of type ``type`` (with name ``suggested_name`` if provided and available)."""
        fresh_name = self.get_fresh_name('x' if suggested_name is None else self.get_fresh_name(suggested_name))
        v = FreshVar(self, type, fresh_name)
        if self.__state == 'pre':
            self.__pre_state.fresh.append(v)
        elif self.__state == 'post':
            self.__post_state.fresh.append(v)
        else:
            raise Exception("wrong state")
        return v

    def alloc(self, type : Union['LLVMType', 'JVMType'], *, read_only : bool = False,
                                        alignment : Optional[int] = None,
                                        points_to : Optional[SetupVal] = None) -> SetupVal:
        """Allocates a pointer of type ``type``.

        If ``read_only == True`` then the allocated memory is immutable.

        If ``alignment != None``, then the start of the allocated region of
        memory will be aligned to a multiple of the specified number of bytes
        (which must be a power of 2).

        If ``points_to != None``, it will also be asserted that the allocated memory contains the
        value specified by ``points_to``.

        :returns A pointer of the proper type to the allocated region."""
        a = Allocated(self, type, mutable = not read_only, alignment = alignment)
        if self.__state == 'pre':
            self.__pre_state.allocated.append(a)
        elif self.__state == 'post':
            self.__post_state.allocated.append(a)
        else:
            raise Exception("wrong state")

        if points_to is not None:
            self.points_to(a, points_to)

        return a

    def alloc_global(self, name: str) -> None:
        """Declare that memory for the named mutable global should be allocated.
        This is done implicitly for immutable globals. A pointer to the
        allocated memory may be obtained using `global_var`."""
        self.__mutable_globals.append(name)

    def points_to(self, pointer : SetupVal, target : SetupVal, *,
                  check_target_type : Union[PointerType, 'LLVMType', 'JVMType', None] = PointerType(),
                  condition : Optional[Condition] = None) -> None:
        """Declare that the memory location indicated by the ``pointer``
        contains the ``target``.

        If ``check_target_type == PointerType()``, then this will check that
        ``target``'s type matches the type that ``pointer``'s type points to.
        If ``check_target_type`` is an ``LLVMType``, then this will check that
        ``target``'s type matches that type.
        If ``check_target_type == None`, then this will not check ``target``'s
        type at all.

        If ``condition != None`, then this will only declare that ``pointer``
        points to ``target`` is the ``condition`` holds.
        """
        pt = PointsTo(pointer, target, check_target_type = check_target_type, condition = condition)
        if self.__state == 'pre':
            self.__pre_state.points_to.append(pt)
        elif self.__state == 'post':
            self.__post_state.points_to.append(pt)
        else:
            raise Exception("wrong state")

    def ghost_value(self, var: GhostVariable, value: CryptolTerm) -> None:
        """Declare that the given ghost variable should have a value specified by the given Cryptol expression.

        Usable either before or after `execute_func`.
        """
        gv = GhostValue(var.name, value)
        if self.__state == 'pre':
            self.__pre_state.ghost_values.append(gv)
        elif self.__state == 'post':
            self.__post_state.ghost_values.append(gv)
        else:
            raise Exception("wrong state")

    @deprecated
    def proclaim(self, proposition : Union[str, CryptolTerm, cryptoltypes.CryptolJSON]) -> None:
        """DEPRECATED: Use ``precondition`` or ``postcondition`` instead. This method will
        eventually be removed."""
        if not isinstance(proposition, CryptolTerm):
            condition = Condition(CryptolTerm(proposition))
        else:
            condition = Condition(proposition)
        if self.__state == 'pre':
            self.__pre_state.conditions.append(condition)
        elif self.__state == 'post':
            self.__post_state.conditions.append(condition)
        else:
            raise Exception("wrong state")

    def precondition(self, proposition : Union[str, CryptolTerm, cryptoltypes.CryptolJSON]) -> None:
        """Establishes ``proposition`` as a precondition for the function ```Contract```
        being specified.

        Preconditions must be specified before ``execute_func`` is called in the contract specification."""
        if not isinstance(proposition, CryptolTerm):
            condition = Condition(CryptolTerm(proposition))
        else:
            condition = Condition(proposition)
        if self.__state == 'pre':
            self.__pre_state.conditions.append(condition)
        else:
            raise Exception("preconditions must be specified before execute_func is called in the contract")

    def postcondition(self, proposition : Union[str, CryptolTerm, cryptoltypes.CryptolJSON]) -> None:
        """Establishes ``proposition`` as a postcondition for the function ```Contract```
        being specified.

        Postconditions must be specified after ``execute_func`` is called in the contract specification."""
        if not isinstance(proposition, CryptolTerm):
            condition = Condition(CryptolTerm(proposition))
        else:
            condition = Condition(proposition)
        if self.__state == 'post':
            self.__post_state.conditions.append(condition)
        else:
            raise Exception("postconditions must be specified after execute_func is called in the contract")

    def returns(self, val : Union[Void,SetupVal]) -> None:
        if self.__state == 'post':
            if self.__returns is None:
                self.__returns = val
            else:
                raise ValueError("Return value already specified")
        else:
            raise ValueError("Not in postcondition")

    def lemma_name(self, hint  : Optional[str] = None) -> str:
        if hint is None:
            hint = self.__class__.__name__

        name = uniquify('lemma_' + hint, used_lemma_names)

        used_lemma_names.add(name)

        return name

    def definition_lineno(self) -> Optional[int]:
        return self.__definition_lineno

    def definition_filename(self) -> Optional[str]:
        return self.__definition_filename

    def to_json(self) -> Any:
        if self.__cached_json is not None:
            return self.__cached_json
        else:
            if self.__state != 'pre':
                raise Exception(f'Internal error: wrong contract state -- expected \'pre\', but got: {self.__state!r}')

            self.specification()

            if self.__state != 'post':
                raise Exception(f'Internal error: wrong contract state -- expected \'post\', but got: {self.__state!r}')

            self.__state = 'done'

            if self.__returns is None:
                raise Exception("forgot return")

            self.__cached_json = \
                {'mutable globals': self.__mutable_globals,
                 'pre vars': [v.to_init_json() for v in self.__pre_state.fresh],
                 'pre conds': [c.to_json() for c in self.__pre_state.conditions],
                 'pre allocated': [a.to_init_json() for a in self.__pre_state.allocated],
                 'pre ghost values': [g.to_json() for g in self.__pre_state.ghost_values],
                 'pre points tos': [pt.to_json() for pt in self.__pre_state.points_to],
                 'argument vals': [a.to_json() for a in self.__arguments] if self.__arguments is not None else [],
                 'post vars': [v.to_init_json() for v in self.__post_state.fresh],
                 'post conds': [c.to_json() for c in self.__post_state.conditions],
                 'post allocated': [a.to_init_json() for a in self.__post_state.allocated],
                 'post ghost values': [g.to_json() for g in self.__post_state.ghost_values],
                 'post points tos': [pt.to_json() for pt in self.__post_state.points_to],
                 'return val': self.__returns.to_json()}

            return self.__cached_json

##################################################
# Helpers for value construction
##################################################

# It's tempting to name this `global` to mirror SAWScript's `llvm_global`,
# but that would clash with the Python keyword `global`.
def global_var(name: str) -> SetupVal:
    """Returns a pointer to the named global ``name`` (i.e., a ``GlobalVarVal``)."""
    return GlobalVarVal(name)

# FIXME Is `Any` too permissive here -- can we be a little more precise?
def cryptol(data : Any) -> 'CryptolTerm':
    """Constructs a Cryptol value from ``data`` (i.e., a ``CryptolTerm``, which is also a ``SetupVal``).

    ``data`` should be a string literal representing Cryptol syntax or the result of a Cryptol-realted server computation."""
    return CryptolTerm(data)

def array(*elements: SetupVal) -> SetupVal:
    """Returns an array with the provided ``elements`` (i.e., an ``ArrayVal``).

    N.B., one or more ``elements`` must be provided.""" # FIXME why? document this here when we figure it out.
    if len(elements) == 0:
        raise ValueError('An array must be constructed with one or more elements')
    for e in elements:
        if not isinstance(e, SetupVal):
            raise ValueError('array expected a SetupVal, but got {e!r}')
    return ArrayVal(list(elements))

def elem(base: SetupVal, index: int) -> SetupVal:
    """Returns the value of the array element at position ``index`` in ``base`` (i.e., an ``ElemVal``).

    Can also be created by using an ``int`` indexing key on a ``SetupVal``: ``base[index]``."""
    if not isinstance(base, SetupVal):
        raise ValueError('elem expected a SetupVal, but got {base!r}')
    if not isinstance(index, int):
        raise ValueError('elem expected an int, but got {index!r}')
    return ElemVal(base, index)

def field(base : SetupVal, field_name : str) -> SetupVal:
    """Returns the value of struct ``base``'s field ``field_name`` (i.e., a ``FieldVal``).

    Can also be created by using a ``str`` indexing key on a ``SetupVal``: ``base[field_name]``."""
    if not isinstance(base, SetupVal):
        raise ValueError('field expected a SetupVal, but got {base!r}')
    if not isinstance(field_name, str):
        raise ValueError('field expected a str, but got {field_name!r}')
    return FieldVal(base, field_name)

def global_initializer(name: str) -> SetupVal:
    """Returns the initializer value of a named global ``name`` (i.e., a ``GlobalInitializerVal``)."""
    if not isinstance(name, str):
        raise ValueError('global_initializer expected a str naming a global value, but got {name!r}')
    return GlobalInitializerVal(name)

def null() -> SetupVal:
    """Returns a null pointer value (i.e., a ``NullVal``)."""
    return NullVal()

def struct(*fields : SetupVal) -> SetupVal:
    """Returns an LLVM structure value with the given ``fields`` (i.e., a ``StructVal``)."""
    for field in fields:
        if not isinstance(field, SetupVal):
            raise ValueError('struct expected a SetupVal, but got {field!r}')
    return StructVal(list(fields))
