from cryptol import cryptoltypes
from .utils import deprecated

from .mir_type import *
from .crucible import *

##################################################
# Helpers for type construction
##################################################

bool_ty = MIRBoolType()
"""A MIR boolean type."""

char_ty = MIRCharType()
"""A MIR character type."""

str_ty = MIRStrType()
"""A MIR string type. Currently, SAW can only handle references to strings
(``&str``)."""

i8 = MIRI8Type()
"""A MIR 8-bit signed integer type."""

i16 = MIRI16Type()
"""A MIR 16-bit signed integer type."""

i32 = MIRI32Type()
"""A MIR 32-bit signed integer type."""

i64 = MIRI64Type()
"""A MIR 64-bit signed integer type."""

i128 = MIRI128Type()
"""A MIR 128-bit signed integer type."""

isize = MIRIsizeType()
"""A MIR signed integer type that is pointer-sized."""

f32 = MIRF32Type()
"""A MIR single-precision floating-point type."""

f64 = MIRF64Type()
"""A MIR double-precision floating-point type."""

lifetime = MIRLifetimeType()
"""A MIR lifetime type."""

u8 = MIRU8Type()
"""A MIR 8-bit unsigned integer type."""

u16 = MIRU16Type()
"""A MIR 16-bit unsigned integer type."""

u32 = MIRU32Type()
"""A MIR 32-bit unsigned integer type."""

u64 = MIRU64Type()
"""A MIR 64-bit unsigned integer type."""

u128 = MIRU128Type()
"""A MIR 128-bit unsigned integer type."""

usize = MIRUsizeType()
"""A MIR unsigned integer type that is pointer-sized."""

def adt_ty(adt: MIRAdt) -> 'MIRAdtType':
    """A MIR algebraic data type (ADT), i.e., a struct or an enum."""
    return MIRAdtType(adt)

def array_ty(size : int, ty : 'MIRType') -> 'MIRArrayType':
    """``[ty; size]``, i.e. a MIR array of ``size`` elements of type ``ty``."""
    return MIRArrayType(ty, size)

def ref_ty(ty : 'MIRType') -> 'MIRRefType':
    """``&ty``, i.e., an immutable MIR reference type pointing to something of
    type ``ty``."""
    return MIRRefType(ty)

def ref_mut_ty(ty : 'MIRType') -> 'MIRRefMutType':
    """``&mut ty``, i.e., a mutable MIR reference type pointing to something of
    type ``ty``."""
    return MIRRefMutType(ty)

def slice_ty(ty : MIRType) -> 'MIRSliceType':
    """``[ty]``, i.e., a MIR slice to a type ``ty``. Currently, SAW can only
    handle references to slices (``&[ty]``)"""
    return MIRSliceType(ty)

def tuple_ty(*tuple_types : MIRType) -> 'MIRTupleType':
    """A MIR tuple type with fields of type ``tuple_types``."""
    return MIRTupleType(list(tuple_types))
