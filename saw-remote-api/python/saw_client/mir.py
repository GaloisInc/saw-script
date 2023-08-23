from cryptol import cryptoltypes
from .utils import deprecated

from .mir_type import *
from .crucible import *

##################################################
# Helpers for type construction
##################################################

bool_ty = MIRBoolType()
char_ty = MIRCharType()
str_ty  = MIRStrType()

i8    = MIRI8Type()
i16   = MIRI16Type()
i32   = MIRI32Type()
i64   = MIRI64Type()
i128  = MIRI128Type()
isize = MIRIsizeType()

f32 = MIRF32Type()
f64 = MIRF64Type()

u8    = MIRU8Type()
u16   = MIRU16Type()
u32   = MIRU32Type()
u64   = MIRU64Type()
u128  = MIRU128Type()
usize = MIRUsizeType()

def array_ty(size : int, ty : 'MIRType') -> 'MIRArrayType':
    """``[ty; size]``, i.e. a MIR array of ``size`` elements of type ``ty``."""
    return MIRArrayType(ty, size)

def slice_ty(ty : MIRType) -> 'MIRSliceType':
    """``[ty]``, i.e., a MIR slice to a type ``ty``."""
    return MIRSliceType(ty)

def tuple_ty(*tuple_types : MIRType) -> 'MIRTupleType':
    """A MIR tuple type with fields of type ``tuple_types``."""
    return MIRTupleType(list(tuple_types))
