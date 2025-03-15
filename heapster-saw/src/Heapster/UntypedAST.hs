module Heapster.UntypedAST where

import GHC.Natural

import Heapster.Located

-- | Unchecked function permission
-- @(context). inputs -o outputs@
data AstFunPerm = AstFunPerm
  Pos
  [(Located String, AstType)] -- ^ The context of ghost variables
  [(Located String, AstExpr)] -- ^ The input permissions
  [(Located String, AstType)] -- ^ The context of ghost output variables
  [(Located String, AstExpr)] -- ^ The output permissions
  deriving Show

-- | Unchecked array permission
-- @[lifetime]array(rw, offset, size, width) |-> permission
data ArrayPerm =
  ArrayPerm Pos (Maybe AstExpr) AstExpr AstExpr (Maybe AstExpr) AstExpr
  -- ^ @array@ position, lifetime, rw, offset, size, width, permission
  deriving Show

-- | Unchecked types
data AstType
  = TyUnit Pos                  -- ^ unit type
  | TyBool Pos                  -- ^ bool type
  | TyNat Pos                   -- ^ nat type
  | TyBV Pos Natural            -- ^ bitvector type
  | TyLlvmPtr Pos Natural       -- ^ llvm pointer with width
  | TyLlvmFrame Pos Natural     -- ^ llvm frame with width
  | TyLlvmBlock Pos Natural     -- ^ llvm block with width
  | TyLlvmShape Pos Natural     -- ^ llvm shape with width
  | TyLifetime Pos              -- ^ lifetime
  | TyRwModality Pos            -- ^ rwmodality
  | TyPermList Pos              -- ^ permlist
  | TyStruct Pos [AstType]      -- ^ struct(types)
  | TyPerm Pos AstType          -- ^ perm(type)
  deriving Show

-- | Unchecked expressions
data AstExpr
  = ExUnit Pos                  -- ^ unit
  | ExAlways Pos                -- ^ always
  | ExNat Pos Natural           -- ^ number literal
  | ExVar Pos String (Maybe [AstExpr]) (Maybe AstExpr) -- ^ identifier, shape arguments, offset
  | ExAdd Pos AstExpr AstExpr   -- ^ addition
  | ExNeg Pos AstExpr           -- ^ negation
  | ExMul Pos AstExpr AstExpr   -- ^ multiplication or permission conjunction
  | ExRead Pos                  -- ^ read modality
  | ExWrite Pos                 -- ^ read/write modality
  | ExStruct Pos [AstExpr]      -- ^ struct literal with field expressions
  | ExLlvmWord Pos AstExpr      -- ^ llvmword with value
  | ExLlvmFrame Pos [(AstExpr, Natural)] -- ^ llvmframe literal
  | ExOr Pos AstExpr AstExpr    -- ^ or permission
  | ExFalse Pos                 -- ^ false permission
  | ExAny Pos                   -- ^ any permission

  | ExEmptySh Pos               -- ^ empty shape
  | ExEqSh Pos AstExpr AstExpr  -- ^ equal shape
  | ExTrue Pos                  -- ^ trivial permission
  | ExExists Pos String AstType AstExpr -- ^ existentially quantified value
  | ExSeqSh Pos AstExpr AstExpr -- ^ sequenced shapes
  | ExOrSh Pos AstExpr AstExpr  -- ^ alternative shapes
  | ExExSh Pos String AstType AstExpr -- ^ existentially quantified shape
  | ExFieldSh Pos (Maybe AstExpr) AstExpr -- ^ field shape
  | ExPtrSh Pos (Maybe AstExpr) (Maybe AstExpr) AstExpr -- ^ pointer shape
  | ExArraySh Pos AstExpr AstExpr AstExpr -- ^ array shape
  | ExTupleSh Pos AstExpr -- ^ field shape
  | ExFalseSh Pos               -- ^ false shape

  | ExEqual Pos AstExpr AstExpr -- ^ equal bitvector proposition
  | ExNotEqual Pos AstExpr AstExpr -- ^ not-equal bitvector proposition
  | ExLessThan Pos AstExpr AstExpr -- ^ less-than bitvector proposition
  | ExLessEqual Pos AstExpr AstExpr -- ^ less-than or equal-to bitvector proposition

  | ExEq Pos AstExpr            -- ^ equal permission
  | ExLOwned Pos [AstExpr] [(Located String, AstExpr)] [(Located String, AstExpr)] -- ^ owned permission
  | ExLCurrent Pos (Maybe AstExpr) -- ^ current permission
  | ExLFinished Pos -- ^ finished permission
  | ExShape Pos AstExpr -- ^ shape literal
  | ExFree Pos AstExpr -- ^ free literal
  | ExPtr Pos (Maybe AstExpr) AstExpr AstExpr (Maybe AstExpr) AstExpr -- ^ pointer permission
  | ExMemblock Pos (Maybe AstExpr) AstExpr AstExpr AstExpr AstExpr -- ^ memblock permission
  | ExLlvmFunPtr Pos AstExpr AstExpr AstFunPerm -- ^ function pointer permission
  | ExArray Pos (Maybe AstExpr) AstExpr AstExpr AstExpr AstExpr AstExpr -- ^ array permission
  deriving Show

-- | Returns outermost position
instance HasPos AstExpr where
  pos (ExUnit       p          ) = p
  pos (ExAlways     p          ) = p
  pos (ExNat        p _        ) = p
  pos (ExVar        p _ _ _    ) = p
  pos (ExAdd        p _ _      ) = p
  pos (ExNeg        p _        ) = p
  pos (ExMul        p _ _      ) = p
  pos (ExRead       p          ) = p
  pos (ExWrite      p          ) = p
  pos (ExStruct     p _        ) = p
  pos (ExLlvmWord   p _        ) = p
  pos (ExEmptySh    p          ) = p
  pos (ExEqSh       p _ _      ) = p
  pos (ExEq         p _        ) = p
  pos (ExOr         p _ _      ) = p
  pos (ExFalse      p          ) = p
  pos (ExTrue       p          ) = p
  pos (ExAny        p          ) = p
  pos (ExExists     p _ _ _    ) = p
  pos (ExSeqSh      p _ _      ) = p
  pos (ExOrSh       p _ _      ) = p
  pos (ExExSh       p _ _ _    ) = p
  pos (ExFieldSh    p _ _      ) = p
  pos (ExTupleSh    p _        ) = p
  pos (ExPtrSh      p _ _ _    ) = p
  pos (ExEqual      p _ _      ) = p
  pos (ExNotEqual   p _ _      ) = p
  pos (ExLessThan   p _ _      ) = p
  pos (ExLessEqual  p _ _      ) = p
  pos (ExLOwned     p _ _ _    ) = p
  pos (ExLCurrent   p _        ) = p
  pos (ExLFinished  p          ) = p
  pos (ExShape      p _        ) = p
  pos (ExFree       p _        ) = p
  pos (ExPtr        p _ _ _ _ _) = p
  pos (ExMemblock   p _ _ _ _ _) = p
  pos (ExLlvmFunPtr p _ _ _    ) = p
  pos (ExLlvmFrame  p _        ) = p
  pos (ExArray      p _ _ _ _ _ _) = p
  pos (ExArraySh    p _ _ _    ) = p
  pos (ExFalseSh    p          ) = p

-- | Returns outermost position
instance HasPos AstType where
  pos (TyUnit       p   ) = p
  pos (TyBool       p   ) = p
  pos (TyNat        p   ) = p
  pos (TyBV         p  _) = p
  pos (TyLlvmPtr    p  _) = p
  pos (TyLlvmFrame  p  _) = p
  pos (TyLlvmBlock  p  _) = p
  pos (TyLlvmShape  p  _) = p
  pos (TyLifetime   p   ) = p
  pos (TyRwModality p   ) = p
  pos (TyPermList   p   ) = p
  pos (TyStruct     p  _) = p
  pos (TyPerm       p  _) = p
