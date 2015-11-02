module Oz.Operation

import SLT
import public Operation.Classes

import Data.Bits
import UInt
import SInt

----------- Unary Operations -----------

namespace Unary
  data LogicUop = Not

  data SArithUop = Abs | Negate

  data Uop : SLType -> SLType -> Type where
    Logic  : ( Logic $ iSL t) =>  LogicUop -> Uop t t
    SArith : (SArith $ iSL t) => SArithUop -> Uop t t

----------- Binary Operations -----------

namespace Binary
  data LogicBop = And | Or | Xor | Nand | Nor | Xnor

  data ArithBop = Plus | Times | Minus | UDiv | URem

  data SArithBop = SDiv | SRem

  data ShiftBop = L | RA | RL

  data OrdBop = EQ | NE | GT | GTE | LT | LTE

  data Bop : SLType -> SLType -> SLType -> Type where
    Logic  : ( Logic $ iSL t) =>  LogicBop -> Bop t t t
    Arith  : ( Arith $ iSL t) =>  ArithBop -> Bop t t t
    SArith : (SArith $ iSL t) => SArithBop -> Bop t t t
    Ord    : (   Ord $ iSL t) =>    OrdBop -> Bop t t Bit
    Shift  : ( Shift (iSL t) (iSL d),  Arith $ iSL d) => ShiftBop -> Bop t d t

----------- Bit Instances -----------

instance Logic Bool where
  not = Prelude.Bool.not
  and x y = x && y
  or   x y =  x || y
  xor  x y = (x || y) && (not (x && y))
  nand x y = not (x && y)
  nor  x y = not (x || y)
  xnor x y = not (x `xor` y)

----------- Vector Instances -----------

instance Logic (Bits k) where
  not  = complement
  and  = Bits.and
  or   = Bits.or
  xor  = Bits.xor
  nand x y = complement (x `and` y)
  nor  x y = complement (x `or`  y)
  xnor x y = complement (x `nor` y)

instance Shift (Bits k) (UInt k) where
  shiftL  v (UI d) = shiftLeft v d
  shiftRL v (UI d) = shiftRightLogical v d
  shiftRA v (UI d) = shiftRightArithmetic v d
