module Oz.Simulation.Utils

import SLT
import Interface
import Operation

import Data.Bits
import public BitUtils
import UInt
import SInt


unOp : Uop a b -> iSL a -> iSL b
unOp (Logic Not) = not
unOp (SArith Abs) = abs
unOp (SArith Negate) = negate

%assert_total -- can't div or rem over 0
binOp : Bop a b c -> iSL a -> iSL b -> iSL c
binOp (Logic And)  = and
binOp (Logic Or)   = or
binOp (Logic Xor)  = xor
binOp (Logic Nand) = nand
binOp (Logic Nor)  = nor
binOp (Logic Xnor) = xnor

binOp (Arith Plus)  = (+)
binOp (Arith Times) = (*)
binOp (Arith Minus) = (-)
binOp (Arith UDiv)  = udiv
binOp (Arith URem)  = urem

binOp (SArith SDiv) = sdiv
binOp (SArith SRem) = srem

binOp (Shift L)  = shiftL
binOp (Shift RL) = shiftRL
binOp (Shift RA) = shiftRA

binOp (Ord EQ)  = (==)
binOp (Ord NE)  = (/=)
binOp (Ord GT)  = (>)
binOp (Ord GTE) = (>=)
binOp (Ord LT)  = (<)
binOp (Ord LTE) = (<=)


pack : {ts : Bus n w} -> (Load ts) -> Bits w
pack [] = intToBits 0
pack (x::xs) = concat (toBits x) (pack xs)
pack (l||r) = concat (pack l) (pack r)

unpack : {ts : Bus n w} -> Bits w -> Load ts
unpack b {ts} with (ts)
  | [] = []
  | (x::xs) = let (m, n) = split b  in (fromBits m) :: unpack n
  | (l||r) = let (m, n) = split b in unpack m || unpack n
