module Oz.SInt

import Data.Bits
import Data.Fin

import UInt
import Operation.Classes

%default total
%access public

||| Signed integers
data SInt : Nat -> Type where
  SI : Bits n -> SInt n

mkSInt : Integer -> SInt n
mkSInt x = SI (intToBits x)

sBin : (Bits n -> Bits n -> Bits n) -> SInt n -> SInt n -> SInt n
sBin f (SI x) (SI y) = SI (f x y)

sComp : (Bits n -> Bits n -> a) -> SInt n -> SInt n -> a
sComp f (SI x) (SI y) = f x y

extend : SInt n -> SInt (n + m)
extend (SI v) {m} =
  let ze = (zeroExtend v)
      m' = intToBits (cast m)
      sl = shiftLeft ze m'
      sr = shiftRightArithmetic sl m'
  in SI sr

instance Eq (SInt n) where
  (==) = sComp (==)

instance Ord (SInt n) where
  (<) = sComp (<)
  (<=) = sComp (<=)
  (>=) = sComp (>=)
  (>) = sComp (>)
  compare = sComp compare

instance Logic (SInt k) where
  not (SI v) = SI (complement v)
  and  = sBin and
  or   = sBin or
  xor  = sBin xor
  nand (SI l) (SI r) = SI (complement (l `and` r))
  nor  (SI l) (SI r) = SI (complement (l `or`  r))
  xnor (SI l) (SI r) = SI (complement (l `xor` r))

instance Shift (SInt k) (UInt k) where
  shiftL  (SI v) (UI d) = SI (shiftLeft v d)
  shiftRL (SI v) (UI d) = SI (shiftRightLogical v d)
  shiftRA (SI v) (UI d) = SI (shiftRightArithmetic v d)

instance Num (SInt n) where
  (+) = sBin plus
  (*) = sBin times
  fromInteger = mkSInt

instance Arith (SInt n) where
  (-) = sBin minus
  udiv = sBin udiv
  urem = sBin urem

instance SArith (SInt k) where
  negate s = mkSInt 0 - s
  abs s@(SI v) = case k of
    Z  => s
    S n => if getBit last v then negate s else s
  sdiv = sBin sdiv
  srem = sBin srem

instance Cast (SInt n) (Bits n) where
  cast (SI x) = x

instance Cast (Bits n) (SInt n) where
  cast x = SI x

instance Show (SInt n) where
  show s@(SI v) = case n of
    Z   => show $ bitsToInt v
    S n => if getBit last v
           then let (SI v') = negate s in ("-" ++ (show $ bitsToInt v'))
           else show $ bitsToInt v
