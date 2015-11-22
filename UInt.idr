module Oz.UInt

import Data.Fin

import Data.Bits
import Operation.Classes

%default total
%access public

||| UInt integers
data UInt : Nat -> Type where
  UI : Bits n -> UInt n

mkUInt : Integer -> UInt n
mkUInt x = UI (intToBits x)

uBin : (Bits n -> Bits n -> Bits n) -> UInt n -> UInt n -> UInt n
uBin f (UI x) (UI y) = UI (f x y)

uComp : (Bits n -> Bits n -> a) -> UInt n -> UInt n -> a
uComp f (UI x) (UI y) = f x y

instance Eq (UInt n) where
  (==) = uComp (==)

instance Ord (UInt n) where
  (<) = uComp (<)
  (<=) = uComp (<=)
  (>=) = uComp (>=)
  (>) = uComp (>)
  compare = uComp compare

instance Logic (UInt k) where
  not (UI v) = UI (complement v)
  and  = uBin and
  or   = uBin or
  xor  = uBin xor
  nand (UI l) (UI r) = UI (complement (l `and` r))
  nor  (UI l) (UI r) = UI (complement (l `or`  r))
  xnor (UI l) (UI r) = UI (complement (l `xor` r))

instance Shift (UInt k) (UInt k) where
  shiftL  (UI v) (UI d) = UI (shiftLeft v d)
  shiftRL (UI v) (UI d) = UI (shiftRightLogical v d)
  shiftRA (UI v) (UI d) = UI (shiftRightArithmetic v d)

instance Num (UInt n) where
  (+) = uBin plus
  (*) = uBin times
  fromInteger = mkUInt

instance Arith (UInt n) where
  (-) = uBin minus
  udiv = uBin udiv
  urem = uBin urem

instance Cast (UInt n) (Bits n) where
  cast (UI x) = x

instance Cast (Bits n) (UInt n) where
  cast x = UI x

toFin : {n : Nat} -> UInt n -> Fin (power 2 n)
toFin {n=Z} _ = FZ
toFin {n=S k} (UI v) =
  let f = toFin (UI $ truncate v {m=1})
  in (rewrite plusZeroRightNeutral (power 2 k) in
    if getBit last v
    then shift   (power 2 k) f
    else weakenN (power 2 k) f)

instance Show (UInt n) where
  show (UI v) = show (bitsToInt v)
