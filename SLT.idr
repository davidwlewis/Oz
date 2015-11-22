module Oz.SLT

import Data.Fin
import Data.Vect

import Operation.Classes

import Data.Bits
import BitUtils
import public UInt
import public SInt

%default total

mutual
  data SLType : Type where
    Bit      : SLType
    Vector   : (r : Nat) -> SLType
    Unsigned : (r : Nat) -> SLType
    Signed   : (r : Nat) -> SLType
    Array    : (n : Nat) -> (c : SLType) -> {auto tc : Logic c} -> SLType

  data Logic : SLType -> Type where
    LogicBit      : Logic Bit
    LogicVector   : Logic (Vector r)
    LogicUnsigned : Logic (Unsigned r)
    LogicSigned   : Logic (Signed r)

  iSL : SLType -> Type
  iSL Bit = Bool
  iSL (Vector n) = Bits n
  iSL (Unsigned n) = UInt n
  iSL (Signed n) = SInt n
  iSL (Array n t) = Vect (2 `power` n) (iSL t)

wSL : SLType -> Nat
wSL Bit = 1
wSL (Vector n) = n
wSL (Unsigned n) = n
wSL (Signed n) = n
wSL (Array n t) = (2 `power` n) * (wSL t)

toBits : iSL t -> Bits (wSL t)
toBits {t} v = case t of
  Bit => intToBits (if v then 1 else 0)
  (Vector n) => v
  (Unsigned n) => cast v
  (Signed n) => cast v
  (Array n t) => (intToBits 0) --TODO

fromBits : Bits (wSL t) -> iSL t
fromBits {t} b = case t of
  Bit => getBit FZ b
  (Vector n) => b
  (Unsigned n) => cast b
  (Signed n) => cast b
  (Array n t) => replicate (2 `power` n) (fromBits (intToBits 0)) --TODO
