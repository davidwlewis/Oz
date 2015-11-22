module Oz.Signal

import Data.Fin

import SLT
import Interface
import Operation

import Data.Bits
import UInt
import SInt

mutual
  ||| A Signal is a typed wire that can be fully determined from some context
  data Signal : Bus p w -> SLType -> Type where
    Literal : iSL t -> Signal i t
    Pin : {v : Bus i iw} -> (x : Fin i) -> Signal v (index x v)

    ||| Operations
    UnOp : Uop a b -> Signal i a -> Signal i b
    BinOp : Bop a b c -> Signal i a -> Signal i b -> Signal i c

    ||| Multiplexing - List (Predicate, Choice) -> Default -> Result
    Mux : List ((Signal i Bit, Signal i t)) -> Signal i t -> Signal i t

    ||| Conversions - TODO: Coerce should sign-extend for signed->signed
    Cast   : (Logic $ iSL a, Logic $ iSL b) => Signal i a -> {auto ok : (wSL a) = (wSL b)} -> Signal i b
    SExtend : Signal i (Signed n) -> Signal i (Signed (n + m))
    Coerce : (Logic $ iSL a, Logic $ iSL b) => Signal i a -> Signal i b

    ||| Bitwise Combinators
    Concat : Signal i a -> Signal i b -> Signal i (Vector (wSL a + wSL b))
    Slice : (Logic $ iSL a) => Signal i a -> (offset : Integer) -> Signal i b

    ||| Arrays - Read (address, mem) Write ([enable, address, data], mem)
    Read  : {auto tc : Logic t} -> Signal i (Unsigned n) -> Signal i (Array n t) -> Signal i t
    Write : {auto tc : Logic t} -> Pipeline i [Bit, Unsigned n, t] -> Signal i (Array n t) -> Signal i (Array n t)

  data Pipeline : Bus i iw -> Bus o ow -> Type where
    Nil : Pipeline i []
    (::) : Signal i t -> Pipeline i o -> Pipeline i (t :: o)
    (||) : Pipeline i l -> Pipeline i r -> Pipeline i (l || r)

data Circuit : Bus i iw -> Bus o ow -> Type where
  Id : Circuit x x
  Comb : Pipeline i o -> Circuit i o

  Ser : Circuit a b -> Circuit b c -> Circuit a c
  Par : Circuit a b -> Circuit c d -> Circuit (a || c) (b || d)

  Fork   : Circuit a b -> Circuit a c -> Circuit a (b || c)
  First  : Circuit a b -> Circuit (a || c) (b || c)
  Second : Circuit a b -> Circuit (c || a) (c || b)

  Pack : {b : Bus o ow} -> Circuit a b -> Circuit a [Vector ow]
  Unpack : {a : Bus i iw} -> Circuit a b -> Circuit [Vector iw] b

  Feedback : Circuit (a || b) c -> Load b -> Pipeline c b -> Circuit a c

infixl 2 &>
infixl 3 ||>

(&>) : Circuit a b -> Circuit b c -> Circuit a c; (&>) = Ser
(||>) : Circuit a b -> Circuit c d -> Circuit (a || c) (b || d); (||>) = Par

(==) : (Ord $ iSL a, Eq $ iSL a) => Signal i a -> Signal i a -> Signal i Bit
(==) = BinOp (Ord EQ)

(/=) : (Ord $ iSL a, Eq $ iSL a) => Signal i a -> Signal i a -> Signal i Bit
(/=) = BinOp (Ord NE)


(>) : (Ord $ iSL a) => Signal i a -> Signal i a -> Signal i Bit
(>)  = BinOp (Ord GT)

(>=) : (Ord $ iSL a) => Signal i a -> Signal i a -> Signal i Bit
(>=) = BinOp (Ord GTE)

(<) : (Ord $ iSL a) => Signal i a -> Signal i a -> Signal i Bit
(<)  = BinOp (Ord LT)

(<=) : (Ord $ iSL a) => Signal i a -> Signal i a -> Signal i Bit
(<=) = BinOp (Ord LTE)

total
unpackSignal : (Logic $ iSL t) => Signal i t -> {b : Bus o (wSL t)} -> Pipeline i b
unpackSignal s {b} = slices s b 0 where
  slices : (Logic $ iSL $ t) => Signal i t -> (b : Bus o ow) -> Integer -> Pipeline i b
  slices s [] _ = []
  slices s (x :: xs) offs =
    let offs' = offs + (cast $ wSL x)
    in (Slice s offs) :: (slices s xs offs')
  slices s ((||) l r {lw}) offs =
    let offs' = offs + (cast lw)
    in slices s l offs || slices s r offs'

instance (Logic $ iSL a) => Logic (Signal i a) where
  not  = UnOp (Logic Not)
  and  = BinOp (Logic And)
  or   = BinOp (Logic Or)
  xor  = BinOp (Logic Xor)
  nand = BinOp (Logic Nand)
  nor  = BinOp (Logic Nor)
  xnor = BinOp (Logic Xnor)

instance (Num $ iSL a, Arith $ iSL a) => Num (Signal i a) where
  (+) = BinOp (Arith Plus)
  (*) = BinOp (Arith Times)
  fromInteger = Literal . fromInteger

instance (Arith $ iSL a) => Arith (Signal i a) where
  (-) = BinOp (Arith Minus)
  udiv = BinOp (Arith UDiv)
  urem = BinOp (Arith URem)

instance (SArith $ iSL a) => SArith (Signal i a) where
  abs = UnOp (SArith Abs)
  negate = UnOp (SArith Negate)
  sdiv = BinOp (SArith SDiv)
  srem = BinOp (SArith SRem)

instance (Shift (iSL a) (iSL b), Arith $ iSL b) => Shift (Signal i a) (Signal i b) where
  shiftL  = BinOp (Shift L)
  shiftRL = BinOp (Shift RL)
  shiftRA = BinOp (Shift RA)
