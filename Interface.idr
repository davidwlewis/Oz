module Oz.Interface

import Data.Fin
import SLT

import Data.Bits
import UInt
import SInt


splitFin : Fin (m + n) -> Either (Fin m) (Fin n)
splitFin {m =   Z } x  = Right x
splitFin {m = S m'} FZ = Left FZ
splitFin {m = S m'} (FS x) with (splitFin {m = m'} x)
  | (Left y)  = Left (FS y)
  | (Right y) = Right y

namespace Bus
  ||| A vector of Types with join constructor
  data Bus : Nat -> Nat -> Type where
    Nil : Bus 0 0
    (::) : (t : SLType) -> Bus n w -> Bus (S n) (wSL t + w)
    (||) : Bus l lw -> Bus r rw -> Bus (l + r) (lw + rw)

  ||| Extract an element from a Bus
  index : Fin n -> Bus n w -> SLType
  index FZ (x::xs) = x
  index (FS i) (x::xs) = index i xs
  index i (l||r) with (splitFin i)
    | (Left j)  = index j l
    | (Right j) = index j r

namespace Load
  ||| The Bus parameter gives the type of the data.
  data Load : Bus p w -> Type where
    Nil : Load []
    (::) : iSL t -> Load ts -> Load (t::ts)
    (||) : Load ts -> Load bs -> Load (ts || bs)

  ||| Extract an element from a Load
  index : (i : Fin n) -> Load ts -> iSL (index i ts)
  index FZ (x::xs) = x
  index (FS i) (x::xs) = index i xs
  index i (l||r) with (splitFin i)
    | (Left j)  = index j l
    | (Right j) = index j r

instance Show (Load b) where
  show xs = "[" ++ show' "" xs ++ "]" where
    show' : String -> Load _ -> String
    show' acc []        = acc
    show' acc [x]       = Strings.(++) acc (show (toBits x))
    show' acc (x :: xs) = show' (acc ++ (show (toBits x)) ++ ", ") xs
    show' acc (l || r)  = show l ++ " || " ++ show r
