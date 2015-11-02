module Oz.BitUtils

import Data.Fin
import Data.Bits


-- TODO : optional signed extend
coerce : Bits n -> Bits t
coerce s {n} {t} with (cmp n t)
  coerce s {n=t + (S j)} {t=t} | CmpGT j = truncate {m=(S j)} $
    rewrite (plusCommutative   j t) in
    rewrite (plusSuccRightSucc t j) in
    s
  coerce s {n=n} {t=n}         | CmpEQ = s
  coerce s {n=n} {t=n + (S j)} | CmpLT j = zeroExtend {m=(S j)} s

concat : Bits n -> Bits m -> Bits (n + m)
concat a b {n} {m} = sl `or` r where
  sl = rewrite plusCommutative n m in shiftLeft (zeroExtend b) (intToBits (cast n))
  r = zeroExtend a

split : Bits (n + m) -> (Bits n, Bits m)
split b {n} {m} =
  let n' = intToBits (cast n)
      sr = shiftRightLogical b n'
      bn : Bits (m + n) = rewrite (plusCommutative m n) in b
  in (truncate bn, truncate sr)

slice : Bits m -> Integer -> Bits n
slice b offs = coerce (shiftRightLogical b (intToBits offs))
