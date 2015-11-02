module Operation.Classes

-- Each Idris type represented by an SLType implements one or more of these.
-- All operations are consistent with VHDL
class Logic a where
  not  : a -> a
  and  : a -> a -> a
  or   : a -> a -> a
  xor  : a -> a -> a
  nand : a -> a -> a
  nor  : a -> a -> a
  xnor : a -> a -> a

class Num a => Arith a where
  (-) : a -> a -> a
  udiv  : a -> a -> a
  urem  : a -> a -> a

class SArith a where
  abs    : a -> a
  negate : a -> a
  sdiv   : a -> a -> a
  srem   : a -> a -> a

class Shift a b where
  shiftL  : a -> b -> a
  shiftRL : a -> b -> a
  shiftRA : a -> b -> a
