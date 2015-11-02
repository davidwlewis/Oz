module Oz.WhiteRock

import Data.Fin
import Data.Vect

import SLT
import BitUtils
import Operation
import Interface
import Signal
import Simulation
import Simulation.Utils

import Data.Bits
import UInt
import SInt

decoderI : Bus 4 61
decoderI = [
  Unsigned 13,   -- PC
  Vector 16,     -- Instruction
  Unsigned 16,   -- T
  Unsigned 16 ]  -- R

decoderO : Bus 11 72
decoderO = [
  Unsigned 13,       -- New PC
  Bit, Unsigned 16,  -- New R
  Bit, Unsigned 16,  -- New N
  Unsigned 4,        -- ALU Opcode
  Bit, Unsigned 15,  -- Instruction Literal
  Bit,               -- Flag: N -> [T]
  Signed 2,          -- DSP delta
  Signed 2 ]         -- RSP delta



literal : Bus 2 16
literal = [Bit, Unsigned 15]

inst : Bus 9 16
inst = [
  Unsigned 3,          -- instruction type
  Bit,                 -- Flag: R -> PC
  Unsigned 4,          -- ALU Opcode
  Bit, Bit, Bit, Bit,  -- Flags
  Signed 2, Signed 2]  -- SP deltas


--- Not working. Inlining all the buses makes it work though.

decoderStage1 : Circuit decoderI (literal || inst)
decoderStage1 = Comb $ toBundle (Pin 1) || toBundle (Pin 1)

decoderStage2 : Circuit inst [Bit, Bit, Bit, Bit]
decoderStage2 = Comb [
  Pin 0 == 0,
  Pin 0 == 2,
  Pin 0 == 4,
  Pin 0 == 6
]
