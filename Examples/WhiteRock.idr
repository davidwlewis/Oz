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

DecoderI : Bus 4 61
DecoderI = [
  Unsigned 13,   -- PC
  Vector 16,     -- Instruction
  Unsigned 16,   -- T
  Unsigned 16 ]  -- R

DecoderO : Bus 11 72
DecoderO = [
  Unsigned 13,       -- New PC
  Bit, Unsigned 16,  -- New R
  Bit, Unsigned 16,  -- New N
  Unsigned 4,        -- ALU Opcode
  Bit, Unsigned 15,  -- Instruction Literal
  Bit,               -- Flag: N -> [T]
  Signed 2,          -- DSP delta
  Signed 2 ]         -- RSP delta



Literal : Bus 2 16
Literal = [Bit, Unsigned 15]

Inst : Bus 9 16
Inst = [
  Unsigned 3,          -- instruction type
  Bit,                 -- Flag: R -> PC
  Unsigned 4,          -- ALU Opcode
  Bit, Bit, Bit, Bit,  -- Flags
  Signed 2, Signed 2]  -- SP deltas


decoderStage1 : Circuit DecoderI (Literal || Inst)
decoderStage1 = Comb $ unpackSignal (Pin 1) || unpackSignal (Pin 1)

decoderStage2 : Circuit Inst [Bit, Bit, Bit, Bit]
decoderStage2 = Comb [
  Pin 0 == 0,
  Pin 0 == 2,
  Pin 0 == 4,
  Pin 0 == 6
]
