module Oz.Examples.Stack

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

SP : SLType; SP = Unsigned 5
WORD : SLType; WORD = Unsigned 8


||| The composed stack element
||| In : wEn, input, dsp
||| Out : output, sp'
stack : Circuit [Bit, WORD, Signed 2] [WORD, SP]
stack = Feedback (sp &> (First wr) &> rd) [31] [Pin 1] where
  ||| Update the stack pointer
  sp : Circuit ([Bit, WORD, Signed 2] || [SP]) ([Bit, WORD, SP] || [SP])
  sp = Comb $ [Pin 0, Pin 1, (Pin 3) + (Cast $ SExtend (Pin 2))] || [Pin 3]
  ||| Write to array
  wr : Circuit [Bit, WORD, SP] [Array 5 (WORD), SP]
  wr = Feedback
    (Comb [Write [Pin 0, Pin 2, Pin 1] (Pin 3), Pin 2])
    [Vect.replicate 32 0]
    [Pin 0]
  ||| Read from array
  rd : Circuit ([Array 5 (WORD), SP] || [SP]) [WORD, SP]
  rd = Comb [Read (Pin 2) (Pin 0), Pin 1]


demo : List $ Load [WORD, SP]
demo = streamCircuit stack (
  [ True,  17,  1] ::          -- Push  17
  [ True,   8,  1] ::          -- Push   8
  [ True, 175,  1] ::          -- Push 175
  [False,   0,  0] ::          -- Peek 175
  [False,   0, -1] ::          -- Pop  175
  [False,   0, -1] ::          -- Pop    8
  [False,   0, -1] ::          -- Pop   17
   Nil
)
