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

infixl 4 #>

(#>) : Circuit a b -> Circuit b c -> Circuit a c
(#>) = Ser

SP : SLType
SP = Unsigned 5

WORD : SLType
WORD = Unsigned 16


||| Update the stack pointer
sp : Circuit ([Signed 2, Bit, WORD] || [SP])        -- dSP, wEn, input || sp
             ([SP, SP, Bit, WORD])                  -- sp, sp', wEn, input
sp = Comb [Pin 3,
           (Pin 3) + (Cast $ SExtend (Pin 0)),
           Pin 1,
           Pin 2]

||| Write to array
wr : Circuit [SP, SP, Bit, WORD]                    -- sp, sp', wEn, input
             [SP, SP, Array 5 (WORD)]               -- sp, sp', mem
wr = Feedback
  (Comb [Pin 0,
         Pin 1,
         Write [Pin 2, Pin 1, Pin 3] (Pin 4)])
  [Vect.replicate 32 0]
  [Pin 2]

||| Read from array
rd : Circuit [SP, SP, Array 5 (WORD)]               -- sp, sp', mem
             [SP, WORD]                             -- sp', output
rd = Comb [Pin 1,
           Read (Pin 0) (Pin 2)]



||| Put it all together
stack : Circuit [Signed 2, Bit, WORD]               -- dSP, wEn, d
                [SP, WORD]                          -- sp', output
stack = Feedback (sp #> wr #> rd) [31] [Pin 0]




demo : List $ Load [SP, WORD]
demo = streamCircuit stack (
  [ 1, True,  17] ::          -- Push  17
  [ 1, True,   8] ::          -- Push   8
  [ 1, True, 175] ::          -- Push 175
  [ 0, False,  0] ::          -- Peek 175
  [-1, False,  0] ::          -- Pop  175
  [-1, False,  0] ::          -- Pop    8
  [-1, False,  0] ::          -- Pop   17
   Nil
)
