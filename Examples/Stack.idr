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


infixl 4 #>, &>

(#>) : Circuit a b -> Circuit b c -> Circuit a c
(#>) = Ser

(&>) : Circuit a b -> Circuit c d -> Circuit (a || c) (b || d)
(&>) = Par

||| Carry stack pointer
sp : Circuit [Unsigned 5] [Unsigned 5]
sp = Comb [Pin 0]

||| Update the stack pointer
sp' : Circuit ([Signed 2, Pair Bit (Unsigned 16)] || [Unsigned 5])
               ([Unsigned 5] || [Unsigned 5, Pair Bit (Unsigned 16)])
sp' = Comb ([Pin 2] || [(Pin 2) + (Cast $ SExtend (Pin 0)), Pin 1])


||| Write to memory
wr : Circuit ([Unsigned 5, Pair Bit (Unsigned 16)] || [Array 5 (Unsigned 16)])
              [Unsigned 5, Array 5 (Unsigned 16)]
wr = Comb [Pin 0, Write [First (Pin 1), (Pin 0), Second (Pin 1)] (Pin 2)]

||| Memory feedback
wr' : Circuit [Unsigned 5, Pair Bit (Unsigned 16)]
              [Unsigned 5, Array 5 (Unsigned 16)]
wr' = Feedback wr [replicate 32 0] [Pin 1]

||| Read from memory
rd : Circuit ([Unsigned 5] || [Unsigned 5, Array 5 (Unsigned 16)]) [Unsigned 5, Unsigned 16]
rd = Comb [(Pin 1), Read (Pin 0) (Pin 2)]

||| Put it all together
stack : Circuit [Signed 2, Pair Bit (Unsigned 16)] [Unsigned 5, Unsigned 16]
stack = Feedback (sp' #> (sp &> wr') #> rd) [31] [Pin 0]




demo : List $ Load [Unsigned 5, Unsigned 16]
demo = streamCircuit stack (
  [ 1, (True,  17)] :: -- Push  17
  [ 1, (True,   8)] :: -- Push   8
  [ 1, (True, 175)] :: -- Push 175
  [ 0, (False,  0)] :: -- Peek 175
  [-1, (False,  0)] :: -- Pop  175
  [-1, (False,  0)] :: -- Pop    8
  [-1, (False,  0)] :: -- Pop   17
   Nil
)
