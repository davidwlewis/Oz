module Oz.Exmaples.Basics

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

--- Memory element tests

testWrite : Circuit ([Unsigned 3] || [Array 3 (Unsigned 8)]) [Array 3 (Unsigned 8)]
testWrite = Comb [Write [Literal True, (Pin 0), Coerce (Pin 0)] (Pin 1)]

fbWrite : Circuit [Unsigned 3] [Array 3 (Unsigned 8)]
fbWrite = Feedback testWrite [Vect.replicate 8 0] [(Pin 0)]

demo : List (Load [Array 3 (Unsigned 8)])
demo = streamCircuit fbWrite [[0], [1], [2], [3], [4], [5], [6], [7]]


--- Packing and unpacking

input : Load [Bit, Unsigned 4, Unsigned 3]
input = [False, 3, 2]

packTest : Bits 8
packTest = pack input

unpackTest : Load [Bit, Unsigned 4, Unsigned 3]
unpackTest = unpack packTest

sliceTest: Circuit [Vector 8] [Bit, Unsigned 4, Unsigned 3]
sliceTest = Comb (toBundle (Pin 0))

runSliceTest : Load [Bit, Unsigned 4, Unsigned 3]
runSliceTest = snd $ runCircuit sliceTest [packTest]


--- Shifting with feedback

testShift : Circuit [] [Unsigned 16]
testShift = Feedback
  (Comb [shiftL (Pin 0) (Literal {t=Unsigned 16} 1)])
  [1]
  [(Pin 0)]

demo2 : List (Load [Unsigned 16])
demo2 = streamCircuit testShift (replicate 10 [])
