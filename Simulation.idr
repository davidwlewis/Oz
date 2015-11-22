module Oz.Simulation

import Data.Fin
import Data.Vect

import SLT
import Operation
import Interface
import Signal
import Simulation.Utils

import Data.Bits
import UInt
import SInt

%access public
%default total

mutual
  ||| Determines the value of a signal given contextual state
  runSignal : Signal i t -> Load i -> iSL t
  runSignal (Literal x)         d = x
  runSignal (Pin p)             d = index p d
  runSignal (UnOp op a)         d = unOp op (runSignal a d)
  runSignal (BinOp op a b)      d = binOp op (runSignal a d) (runSignal b d)
  runSignal (Mux [] def)        d = runSignal def d
  runSignal (Mux ((p,c)::xs) f) d = assert_total (if runSignal p d then runSignal c d else runSignal (Mux xs f) d)
  runSignal (Cast s {b} {ok})   d = fromBits {t=b} (rewrite sym ok in toBits $ runSignal s d)
  runSignal (SExtend s)         d = extend (runSignal s d)
  runSignal (Coerce s)          d = (fromBits . coerce . toBits) (runSignal s d)
  runSignal (Concat a b)        d = concat (toBits $ runSignal a d) (toBits $ runSignal b d)
  runSignal (Slice s o)         d = fromBits (slice (toBits $ runSignal s d) o)
  runSignal (Read a m)          d = Vect.index (toFin $ runSignal a d) (runSignal m d)
  runSignal (Write b m)         d = assert_total $
    let [enable, address, value] = runPipeline b d
        memory = (runSignal m d)
    in if enable then replaceAt (toFin address) value memory else memory


  runPipeline : Pipeline i o -> Load i -> Load o
  runPipeline [] d = []
  runPipeline (s :: sb) d = (runSignal s d) :: (runPipeline sb d)
  runPipeline (l || r)  d = (runPipeline l d) || (runPipeline r d)

runCircuit : Circuit i o -> Load i -> (Circuit i o, Load o)
runCircuit Id inp = (Id, inp)
runCircuit c@(Comb b) inp = (c, runPipeline b inp)
runCircuit (Ser l r) inp =
  let (l', m) = runCircuit l inp
      (r', out) = runCircuit r m
  in (Ser l' r', out)
runCircuit (Par t b) (inpT || inpB) =
  let (t', outT) = runCircuit t inpT
      (b', outB) = runCircuit b inpB
  in (Par t' b', outT || outB)
runCircuit (Fork t b) inp =
  let (t', outT) = runCircuit t inp
      (b', outB) = runCircuit b inp
  in (Fork t' b', outT || outB)
runCircuit (First t) (inpT || inpB) =
  let (t', outT) = runCircuit t inpT
  in (First t', outT || inpB)
runCircuit (Second b) (inpT || inpB) =
  let (b', outB) = runCircuit b inpB
  in (Second b', inpT || outB)
runCircuit (Pack c) inp =
  let (c', out) = runCircuit c inp
  in (Pack c', [pack out])
runCircuit (Unpack c) [inp] =
  let (c', out) = runCircuit c (unpack inp)
  in (Unpack c', out)
runCircuit (Feedback c fb loop) inp =
  let (c', out) = runCircuit c (inp || fb)
      fb' = (runPipeline loop out)
  in (Feedback c' fb' loop, out)

|||Should probably operate over streams, lists are more convenient for testing.
streamCircuit : Circuit i o -> List (Load i) -> List (Load o)
streamCircuit _ [] = []
streamCircuit c (i::is) =
  let (c', o) = runCircuit c i
  in o :: streamCircuit c' is
