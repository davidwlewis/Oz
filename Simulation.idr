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
  runSignal (First p)           d = fst (runSignal p d)
  runSignal (Second p)          d = snd (runSignal p d)
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
    let [enable, address, value] = runBundle b d
        memory = (runSignal m d)
    in if enable then replaceAt (toFin address) value memory else memory


  runBundle : Bundle i o -> Load i -> Load o
  runBundle [] d = []
  runBundle (s :: sb) d = (runSignal s d) :: (runBundle sb d)
  runBundle (l || r)  d = (runBundle l d) || (runBundle r d)

runCircuit : Circuit i o -> Load i -> (Circuit i o, Load o)
runCircuit c@Null inp = (c, [])
runCircuit c@(Comb b) inp = (c, runBundle b inp)
runCircuit c@(Ser l r) inp =
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
runCircuit (Pack c) inp =
  let (c', out) = runCircuit c inp
  in (Pack c', [pack out])
runCircuit (Unpack c) [inp] =
  let (c', out) = runCircuit c (unpack inp)
  in (Unpack c', out)
runCircuit (Feedback c fb loop) inp =
  let (c', out) = runCircuit c (inp || fb)
      fb' = (runBundle loop out)
  in (Feedback c' fb' loop, out)

|||Should probably operate over streams, lists are more convenient for testing.
streamCircuit : Circuit i o -> List (Load i) -> List (Load o)
streamCircuit _ [] = []
streamCircuit c (i::is) =
  let (c', o) = runCircuit c i
  in o :: streamCircuit c' is
