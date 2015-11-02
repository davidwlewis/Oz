module Oz.PajaritoRoad

import Data.Fin

import SLT
import Operation
import Interface
import Signal
import Simulation

import Data.Bits
import UInt
import SInt

import Data.Morphisms
import Control.Category
import Control.Arrow

-- Not currently used, just messing about. Highly abstract version of Circuit.
data C a b = MkC (a -> (Lazy (C a b), (b)))

C' : Bus i iw -> Bus o ow -> Type
C' a b = C (Load a) (Load b)

instance Category C where
  id = assert_total $ MkC $ \a => (id, a)
  (.) x y = dot x y where
    dot : C b c -> C a b -> C a c
    dot (MkC c2) (MkC c1) = assert_total $
      MkC $ \i =>
        let (c1', m) = c1 i
            (c2', o) = c2 m
        in (dot c2' c1', o)

instance Arrow C where
  arrow f = assert_total $ MkC $ \a => (arrow f, f a)
  first (MkC c) = assert_total $ MkC $ \(a, b) =>
    let (c', r) = c a
    in (first c', (r, b))

runC : C a b -> List a -> List b
runC _ [] = []
runC (MkC c) (x::xs) =
  let (c', r) = c x
  in r :: runC c' xs

cb : Bundle i o -> C' i o
cb b = arrow (runBundle b)

fb : C' (i||l) o -> C' o l -> Load l -> C' i o
fb (MkC cir) (MkC loop) ld = MkC $ \a =>
  let (c', res) = cir (a || ld)
      (loop', ld') = loop res
  in (fb c' loop' ld' , res)

par : C' a b -> C' c d -> C' (a||c) (b||d)
par l r = (arrow $ \(a||c) => (a, c))
      >>> (l *** r)
      >>> (arrow $ uncurry (||))


{- the following notation doesn't exist in idris, but it may in future
par l r = proc i -> do (a, c) <- (arrow $ \(a||c) => (a, c)) -< i
                       b <- l -< a
                       d <- r -< c
                       returnA -< (b||d) -}

testTypedC : C' [] [Signed 3]
testTypedC = fb (cb [1 + (Pin 0)]) (cb [Pin 0]) [0]

demo2 : List (Load [Signed 3])
demo2 = runC testTypedC (replicate 10 [])
