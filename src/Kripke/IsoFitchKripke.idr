module Kripke.IsoFitchKripke

import Control.Isomorphism
import Data.NEList

%default total
%access public export

data FitchList : Type -> Type where
  Nil : FitchList a
  (::) : a -> FitchList a -> FitchList a
  Lock : FitchList a -> FitchList a

isoFK : Iso (FitchList a) (NEList (List a))
isoFK = MkIso to fro tofro froto
  where

  to : FitchList a -> NEList (List a)
  to []        = [] +: []
  to (Lock xs) = let ih = to xs in [] +: (head ih :: tail ih)
  to (x::xs)   = let ih = to xs in (x::head ih) +: tail ih

  fro : NEList (List a) -> FitchList a
  fro ([]      +: [])      = []
  fro ([]      +: (t::ts)) = Lock $ assert_total $ fro (t +: ts)
  fro ((h::hs) +: t)       = h :: (assert_total $ fro (hs +: t))

  tofro : (y : NEList (List a)) -> to (fro y) = y
  tofro ([]      +: [])      = Refl
  tofro ([]      +: (t::ts)) = rewrite assert_total $ tofro (t +: ts) in Refl
  tofro ((h::hs) +: t)       = rewrite assert_total $ tofro (hs +: t) in Refl

  froto : (y : FitchList a) -> fro (to y) = y
  froto []        = Refl
  froto (x::xs)   with (to xs) proof prf
    | (h +: t) = rewrite prf in cong $ froto xs
  froto (Lock xs) with (to xs) proof prf
    | (h +: t) = rewrite prf in cong $ froto xs
