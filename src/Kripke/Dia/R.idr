module Kripke.Dia.R

import Subset
import Data.List
import Data.List.Quantifiers
import Ty.Dia

%default total
%access public export

-- adapted from Clouston (2018)
-- this is more like K4dia + R (i.e., SVars)

data Pref : a -> List a -> a -> List a -> Type where
  ShiftP : Pref x xs y (x::xs)
  ThereP : Pref x xs y ys -> Pref x xs z (y::ys)

prefSub :             Subset g d -> Pairwise Subset ph ps -> Pref x xs g ph
      -> (y ** ys ** (Subset x y,   Pairwise Subset xs ys,   Pref y ys d ps))
prefSub {ph=_::_} {ps=[]}    _     ss   _          = absurd ss
prefSub {ph=_::_} {ps=q::ps} _ (s1,ss)  ShiftP     = (q ** ps ** (s1, ss, ShiftP))
prefSub {ph=_::_} {ps=q::ps} _ (s1,ss) (ThereP ep) =
  let (y**ys**(s2,ss2,epp)) = prefSub s1 ss ep in
  (y**ys**(s2, ss2, ThereP epp))

data Term : List (List Ty) -> List Ty -> Ty -> Type where
  Var    : Elem a g -> Term ph g a
  SVar   : Any (Elem a) ph -> Term ph g a
  Lam    : Term ph (a::g) b -> Term ph g (a~>b)
  App    : Term ph g (a~>b) -> Term ph g a -> Term ph g b
  Shut   : Term (g::ph) [] a -> Term ph g (Box a)
  Open   : Pref g ph d ps -> Term ph g (Box a) -> Term ps d a
  Pure   : Pref g ph d ps -> Term ph g a -> Term ps d (Dia a)
  Letdia : Term ph g (Dia a) -> Term [[a]] [] b -> Term ph g b

axiomK : Term ph g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Shut $ App (Open ShiftP (Var $ There Here))
                                (Open ShiftP (Var Here))

fmap : Term ph g ((a ~> b) ~> Box a ~> Box b)
fmap = Lam $ Lam $ Shut $ App (SVar $ Here (There Here))
                              (Open ShiftP (Var Here))

axiomR : Term ph g (a ~> Box a)
axiomR = Lam $ Shut $ SVar $ Here Here

axiom4 : Term ph g (Box a ~> Box (Box a))
axiom4 = Lam $ Shut $ Shut $ Open (ThereP ShiftP) (Var Here)

axiomDia4 : Term ph g (Dia (Dia a) ~> Dia a)
axiomDia4 = Lam $ Letdia (Var Here) (SVar $ Here Here)

-- dia -| box

wrap : Term ph g (a ~> Box (Dia a))
wrap = Lam $ Shut $ Pure ShiftP $ Var Here

unwrap : Term ph g (Dia (Box a) ~> a)
unwrap = Lam $ Letdia (Var Here)
                      (Open ShiftP $ Var Here)

-- structural rule

rename : Subset g d -> Pairwise Subset ph ps -> Term ph g a -> Term ps d a
rename         s _  (Var el)     = Var $ s el
rename         _ ss (SVar ael)   = SVar $ pairwiseApply ss ael
rename         s ss (Lam t)      = Lam $ rename (ext s) ss t
rename         s ss (App t u)    = App (rename s ss t) (rename s ss u)
rename {g} {d} s ss (Shut t)     = Shut $ rename id (MkPair {A=Subset g d} s ss) t
rename         s ss (Open pr t)  =
  let (_**_**(s2,ss2,pr2)) = prefSub s ss pr in
  Open pr2 (assert_total $ rename s2 ss2 t) -- totality checker chokes
rename         s ss (Pure pr t)  =
  let (_**_**(s2,ss2,pr2)) = prefSub s ss pr in
  Pure pr2 (assert_total $ rename s2 ss2 t)
rename         s ss (Letdia t u) = Letdia (rename s ss t) u

monoDia : Term [] [] (a~>b) -> Term [] [] (Dia a ~> Dia b)
monoDia t = Lam $ Letdia (Var Here) $
                  Pure ShiftP $ App (rename nilSubset () t)
                                    (Var Here)
