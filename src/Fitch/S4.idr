module Fitch.S4

import Subset
import Data.List
import Fitch.Ty

%default total
%access public export

data ElemPref : a -> List a -> a -> List a -> Type where
  HereP : ElemPref x xs x xs
  ThereP : ElemPref x xs y ys -> ElemPref x xs z (y::ys)

data Term : List (List Ty) -> List Ty -> Ty -> Type where
  Var  : Elem a g -> Term ph g a
  Lam  : Term ph (a::g) b -> Term ph g (a~>b)
  App  : Term ph g (a~>b) -> Term ph g a -> Term ph g b
  Shut : Term (g::ph) [] a -> Term ph g (Box a)                 -- ~quasiquote
  Open : ElemPref g ph d ps -> Term ph g (Box a) -> Term ps d a -- ~unquote

axiomT : Term ph g (Box a ~> a)
axiomT = Lam $ Open HereP (Var Here)

axiomK : Term ph g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Shut $ App (Open (ThereP HereP) (Var $ There Here))
                                (Open (ThereP HereP) (Var Here))

axiom4 : Term ph g (Box a ~> Box (Box a))
axiom4 = Lam $ Shut $ Shut $ Open (ThereP $ ThereP HereP) (Var Here)

-- smallstep

rename : Subset g d -> Subset2 ph ps -> Term ph g a -> Term ps d a
rename                           s     _   (Var el)    = Var $ s el
rename                           s     s2  (Lam t)     = Lam $ rename (ext s) s2 t
rename                           s     s2  (App t u)   = App (rename s s2 t) (rename s s2 u)
rename {g} {d}                   s     s2  (Shut t)    = Shut $ rename id (MkPair {A=Subset g d} s s2) t
rename {ph=[]}      {ps=[]}      s     s2  (Open ep t) = ?wat
rename {ph=_::_}    {ps=[]}      _     s2  (Open ep t) = absurd s2
rename {ph=[]}      {ps=_::_}    _     s2  (Open ep t) = absurd s2
rename {ph=ph::phs} {ps=ps::pss} _ (q, s2) (Open ep t) = Open ?wat2 ?wat3
