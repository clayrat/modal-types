module Kripke.T

import Subset
import Data.List
import Ty

%default total
%access public export

data Pref : a -> List a -> a -> List a -> Type where
  HereP  : Pref x xs    x  xs
  ShiftP : Pref x xs y (x::xs)

prefSub :             Subset g d -> Pairwise Subset ph ps -> Pref x xs g ph
      -> (y ** ys ** (Subset x y,   Pairwise Subset xs ys,   Pref y ys d ps))
prefSub {d}       {ps}       s     ss  HereP  = (d ** ps ** (s, ss, HereP))
prefSub {ph=_::_} {ps=[]}    _     ss  ShiftP = absurd ss
prefSub {ph=_::_} {ps=q::ps} _ (s1,ss) ShiftP = (q ** ps ** (s1, ss, ShiftP))

data Term : List (List Ty) -> List Ty -> Ty -> Type where
  Var  : Elem a g -> Term ph g a
  Lam  : Term ph (a::g) b -> Term ph g (a~>b)
  App  : Term ph g (a~>b) -> Term ph g a -> Term ph g b
  Shut : Term (g::ph) [] a -> Term ph g (Box a)             -- ~quasiquote
  Open : Pref g ph d ps -> Term ph g (Box a) -> Term ps d a -- ~unquote01

axiomK : Term ph g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Shut $ App (Open ShiftP (Var $ There Here))
                                (Open ShiftP (Var Here))

axiomT : Term ph g (Box a ~> a)
axiomT = Lam $ Open HereP (Var Here)

rename : Subset g d -> Pairwise Subset ph ps -> Term ph g a -> Term ps d a
rename         s _  (Var el)    = Var $ s el
rename         s ss (Lam t)     = Lam $ rename (ext s) ss t
rename         s ss (App t u)   = App (rename s ss t) (rename s ss u)
rename {g} {d} s ss (Shut t)    = Shut $ rename id (MkPair {A=Subset g d} s ss) t
rename         s ss (Open ep t) =
  let (_**_**(s2,ss2,ep2)) = prefSub s ss ep in
  Open ep2 (rename s2 ss2 t)
