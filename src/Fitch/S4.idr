module Fitch.S4

import Subset
import Data.List
import Data.NEList
import Fitch.Ty

%default total
%access public export

data ElemPref : a -> List a -> NEList a -> Type where
  HereP : ElemPref x xs (x+:xs)
  ThereP : ElemPref x xs (y+:ys) -> ElemPref x xs (z+:y::ys)

data Term : NEList (List Ty) -> Ty -> Type where
  Var  : Elem a g -> Term (g +: ph) a
  Lam  : Term ((a::g) +: ph) b -> Term (g +: ph) (a~>b)
  App  : Term gs (a~>b) -> Term gs a -> Term gs b
  Shut : Term ([] +: (g::ph)) a -> Term (g +: ph) (Box a)
  Open : Term (g +: ph) (Box a) -> ElemPref g ph ps -> Term ps a

axiomT : Term (g+:ph) (Box a ~> a)
axiomT = Lam $ Open (Var Here) HereP

axiomK : Term (g+:ph) (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Shut $ App (Open (Var $ There Here) (ThereP HereP))
                                (Open (Var Here) (ThereP HereP))

axiom4 : Term (g+:ph) (Box a ~> Box (Box a))
axiom4 = Lam $ Shut $ Shut $ Open (Var Here) (ThereP $ ThereP HereP)

-- smallstep

-- rename : SubsetN g d -> Term g a -> Term d a
-- rename {d=d+:ph}    r (Var el)    = Var ?wat -- $ r el
-- rename {d=d+:ph}    r (Lam t)     = Lam $ rename ?wat2 t --(ext r) t
-- rename              r (App t1 t2) = App (rename r t1) (rename r t2)
-- rename {d=d+:ph}    r (Shut t)    = Shut ?wat3
-- rename {d=s+:d::ph} r (Open t)    = Open ?wat4
-- rename {d=s+:[]}    r (Open t)    = ?wat5

