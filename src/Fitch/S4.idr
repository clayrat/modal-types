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
  Open : ElemPref g ph ps -> Term (g +: ph) (Box a) -> Term ps a

axiomT : Term (g+:ph) (Box a ~> a)
axiomT = Lam $ Open HereP (Var Here)

axiomK : Term (g+:ph) (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Shut $ App (Open (ThereP HereP) (Var $ There Here))
                                (Open (ThereP HereP) (Var Here))

axiom4 : Term (g+:ph) (Box a ~> Box (Box a))
axiom4 = Lam $ Shut $ Shut $ Open (ThereP $ ThereP HereP) (Var Here)

-- smallstep

--SubsetPref : NEList a -> NEList a -> Type
--SubsetPref {a} g d = {x : a} -> {xs : List a} -> ElemPref x xs g -> ElemPref x xs d
--
--relabel : SubsetPref g d -> Term g a -> Term d a
--relabel {g=g+:gs} {d=d+:ds} s (Var  el)   = Var ?wat
--relabel {g=g+:gs} {d=d+:ds} s (Lam  t)    = Lam $ relabel ?wat2 t
--relabel s (App  t u)  = App (relabel s t) (relabel s u)
--relabel {g=g+:gs} {d=d+:ds} s (Shut t)    = Shut $ relabel ?wat4 t
--relabel s (Open ep t) = ?wat5
