module Fitch.K

import Subset
import Data.List
import Fitch.Ty

%default total
%access public export

data Term : List (List Ty) -> List Ty -> Ty -> Type where
  Var  : Elem a g -> Term ph g a
  Lam  : Term ph (a::g) b -> Term ph g (a~>b)
  App  : Term ph g (a~>b) -> Term ph g a -> Term ph g b
  Shut : Term (g::ph) [] a -> Term ph g (Box a)         -- ~quasiquote
  Open : Term ph g (Box a) -> Term (g::ph) d a          -- ~unquote0

axiomK : Term ph g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Shut $ App (Open $ Var $ There Here)
                                (Open $ Var Here)

rename : Subset g d -> Subset2 ph ps -> Term ph g a -> Term ps d a
rename           s     _   (Var el)  = Var $ s el
rename           s     s2  (Lam t)   = Lam $ rename (ext s) s2 t
rename           s     s2  (App t u) = App (rename s s2 t) (rename s s2 u)
rename {g} {d}   s     s2  (Shut t)  = Shut $ rename id (MkPair {A=Subset g d} s s2) t
rename {ps=[]}   _     s2  (Open _)  = absurd s2
rename {ps=_::_} _ (q, s2) (Open t)  = Open $ rename q s2 t
