module Fitch.K

import Subset
import Data.List
import Data.NEList
import Fitch.Ty

%default total
%access public export

data Term : NEList (List Ty) -> Ty -> Type where
  Var  : Elem a g -> Term (g +: ph) a
  Lam  : Term ((a::g) +: ph) b -> Term (g +: ph) (a~>b)
  App  : Term gs (a~>b) -> Term gs a -> Term gs b
  Shut : Term ([] +: (g::ph)) a -> Term (g +: ph) (Box a)   -- ~quasiquote
  Open : Term (g +: ph) (Box a) -> Term (d +: g :: ph) a    -- ~unquote

axiomK : Term (g+:ph) (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Shut $ App (Open $ Var $ There Here)
                                (Open $ Var Here)

-- rename : Subset g d -> Term (g+:gs) a -> Term (d+:gs) a
-- rename r (Var el)  = Var $ r el
-- rename r (Lam t)   = Lam $ rename (ext r) t
-- rename r (App t u) = App (rename r t) (rename r u)
-- rename r (Shut t)  = Shut ?wat
-- rename r (Open t)  = Open t
