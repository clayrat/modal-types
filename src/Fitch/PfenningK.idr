module Fitch.PfenningK

import Data.List
import Data.NEList

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | Box Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Term : NEList (List Ty) -> Ty -> Type where
  Var   : Elem a g -> Term (g +: gs) a
  Lam   : Term ((a::g) +: gs) b -> Term (g +: gs) (a~>b)
  App   : Term ph (a~>b) -> Term ph a -> Term ph b
  Shut  : Term ([] +: (g::gs)) a -> Term (g +: gs) (Box a)
  Open  : Term (g +: gs) (Box a) -> Term (d +: g::gs) a

axiomK : Term ph (Box (a ~> b) ~> Box a ~> Box b)
axiomK {ph=g+:gs} = Lam $ Lam $ Shut $ App (Open $ Var $ There Here) (Open $ Var Here)
