module Kripke.GL

import Data.List
import Subset

%default total
%access public export

-- https://github.com/L-TChen/ModalTypeTheory/blob/master/Kripke/IGL.agda

data Ty = A
        | Imp Ty Ty
        | Prod Ty Ty
        | Box Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Term : List (List Ty) -> List Ty -> Ty -> Type where
  Var  : Elem a g -> Term ph g a
  Lam  : Term ph (a::g) b -> Term ph g (a~>b)
  App  : Term ph g (a~>b) -> Term ph g a -> Term ph g b
  Pair : Term ph g a -> Term ph g b -> Term ph g (Prod a b)
  Fst  : Term ph g (Prod a b) -> Term ph g a
  Snd  : Term ph g (Prod a b) -> Term ph g b
  Shut : Term (g::ph) [] a -> Term ph g (Box a)
  Open : Term ph g (Box a) -> Term (g::ph) d a
  IRec : Term (g::ph) [Box a] a -> Term ph g (Box a)

axiomK : Term ph g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Shut $ App (Open $ Var $ There Here)
                                (Open $ Var Here)

axiomGL : Term d g (Box (Box a ~> a) ~> Box a)
axiomGL = Lam $ IRec $ App (Open $ Var Here) (Var Here)

axiom4 : Term ph g (Box a ~> Box (Box a))
axiom4 = Lam $ Shut $ Fst $ Open $ IRec $ Pair (Shut $ Snd $ Open $ Var Here)
                                               (Open $ Var Here)

diag : Term (g::ph) [Box (Prod (Box a) a)] a -> Term (g::ph) [] (Box a)
diag t = Fst $ Open $ IRec $ Pair (Shut $ Snd $ Open $ Var Here) t

diagTo4 : Term ph g (Box a ~> Box (Box a))
diagTo4 = Lam $ Shut $ diag $ Open $ Var Here