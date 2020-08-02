module Dual.S4dia

import Data.List
import Subset
import Ty.Dia

%default total
%access public export

mutual
  data Term : List Ty -> List Ty -> Ty -> Type where
    Var    : Elem a g -> Term d g a
    MVar   : Elem a d -> Term d g a
    Lam    : Term d (a::g) b -> Term d g (a~>b)
    App    : Term d g (a~>b) -> Term d g a -> Term d g b
    Shut   : Term d [] a -> Term d g (Box a)
    Letbox : Term d g (Box a) -> Term (a::d) g b -> Term d g b
    Pure   : PTerm d g a -> Term d g (Dia a)

  data PTerm : List Ty -> List Ty -> Ty -> Type where
    Wrap    : Term d g a -> PTerm d g a
    PLetbox : Term d g (Box a) -> PTerm (a::d) g b -> PTerm d g b
    Letdia  : Term d g (Dia a) -> PTerm d [a] b -> PTerm d g b

axiomK : Term d g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Letbox (Var $ There Here)
                            (Letbox (Var Here)
                                    (Shut $ App (MVar $ There Here) (MVar Here)))

-- aka axiom T
eval : Term d g (Box a ~> a)
eval = Lam $ Letbox (Var Here) (MVar Here)

axiom4 : Term d g (Box a ~> Box (Box a))
axiom4 = Lam $ Letbox (Var Here) (Shut $ Shut $ MVar Here)

-- aka dia-K
commute : Term d g (Box (a ~> b) ~> Dia a ~> Dia b)
commute = Lam $ Lam $ Letbox (Var $ There Here)
                             (Pure $ Letdia (Var Here)
                                            (Wrap $ App (MVar Here) (Var Here)))

-- aka dia-T
pure : Term d g (a ~> Dia a)
pure = Lam $ Pure $ Wrap $ Var Here

-- aka dia-4
flatten : Term d g (Dia (Dia a) ~> Dia a)
flatten = Lam $ Pure $ Letdia (Var Here)
                              (Letdia (Var Here) (Wrap $ Var Here))
