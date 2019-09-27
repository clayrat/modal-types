module Dual.GL

import Data.List
import Dual.Ty
import Subset

%default total
%access public export

data Term : List Ty -> List Ty -> Ty -> Type where
  Var    : Elem a g -> Term d g a
  Lam    : Term d (a::g) b -> Term d g (a~>b)
  App    : Term d g (a~>b) -> Term d g a -> Term d g b
  ShutFx : Term d (Box a::d) a -> Term d g (Box a)
  Letbox : Term d g (Box a) -> Term (a::d) g b -> Term d g b

axiomK : Term d g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Letbox (Var $ There Here)
                            (Letbox (Var Here)
                                    (ShutFx $ App (Var $ There $ There Here) (Var $ There Here)))

axiom4 : Term d g (Box a ~> Box (Box a))
axiom4 = Lam $ Letbox (Var Here) (ShutFx $ ShutFx $ Var $ There Here)

axiomGL : Term d g (Box (Box a ~> a) ~> Box a)
axiomGL = Lam $ Letbox (Var Here) (ShutFx $ App (Var $ There Here) (Var Here))
