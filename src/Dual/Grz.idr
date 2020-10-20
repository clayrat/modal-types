module Dual.Grz

import Data.List
import Ty
import Subset

%default total

data Term : List Ty -> List Ty -> Ty -> Type where
  Var    : Elem a g -> Term d g a
  MVar   : Elem a d -> Term d g a
  Lam    : Term d (a::g) b -> Term d g (a~>b)
  App    : Term d g (a~>b) -> Term d g a -> Term d g b
  ShutFx : Term d [Box (a ~> Box a)] a -> Term d g (Box a)
  Letbox : Term d g (Box a) -> Term (a::d) g b -> Term d g b

axiomK : Term d g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Letbox (Var $ There Here) $
                     Letbox (Var Here) $
                     ShutFx $ App (MVar $ There Here) (MVar Here)

axiom4 : Term d g (Box a ~> Box (Box a))
axiom4 = Lam $ Letbox (Var Here) (ShutFx $ ShutFx $ MVar Here)

axiomT : Term d g (Box a ~> a)
axiomT = Lam $ Letbox (Var Here) (MVar Here)

axiomGrz : Term d g (Box (Box (a ~> Box a) ~> a) ~> a)
axiomGrz = Lam $ Letbox (Var Here) $
                 App (MVar Here)
                     (ShutFx $ Lam $ ShutFx $ App (MVar Here) (Var Here))
