module Dual.SeqCalc.S4

import Data.List
import Ty
import Subset

%default total
%access public export

mutual
  data Term : List Ty -> List Ty -> Ty -> Type where
    Var  : Elem a g -> Spine d g a b -> Term d g b
    MVar : Elem a d -> Spine d g a b -> Term d g b
    Lam  : Term d (a::g) b -> Term d g (a~>b)
    Shut : Term d [] a -> Term d g (Box a)
    Cut  : Term d g a -> Spine d g a b -> Term d g b

  data Spine : List Ty -> List Ty -> Ty -> Ty -> Type where
    Nil  : Spine d g a a
    Cons : Term d g a -> Spine d g b c -> Spine d g (a~>b) c
    BoxL : Term (a::d) g b -> Spine d g (Box a) b

axiomK : Term d g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Cut (Var (There Here) Nil) $
                     BoxL $
                     Cut (Var Here Nil) $
                     BoxL $
                     Shut $ Cut (MVar (There Here) Nil) $
                            Cons (MVar Here Nil) Nil

-- aka axiom T
eval : Term d g (Box a ~> a)
eval = Lam $ Cut (Var Here Nil) $ BoxL $ MVar Here Nil

axiom4 : Term d g (Box a ~> Box (Box a))
axiom4 = Lam $ Cut (Var Here Nil) $ BoxL $ Shut $ Shut $ MVar Here Nil