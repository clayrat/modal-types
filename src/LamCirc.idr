module LamCirc

import Data.List
import Subset

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | Circ Ty     -- next

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Term : List (Ty, Nat) -> Nat -> Ty -> Type where
  Var  : Elem (a,n) g -> Term g n a
  Lam  : Term ((a,n)::g) n b -> Term g n (a~>b)
  App  : Term g n (a~>b) -> Term g n a -> Term g n b
  Next : Term g (S n) a -> Term g n (Circ a)
  Prev : Term g n (Circ a) -> Term g (S n) a

axiomL4 : Term g n ((Circ a ~> Circ b) ~> Circ (a ~> b))
axiomL4 = Lam $ Next $ Lam $ Prev $ App (Var $ There Here) (Next $ Var Here)

axiomK : Term g n (Circ (a ~> b) ~> Circ a ~> Circ b)
axiomK = Lam $ Lam $ Next $ App (Prev $ Var $ There Here) (Prev $ Var Here)
