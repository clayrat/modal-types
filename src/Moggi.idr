module Moggi

import Data.List
import Subset

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | M Ty     -- effect

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

mutual
  data Term : List Ty -> Ty -> Type where
    Var    : Elem a g -> Term g a
    Lam    : Term (a::g) b -> Term g (a~>b)
    App    : Term g (a~>b) -> Term g a -> Term g b
    Val    : PTerm g a -> Term g (M a)

  data PTerm : List Ty -> Ty -> Type where
    Wrap   : Term g a -> PTerm g a
    Letval : Term g (M a) -> PTerm (a::g) b -> PTerm g b

pure : Term g (a ~> M a)
pure = Lam $ Val $ Wrap $ Var Here

flatten : Term g (M (M a) ~> M a)
flatten = Lam $ Val $ Letval (Var Here)
                             (Letval (Var Here)
                                     (Wrap $ Var Here))

map : Term g ((a ~> b) ~> M a ~> M b)
map = Lam $ Lam $ Val $ Letval (Var Here)
                               (Wrap $ App (Var $ There $ There Here)
                                           (Var Here))

flatMap : Term g ((a ~> M b) ~> M a ~> M b)
flatMap = Lam $ Lam $ Val $ Letval (Var Here)
                                   (Letval (App (Var $ There $ There Here)
                                                (Var Here))
                                           (Wrap $ Var Here))
