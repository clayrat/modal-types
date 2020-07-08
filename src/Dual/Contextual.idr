module Dual.Contextual

import Data.List
import Data.List.Quantifiers

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | Box (List Ty) Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

record BoxT where
  constructor MkBox
  ph : List Ty
  t : Ty

data Term : List BoxT -> List Ty -> Ty -> Type where
  Var    : Elem a g -> Term d g a
  MVar   : Elem (MkBox ps a) d -> {auto e : All (Term d g) ps} -> Term d g a
  Lam    : Term d (a::g) b -> Term d g (a~>b)
  App    : Term d g (a~>b) -> Term d g a -> Term d g b
  Shut   : Term d g a -> Term d s (Box g a)
  Letbox : Term d g (Box ps a) -> Term (MkBox ps a::d) g b -> Term d g b

weak : Term d g (Box [b] a ~> Box [b,c] a)
weak = Lam $ Letbox (Var Here) (Shut $ MVar Here)

contract : Term d g (Box [b,b] a ~> Box [b] a)
contract = Lam $ Letbox (Var Here) (Shut $ MVar Here)

triv : Term d g (Box [a] a)
triv = Shut $ Var Here

comp : Term d g (Box [a] b ~> Box [a] (Box [b] c) ~> Box [a] c)
comp = Lam $ Lam $ Letbox (Var $ There Here) $
                   Letbox (Var Here) $
                   Shut $
                   Letbox (MVar Here) (MVar Here)

discard : Term d g (Box [] a ~> a)
discard = Lam $ Letbox (Var Here) (MVar Here)

wrap : Term d g (Box [b] a ~> Box [c] (Box [b] a))
wrap = Lam $ Letbox (Var Here) (Shut $ Shut $ MVar Here)

map1 : Term s g (Box [c] (a ~> b) ~> Box [d] a ~> Box [c,d] b)
map1 = Lam $ Lam $ Letbox (Var $ There Here) $
                   Letbox (Var Here) $
                   Shut $ App (MVar $ There Here) (MVar Here)

map2 : Term d g (Box [a] (a ~> b) ~> Box [b] c ~> Box [a] c)
map2 = Lam $ Lam $ Letbox (Var $ There Here) $
                   Letbox (Var Here) $
                   Shut (MVar Here)

reboxto : Term d g (Box [] (a ~> b) ~> Box [a] b)
reboxto = Lam $ Letbox (Var Here) $
                Shut $ App (MVar Here) (Var Here)

reboxfro : Term d g (Box [a] b ~> Box [] (a ~> b))
reboxfro = Lam $ Letbox (Var Here) $
                 Shut $ Lam $ MVar Here
