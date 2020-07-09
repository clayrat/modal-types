module Kripke.Contextual.K

import Data.List
import Data.List.Quantifiers
import Kripke.Contextual.Ty

%default total
%access public export

data Term : List (List Ty) -> List Ty -> Ty -> Type where
  Var  : Elem a g -> Term ph g a
  Lam  : Term ph (a::g) b -> Term ph g (a~>b)
  App  : Term ph g (a~>b) -> Term ph g a -> Term ph g b
  Shut : Term (g::ph) d a -> Term ph g (Box d a)
  Open : Term ph g (Box s a) -> {auto e : All (Term (g::ph) d) s} -> Term (g::ph) d a

weak : Term ph g (Box [b] a ~> Box [b,c] a)
weak = Lam $ Shut $ Open (Var Here) -- {e=[Var Here]}

contract : Term d g (Box [b,b] a ~> Box [b] a)
contract = Lam $ Shut $ Open (Var Here) -- {e=[Var Here, Var Here]}

exch : Term d g (Box [b,c] a ~> Box [c,b] a)
exch = Lam $ Shut $ Open (Var Here) -- {e=[Var $ There Here, Var Here]}

triv : Term d g (Box [a] a)
triv = Shut $ Var Here

map1 : Term s g (Box [c] (a ~> b) ~> Box [d] a ~> Box [c,d] b)
map1 = Lam $ Lam $ Shut $ App (Open $ Var $ There Here) -- {e=[Var Here]}
                              (Open $ Var Here) -- {e=[Var Here]}

map2 : Term ph g (Box [a] (a ~> b) ~> Box [b] c ~> Box [a] c)
map2 = Lam $ Lam $ Shut $ Open (Var Here)
                               {e=[App (Open (Var $ There Here)) -- {e=[Var Here]}
                                       (Var Here)]}

ex1 : Term ph g (Box [c] (a ~> b) ~> Box [c] a ~> Box [c] b)
ex1 = Lam $ Lam $ Shut $ App (Open $ Var $ There Here) -- {e=[Var Here]}
                             (Open $ Var Here) -- {e=[Var Here]}

ex2 : Term ph g (Box [b] a ~> Box [c,d] b ~> Box [c,d] a)
ex2 = Lam $ Lam $ Shut $ Open (Var $ There Here) -- {e=[Open (Var Here) {e=[Var Here, Var $ There Here]}]}

reboxto : Term ph g (Box [] (a ~> b) ~> Box [a] b)
reboxto = Lam $ Shut $ App (Open $ Var Here) -- {e=[]}
                           (Var Here)

reboxfro : Term d g (Box [a] b ~> Box [] (a ~> b))
reboxfro = Lam $ Shut $ Lam $ Open $ Var Here -- {e=[Var Here]}
