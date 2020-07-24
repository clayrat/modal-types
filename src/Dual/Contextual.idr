module Dual.Contextual

import Data.List
import Data.List.Quantifiers
import All
import Subset

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

rename : Subset g s -> Term d g a -> Term d s a
rename s (Var el)      = Var $ s el
rename s (MVar el {e}) = MVar el {e=assert_total $ mapPointwise (rename s) e}
rename s (Lam t)       = Lam $ rename (ext s) t
rename s (App t u)     = App (rename s t) (rename s u)
rename s (Shut t)      = Shut t
rename s (Letbox t u)  = Letbox (rename s t) (rename s u)

admit : Term (MkBox ps a::d) g c -> Term d (Box ps a::g) c
admit t = Letbox (Var Here) (rename There t)

weak : Term d g (Box [b] a ~> Box [b,c] a)
weak = Lam $ Letbox (Var Here) (Shut $ MVar Here) -- {e=[Var Here]}

contract : Term d g (Box [b,b] a ~> Box [b] a)
contract = Lam $ Letbox (Var Here) (Shut $ MVar Here) -- {e=[Var Here, Var Here]}

exch : Term d g (Box [b,c] a ~> Box [c,b] a)
exch = Lam $ Letbox (Var Here) (Shut $ MVar Here) --{e=[Var $ There Here, Var Here]}

triv : Term d g (Box [a] a)
triv = Shut $ Var Here

comp : Term d g (Box [a] b ~> Box [a] (Box [b] c) ~> Box [a] c)
comp = Lam $ Lam $ Letbox (Var $ There Here) $
                   Letbox (Var Here) $
                   Shut $
                   Letbox (MVar Here) -- {e=[Var Here]}
                          (MVar Here) -- {e=[MVar (There $ There Here) {e=[Var Here]}]}

eval : Term d g (Box [] a ~> a)
eval = Lam $ Letbox (Var Here) (MVar Here) -- {e=[]}

wrap : Term d g (Box [b] a ~> Box [c] (Box [b] a))
wrap = Lam $ Letbox (Var Here) (Shut $ Shut $ MVar Here) -- {e=[Var Here]}

map1 : Term s g (Box [c] (a ~> b) ~> Box [d] a ~> Box [c,d] b)
map1 = Lam $ Lam $ Letbox (Var $ There Here) $
                   Letbox (Var Here) $
                   Shut $ App (MVar (There Here)) -- {e=[Var Here]}
                              (MVar Here)         -- {e=[Var $ There Here]}

map2 : Term d g (Box [a] (a ~> b) ~> Box [b] c ~> Box [a] c)
map2 = Lam $ Lam $ Letbox (Var $ There Here) $
                   Letbox (Var Here) $
                   Shut (MVar Here) -- {e=[App (MVar (There Here) {e=[Var Here]}) (Var Here)]}

reboxto : Term d g (Box [] (a ~> b) ~> Box [a] b)
reboxto = Lam $ Letbox (Var Here) $
                Shut $ App (MVar Here) -- {e=[]}
                           (Var Here)

reboxfro : Term d g (Box [a] b ~> Box [] (a ~> b))
reboxfro = Lam $ Letbox (Var Here) $
                 Shut $ Lam $ MVar Here -- {e=[Var Here]}

reboxto2 : Term d g (Box [] (a ~> b ~> c) ~> Box [a,b] c)
reboxto2 = Lam $ Letbox (Var Here) $
                 Shut $ App (App (MVar Here {e=[]}) (Var Here)) (Var $ There Here)
