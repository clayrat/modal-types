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
rename s (MVar el {e}) = MVar el {e=assert_total $ mapPredicate (rename s) e}
rename s (Lam t)       = Lam $ rename (ext s) t
rename s (App t u)     = App (rename s t) (rename s u)
rename s (Shut t)      = Shut t
rename s (Letbox t u)  = Letbox (rename s t) (rename s u)

renameM : Subset d s -> Term d g a -> Term s g a
renameM s (Var el)      = Var el
renameM s (MVar el {e}) = MVar (s el) {e=assert_total $ mapPredicate (renameM s) e}
renameM s (Lam t)       = Lam $ renameM s t
renameM s (App t u)     = App (renameM s t) (renameM s u)
renameM s (Shut t)      = Shut $ renameM s t
renameM s (Letbox t u)  = Letbox (renameM s t) (renameM (ext s) u)

idEntail : (g : List Ty) -> All (Term d g) g
idEntail []     = []
idEntail (a::g) = Var Here :: mapPredicate (rename There) (idEntail g)

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

-- substitution

Subst : List BoxT -> List Ty -> List Ty -> Type
Subst d g s = {x : Ty} -> Elem x g -> Term d s x

exts : Subst d g s -> Subst d (b::g) (b::s)
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : Subst d g s -> Term d g a -> Term d s a
subst s (Var el)      = s el
subst s (MVar {e} el) = MVar el {e=assert_total $ mapPredicate (subst s) e}
subst s (Lam t)       = Lam $ subst (exts s) t
subst s (App t u)     = App (subst s t) (subst s u)
subst s (Shut t)      = Shut t
subst s (Letbox t u)  = Letbox (subst s t) (subst (renameM There . s) u)

SubstM : List BoxT -> List BoxT -> Type
SubstM d s = {x : Ty} -> {g : List Ty} -> Elem (MkBox g x) d -> Term s g x

extsM : SubstM d s -> SubstM (b::d) (b::s)
extsM _  Here      = MVar Here {e=idEntail _}
extsM s (There el) = renameM There (s el)

substM : SubstM d s -> Term d g a -> Term s g a
substM s (Var el)      = Var el
substM s (MVar {e} el) = subst (\el2 => assert_total $ substM s $ indexAll el2 e) (s el)
substM s (Lam t)       = Lam $ substM s t
substM s (App t u)     = App (substM s t) (substM s u)
substM s (Shut t)      = Shut $ substM s t
substM s (Letbox t u)  = Letbox (substM s t) (substM (extsM s) u)

subst1 : Term d (b::g) a -> Term d g b -> Term d g a
subst1 {d} {g} {b} t u = subst {g=b::g} go t
  where
  go : Subst d (b::g) g
  go  Here      = u
  go (There el) = Var el

subst1M : Term (MkBox s b::d) g a -> Term d s b -> Term d g a
subst1M {d} {s} {b} t u = substM {d=MkBox s b::d} go t
  where
  go : SubstM (MkBox s b::d) d
  go  Here      = u
  go (There el) = MVar el {e=idEntail _}

isVal : Term d g a -> Bool
isVal (Lam _)  = True
isVal (Var _)  = True
--isVal (Shut _)  = True
isVal  _       = False

step : Term d g a -> Maybe (Term d g a)
step (App    (Lam body) sub ) = Just $ subst1 body sub
step (App     t         u   ) =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Letbox (Shut sub) body) = Just $ subst1M body sub
step (Letbox  t         u   ) =
  if isVal t
    then Nothing
    else [| Letbox (step t) (pure u) |]
step  _                       = Nothing
