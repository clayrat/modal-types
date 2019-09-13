module Dual.KavvosS4

import Data.List
import Dual.Ty
import Subset

%default total
%access public export

data Term : List Ty -> List Ty -> Ty -> Type where
  Var  : Elem a g -> Term d g a
  MVar : Elem a d -> Term d g a
  Lam  : Term d (a::g) b -> Term d g (a~>b)
  App  : Term d g (a~>b) -> Term d g a -> Term d g b
  Prod : Term d g a -> Term d g b -> Term d g (a/\b)
  Fst  : Term d g (a/\b) -> Term d g a
  Snd  : Term d g (a/\b) -> Term d g b
  Shut : Term d [] a -> Term d g (Box a)
  Open : Term d g (Box a) -> Term (a::d) g c -> Term d g c

rename : Subset g s -> Term d g a -> Term d s a
rename r (Var el)   = Var $ r el
rename r (MVar el)  = MVar el
rename r (Lam t)    = Lam $ rename (ext r) t
rename r (App t u)  = App (rename r t) (rename r u)
rename r (Prod t u) = Prod (rename r t) (rename r u)
rename r (Fst t)    = Fst $ rename r t
rename r (Snd t)    = Snd $ rename r t
rename r (Shut t)   = Shut t
rename r (Open t u) = Open (rename r t) (rename r u)

exch : Term d (g1 ++ a::b::g) c -> Term d (g1 ++ b::a::g) c
exch = rename (pref permute)

renameM : Subset d s -> Term d g a -> Term s g a
renameM r (Var el)   = Var el
renameM r (MVar el)  = MVar $ r el
renameM r (Lam t)    = Lam $ renameM r t
renameM r (App t u)  = App (renameM r t) (renameM r u)
renameM r (Prod t u) = Prod (renameM r t) (renameM r u)
renameM r (Fst t)    = Fst $ renameM r t
renameM r (Snd t)    = Snd $ renameM r t
renameM r (Shut t)   = Shut $ renameM r t
renameM r (Open t u) = Open (renameM r t) (renameM (ext r) u)

exchM : Term (d1 ++ a::b::d) g c -> Term (d1 ++ b::a::d) g c
exchM = renameM (pref permute)

Subst : List Ty -> List Ty -> List Ty -> Type
Subst d g s = {x : Ty} -> Elem x g -> Term d s x

exts : Subst d g s -> Subst d (b::g) (b::s)
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : Subst d g s -> Term d g a -> Term d s a
subst s (Var el)   = s el
subst s (MVar el)  = MVar el
subst s (Lam t)    = Lam $ subst (exts s) t
subst s (App t u)  = App (subst s t) (subst s u)
subst s (Prod t u) = Prod (subst s t) (subst s u)
subst s (Fst t)    = Fst $ subst s t
subst s (Snd t)    = Snd $ subst s t
subst s (Shut t)   = Shut t
subst s (Open t u) = Open (subst s t) (subst (renameM There . s) u)
