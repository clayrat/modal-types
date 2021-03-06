module Dual.K

import Data.List
import Ty
import Subset

%default total
%access public export

data Term : List Ty -> List Ty -> Ty -> Type where
  Var    : Elem a g -> Term d g a
  Lam    : Term d (a::g) b -> Term d g (a~>b)
  App    : Term d g (a~>b) -> Term d g a -> Term d g b
  Shut   : Term [] d a -> Term d g (Box a)
  Letbox : Term d g (Box a) -> Term (a::d) g b -> Term d g b

axiomK : Term d g (Box (a ~> b) ~> Box a ~> Box b)
axiomK = Lam $ Lam $ Letbox (Var $ There Here)
                            (Letbox (Var Here)
                                    (Shut $ App (Var $ There Here) (Var Here)))

-- reduction

rename : Subset g s -> Term d g a -> Term d s a
rename r (Var el)     = Var $ r el
rename r (Lam t)      = Lam $ rename (ext r) t
rename r (App t u)    = App (rename r t) (rename r u)
rename r (Shut t)     = Shut t
rename r (Letbox t u) = Letbox (rename r t) (rename r u)

exch : Term d (g1 ++ a::b::g) c -> Term d (g1 ++ b::a::g) c
exch = rename (pref permute)

contr : Term d (g1 ++ a::a::g) c -> Term d (g1 ++ a::g) c
contr = rename (pref $ contract Here)

renameM : Subset d s -> Term d g a -> Term s g a
renameM r (Var el)     = Var el
renameM r (Lam t)      = Lam $ renameM r t
renameM r (App t u)    = App (renameM r t) (renameM r u)
renameM r (Shut t)     = Shut $ rename r t
renameM r (Letbox t u) = Letbox (renameM r t) (renameM (ext r) u)

exchM : Term (d1 ++ a::b::d) g c -> Term (d1 ++ b::a::d) g c
exchM = renameM (pref permute)

contrM : Term (d1 ++ a::a::d) g c -> Term (d1 ++ a::d) g c
contrM = renameM (pref $ contract Here)

Subst : List Ty -> List Ty -> List Ty -> Type
Subst d g s = {x : Ty} -> Elem x g -> Term d s x

exts : Subst d g s -> Subst d (b::g) (b::s)
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : Subst d g s -> Term d g a -> Term d s a
subst s (Var el)     = s el
subst s (Lam t)      = Lam $ subst (exts s) t
subst s (App t u)    = App (subst s t) (subst s u)
subst s (Shut t)     = Shut t
subst s (Letbox t u) = Letbox (subst s t) (subst (renameM There . s) u)

subst1 : Term d (b::g) a -> Term d g b -> Term d g a
subst1 {d} {g} {b} t s = subst {g=b::g} go t
  where
  go : Subst d (b::g) g
  go  Here      = s
  go (There el) = Var el

SubstM : List Ty -> List Ty -> List Ty -> Type
SubstM d s g = {x : Ty} -> Elem x d -> Term s g x

--extsM : SubstM d s g -> SubstM (b::d) (b::s) g
--extsM _  Here      = ?wat
--extsM s (There el) = renameM There (s el)
--
--shiftM : SubstM d s [] -> SubstM s [] d
--shiftM s  Here      = ?wat1
--shiftM s (There el) = ?wat2

--substM : SubstM d s [] -> Term d g a -> Term s g a
--substM s (Var el)     = Var el
--substM s (Lam t)      = Lam $ substM s t
--substM s (App t u)    = App (substM s t) (substM s u)
--substM s (Shut t)     = Shut $ subst (shiftM s) t
--substM s (Letbox t u) = Letbox (substM s t) (substM (extsM s) u)

subst1M : Term (b::d) g a -> Term [] d b -> Term d g a
subst1M (Var el)     v = Var el
subst1M (Lam t)      v = Lam $ subst1M t v
subst1M (App t u)    v = App (subst1M t v) (subst1M u v)
subst1M (Shut t)     v = Shut $ subst1M ?wat ?wat2
subst1M (Letbox t u) v = ?wat5

--subst1M {d} {g} {b} t u = substM go t
--  where
--  go : SubstM (b::d) d []
--  go  Here      = ?wat --s
--  go (There el) = ?wat1 --MVar el

isVal : Term d g a -> Bool
isVal (Lam _)  = True
isVal (Var _)  = True
isVal  _       = False

step : Term d g a -> Maybe (Term d g a)
step (App    (Lam body) sub ) = Just $ subst1 body sub
step (App     t         u   ) =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Letbox (Shut sub) body) = Just $ ?wat0 --subst1M body sub
step (Letbox  t         u   ) =
  if isVal t
    then Nothing
    else [| Letbox (step t) (pure u) |]
step  _                       = Nothing
