module DILL

import Data.List
import Subset

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | Bang Ty     -- intuitionistic type

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

data Split : List Ty -> List Ty -> List Ty -> Type where
  Nil : Split [] [] []
  ConsR : Split xs xs1 xs2 -> Split (x :: xs)      xs1 (x :: xs2)
  ConsL : Split xs xs1 xs2 -> Split (x :: xs) (x:: xs1)      xs2

splitLeft : Split l l []
splitLeft {l=[]}   = Nil
splitLeft {l=_::_} = ConsL $ splitLeft

splitRisEq : Split l [] l2 -> l = l2
splitRisEq  Nil      = Refl
splitRisEq (ConsR s) = cong $ splitRisEq s

splitLen : Split l l1 l2 -> length l = length l1 + length l2
splitLen                   Nil      = Refl
splitLen {l1} {l2=_::xs2} (ConsR s) =
  rewrite plusAssociative (length l1) 1 (length xs2) in
  rewrite plusCommutative (length l1) 1 in
  cong $ splitLen s
splitLen                  (ConsL s) = cong $ splitLen s

data Term : List Ty -> List Ty -> Ty -> Type where
  Var     : Term [a] g a
  IVar    : Elem a g -> Term [] g a
  Lam     : Term (a::l) g b -> Term l g (a~>b)
  App     : Split l l1 l2 -> Term l1 g (a~>b) -> Term l2 g a -> Term l g b
  Shut    : Term [] g a -> Term [] g (Bang a)
  Letbang : Split l l1 l2 -> Term l1 g (Bang a) -> Term l2 (a::g) b -> Term l g b   -- let !t1 = t2 in t3

ok : Term [] g (a ~> a)
ok = Lam Var

ok2 : Term [] g (a ~> Bang b ~> a)
ok2 = Lam $ Lam $ Letbang (ConsL $ ConsR Nil) Var Var

ok3 : Term [] g (Bang b ~> a ~> a)
ok3 = Lam $ Lam $ Letbang (ConsR $ ConsL Nil) Var Var

-- bad : Term [] [] (b ~> a ~> a)
-- bad = Lam $ Lam $ Letbang (ConsR $ ConsL Nil) ?wat Var

-- bad2 : Term [] [] (a ~> b ~> a)
-- bad2 = Lam $ Lam $ Letbang (ConsL $ ConsR Nil) ?wat Var

rename : Subset g d -> Term l g a -> Term l d a
rename r  Var            = Var
rename r (IVar el)       = IVar $ r el
rename r (Lam t)         = Lam $ rename r t
rename r (App s t u)     = App s (rename r t) (rename r u)
rename r (Shut t)        = Shut $ rename r t
rename r (Letbang s t u) = Letbang s (rename r t) (rename (ext r) u)

discard : Term l [] (Bang a) -> Term [] g b -> Term l g b
discard t u = Letbang splitLeft (rename absurd t) (rename There u)

derelict : Term [] g (Bang a) -> Term [] g a
derelict t = Letbang Nil t (IVar Here)

substI1 : Term l (a::g) b -> Term [] g a -> Term l g b
substI1  Var              v = Var
substI1 (IVar Here)       v = v
substI1 (IVar (There el)) v = IVar el
substI1 (Lam t)           v = Lam $ substI1 t v
substI1 (App s t u)       v = App s (substI1 t v) (substI1 u v)
substI1 (Shut t)          v = Shut $ substI1 t v
substI1 (Letbang s t u)   v = Letbang s (substI1 t v) (assert_total $ substI1 (rename permute u) (rename There v))
