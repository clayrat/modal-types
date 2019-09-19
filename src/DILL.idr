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
  Lift    : Term [] g a -> Term [] g (Bang a)
  Letbang : Split l l1 l2 -> Term l1 g (Bang a) -> Term l2 (a::g) b -> Term l g b   -- let !a = t in u

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
rename r (Lift t)        = Lift $ rename r t
rename r (Letbang s t u) = Letbang s (rename r t) (rename (ext r) u)

discard : Term l [] (Bang a) -> Term [] g b -> Term l g b
discard t u = Letbang splitLeft (rename absurd t) (rename There u)

-- aka eval/axiom T
derelict : Term [] g (Bang a ~> a)
derelict = Lam $ Letbang splitLeft Var (IVar Here)

axiomK : Term [] g (Bang (a ~> b) ~> Bang a ~> Bang b)
axiomK = Lam $ Lam $ Letbang (ConsL $ ConsR Nil) Var
                             (Letbang splitLeft Var (Lift $ App Nil (IVar Here) (IVar $ There Here)))

-- aka axiom4
dig : Term [] g (Bang a ~> Bang (Bang a))
dig = Lam $ Letbang splitLeft Var (Lift $ Lift $ IVar Here)

-- aka contraction
copy : Term l [] (Bang a) -> Term [] (a :: a :: g) b -> Term l g b
copy t u = Letbang splitLeft (rename absurd t) (rename (contract Here) u)

promote1 : Term l [] (Bang a) -> Term [] [a] b -> Term l [] (Bang b)
promote1 t u = Letbang splitLeft t (Lift u)

promote2 : Split l l1 l2 -> Term l1 [] (Bang a) -> Term l2 [] (Bang b) -> Term [] [b,a] c -> Term l [] (Bang c)
promote2 sp t1 t2 u = Letbang sp t1 (Letbang splitLeft (rename absurd t2) (Lift u))

substI1 : Term l (a::g) b -> Term [] g a -> Term l g b
substI1  Var              v = Var
substI1 (IVar Here)       v = v
substI1 (IVar (There el)) v = IVar el
substI1 (Lam t)           v = Lam $ substI1 t v
substI1 (App s t u)       v = App s (substI1 t v) (substI1 u v)
substI1 (Lift t)          v = Lift $ substI1 t v
substI1 (Letbang s t u)   v = Letbang s (substI1 t v) (assert_total $ substI1 (rename permute u) (rename There v))
