module Linear.DILLten

import Data.List
import Subset
import Split

%default total
%access public export

infixr 5 ~*

data Ty = A
        | (~*) Ty Ty
        | I
        | Ten Ty Ty
        | Bang Ty     -- intuitionistic type

data Term : List Ty -> List Ty -> Ty -> Type where
  Var     : Term [a] g a
  IVar    : Elem a g -> Term [] g a
  MkI     : Term [] g I
  LetI    : Split l l1 l2 -> Term l1 g I -> Term l2 g a -> Term l g a                 -- let * = t in u
  MkTen   : Split l l1 l2 -> Term l1 g a -> Term l2 g b -> Term l g (Ten a b)
  LetTen  : Split l l1 l2 -> Term l1 g (Ten a b) -> Term (b::a::l2) g c -> Term l g c -- let (a,b) = t in u
  Lam     : Term (a::l) g b -> Term l g (a~*b)
  App     : Split l l1 l2 -> Term l1 g (a~*b) -> Term l2 g a -> Term l g b
  Lift    : Term [] g a -> Term [] g (Bang a)
  Letbang : Split l l1 l2 -> Term l1 g (Bang a) -> Term l2 (a::g) b -> Term l g b     -- let !a = t in u

ok : Term [] g (a ~* a)
ok = Lam Var

ok2 : Term [] g (a ~* Bang b ~* a)
ok2 = Lam $ Lam $ Letbang (ConsL $ ConsR Nil) Var Var

ok3 : Term [] g (Bang b ~* a ~* a)
ok3 = Lam $ Lam $ Letbang (ConsR $ ConsL Nil) Var Var

ok4 : Term [] g (a ~* b ~* Ten a b)
ok4 = Lam $ Lam $ MkTen (ConsR $ ConsL Nil) Var Var

ok5 : Term [] g (b ~* a ~* Ten a b)
ok5 = Lam $ Lam $ MkTen (ConsL $ ConsR Nil) Var Var

dup : Term [] g (Bang a ~* Ten (Bang a) (Bang a))
dup = Lam $ Letbang splitLeft Var (MkTen Nil (Lift $ IVar Here) (Lift $ IVar Here))

del : Term [] g (Bang a ~* I)
del = Lam $ Letbang splitLeft Var MkI

symTen : Term [] g (Ten a b ~* Ten b a)
symTen = Lam $ LetTen splitLeft Var (MkTen (ConsL $ ConsR Nil) Var Var)

idL : Term [] g (Ten I a ~* a)
idL = Lam $ LetTen splitLeft Var $ LetI (ConsR $ ConsL Nil) Var Var

idL' : Term [] g (a ~* Ten I a)
idL' = Lam $ MkTen splitRight MkI Var

idR : Term [] g (Ten a I ~* a)
idR = Lam $ LetTen splitLeft Var $ LetI (ConsL $ ConsR Nil) Var Var

idR' : Term [] g (a ~* Ten a I)
idR' = Lam $ MkTen splitLeft Var MkI

assocTen : Term [] g (Ten (Ten a b) c ~* Ten a (Ten b c))
assocTen = Lam $ LetTen splitLeft Var
                   (LetTen (ConsR $ ConsL Nil) Var
                      (MkTen (ConsR $ ConsL $ ConsR Nil) Var
                         (MkTen (ConsL $ ConsR Nil) Var Var)))

curry : Term [] g ((Ten a b ~* c) ~* a ~* b ~* c)
curry = Lam $ Lam $ Lam $ App (ConsR $ ConsR $ ConsL Nil) Var (MkTen (ConsR $ ConsL Nil) Var Var)

uncurry : Term [] g ((a ~* b ~* c) ~* Ten a b ~* c)
uncurry = Lam $ Lam $ LetTen (ConsL $ ConsR Nil) Var $ App (ConsR $ ConsL $ ConsL Nil) (App (ConsR $ ConsL Nil) Var Var) Var

-- bad : Term [] [] (b ~* a ~* a)
-- bad = Lam $ Lam $ Letbang (ConsR $ ConsL Nil) ?wat Var

-- bad2 : Term [] [] (a ~* b ~* a)
-- bad2 = Lam $ Lam $ Letbang (ConsL $ ConsR Nil) ?wat Var

rename : Subset g d -> Term l g a -> Term l d a
rename r  Var            = Var
rename r (IVar el)       = IVar $ r el
rename r  MkI            = MkI
rename r (LetI s t u)    = LetI s (rename r t) (rename r u)
rename r (MkTen s t u)   = MkTen s (rename r t) (rename r u)
rename r (LetTen s t u)  = LetTen s (rename r t) (rename r u)
rename r (Lam t)         = Lam $ rename r t
rename r (App s t u)     = App s (rename r t) (rename r u)
rename r (Lift t)        = Lift $ rename r t
rename r (Letbang s t u) = Letbang s (rename r t) (rename (ext r) u)

discard : Term l [] (Bang a) -> Term [] g b -> Term l g b
discard t u = Letbang splitLeft (rename absurd t) (rename There u)

-- aka eval/axiom T
derelict : Term [] g (Bang a ~* a)
derelict = Lam $ Letbang splitLeft Var (IVar Here)

axiomK : Term [] g (Bang (a ~* b) ~* Bang a ~* Bang b)
axiomK = Lam $ Lam $ Letbang (ConsL $ ConsR Nil) Var
                             (Letbang splitLeft Var (Lift $ App Nil (IVar Here) (IVar $ There Here)))

-- aka axiom4
dig : Term [] g (Bang a ~* Bang (Bang a))
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
