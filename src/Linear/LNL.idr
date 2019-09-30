module Linear.LNL

import Data.List
import Subset
import Split

%default total
%access public export

infixr 5 ~>
infixr 5 ~*

mutual
  data Ty = A
          | (~>) Ty Ty
          | G LTy

  data LTy = LA
           | (~*) LTy LTy
           | F Ty

Bang : LTy -> LTy
Bang = F . G

mutual
  data Term : List Ty -> Ty -> Type where
    Var : Elem a g -> Term g a
    Lam : Term (a::g) b -> Term g (a~>b)
    App : Term g (a~>b) -> Term g a -> Term g b
    GG  : LTerm g [] a -> Term g (G a)

  data LTerm : List Ty -> List LTy -> LTy -> Type where
    LVar : LTerm g [a] a
    LLam : LTerm g (a::l) b -> LTerm g l (a~*b)
    LApp : Split l ll lr -> LTerm g ll (a~*b) -> LTerm g lr a -> LTerm g l b
    FF   : Term g a -> LTerm g [] (F a)
    LetF : Split l ll lr -> LTerm g ll (F a) -> LTerm (a::g) lr b -> LTerm g l b
    Der  : Term g (G a) -> LTerm g [] a

ok : LTerm g [] (a ~* a)
ok = LLam LVar

ok2 : LTerm g [] (a ~* Bang b ~* a)
ok2 = LLam $ LLam $ LetF (ConsL $ ConsR Nil) LVar LVar

ok3 : LTerm g [] (Bang b ~* a ~* a)
ok3 = LLam $ LLam $ LetF (ConsR $ ConsL Nil) LVar LVar

axiomK : LTerm g [] (Bang (a ~* b) ~* Bang a ~* Bang b)
axiomK = LLam $ LLam $ LetF (ConsL $ ConsR Nil) LVar
                            (LetF splitLeft LVar
                                           (FF $ GG $ LApp Nil (Der $ Var Here) (Der $ Var $ There Here)))

-- aka eval/axiom T/counit of F -| G
derelict : LTerm g [] (Bang a ~* a)
derelict = LLam $ LetF splitLeft LVar (Der $ Var Here)

-- aka axiom4
dig : LTerm g [] (Bang a ~* Bang (Bang a))
dig = LLam $ LetF splitLeft LVar (FF $ GG $ FF $ Var Here)

-- unit of F -| G
introGF : Term g (a ~> G (F a))
introGF = Lam $ GG $ FF $ Var Here

mutual
  rename : Subset g d -> Term g a -> Term d a
  rename s (Var e)   = Var $ s e
  rename s (Lam t)   = Lam $ rename (ext s) t
  rename s (App u v) = App (rename s u) (rename s v)
  rename s (GG  l)   = GG $ renameL s l

  renameL : Subset g d -> LTerm g l a -> LTerm d l a
  renameL s  LVar         = LVar
  renameL s (LLam t)      = LLam $ renameL s t
  renameL s (LApp sp u v) = LApp sp (renameL s u) (renameL s v)
  renameL s (FF t )       = FF $ rename s t
  renameL s (LetF sp u v) = LetF sp (renameL s u) (renameL (ext s) v)
  renameL s (Der t)       = Der $ rename s t

weaken : LTerm g [] (Bang a) -> LTerm [] d b -> LTerm g d b
weaken u v = LetF splitRight u (renameL absurd v)

mapF : Term g (a ~> b) -> LTerm g [] (F a ~* F b)
mapF t = LLam $ LetF splitLeft LVar (FF $ App (rename There t) (Var Here))

mapG : LTerm g [] (a ~* b) -> Term g (G a ~> G b)
mapG t = Lam $ GG $ LApp Nil (renameL There t) (Der $ Var Here)
