module Linear.LNL

import Data.List
import Subset
import Split

%default total
%access public export

mutual
  data Ty = A
          | Imp Ty Ty
          | G LTy

  data LTy = LA
           | Lmp LTy LTy
           | F Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

infixr 5 ~*
(~*) : LTy -> LTy -> LTy
(~*) = Lmp

mutual
  data Term : List Ty -> Ty -> Type where
    Var : Elem a t -> Term t a
    Lam : Term (a::t) b -> Term t (a~>b)
    App : Term t (a~>b) -> Term t a -> Term t b
    GG  : LTerm t [] a -> Term t (G a)

  data LTerm : List Ty -> List LTy -> LTy -> Type where
    LVar : LTerm t [a] a
    LLam : LTerm t (a::g) b -> LTerm t g (a~*b)
    LApp : Split g l r -> LTerm t l (a~*b) -> LTerm t r a -> LTerm t g b
    FF   : Term t a -> LTerm t [] (F a)
    LetF : Split g l r -> LTerm t l (F x) -> LTerm (x::t) r a -> LTerm t g a
    Der  : Term t (G a) -> LTerm t [] a

ok : LTerm g [] (a ~* a)
ok = LLam LVar

ok2 : LTerm g [] (a ~* F (G b) ~* a)
ok2 = LLam $ LLam $ LetF (ConsL $ ConsR Nil) LVar LVar

ok3 : LTerm g [] (F (G b) ~* a ~* a)
ok3 = LLam $ LLam $ LetF (ConsR $ ConsL Nil) LVar LVar

axiomK : LTerm g [] (F (G (a ~* b)) ~* F (G a) ~* F (G b))
axiomK = LLam $ LLam $ LetF (ConsL $ ConsR Nil) LVar
                            (LetF splitLeft LVar
                                           (FF $ GG $ LApp Nil (Der $ Var Here) (Der $ Var $ There Here)))

-- aka eval/axiom T
derelict : LTerm g [] (F (G a) ~* a)
derelict = LLam $ LetF splitLeft LVar (Der $ Var Here)

-- aka axiom4
dig : LTerm g [] (F (G a) ~* F (G (F (G a))))
dig = LLam $ LetF splitLeft LVar (FF $ GG $ FF $ Var Here)
