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
           | F Ty
           | Lmp LTy LTy


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
    LApp : Split g l r -> LTerm t l (a~*b) -> LTerm t r a -> LTerm t g a
    FF   : Term t a -> LTerm t [] (F a)
    LetF : Split g l r -> LTerm t l (F x) -> LTerm (x::t) r a -> LTerm t g a
    Der  : Term t (G a) -> LTerm t [] a

ok : LTerm g [] (a ~* a)
ok = LLam LVar

ok2 : LTerm g [] (a ~* F (G b) ~* a)
ok2 = LLam $ LLam $ LetF (ConsL $ ConsR Nil) LVar LVar

ok3 : LTerm g [] (F (G b) ~* a ~* a)
ok3 = LLam $ LLam $ LetF (ConsR $ ConsL Nil) LVar LVar

derelict : LTerm g [] (F (G a) ~* a)
derelict = LLam $ LetF splitLeft LVar (Der $ Var Here)
