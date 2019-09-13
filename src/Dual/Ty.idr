module Dual.Ty

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | Conj Ty Ty
        | Box Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

infixr 4 /\
(/\) : Ty -> Ty -> Ty
(/\) = Imp