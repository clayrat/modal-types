module Ty.Dia

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | Box Ty
        | Dia Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp