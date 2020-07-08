module Kripke.Ty

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | Box Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp