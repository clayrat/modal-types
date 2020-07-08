module Kripke.Contextual.Ty

%default total
%access public export

data Ty = A
        | Imp Ty Ty
        | Box (List Ty) Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp