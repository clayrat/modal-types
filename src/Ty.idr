module Ty

%default total

public export
data Ty = A
        | Imp Ty Ty
        | Box Ty

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp