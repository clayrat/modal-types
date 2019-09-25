module Subset

import Data.List
%hide Prelude.Pairs.Subset

%access public export
%default total

elemMap : {x : a} -> {xs : List a} -> (f : a -> b) -> Elem x xs -> Elem (f x) (map f xs)
elemMap f  Here      = Here
elemMap f (There el) = There $ elemMap f el

Subset : (g : List a) -> (d : List a) -> Type
Subset {a} g d = {x : a} -> Elem x g -> Elem x d

subsetId : Subset g g
subsetId = id

subsetTrans : Subset g d -> Subset d t -> Subset g t
subsetTrans gd dt = dt . gd

nilSubset : Subset [] xs
nilSubset = absurd

ext : Subset g d -> Subset (b::g) (b::d)
ext _  Here      = Here
ext r (There el) = There (r el)

contract : Elem x d -> Subset (x::d) d
contract el  Here     = el
contract _  (There s) = s

permute : Subset (a::b::g) (b::a::g)
permute  Here              = There Here
permute (There  Here     ) = Here
permute (There (There el)) = There (There el)

pref : Subset g d -> Subset (s++g) (s++d)
pref {s=[]}    sub  el        = sub el
pref {s=s::ss} sub  Here      = Here
pref {s=s::ss} sub (There el) = There $ pref {s=ss} sub el

--

Subset2 : (g : List (List a)) -> (d : List (List a)) -> Type
Subset2 []      []      = ()
Subset2 []      (_::_ ) = Void
Subset2 (_::_ ) []      = Void
Subset2 (g::gs) (d::ds) = (Subset g d, Subset2 gs ds)

--Initial : (g : List (List a)) -> (d : List (List a)) -> Type
--Initial []      _       = ()
--Initial (_::_ ) []      = Void
--Initial (g::gs) (d::ds) = (Subset g d, Initial gs ds)
