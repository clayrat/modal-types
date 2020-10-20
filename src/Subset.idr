module Subset

import Data.List
import Data.List.Quantifiers
%hide Prelude.Pairs.Subset
%default total

export
elemMap : (f : a -> b) -> Elem x xs -> Elem (f x) (map f xs)
elemMap f  Here      = Here
elemMap f (There el) = There $ elemMap f el

public export
Subset : (g : List a) -> (d : List a) -> Type
Subset {a} g d = {x : a} -> Elem x g -> Elem x d

subsetId : Subset g g
subsetId = id

subsetTrans : Subset g d -> Subset d t -> Subset g t
subsetTrans gd dt = dt . gd

export
nilSubset : Subset [] xs
nilSubset = absurd

export
ext : Subset g d -> Subset (b::g) (b::d)
ext _  Here      = Here
ext r (There el) = There (r el)

export
contract : Elem z d -> Subset (z::d) d
contract el  Here     = el
contract _  (There s) = s

export
permute : Subset (a::b::g) (b::a::g)
permute  Here              = There Here
permute (There  Here     ) = Here
permute (There (There el)) = There (There el)

export
pref : {s : List t} -> Subset g d -> Subset (s++g) (s++d)
pref {s=[]}    sub  el        = sub el
pref {s=s::ss} sub  Here      = Here
pref {s=s::ss} sub (There el) = There $ pref {s=ss} sub el

public export
Pairwise : (a -> a -> Type) -> List a -> List a -> Type
Pairwise r []      []      = ()
Pairwise r []      (_::_ ) = Void
Pairwise r (_::_ ) []      = Void
Pairwise r (g::gs) (d::ds) = (r g d, Pairwise r gs ds)

export
pairwiseApply : Pairwise Subset ph ps -> Any (Elem a) ph -> Any (Elem a) ps
pairwiseApply {ps=_::_} (s,_ ) (Here el)   = Here $ s el
pairwiseApply {ps=[]}       _  (There _) impossible
pairwiseApply {ps=_::_} (_,pw) (There ael) = There $ pairwiseApply pw ael
