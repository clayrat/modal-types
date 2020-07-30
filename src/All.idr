module All

import Data.List.Quantifiers
%default total

export
mapPredicate : (f : {x : t} -> p x -> q x) -> All p l -> All q l
mapPredicate f [] = []
mapPredicate f (p::pl) = f p :: mapPredicate f pl