module All

import Data.List.Quantifiers
%hide Prelude.Pairs.Subset

%access public export
%default total

mapPointwise : (f : {x : t} -> p x -> q x) -> All p l -> All q l
mapPointwise f [] = []
mapPointwise f (p::pl) = f p :: mapPointwise f pl