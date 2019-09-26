module Split

%access public export
%default total

data Split : List a -> List a -> List a -> Type where
  Nil   : Split [] [] []
  ConsR : Split xs ls rs -> Split (x::xs)     ls (x::rs)
  ConsL : Split xs ls rs -> Split (x::xs) (x::ls)    rs

splitLeft : Split l l []
splitLeft {l=[]}   = Nil
splitLeft {l=_::_} = ConsL splitLeft

splitRight : Split l [] l
splitRight {l=[]}   = Nil
splitRight {l=_::_} = ConsR splitRight

splitLen : Split l ll lr -> length l = length ll + length lr
splitLen                  Nil      = Refl
splitLen {ll} {lr=_::rs} (ConsR s) =
  rewrite plusAssociative (length ll) 1 (length rs) in
  rewrite plusCommutative (length ll) 1 in
  cong $ splitLen s
splitLen                 (ConsL s) = cong $ splitLen s