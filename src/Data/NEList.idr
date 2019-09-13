module Data.NEList

import Data.Vect

%default total
%access public export

infixr 5 +:
record NEList (a : Type) where
  constructor (+:)
  head : a
  tail : List a

nelInjective : (h1 +: t1) = (h2 +: t2) -> (h1=h2, t1=t2)
nelInjective Refl = (Refl, Refl)

toList : NEList a -> List a
toList xxs = head xxs :: tail xxs

fromList : List a -> Maybe (NEList a)
fromList []        = Nothing
fromList (x :: xs) = Just (x +: xs)

length : NEList a -> Nat
length = S . length . tail

toVect : (nel : NEList a) -> Vect (length nel) a
toVect (h +: t) = h :: Vect.fromList t

cons : a -> NEList a -> NEList a
cons x xxs = x +: toList xxs

consopt : a -> Maybe (NEList a) -> NEList a
consopt x mxs = x +: lowerMaybe (map toList mxs)

singleton : a -> NEList a
singleton x = x +: []

(++) : NEList a -> NEList a -> NEList a
(++) (x +: xs) ys = x +: (xs ++ NEList.toList ys)

Show a => Show (NEList a) where
  show = show . toList

Eq a => Eq (NEList a) where
  (x +: xs) == (y +: ys) = x == y && xs == ys

Semigroup (NEList a) where
   (<+>) = (++)

Functor NEList where
  map f (x +: xs) = (f x) +: (f <$> xs)

Applicative NEList where
  pure = singleton
  (f +: fs) <*> (x +: xs) = (f x) +: ((f <$> xs) ++ (fs <*> (x::xs)))

Monad NEList where
  (x +: xs) >>= f =
    let
      (y +: ys) = f x
      zs = xs >>= toList . f
     in
    y +: (ys ++ zs)

Foldable NEList where
  foldl c n xxs = foldl c n (NEList.toList xxs)
  foldr c n xxs = foldr c n (NEList.toList xxs)

foldl1 : (a -> a -> a) -> NEList a -> a
foldl1 c (x +: xs) = foldl c x xs

foldr1 : (a -> a -> a) -> NEList a -> a
foldr1 c (x +: xs) = go x xs
  where
  go : a -> List a -> a
  go x []        = x
  go x (y :: ys) = c x (go y ys)

foldrf : (a -> b -> b) -> (a -> b) -> NEList a -> b
foldrf c s (x +: xs) = go x xs
  where
  go x []        = s x
  go x (y :: ys) = c x (go y ys)

Traversable NEList where
  traverse f (x +: xs) = [| (f x) +: (traverse f xs) |]
