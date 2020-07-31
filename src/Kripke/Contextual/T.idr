module Kripke.Contextual.T

import Data.List
import Data.List.Quantifiers
import Ty.Contextual

%default total
%access public export

data Pref : a -> List a -> a -> List a -> Type where
  HereP  : Pref x xs    x  xs
  ShiftP : Pref x xs y (x::xs)

data Term : List (List Ty) -> List Ty -> Ty -> Type where
  Var  : Elem a g -> Term ph g a
  Lam  : Term ph (a::g) b -> Term ph g (a~>b)
  App  : Term ph g (a~>b) -> Term ph g a -> Term ph g b
  Shut : Term (g::ph) d a -> Term ph g (Box d a)
  Open : Pref g ph d ps -> Term ph g (Box s a) -> {auto e : All (Term ps d) s} -> Term ps d a

weak : Term ph g (Box [b] a ~> Box [b,c] a)
weak = Lam $ Shut $ Open ShiftP (Var Here) --{e=[Var Here]}

contract : Term ph g (Box [b,b] a ~> Box [b] a)
contract = Lam $ Shut $ Open ShiftP (Var Here) -- {e=[Var Here, Var Here]}

exch : Term ph g (Box [b,c] a ~> Box [c,b] a)
exch = Lam $ Shut $ Open ShiftP (Var Here) -- {e=[Var $ There Here, Var Here]}

comp : Term ph g (Box [a] b ~> Box [a] (Box [b] c) ~> Box [a] c)
comp = Lam $ Lam $
       Shut $ Open HereP
             (Open ShiftP (Var Here)) -- {e=[Var Here]}
             {e=[Open ShiftP (Var $ There Here)]} --{e=[Var Here]}

eval : Term ph g (Box [] a ~> a)
eval = Lam $ Open HereP (Var Here) -- {e=[]}
