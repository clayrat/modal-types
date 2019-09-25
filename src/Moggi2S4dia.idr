module Moggi2S4dia

import Data.List
import Moggi as MG
import Dual.S4dia as S4
import Subset

%default total
%access public export

-- `Box a` denotes stable values, that is, values that survive effects
-- `Dia a` denotes computations returning values of type `a`
-- In the monadic metalanguage, all values are stable, so a function `a~>b` accepts a stable value of type `a` and returns a value of type `b`
-- `M a` is a computation which returns a stable value of type `a`

embedTy : MG.Ty -> S4.Ty
embedTy  A        = A
embedTy (Imp a b) = Imp (Box (embedTy a)) (embedTy b)
embedTy (M a)     = Dia $ Box $ embedTy a

mutual
  embedTm : MG.Term g a -> S4.Term (map embedTy g) d (embedTy a)
  embedTm              (Var e)   = MVar $ elemMap embedTy e
  embedTm {a=a~>b} {d} (Lam t)   = Lam $ Letbox (Var Here) (embedTm {d=Box (embedTy a)::d} t)
  embedTm              (App u v) = App (embedTm u) (Shut $ embedTm v)
  embedTm              (Val t)   = Pure (embedPTm t)

  embedPTm : MG.PTerm g a -> S4.PTerm (map embedTy g) d (Box (embedTy a))
  embedPTm (Wrap t)         = Wrap $ Shut (embedTm t)
  embedPTm (Letval {a} u v) = Letdia (embedTm u) (PLetbox (Var Here) (embedPTm {d=[Box (embedTy a)]} v))
