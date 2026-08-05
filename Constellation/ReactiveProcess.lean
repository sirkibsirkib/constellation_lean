import Constellation.ProcessesWithAtomic
import Constellation.AbstractReactive

abbrev Name := String
abbrev Fakt := String

instance: Sig where
  Update := Name
  State  := List Name
  update σ n := n :: σ

instance: Sig2 where
  Fact   := Fakt
  Effect := Process

def State := Finset Name × Finset Fakt

inductive Reach
    {decls: Name → List ReactiveRule }
: State → Prop where

  | step n:
      Reach ({n}, ∅)

  | unpend p n l:
      Reach p (n :: l) →
      Reach (p * decls n) l

  | exec (n: Name) N F:
      Reach (N, F) →
      n ∈ N →
      Reach (N.erase n, List.foldr Process.par F (trig_all (decls n)))
