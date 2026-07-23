import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Constellation.FunRel
import Std
open Std

abbrev Var := String
inductive Process: Type where
  | halt
  | add (v: Var)
  | rem (v: Var)
  | par (p1 p2: Process)
  | seq (p1 p2: Process)
  | atomic (p: Process)
  | ite (v: Var) (t e: Process)
deriving BEq

abbrev Holds := Finset Var

abbrev Pending := List Process

-- Whoops I am trying to define a paradox
inductive Exec: EndoRel (Pending × Holds) where
  | step P H p:
      p ∈ P →
      Exec (P, H) (P.erase p, H)

  | atom P H H' p:
      p.atomic ∈ P →
      Bigstep Exec ([p], H) ([], H') →
      Exec (P, H) (P.erase p.atomic, H')
