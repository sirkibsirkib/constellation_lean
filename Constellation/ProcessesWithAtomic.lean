import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Constellation.FunRel
import Std
open Std

/-
Let's try an experiment.

Let's ignore rules entirely for now.
Let's just focus on the matter of atomicity.
-/

abbrev Var := String

inductive Process: Type where
  | halt
  | add (v: Var)
  | rem (v: Var)
  | par (p1 p2: Process)
  | seq (p1 p2: Process)
  -- | ite (v: Var) (t e: Process)
deriving BEq


infix:85 "▸" => Process.seq
notation:max "▪" => Process.halt
infix:85 "∣∣" => Process.par

abbrev Holds := Finset Var

abbrev Pending := List Process

mutual
  inductive Exec: EndoRel (Pending × Holds) where
    | halt P H:
        Exec (▪ :: P, H) (P, H)

    | add P H v:
        Process.add v ∈ P →
        Exec (Process.add v :: P, H) (P, insert v H)

    | rem P H v:
        Exec (Process.rem v :: P, H) (P, H.erase v)

    | par P H p1 p2:
        p1 ∣∣ p2 ∈ P →
        Exec (p1 ∣∣ p2 :: P, H) (p1 :: p2 :: P, H)

    | seq P H H' p1 p2:
        Completes ([p1], H) ([], H') →
        Exec      (p1 ▸ p2 :: P, H) (p2 :: P, H')


  inductive Completes: EndoRel (Pending × Holds) where
    | intro P H H':
        Exec⋆     (P, H) ([], H') →
        Completes (P, H) ([], H')
end

theorem completes_empty:
  ∀ P H P' H',
    Completes (P,H) (P',H') →
    P'=[]
:= by
  intro _ _ _ _ h
  cases h
  rfl

theorem empty_completes (H: Holds):
  ∃ E, Completes ([], H) E
:= by
  exists ([], H)
  constructor
  constructor

namespace Process
  abbrev later  (p: Process): Process := ▪ ▸ p
  abbrev atomic (p: Process): Process := p ▸ ▪

end Process

theorem just_halt_completes: ∀ H, Completes ([▪], H) ([], H)
:= by
  intro _
  repeat constructor


theorem p_iff_p_later:
  ∀ (P P': Pending) (H H': Holds) (p: Process),
    Completes (p :: P, H) (P', H')
    ↔
    Completes (p.later :: P, H) (P', H')
:= by
  intro P P' H H' p
  constructor
  . intro h
    cases h
    constructor
    rename_i h
    cases h
    rename_i h
    constructor
    cases h
    . rename_i h
      cases h
      . unfold Process.later
        have q := just_halt_completes H
        have r := Exec.seq [] _ _ _ ▪ q

        right
        . sorry
        . sorry
        . sorry
      . sorry
      . sorry
    . sorry
  . intro h
    cases h
    rename_i h
    constructor
    sorry
