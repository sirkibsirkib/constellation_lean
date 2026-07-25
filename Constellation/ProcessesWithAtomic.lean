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
  | atomic (p: Process)
deriving BEq


infix:85 "▸" => Process.seq
notation:max "▪" => Process.halt
infix:85 " ∣∣ " => Process.par

abbrev Holds := Finset Var

mutual
  inductive Exec: EndoRel (Process × Holds) where
    | add H v:
        Exec (Process.add v, H) (▪, insert v H)

    | rem H v:
        Exec (Process.rem v, H) (▪, H.erase v)

    | parBase H H' p:
        Exec (▪ ∣∣ p, H) (p, H')

    | parLift H p1 p1' p2:
        Exec (p1, H) (p1', H) →
        Exec (p1 ∣∣ p2, H) (p1' ∣∣ p2, H)

    | parCommute H p1 p1' p2 p2':
        Exec (p1 ∣∣ p2, H) (p1' ∣∣ p2', H) →
        Exec (p2 ∣∣ p1, H) (p2' ∣∣ p1', H)

    | atomic H H' p p2:
        -- atomic cannot take incremental steps!
        Completes (p, H) (▪, H') →
        Exec      (p.atomic ∣∣ p2, H) (p2, H')

    | seqBase H H' p:
        Exec (▪ ▸ p, H) (p, H')

    | seqStep H H' p1 p1' p2 :
        Exec (p1, H) (p1', H') →
        Exec (p1 ▸ p2, H) (p1' ▸ p2, H')


  inductive Completes: EndoRel (Process × Holds) where
    | intro p H H':
        Exec⋆     (p, H) (▪, H') →
        Completes (p, H) (▪, H')
end

theorem par_associates:
  ∀ (a b c a' b' c': Process) (H H': Holds),
    Exec ( a ∣∣(b ∣∣ c), H) (a' ∣∣(b' ∣∣ c'), H) →
    Exec ((a ∣∣ b)∣∣ c , H) ((a' ∣∣ b')∣∣ c', H)
:= by
  sorry

def norms_to p H H' :=
  Completes (p, H) (▪, H')
  ∧ ∀ Hx,
    Completes (p, H) (▪, Hx) →
    H' = Hx
