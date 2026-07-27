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

inductive Process (State: Type): Type where
  | halt
  | update (f: State → Option State)
  | par (p1 p2: Process State)
  | seq (p1 p2: Process State)
  | atomic (p: Process State)


infix:85 "▸" => Process.seq
notation:max "▪" => Process.halt
infix:85 " ∣∣ " => Process.par

abbrev Holds := Finset Var

mutual
  inductive Exec {State: Type}: EndoRel (Process State × State) where
    | update f σ σ':
        f σ = some σ' →
        Exec (Process.update f, σ) (▪, σ')

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


  inductive Completes {State: Type}: EndoRel (Process State × State) where
    | intro p σ σ':
        Exec⋆     (p, σ) (▪, σ') →
        Completes (p, σ) (▪, σ')
end

theorem par_associates (State: Type):
  ∀ (a b c a' b' c': Process State) (σ σ': State),
    Exec ( a ∣∣(b ∣∣ c), σ) (a' ∣∣(b' ∣∣ c'), σ') →
    Exec ((a ∣∣ b)∣∣ c , σ) ((a' ∣∣ b')∣∣ c', σ')
:= by
  sorry

def norms_to (State: Type) :=
  ∀ p (σ σ': State),
    Completes (p, σ) (▪, σ')
    ∧ ∀ σ'',
        Completes (p, σ') (▪, σ'') →
        σ' = σ''
