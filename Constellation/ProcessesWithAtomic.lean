import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Constellation.FunRel
import Std
open Std

/-
Let's try another approach:
1. lay a process-oriented groundwork.
  Focus on atomicity, sequence, concurrency, etc.
2. build a layer of decl / reactive rules atop.
-/

-------------------------

class Sig where
  Update: Type
  State: Type
  update: State → Update → Option State

variable [Sig]

inductive Process: Type where
  | done
  | update (u: Sig.Update)
  | atomic (p: Process)
  | par    (p1 p2: Process)
  | seq    (p1 p2: Process)
  | choose (p1 p2: Process)

-- Shorter notations for constructing processes
infix:85 "\\" => Process.choose
infix:85 "▸" => Process.seq
notation "▪" => Process.done
notation "⸨" p "⸩" => Process.atomic p

instance: Mul Process where
  mul := Process.par

section ProcessExamples
  variable (p q r: Process)
  example := p * ▪ \ q
  example := (p ▸ r ) ▸ (q ▸ r)
  example := ⸨p * p * q ▸⸨r ▸ ▪⸩⸩ ▸ ▪
end ProcessExamples

/-
Operational semantics:
  a relation over Process-State pairs
-/
inductive Exec: EndoRel (Process × Sig.State) where
  | update u σ σ':
      Sig.update σ u = some σ' →
      Exec (Process.update u, σ) (▪, σ')

  | seq_base σ σ' p:
      -- Peel off preceding `▪ ▸`
      Exec (▪ ▸ p, σ) (p, σ')

  | seq_step σ σ' p1 p1' p2 :
      -- left of `▸` can step in-place, but right cannot.
      Exec (p1     , σ) (p1'     , σ') →
      Exec (p1 ▸ p2, σ) (p1' ▸ p2, σ')

  | choose_left p1 p2 σ:
      Exec (p1 \ p2, σ) (p1, σ)

  | choose_comm p1 p2 σ:
      Exec (p2 \ p1, σ) (p1 \ p2, σ)

  | par_comm σ p1 p2:
      Exec (p1 * p2, σ) (p2 * p1, σ)

  | par_done σ σ' p:
      Exec (▪ * p, σ) (p, σ')

  | par_left σ σ' p1 p1' p2:
      Exec (p1     , σ) (p1'     , σ') →
      Exec (p1 * p2, σ) (p1' * p2, σ')

  | atomic σ σ' p:
      -- if   `p` completes after any number of steps,
      -- then `p.atomic` completes in one step
      Exec⋆ (p       , σ) (▪, σ') →
      Exec  (p.atomic, σ) (▪, σ')

abbrev completes σ p σ' := Exec⋆ (p, σ) (▪, σ')

namespace Process
  def norms_to (p: Process) (σ σ1: Sig.State): Prop :=
      completes σ p σ1
      ∧ (∀ σ2,
          completes σ p σ2 →
          σ1 = σ2)
end Process

theorem done_no_step:
  ∀ {σ: Sig.State} {x}, ¬ Exec (▪, σ) x
:= by
  intro σ ⟨p, σ'⟩ h
  cases h

theorem done_zero_steps:
  ∀ {σ: Sig.State} {x}, ¬ Exec⊹ (▪, σ) x
:= by
  intro _ _ h
  cases h <;> contradiction

theorem done_norms:
  ∀ (σ: Sig.State),
    ▪.norms_to σ σ
:= by
  intro σ
  constructor -- ∧
  · constructor
  · intro σ2 h
    unfold completes at h
    cases h
    . rfl
    . next h_some_steps =>
      exfalso
      exact done_zero_steps h_some_steps

theorem choose_right p1 p2 (σ: Sig.State)
: Exec⊹ (p1 \ p2, σ) (p2, σ)
:= by
  apply TransClos.step (y := (p2\p1, σ))
      <;> repeat constructor

  example (σ: Sig.State) (p: Process):
    completes σ (p\▪) σ
  := by
    constructor
    apply TransClos.step (y := ((▪\p), σ))
      <;> repeat constructor
