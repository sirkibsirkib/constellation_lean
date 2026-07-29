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

inductive Process (State: Type): Type where
  | done
  | update (f: State → Option State)
  | atomic (p: Process State)
  | par    (p1 p2: Process State)
  | seq    (p1 p2: Process State)
  | choose (p1 p2: Process State)

def await (State: Type) (pred: State → Bool) :=
  Process.update (some ∘ Option.filter pred)

-- Shorter notations for constructing processes
infix:85 "\\" => Process.choose
infix:85 "▸" => Process.seq
notation "▪" => Process.done
notation "⸨" p "⸩" => Process.atomic p
instance (State: Type): Mul (Process State) where
  mul := Process.par

section ProcessExamples

  variable
    (State: Type)
    (p q r: Process State)

  example := p * ▪ \ q
  example := (p ▸ r ) ▸ (q ▸ r)
  example := ⸨p * p * q ▸⸨r ▸ ▪⸩⸩ ▸ ▪

end ProcessExamples

/-
Operational semantics:
  a relation over Process-State pairs
-/
inductive Exec {State: Type}: EndoRel (Process State × State) where
  | update f σ σ':
      f σ = some σ' →
      Exec (Process.update f, σ) (▪, σ')

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

abbrev completes {State: Type} (σ: State) (p: Process State) (σ': State) :=
  Exec⋆ (p, σ) (▪, σ')

namespace Process
  def norms_to {State: Type} (p: Process State) (σ σ1: State): Prop :=
      completes σ p σ1
      ∧ (∀ σ2,
          completes σ p σ2 →
          σ1 = σ2)
end Process

theorem done_no_step {State: Type}:
  ∀ {σ: State} {x}, ¬ Exec (▪, σ) x
:= by
  intro σ ⟨p, σ'⟩ h
  cases h

theorem done_zero_steps {State: Type}:
  ∀ {σ: State} {x}, ¬ Exec⊹ (▪, σ) x
:= by
  intro _ _ h
  cases h <;> contradiction

theorem done_norms {State: Type}:
  ∀ (σ: State),
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

theorem choose_right {State: Type} p1 p2 (σ: State)
: Exec⊹ (p1 \ p2, σ) (p2, σ)
:= by
  apply TransClos.step (y := (p2\p1, σ))
      <;> repeat constructor

  example (State: Type) (σ: State) (p: Process State):
    completes σ (p\▪) σ
  := by
    constructor
    apply TransClos.step (y := ((▪\p), σ))
      <;> repeat constructor
