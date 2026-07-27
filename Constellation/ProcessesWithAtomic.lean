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

inductive Process (State: Type): Type where
  | halt
  | update (f: State → Option State)
  | atomic (p: Process State)
  | par    (p1 p2: Process State)
  | seq    (p1 p2: Process State)
  | choose (p1 p2: Process State)

infix:85 "\\" => Process.choose
infix:85 "▸" => Process.seq
notation:max "▪" => Process.halt

instance (State: Type): Mul (Process State) where
  mul := Process.par

example S: Process S := ▪
example S: Process S := ▪\▪


inductive Exec {State: Type}: EndoRel (Process State × State) where
  | update f σ σ':
      f σ = some σ' →
      Exec (Process.update f, σ) (▪, σ')

  | choose_left p1 p2 σ:
      Exec (p1 \ p2, σ) (p1, σ)

  | choose_comm p1 p2 σ:
      Exec (p2 \ p1, σ) (p1 \ p2, σ)

  | par_comm σ p1 p2:
      Exec (p1 * p2, σ) (p2 * p1, σ)

  | par_halt σ σ' p:
      Exec (▪ * p, σ) (p, σ')

  | par_left σ σ' p1 p1' p2:
      Exec (p1     , σ) (p1'     , σ') →
      Exec (p1 * p2, σ) (p1' * p2, σ')

  | atomic σ σ' p:
      -- if   `p` completes in any number of steps,
      -- then `p.atomic` completes in one step
      Exec⋆ (p       , σ) (▪, σ') →
      Exec  (p.atomic, σ) (▪, σ')

  | seq_base σ σ' p:
      -- Peel off preceding `▪ ▸`
      Exec (▪ ▸ p, σ) (p, σ')

  | seq_step σ σ' p1 p1' p2 :
      -- left of `▸` can step in-place, but right cannot.
      Exec (p1     , σ) (p1'     , σ') →
      Exec (p1 ▸ p2, σ) (p1' ▸ p2, σ')

abbrev completes {State: Type} (σ: State) (p: Process State) (σ': State) :=
  Exec⋆ (p, σ) (▪, σ')

namespace Process
  def norms_to {State: Type} (p: Process State) (σ σ1: State): Prop :=
      completes σ p σ1
      ∧ (∀ σ2,
          completes σ p σ2 →
          σ1 = σ2)
end Process

theorem halt_no_step {State: Type}:
  ∀ {σ: State} {x}, ¬ Exec (▪, σ) x
:= by
  intro _ _ h
  cases h

theorem halt_zero_steps {State: Type}:
  ∀ {σ: State} {x}, ¬ Exec⊹ (▪, σ) x
:= by
  intro _ _ h
  cases h <;> contradiction

theorem halt_norms {State: Type}:
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
      exact halt_zero_steps h_some_steps

def await (State: Type) (pred: State → Bool) :=
  Process.update (some ∘ Option.filter pred)

theorem choose_right {State: Type} p1 p2 (σ: State)
: Exec⊹ (p1 \ p2, σ) (p2, σ)
:= by
  apply TransClos.step (y := (p2\p1, σ))
      <;> repeat constructor

theorem exec_midstep {State: Type} {x z: Process State × State}
    (py: Process State)
    (σy: State)
    (h1: Exec⊹ x (py,σy))
    (h2: Exec⊹   (py,σy) z)
  :      Exec⊹ x         z
:= TransClos.midstep h1 h2

  example (State: Type) (σ: State) (p: Process State):
    completes σ (p\▪) σ
  := by
    constructor
    apply TransClos.step (y := ((▪\p), σ))
      <;> repeat constructor



inductive Run
    {Name: Type}
    {decls: Name → Process (List Name) }
: Rel (Process (List Name)) (List Name) where

  | init p:
      Run p []

  | exec p p' l':
      Run   p  [] →
      Exec (p, []) (p', l') →
      Run           p'  l'

  | unpend p n l:
      Run p (n :: l) →
      Run (p * decls n) l

def call (s: String): Process (List String) :=
  Process.update (some ∘ List.cons s)

def decls: String → Process (List String)
  | "main" => call "main"
  | _ => ▪

theorem eg1: Run (decls := decls) ▪ [] := Run.init ▪

theorem eg2: Run (decls := decls) (call "main") [] := Run.init _

theorem eg3: Exec (call "main", []) (▪, ["main"]) := by
  apply Exec.update
  simp

theorem eg4: Run (decls := decls) ▪ ["main"] := by
  apply Run.exec _ _ _ eg2 eg3

theorem eg5: Run (decls := decls) (call "main") [] := by
  sorry
