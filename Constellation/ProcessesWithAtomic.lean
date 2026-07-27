import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Constellation.FunRel
import Std
open Std

/-
Let's try an experiment.

Let's ignore rules entirely for now.
Let's just focus on tσe matter of atomicity.
-/

inductive Process (State: Type): Type where
  | halt
  | update (f: State → Option State)
  | atomic (p: Process State)
  | par    (p1 p2: Process State)
  | seq    (p1 p2: Process State)
  | choose (p1 p2: Process State)

instance (State: Type): Mul (Process State) where
  mul := Process.par

infix:85 "\\" => Process.choose
infix:85 "▸" => Process.seq
notation:max "▪" => Process.halt

def await (State: Type) (pred: State → Bool) :=
  Process.update (some ∘ Option.filter pred)

mutual
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

    | atomic σ σ' p p2:
        -- if σ --p->| σ'
        Completes (p            , σ) (▪ , σ') →
        Exec      (p.atomic * p2, σ) (p2, σ')

    | seq_base σ σ' p:
        Exec (▪ ▸ p, σ) (p, σ')

    | seq_step σ σ' p1 p1' p2 :
        Exec (p1     , σ) (p1'     , σ') →
        Exec (p1 ▸ p2, σ) (p1' ▸ p2, σ')

  inductive Completes {State: Type}: EndoRel (Process State × State) where
    | intro p σ σ':
        Exec⊹     (p, σ) (▪, σ') →
        Completes (p, σ) (▪, σ')
end

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


  local notation:min σ "—" p "⇥" σ' => Completes (p, σ) (▪ , σ')
  local notation:min x "↠" y => Exec⋆ x y

  example (State: Type) (σ: State) (p: Process State):
    σ —p\▪⇥ σ
  := by
    constructor
    apply TransClos.step (y := ((▪\p), σ))
      <;> repeat constructor


theorem par_assoc (State: Type):
  ∀ (a b c: Process State) (σ: State),
    (a * (b * c), σ) ↠ ((a * b) * c, σ)
:= by
  intro a b c σ
  sorry

def norms_to (State: Type) :=
  ∀ (p: Process State) (σ σ': State),
    Completes (p, σ) (▪, σ')
    ∧ ∀ σ'',
        Completes (p, σ') (▪, σ'') →
        σ' = σ''

abbrev Var  := String
abbrev Name := String

inductive Update where
  | Add  (v: Var)
  | Rem  (v: Var)
  | Call (n: Name)

abbrev Holds := Finset Var
abbrev ProcDecls := Name → Process Holds
