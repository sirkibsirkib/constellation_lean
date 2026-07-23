import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Constellation.PopWhere
import Constellation.FunRel
import Std
open Std

abbrev Atom := Char

abbrev PersistentName := String
abbrev  EphemeralName := String

abbrev PersistentNames := Finset PersistentName

inductive Name where
  | Persistent: PersistentName → Name
  | Ephemeral :  EphemeralName → Name

inductive Process: Type where
  | par   (p₁ p₂: Process)
  | trig  (n: EphemeralName)
  | add   (n: PersistentName)
  | rem   (n: PersistentName)
  | later (p: Process)
  | halt
deriving BEq

structure ReactiveRule: Type where
  name  : EphemeralName
  guard : PersistentNames
  effect: List Process

structure DeclRule: Type where
  antecedents: Finset PersistentName
  consequent : PersistentName

structure Program: Type where
  decl: Finset DeclRule
  reac: List ReactiveRule


namespace DeclRule

  def can_fire (r: DeclRule) (σ: Finset PersistentName): Prop :=
      r.consequent  ∉ σ
    ∧ r.antecedents ⊆ σ

  def fire (r: DeclRule) (σ: Finset PersistentName): Finset PersistentName :=
    insert r.consequent σ

  def step (r: DeclRule): EndoRel PersistentNames :=
    λ σ σ' ↦ r.can_fire σ ∧ r.fire σ = σ'

  def reach (r: DeclRule): EndoRel PersistentNames :=
    r.step ⋆

  def any_reach (l: List DeclRule): EndoRel PersistentNames :=
    λ σ σ' ↦
      ∃ (R: EndoRel PersistentNames),
          R ∈ l.map reach
        ∧ R σ σ'

end DeclRule

abbrev Pending    := List Process
abbrev Persisting := PersistentNames

namespace Program
  def trigger_all (p: Program) (trig: EphemeralName) (per: Persisting): Pending :=
    p.reac
      |>.filter (·.name = trig)
      |>.filter (·.guard ⊆ per)
      |>.flatMap (ReactiveRule.effect)
end Program

namespace Process
  def exec (p: Process): EndoFun (Pending × Persisting) :=
    λ (pen, per) ↦ match p with
      | par   p₁ p₂ => (p₁ :: p₂ :: pen, per)
      | trig  n     => sorry
      | add   n     => sorry
      | rem   n     => sorry
      | later p     => sorry
      | halt        => sorry
end Process

-- Synchronous semantics
inductive Runto {p: Program}: Rel Pending Persisting where
  | init: Runto ∅ ∅
  | fire_where (trig: EphemeralName) pen per:
      Runto pen per →
      Runto (pen ++ p.trigger_all trig per) per
  | eval_where (p: Process) pen per:
      p ∈ pen →
      Runto pen per →
      Runto (pen.erase p) per


namespace Process
  def seq (p₁ p₂: Process) := p₁.par p₂.later

  def seq_list: List Process → Process
    | [] => Process.halt
    | p :: l => p.seq (seq_list l)
end Process

instance: Coe (List Process) Process where
  coe := Process.seq_list

notation:max a " ∣∣ " b => Process.par a b

example (p₁ p₂ p₃: Process): Process := [p₁ ∣∣ p₂, p₃ ∣∣ [p₁, p₃] ∣∣ p₂]
