import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Constellation.PopWhere
import Constellation.FunRel
import Std
open Std

abbrev Atom := Char

abbrev PersistentName := String
abbrev  EphemeralName := String

inductive Name where
  | Persistent: PersistentName → Name
  | Ephemeral :  EphemeralName → Name

inductive Process: Type where
  | par  (p₁ p₂: Process)
  | seq  (p₁ p₂: Process)
  | trig (n: EphemeralName)
  | add  (n: PersistentName)
  | rem  (n: PersistentName)

structure ReactiveRule: Type where
  name  : EphemeralName
  guard : PersistentName
  effect: Process

structure DeclRule: Type where
  antecedents: Finset PersistentName
  consequent : PersistentName

structure Program: Type where
  decl: Finset DeclRule
  reac: Finset ReactiveRule

abbrev Pending := List Process
abbrev Persisting := Finset PersistentName

abbrev PersistentNames := Finset PersistentName

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
    λ σ σ' ↦ ∃R,
        R ∈ l.map reach
      ∧ R σ σ'

end DeclRule
