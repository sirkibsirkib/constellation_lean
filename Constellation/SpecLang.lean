import Mathlib.Logic.Relation
open Relation

def Rel α := α → α → Prop

def confluent {α} (R: Rel α): Prop :=
  ∀ x y₁ y₂: α,
    ReflTransGen R x y₁ →
    ReflTransGen R x y₂ →
    Join R y₁ y₂

/-
The essential
-/
structure SpecLang where
  (Spec State Input Output: Type)
  meaning: Spec → State
  advance: State → Input → Option (Output × State)
  compose: State → State → Option State

namespace SpecLang
  abbrev Step (s: SpecLang): Type := s.Input
  abbrev Trace (s: SpecLang): Type := List s.Step
end SpecLang
