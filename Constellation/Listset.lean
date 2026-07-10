import Mathlib.Data.Finset.Basic

theorem q: (∅ : Finset Nat) ⊆ ∅ := by
  apply Finset.Subset.refl
