
abbrev Pred    (α: Sort u) := α → Prop
abbrev EndoRel (α: Sort u) := α → Pred α

abbrev EndoFun (α: Sort u) := α → α

def ReflClos α: EndoFun (EndoRel α) :=
  λ (R: EndoRel α) (x y: α) ↦ x = y ∨ R x y

def TransClos α: EndoFun (EndoRel α) :=
  λ (R: EndoRel α) (x y: α) ↦
    R x y ∨ ∃ z, R x z ∧ R z y

def TrClos {α}: EndoFun (EndoRel α) :=
  λ R ↦ ReflClos α (TransClos α R)

def RtClos {α}: EndoFun (EndoRel α) :=
  λ R ↦ TransClos α (ReflClos α R)

theorem tr_iff_rt {α}:
  ∀ (R: EndoRel α) x y,
    TrClos R x y ↔ RtClos R x y := by
  intro R x y
  simp [TrClos, RtClos, ReflClos, TransClos]
  constructor
  . intro h
    rcases h with _ | _ | h
    . subst x
      left
      left
      rfl
    . left
      right
      assumption
    . right
      obtain ⟨z, ⟨P1, P2⟩⟩ := h
      exists z
      constructor
      . assumption
      . right
        assumption
  . intro h
    rcases h with (h | h) | h
    . subst x
      left
      rfl
    . right
      left
      assumption
    . obtain ⟨z, ⟨P1, P2⟩⟩ := h
      right
      rcases P2 with P2 | P2
      . subst z
        left
        assumption
      . right
        exists z

notation R " ⋆ " => TrClos R

namespace List
  def any_Prop: List Prop → Prop :=
    foldr Or False
end List
