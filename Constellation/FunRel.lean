
abbrev Rel     (α β: Sort u) := α → β → Prop
abbrev EndoRel (α  : Sort u) := Rel α α

abbrev EndoFun (α: Sort u) := α → α

inductive ReflClos {α: Sort u} (R: EndoRel α): EndoRel α where
  | refl x  : ReflClos R x x
  | base x y:          R x y →
              ReflClos R x y


inductive TransClos {α: Sort u} (R: EndoRel α): EndoRel α where
  | base x y  :           R x y →
                TransClos R x y
  | step x y z: TransClos R x y →
                          R   y z →
                TransClos R   y z

theorem tr_rt {α: Sort u}:
  ∀ (R: EndoRel α) (x y: α),
    ReflClos (TransClos R) x y
    ↔
    TransClos (ReflClos R) x y
:= by
  intro R x y
  constructor
  . intro h
    cases h
    . constructor
      constructor
    . next h =>
      cases h
      . constructor
        constructor
        assumption
      . constructor
        constructor
        assumption
  . intro h
    cases h
    . next h =>
      cases h
      . constructor
      . constructor
        constructor
        assumption
    . next _ _ h =>
      cases h
      . constructor
      . constructor
        constructor
        assumption

notation:max R "⊹" => TransClos R
notation:max R "⋆" => ReflClos (R⊹)

namespace List
  def any_Prop: List Prop → Prop :=
    foldr Or False
end List
