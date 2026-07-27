
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
  | step x y z:           R x y →
                TransClos R   y z →
                TransClos R x   z

notation:max R "⊹" => TransClos R
notation:max R "⋆" => ReflClos  R⊹

namespace TransClos

  theorem midstep {α: Sort u} {R: EndoRel α} {x y z: α}
    (h1: R⊹ x y)
    (h2: R⊹   y z)
  :      R⊹ x   z
  := by
    induction h1
    . case base a b h =>
      exact TransClos.step _ _ _ h h2
    . case step a b c h1 h3 ih =>
      exact TransClos.step _ _ _ h1 (ih h2)

end TransClos



namespace List
  def any_Prop: List Prop → Prop :=
    foldr Or False
end List
