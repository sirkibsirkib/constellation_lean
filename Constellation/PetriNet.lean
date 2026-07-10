import Constellation.SpecLang

structure Signature where
  new::
  place: Type
  place_type: place → Type

def eg_sig: Signature :=
  Signature.new Nat
    λ
    | 0 => Unit
    | _ => Bool

namespace Signature
  variable (s: Signature)
  def Mapping := ∀ (p: s.place), s.place_type p
end Signature

-- Define the mapping as a function of place.
-- explicitly match "p" and return in each case
-- a value of the place's type.
example: eg_sig.Mapping :=
  λ (p: eg_sig.place) ↦
    match p with
    | Nat.zero => ()
    | Nat.succ _ => true

-- Collapse "λ (p: eg_sig.place) ↦ match p with" into "λ".
-- I love this!
example: eg_sig.Mapping := λ
  | Nat.zero => ()
  | Nat.succ _ => true

-- Use "intro p" to build a lambda in proof mode.
-- "match _ with" works just as in term mode.
-- ".zero" abbreviates "Nat.zero" in this context
-- "exact" exits proof mode again by closing with a term
example: eg_sig.Mapping := by
  intro p; match p with
  | .zero   => exact ()
  | .succ _ => exact true

-- "cases p" with "." lets lean deconstruct the case.
-- But now the variable is inaccessible in the 2nd case.
-- In this case we do not need it so it is fine!
example: eg_sig.Mapping := by
  intro p; cases p
  . exact ()
  . exact true


-- As above, but we give it a name via a tactic!
example: eg_sig.Mapping := by
  intro p; cases p
  . exact ()
  . rename_i n; show Bool; clear n; exact true


-- As above, but we then discard "n".
-- But first we must collapse "eg_sig.place_type n.succ"
-- into "Bool" (via "show") so that "n" can be discarded.
example: eg_sig.Mapping := by
  intro p; cases p
  . exact ()
  . rename_i n; show Bool; clear n; exact true

-- Here is another wacky way to intro and destruct at once.
example: eg_sig.Mapping := by
  rintro (_ | n)
  . exact ()
  . exact true
