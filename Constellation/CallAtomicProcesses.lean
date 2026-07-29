import Constellation.ProcessesWithAtomic

inductive Reach
    {Name: Type}
    {decls: Name → Process (List Name) }
: Rel (Process (List Name)) (List Name) where

  | init p:
      Reach p []

  | exec p p' l':
      Reach   p  [] →
      Exec (p, []) (p', l') →
      Reach           p'  l'

  | unpend p n l:
      Reach p (n :: l) →
      Reach (p * decls n) l

def call (s: String): Process (List String) :=
  Process.update (some ∘ List.cons s)

def decls: String → Process (List String)
  | "main" => call "main"
  | _ => ▪

section Examples

  abbrev Reach' := Reach (decls := decls)

  example: Reach' ▪ [] := Reach.init ▪

  example: Reach' (call "main") [] := Reach.init _

  example: Reach' ▪ ["main"] := by
    apply Reach.exec (call "main")
    . constructor
    . constructor
      unfold Function.comp
      rfl

end Examples

-- Did not ultimately need this, turns out
theorem exec_midstep {State: Type} {x z: Process State × State}
    (py: Process State)
    (σy: State)
    (h1: Exec⊹ x (py,σy))
    (h2: Exec⊹   (py,σy) z)
  :      Exec⊹ x         z
:= TransClos.midstep h1 h2
