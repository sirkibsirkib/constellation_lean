import Constellation.ProcessesWithAtomic

abbrev Name := String

abbrev Call := Name
abbrev State := List Name

instance: Sig where
  Update := Call
  State  := State
  update σ n := n :: σ

inductive Reach
    {decls: Name → Process }
: Rel Process State where

  | init p:
      Reach p []

  | exec p p' l':
      Reach   p  [] →
      Exec (p, []) (p', l') →
      Reach           p'  l'

  | unpend p n l:
      Reach p (n :: l) →
      Reach (p * decls n) l

def call: String → Process := Process.update

def decls: String → Process
  | "main" => call "main"
  | _ => ▪

section Examples

  abbrev Reach' := Reach (decls := decls)

  example: Reach' ▪ [] := Reach.init ▪

  example: Reach' (call "main") [] := Reach.init _

  example: Reach' ▪ ["main"] := by
    apply Reach.exec (call "main")
    . constructor
    . constructor ; rfl

end Examples
