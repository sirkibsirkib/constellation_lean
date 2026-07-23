import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Constellation.FunRel
import Std
open Std

abbrev Var := String

mutual

  inductive Process: Type where
    | halt
    | add (v: Var)
    | rem (v: Var)
    | par (p1 p2: Process)
    | seq (p1 p2: Process)
    | ite (v: Var) (t e: Process)
  deriving BEq

end

abbrev Holds := Finset Var

abbrev Pending := List Process

inductive Exec: EndoRel (Pending × Holds) where
  | halt P H:
      Process.halt ∈ P →
      Exec (P, H) (P.erase Process.halt, H)

  | add P H v:
      Process.add v ∈ P →
      Exec (P, H) (P.erase (Process.add v), insert v H)

  | rem P H v:
      Process.rem v ∈ P →
      Exec (P, H) (P.erase (Process.rem v), H.erase v)

  | par P H p1 p2:
      p1.par p2 ∈ P →
      Exec (P, H) (p1 :: p2 :: P.erase (p1.par p2), H)

  | seq P H H' p1 p2:
      p1.seq p2 ∈ P →
      Exec⊹ ([p1], H) ([], H') →
      Exec  (P, H) (p2 :: P.erase (p1.seq p2), H')

  | ite_t P H v t e:
      Process.ite v t e ∈ P →
      v ∈ H →
      Exec (P, H) (t :: P.erase (Process.ite v t e), H)

  | ite_e P H v t e:
      Process.ite v t e ∈ P →
      v ∉ H →
      Exec (P, H) (e :: P.erase (Process.ite v t e), H)
