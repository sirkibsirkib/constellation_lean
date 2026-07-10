import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Constellation.PopWhere
import Std
open Std

-- We use Mathlib's Finset (finite set),
-- because they have lots of utilities.
example: Finset Nat := ∅
example: Finset Nat := {1,2,3}
example: Finset Nat := {1,2,3} ∪ {2,3}
example: ({1} ∪ {3,4}: Finset Nat) = ({1,4,3} : Finset Nat) := by decide

abbrev Name := String
abbrev Names := Finset Name

example: Names := ∅
example: Names := {"a", "b"}

-- TODO generalise over "Name" so we can also do "Event"
structure DeclRule where mk::
  body: Names -- antecedents
  head: Name  -- consequent
deriving BEq

example: DeclRule := { body := ∅, head := "a" }
example: DeclRule := DeclRule.mk ∅ "a"

notation body "⟶" head => DeclRule.mk body head
example: DeclRule := ∅ ⟶ "a"
example: DeclRule := {"b"} ⟶ "a"
example: DeclRule := {"b","c","d"} ⟶ "x"

abbrev Facts := Names

def satisfies (f: Facts) (r: DeclRule): Bool :=
  r.body ⊆ f

/-
TODO specify declarative inference first (non-deterministic ordering of steps).
TODO _specify_ Saturate relation of type `List DeclRule → Rules → Rules → Prop`
TODO define "implements" as in terms of this and a given "saturate" function
TODO prove that the below saturate function implements the spec.
-/

-- Datalog-style saturation, as a computable function
def saturate (f: Facts) (l: List DeclRule): Facts :=
  match _h : pop_where (satisfies f) l with
  | (some r, l') => saturate (insert r.head f) l'
  | (none  , _ ) => f
termination_by -- begin proof of termination
  l.length     -- ... via decreasing measure of unapplied rules
decreasing_by
  exact pop_where_some_lt_length _ _ _ _ _h

theorem sat_triv_rules: ∀ (f: Facts), saturate f [] = f := by
  unfold saturate
  simp [pop_where]

example: saturate ∅ [] = ∅ := sat_triv_rules _

abbrev bottom_up := saturate ∅

example: bottom_up [] = ∅ := by
  unfold saturate
  simp [pop_where]

example: bottom_up [∅ ⟶ "a"] = {"a"} := by
  unfold saturate
  simp [pop_where]
  unfold satisfies
  simp
  unfold saturate
  unfold satisfies
  decide

example: bottom_up [∅ ⟶ "a", {"a"} ⟶ "b"] = {"b", "a"} := by
  simp [saturate, satisfies, pop_where]

#eval (bottom_up [
  {"a"} ⟶ "b",
  {} ⟶ "a",
  {"a", "b"} ⟶ "c",
  {"f"} ⟶ "d",
])

#eval bottom_up [
  {"a"} ⟶ "b",
  {} ⟶ "a",
  {"a", "b"} ⟶ "c",
  {"f"} ⟶ "d",
]
example: bottom_up [] = ∅ := sat_triv_rules _

inductive EventKind where
  | action -- only for triggering reactive rules
  | add
  | remove
deriving BEq, Hashable, Repr, DecidableEq

abbrev Event := EventKind × Name
example: Event := (EventKind.add, "a")

notation "₊" n => (EventKind.add, n)
notation "₋" n => (EventKind.remove, n)
notation "#" n => (EventKind.action, n)

example: Event := #"a"
example: Event := ₋"a"

abbrev Pending := Finset Event

example: Pending := {#"a", ₊"b"}

structure ReacRule where mk::
  trigger: Event -- eg. #"a"
  guard: Facts -- these currently persist. Would do no harm if negated
  effects: Pending -- empty not wanted

notation t ":" l "⟹" e => ReacRule.mk t l e
example: ReacRule := (#"a") : ∅ ⟹ ∅
example: ReacRule := (#"a") : {"b"} ⟹ {#"a", ₊"b"}

-- not useful because effects don't necessarily get realised together
def contradictory (r: ReacRule) :=
  ∃ (n: Name),
    {₋n, ₊n} ⊆ r.effects

example: contradictory ((#"a") : {"b"} ⟹ {#"a", ₊"b", ₋"b"}) := by
  exists "b"

example: ∀ e guard, ¬ contradictory (e : guard ⟹ ∅) := by
  intro act guard H
  obtain ⟨name, H⟩ := H
  simp at H

def Program := List DeclRule × List ReacRule
example: Program := ([], [])
example: Program := ([{"a"} ⟶ "b"], [(#"a") : {"b"} ⟹ ∅])

/- In each `Reach {π: Program} (p: Pending) (f: Facts)`,
- `p` is the events in flight, waiting to be received
- `f` is the persistent true facts
The five constructors of this inductive relation
represent the five ways a current configuration can be reached
-/
inductive Reach {π: Program} : Pending → Facts → Prop where
  | initial facts: -- Initialise a system with given facts
      Reach ∅ facts

  | input p f event: -- An arbitrary trigger event is added to pending
      Reach p f → Reach (insert event p) f

  | trigger p f (e: Event) r:
      /-
      A pending trigger event named `n` is consumed,
      which triggers reactive rule `r` in program `π`,
      whose guard is satisfied by the facts (post-saturation wrt `π`),
      appending the pending rules of `r`.
      -/
      Reach p f →
      e ∈ p →
      r.trigger = e →
      r ∈ π.snd →
      r.guard ⊆ (saturate f π.fst) →
      Reach ((p.erase e) ∪ r.effects) f

  | add p f (n: Name): -- a pending `add` takes effect
      Reach p f →
      n ∉ f →
      (EventKind.add, n) ∈ p →
      Reach (p.erase (EventKind.add, n)) (insert n f)

  | remove p f (n: Name): -- a pending `rem` takes effect
      Reach p f →
      n ∈ f →
      (EventKind.remove, n) ∈ p →
      Reach (p.erase (EventKind.remove, n)) (f.erase n)

example (e:Event): @Reach (π := ([],[])) {e} ∅ :=
  Reach.initial (facts := ∅)
  |> Reach.input _ _ e


-- `+b -> +q.` should be expressible.
--    saturation but for events
-- `+b ->  c` no good
-- ` b -> +c` no good

/-
Things we want to prove:
- saturation is confluent + termination = church rosser AKA strong norm.
- there exists a nirmalisation of programs with nested rules, giving a new program without nested rules whose
- somethig something interpreter
- declarative transition system
- reactive transition system atop
- interpreter function, implementing the semantics
- stratification property of programs
- decision procedure: is_Strat: ∀ p: program, strat p ⊕ ¬ strat p
- formalise concurrency of reactive transitions
- execution of programs under composition
- let us not confuse:
  * strict interleaving: exactly one trigger per step
  * weaker: exactly one root trigger
  * weakest: arb set of triggers (perhaps nonempty) per step
- alternative to interleaving: subset fires
  oh no we are doing Reo again
- prove that different

Note: we urgently need to settle on the semantics

More examples

#a => #c1; #c2; #c3 //
^^ This abbreviates ,,
#a  => #c1
#c1 => #c2
#c2 => #c3


// We are trying to encode XOR of postconditions
// it is unclear when the time is passing:
// 1. between #a trig and a checked
// 2. between a checked and -a realised
// 3. between -a realised and #b triggered
// 4. none of the above (then -> and => coincide?)
// Each results in different semantics
a.
#a: a => -a, #b1
#a: a => -a, #b2 // => does not mean time passes.




#a => #c ; #d // ";" means later
#b => +a

operators for seq comp, par comp, choice,

#a => #b // Giovanni wants a quantum of time to pass here
#c => +a

(=>) very asynchronous. we want to think of different rules running concurrently in general

-/
