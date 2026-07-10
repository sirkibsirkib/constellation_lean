import Mathlib.Data.Finset.Basic
import Constellation.SpecLang

open Finset

abbrev ProdTypeId := String

inductive TypeId where
  | prim_int
  | prim_string
  | product_named (id: ProdTypeId)

structure Variable where
  type: TypeId
  name: String


inductive Instance where
  | prim_int (n: Nat)
  | prim_string (s: String)
  | construct (type: ProdTypeId) (args: List Instance)

namespace Instance
  def type (i: Instance): TypeId :=
    match i with
    | prim_int _ => TypeId.prim_int
    | prim_string _ => TypeId.prim_string
    | construct s _ => TypeId.product_named s
end Instance

-- Build an instance expression with a variable store in context
inductive InstExpr where
  | var (v: Variable)
  | project (e: InstExpr) (field_index: Nat)
  | construct (type: TypeId) (args: List InstExpr)

-- Return whether the check passes given a variable store in ctx
inductive Check where
  | eq (e1 e2: InstExpr)
  | not (c: Check)
  | any (lc: List Check)


inductive Prim where
  | int
  | string

-- eFLINT type definition
inductive TypeDef where
  | Product (fields: List TypeId)
  | Prim (prim: Prim)

-- A specification of an effect of triggering an instance
structure Effect where
  triggered_name: String
  add: Bool -- otherwise remove
  what: InstExpr

structure Spec where
  fields_defs: String → Option TypeDef
  deriv_rules: List InstExpr
  effects: TypeId → List Effect

def Kb := Finset Instance
