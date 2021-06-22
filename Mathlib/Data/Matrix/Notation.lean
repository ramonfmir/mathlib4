import Init.Prelude
import Mathlib.Data.Matrix.Basic

universe u
variable {α : Type u}

-- TODO: Move
def fin_zero_elim {α : Fin 0 → Sort u} (x : Fin 0) : α x := x.elim0

def vec_empty : Fin 0 → α := fin_zero_elim

def vec_cons {n : ℕ} (h : α) (t : Fin n → α) : Fin n.succ → α :=
fun i => if p : i.val < n then t ⟨i.val, p⟩ else h
--Fin.cons h t ?

open Lean

syntax "![" term,* "]" : term

macro_rules
  | `(![ $elems,* ]) => do
    let rec expandListLit (i : Nat) (skip : Bool) (result : Syntax) : MacroM Syntax := do
      match i, skip with
      | 0,   _     => pure result
      | i+1, true  => expandListLit i false result
      | i+1, false => expandListLit i true  (← ``(vec_cons $(elems.elemsAndSeps[i]) $result))
    expandListLit elems.elemsAndSeps.size false (← ``(vec_empty))

variable {m n : ℕ}

def fin_range (n : ℕ) : List (Fin n) := sorry
--(range n).pmap Fin.mk (fun x => List.mem_range.1)

instance [Repr α] : Repr (Fin n → α) where
  reprPrec
    | f, _ => Format.bracket
      "![" (@Format.joinSep _ ⟨repr⟩ ((List.range n).map (fun i => f ⟨i, sorry⟩)) ",") "]"

#check ![0,2,3]
