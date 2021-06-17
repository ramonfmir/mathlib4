import Mathlib.Data.Finset.Basic

class Fintype (α : Type u) :=
(elems : Finset α)
(complete : ∀ x : α, x ∈ elems)


instance : Fintype Unit := sorry
