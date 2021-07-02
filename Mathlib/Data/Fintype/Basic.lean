import Mathlib.Data.Finset.Basic

universes u v

variable {α : Type u} {β : Type u} {γ : Type u}

class Fintype (α : Type u) :=
(elems : Finset α)
(complete : ∀ x : α, x ∈ elems)

instance : Fintype Unit := sorry

namespace Finset
variable [Fintype α]

def univ : Finset α := @Fintype.elems α _



end Finset
