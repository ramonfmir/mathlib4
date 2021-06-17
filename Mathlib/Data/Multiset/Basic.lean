import Mathlib.Data.Quot
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm

def Multiset (α : Type u) : Type u :=
quotient (List.isSetoid α)

namespace Multiset

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def mem (a : α) (s : Multiset α) : Prop :=
sorry
-- Quot.lift_on s (fun l => a ∈ l) (fun l₁ l₂ (e : l₁ ~ l₂) => propext $ e.mem_iff)

infix:50 " ∈ " => mem

end Multiset
