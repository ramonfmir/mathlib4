import Mathlib.Data.Quot
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Basic

def Multiset (α : Type u) : Type u :=
quotient (List.isSetoid α)

namespace Multiset

instance : Coe (List α) (Multiset α) := ⟨Quot.mk _⟩

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def mem (a : α) (s : Multiset α) : Prop :=
sorry
-- Quot.lift_on s (fun l => a ∈ l) (fun l₁ l₂ (e : l₁ ~ l₂) => propext $ e.mem_iff)

infix:50 " ∈ " => mem

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr (f : α → β → β) (H : left_commutative f) (b : β) (s : Multiset α) : β :=
Quot.liftOn s (fun l => List.foldr f b l) (fun l₁ l₂ p => p.foldr_eq H b)

/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : Multiset α) : Multiset β :=
Quot.liftOn s
  (fun l : List α => (l.map f : Multiset β)) (fun l₁ l₂ p => Quot.sound (p.map f))

/-- Sum of a multiset given a commutative monoid structure on `α`.
  `sum {a, b, c} = a + b + c` -/
def sum [AddCommMonoid α] : Multiset α → α :=
foldr Add.add (fun x y z => add_left_comm x y z) 0

end Multiset
