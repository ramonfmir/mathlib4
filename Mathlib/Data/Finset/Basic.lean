import DCP.Mathlib.Data.Multiset.Nodup
import DCP.Mathlib.Data.Multiset.Basic

/-- `Finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure Finset (α : Type u) :=
(val : Multiset α)
(nodup : nodup val)

namespace Finset

def mem (a : α) (s : Finset α) : Prop := a ∈ s.1

infix:50 " ∈ " => mem

end Finset
