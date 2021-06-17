import Init.Data.List.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Multiset.Basic

namespace Multiset

universe u
variable {α β : Type u}

section Fold

-- NOTE: commutative and associative should be instances.
variable (op : α → α → α) (hc : commutative op) (ha : associative op)

def fold : α → Multiset α → α := foldr op (left_comm op hc ha)

end Fold

end Multiset
