import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Fold

namespace Finset

universe u
variable {α β : Type u}

section Fold

open Binary

-- NOTE: commutative and associative should be instances.
variable (op : β → β → β) (hc : commutative op) (ha : associative op)

def fold (b : β) (f : α → β) (s : Finset α) : β := (s.val.map f).fold op hc ha b

end Fold

end Finset
