import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Fold

universes u v w
variable {α : Type u} {β : Type v} {γ : Type w}

namespace Finset

/--
`∑ x in s, f x` is the sum of `f x`
as `x` ranges over the elements of the finite set `s`.
-/
protected def sum [AddCommMonoid β] (s : Finset α) (f : α → β) : β := (s.1.map f).sum

@[simp] lemma sum_mk [AddCommMonoid β] (s : Multiset α) (hs) (f : α → β) :
  (⟨s, hs⟩ : Finset α).sum f = (s.map f).sum :=
rfl

end Finset

instance {n} : Fintype (Fin n) := sorry

syntax  "∑ " ident ", " term : term
syntax  "∑ " ident ":" term ", " term : term

macro_rules
  | `(∑ $i:ident, $f:term) => `(Finset.sum Finset.univ (fun $i => $f))
  | `(∑ $i:ident : $type, $f:term) => `(Finset.sum Finset.univ (fun ($i : $type) => $f))

-- TODO: Move.

def Fin.succ {n} (i : Fin n) : Fin (n + 1) := {
  val := i.val + 1
  isLt := sorry
}

theorem Fin.prod_univ_zero [AddCommMonoid β] (f : Fin 0 → β) :
  (∑ i, f i) = 0 :=
  sorry

theorem Fin.sum_univ_succ [AddCommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
  (∑ i, f i) = f 0 + (∑ i : Fin n, f i.succ) :=
  sorry
