
namespace List
universes uu vv
variable {α : Type uu} {β : Type vv}

/-- `perm l₁ l₂` or `l₁ ~ l₂` asserts that `l₁` and `l₂` are permutations
  of each other. This is defined by induction using pairwise swaps. -/
inductive perm : List α → List α → Prop
| nil   : perm [] []
| cons  : ∀ (x : α) {l₁ l₂ : List α}, perm l₁ l₂ → perm (x::l₁) (x::l₂)
| swap  : ∀ (x y : α) (l : List α), perm (y::x::l) (x::y::l)
| trans : ∀ {l₁ l₂ l₃ : List α}, perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

open perm (swap)

infix "~" => perm

protected theorem perm.refl : ∀ (l : List α), l ~ l
| []      => perm.nil
| (x::xs) => (perm.refl xs).cons x

-- @[symm] protected theorem perm.symm {l₁ l₂ : list α} (p : l₁ ~ l₂) : l₂ ~ l₁ :=
-- perm.rec_on p
--   perm.nil
--   (λ x l₁ l₂ p₁ r₁, r₁.cons x)
--   (λ x y l, swap y x l)
--   (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂, r₂.trans r₁)

-- theorem perm_comm {l₁ l₂ : list α} : l₁ ~ l₂ ↔ l₂ ~ l₁ := ⟨perm.symm, perm.symm⟩

-- theorem perm.swap'
--   (x y : α) {l₁ l₂ : list α} (p : l₁ ~ l₂) : y::x::l₁ ~ x::y::l₂ :=
-- (swap _ _ _).trans ((p.cons _).cons _)

-- attribute [trans] perm.trans

theorem perm.eqv (α) : Equivalence (@perm α) := sorry
-- mk_equivalence (@perm α) (@perm.refl α) (@perm.symm α) (@perm.trans α)

instance isSetoid (α) : Setoid (List α) :=
Setoid.mk (@perm α) (perm.eqv α)

end List