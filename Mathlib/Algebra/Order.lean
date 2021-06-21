class Preorder (α : Type u) extends LE α, LT α :=
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c)
(lt := fun a b => a ≤ b ∧ ¬ b ≤ a)
(lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ (a ≤ b ∧ ¬ b ≤ a))

section preorder

variable [Preorder α]

/-- The relation `≤` on a preorder is reflexive. -/
theorem le_refl : ∀ a : α, a ≤ a :=
Preorder.le_refl

/-- The relation `≤` on a preorder is transitive. -/
theorem le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c :=
Preorder.le_trans

-- TODO: LE.le.trans dot notation does not work


theorem lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
Preorder.lt_iff_le_not_le

theorem lt_of_le_not_le : ∀ {a b : α}, a ≤ b → ¬ b ≤ a → a < b
| a, b, hab, hba => lt_iff_le_not_le.mpr ⟨hab, hba⟩

theorem le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬ b ≤ a
| a, b, hab => lt_iff_le_not_le.mp hab

theorem le_of_eq {a b : α} : a = b → a ≤ b :=
fun h => h ▸ le_refl a

theorem ge_trans : ∀ {a b c : α}, a ≥ b → b ≥ c → a ≥ c :=
fun {a b c} h₁ h₂ => le_trans h₂ h₁

theorem lt_irrefl : ∀ a : α, ¬ a < a := sorry

theorem gt_irrefl : ∀ a : α, ¬ a > a :=
lt_irrefl

theorem lt_trans : ∀ {a b c : α}, a < b → b < c → a < c := sorry

theorem gt_trans : ∀ {a b c : α}, a > b → b > c → a > c := sorry

theorem ne_of_lt {a b : α} (h : a < b) : a ≠ b := sorry

theorem ne_of_gt {a b : α} (h : b < a) : a ≠ b := sorry

theorem lt_asymm {a b : α} (h : a < b) : ¬ b < a := sorry

theorem le_of_lt : ∀ {a b : α}, a < b → a ≤ b := sorry

theorem lt_of_lt_of_le : ∀ {a b c : α}, a < b → b ≤ c → a < c := sorry

theorem lt_of_le_of_lt : ∀ {a b c : α}, a ≤ b → b < c → a < c := sorry

theorem gt_of_gt_of_ge {a b c : α} (h₁ : a > b) (h₂ : b ≥ c) : a > c :=
lt_of_le_of_lt h₂ h₁

theorem gt_of_ge_of_gt {a b c : α} (h₁ : a ≥ b) (h₂ : b > c) : a > c :=
lt_of_lt_of_le h₂ h₁

theorem not_le_of_gt {a b : α} (h : a > b) : ¬ a ≤ b :=
(le_not_le_of_lt h).right

theorem not_lt_of_ge {a b : α} (h : a ≥ b) : ¬ a < b := sorry

theorem le_of_lt_or_eq : ∀ {a b : α}, (a < b ∨ a = b) → a ≤ b := sorry

theorem le_of_eq_or_lt {a b : α} (h : a = b ∨ a < b) : a ≤ b := sorry

end preorder