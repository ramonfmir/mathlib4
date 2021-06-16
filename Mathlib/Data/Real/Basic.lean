import DCP.Mathlib.Algebra.Order

def Real : Type := sorry

notation "ℝ" => Real

@[irreducible] private def lt (x y : ℝ) : Prop := sorry
instance : LT ℝ := ⟨lt⟩

@[irreducible] private def le (x y : ℝ) : Prop := x < y ∨ x = y
instance : LE ℝ := ⟨le⟩


instance : Inhabited ℝ := sorry

instance : Preorder ℝ := {
  le := LE.le,
  lt := LT.lt,
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry
}

instance : Add Real := sorry
instance : Mul Real := sorry
instance : OfNat Real n := sorry


-- The following lemmas should actually come from type class instances:

theorem mul_le_mul_of_nonneg_left {a b c : ℝ} : 
  a ≤ b → 0 ≤ c → c * a ≤ c * b := sorry

theorem add_pos_of_nonneg_of_pos {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
  0 < a + b := sorry

theorem mul_nonneg {a b : ℝ} :
  0 ≤ a → 0 ≤ b → 0 ≤ a * b := sorry