/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Pi
import Mathlib.Algebra.BigOperators.Basic

/-!
# Matrices
-/
universes u u' v w

-- open_locale big_operators
-- open dMatrix

/-- `Matrix m n` is the type of matrices whose rows are indexed by the Fintype `m`
    and whose columns are indexed by the Fintype `n`. -/
-- @[nolint unused_arguments]
def Matrix (m : Type u) (n : Type u') [Fintype m] [Fintype n] (α : Type v) : Type (max u u' v) :=
m → n → α

variable {l m n o : Type u} [Fintype l] [Fintype m] [Fintype n] [Fintype o]
variable {m' : o → Type u} [∀ i, Fintype (m' i)]
variable {n' : o → Type u} [∀ i, Fintype (n' i)]
variable {R : Type u} {S : Type u} {α : Type v} {β : Type w}

namespace Matrix

section ext
variable {M N : Matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
⟨fun h => funext $ fun i => funext $ h i, fun h => by { intros; simp [h] }⟩

-- @[ext]
theorem ext : (∀ i j, M i j = N i j) → M = N :=
ext_iff.mp

end ext

/-- `M.map f` is the Matrix obtained by applying `f` to each entry of the Matrix `M`. -/
def map (M : Matrix m n α) (f : α → β) : Matrix m n β := fun i j => f (M i j)

@[simp]
theorem map_apply {M : Matrix m n α} {f : α → β} {i : m} {j : n} :
  M.map f i j = f (M i j) := rfl

@[simp]
theorem map_map {M : Matrix m n α} {β γ : Type u} {f : α → β} {g : β → γ} :
  (M.map f).map g = M.map (g ∘ f) :=
sorry

/-- The transpose of a Matrix. -/
def transpose (M : Matrix m n α) : Matrix n m α
| x, y => M y x

postfix:1500 "ᵀ" => Matrix.transpose

/-- `Matrix.col u` is the column Matrix whose entries are given by `u`. -/
def col (w : m → α) : Matrix m Unit α
| x, y => w x

/-- `Matrix.row u` is the row Matrix whose entries are given by `u`. -/
def row (v : n → α) : Matrix Unit n α
| x, y => v y

-- instance [inhabited α] : inhabited (Matrix m n α) := pi.inhabited _
-- instance [has_add α] : has_add (Matrix m n α) := pi.has_add
-- instance [add_semigroup α] : add_semigroup (Matrix m n α) := pi.add_semigroup
-- instance [add_comm_semigroup α] : add_comm_semigroup (Matrix m n α) := pi.add_comm_semigroup
instance [Zero α] : Zero (Matrix m n α) := Pi.Zero
-- instance [add_monoid α] : add_monoid (Matrix m n α) := pi.add_monoid
-- instance [add_comm_monoid α] : add_comm_monoid (Matrix m n α) := pi.add_comm_monoid
-- instance [has_neg α] : has_neg (Matrix m n α) := pi.has_neg
-- instance [has_sub α] : has_sub (Matrix m n α) := pi.has_sub
-- instance [add_group α] : add_group (Matrix m n α) := pi.add_group
-- instance [add_comm_group α] : add_comm_group (Matrix m n α) := pi.add_comm_group
-- instance [unique α] : unique (Matrix m n α) := pi.unique
-- instance [subsingleton α] : subsingleton (Matrix m n α) := pi.subsingleton
-- instance [nonempty m] [nonempty n] [nontrivial α] : nontrivial (Matrix m n α) :=
-- function.nontrivial

-- instance [has_scalar R α] : has_scalar R (Matrix m n α) := pi.has_scalar
-- instance [has_scalar R α] [has_scalar S α] [smul_comm_class R S α] :
--   smul_comm_class R S (Matrix m n α) := pi.smul_comm_class
-- instance [has_scalar R S] [has_scalar R α] [has_scalar S α] [is_scalar_tower R S α] :
--   is_scalar_tower R S (Matrix m n α) := pi.is_scalar_tower
-- instance [monoid R] [mul_action R α] :
--   mul_action R (Matrix m n α) := pi.mul_action _
-- instance [monoid R] [add_monoid α] [distrib_mul_action R α] :
--   distrib_mul_action R (Matrix m n α) := pi.distrib_mul_action _
-- instance [semiring R] [add_comm_monoid α] [module R α] :
--   module R (Matrix m n α) := pi.module _ _ _

@[simp] theorem map_zero [Zero α] [Zero β] {f : α → β} (h : f 0 = 0) :
  (0 : Matrix m n α).map f = 0 :=
-- by { ext, simp [h], }
sorry

-- theorem map_add [add_monoid α] [add_monoid β] (f : α →+ β)
--   (M N : Matrix m n α) : (M + N).map f = M.map f + N.map f :=
-- by { ext, simp, }

-- theorem map_sub [add_group α] [add_group β] (f : α →+ β)
--   (M N : Matrix m n α) : (M - N).map f = M.map f - N.map f :=
-- by { ext, simp }

-- theorem subsingleton_of_empty_left (hm : ¬ nonempty m) : subsingleton (Matrix m n α) :=
-- ⟨λ M N, by { ext, contrapose! hm, use i }⟩

-- theorem subsingleton_of_empty_right (hn : ¬ nonempty n) : subsingleton (Matrix m n α) :=
-- ⟨λ M N, by { ext, contrapose! hn, use j }⟩

end Matrix

-- /-- The `add_monoid_hom` between spaces of matrices induced by an `add_monoid_hom` between their
-- coefficients. -/
-- def add_monoid_hom.map_Matrix [add_monoid α] [add_monoid β] (f : α →+ β) :
--   Matrix m n α →+ Matrix m n β :=
-- { to_fun := λ M, M.map f,
--   map_zero' := by simp,
--   map_add' := Matrix.map_add f, }

-- @[simp] theorem add_monoid_hom.map_Matrix_apply [add_monoid α] [add_monoid β]
--   (f : α →+ β) (M : Matrix m n α) : f.map_Matrix M = M.map f := rfl

-- open_locale Matrix

-- namespace Matrix

-- section diagonal
-- variables [decidable_eq n]

-- /-- `diagonal d` is the square Matrix such that `(diagonal d) i i = d i` and `(diagonal d) i j = 0`
-- if `i ≠ j`. -/
-- def diagonal [has_zero α] (d : n → α) : Matrix n n α := λ i j, if i = j then d i else 0

-- @[simp] theorem diagonal_apply_eq [has_zero α] {d : n → α} (i : n) : (diagonal d) i i = d i :=
-- by simp [diagonal]

-- @[simp] theorem diagonal_apply_ne [has_zero α] {d : n → α} {i j : n} (h : i ≠ j) :
--   (diagonal d) i j = 0 := by simp [diagonal, h]

-- theorem diagonal_apply_ne' [has_zero α] {d : n → α} {i j : n} (h : j ≠ i) :
--   (diagonal d) i j = 0 := diagonal_apply_ne h.symm

-- @[simp] theorem diagonal_zero [has_zero α] : (diagonal (λ _, 0) : Matrix n n α) = 0 :=
-- by simp [diagonal]; refl

-- @[simp] theorem diagonal_transpose [has_zero α] (v : n → α) :
--   (diagonal v)ᵀ = diagonal v :=
-- begin
--   ext i j,
--   by_cases h : i = j,
--   { simp [h, transpose] },
--   { simp [h, transpose, diagonal_apply_ne' h] }
-- end

-- @[simp] theorem diagonal_add [add_monoid α] (d₁ d₂ : n → α) :
--   diagonal d₁ + diagonal d₂ = diagonal (λ i, d₁ i + d₂ i) :=
-- by ext i j; by_cases h : i = j; simp [h]

-- @[simp] theorem diagonal_map [has_zero α] [has_zero β] {f : α → β} (h : f 0 = 0) {d : n → α} :
--   (diagonal d).map f = diagonal (λ m, f (d m)) :=
-- by { ext, simp only [diagonal, map_apply], split_ifs; simp [h], }

-- section one
-- variables [has_zero α] [has_one α]

-- instance : has_one (Matrix n n α) := ⟨diagonal (λ _, 1)⟩

-- @[simp] theorem diagonal_one : (diagonal (λ _, 1) : Matrix n n α) = 1 := rfl

-- theorem one_apply {i j} : (1 : Matrix n n α) i j = if i = j then 1 else 0 := rfl

-- @[simp] theorem one_apply_eq (i) : (1 : Matrix n n α) i i = 1 := diagonal_apply_eq i

-- @[simp] theorem one_apply_ne {i j} : i ≠ j → (1 : Matrix n n α) i j = 0 :=
-- diagonal_apply_ne

-- theorem one_apply_ne' {i j} : j ≠ i → (1 : Matrix n n α) i j = 0 :=
-- diagonal_apply_ne'

-- @[simp] theorem one_map [has_zero β] [has_one β]
--   {f : α → β} (h₀ : f 0 = 0) (h₁ : f 1 = 1) :
--   (1 : Matrix n n α).map f = (1 : Matrix n n β) :=
-- by { ext, simp only [one_apply, map_apply], split_ifs; simp [h₀, h₁], }

-- end one

-- section numeral

-- @[simp] theorem bit0_apply [has_add α] (M : Matrix m m α) (i : m) (j : m) :
--   (bit0 M) i j = bit0 (M i j) := rfl

-- variables [add_monoid α] [has_one α]

-- theorem bit1_apply (M : Matrix n n α) (i : n) (j : n) :
--   (bit1 M) i j = if i = j then bit1 (M i j) else bit0 (M i j) :=
-- by dsimp [bit1]; by_cases h : i = j; simp [h]

-- @[simp]
-- theorem bit1_apply_eq (M : Matrix n n α) (i : n) :
--   (bit1 M) i i = bit1 (M i i) :=
-- by simp [bit1_apply]

-- @[simp]
-- theorem bit1_apply_ne (M : Matrix n n α) {i j : n} (h : i ≠ j) :
--   (bit1 M) i j = bit0 (M i j) :=
-- by simp [bit1_apply, h]

-- end numeral

-- end diagonal

-- section dot_product

/-- `dot_product v w` is the sum of the entrywise products `v i * w i` -/
def dot_product [Mul α] [AddCommMonoid α] (v w : m → α) : α :=
Finset.sum Finset.univ (fun i => v i * w i)

-- theorem dot_product_assoc [semiring α] (u : m → α) (v : m → n → α) (w : n → α) :
--   dot_product (λ j, dot_product u (λ i, v i j)) w = dot_product u (λ i, dot_product (v i) w) :=
-- by simpa [dot_product, finset.mul_sum, finset.sum_mul, mul_assoc] using finset.sum_comm

-- theorem dot_product_comm [comm_semiring α] (v w : m → α) :
--   dot_product v w = dot_product w v :=
-- by simp_rw [dot_product, mul_comm]

-- @[simp] theorem dot_product_punit [add_comm_monoid α] [has_mul α] (v w : punit → α) :
--   dot_product v w = v ⟨⟩ * w ⟨⟩ :=
-- by simp [dot_product]

-- @[simp] theorem dot_product_zero [semiring α] (v : m → α) : dot_product v 0 = 0 :=
-- by simp [dot_product]

-- @[simp] theorem dot_product_zero' [semiring α] (v : m → α) : dot_product v (λ _, 0) = 0 :=
-- dot_product_zero v

-- @[simp] theorem zero_dot_product [semiring α] (v : m → α) : dot_product 0 v = 0 :=
-- by simp [dot_product]

-- @[simp] theorem zero_dot_product' [semiring α] (v : m → α) : dot_product (λ _, (0 : α)) v = 0 :=
-- zero_dot_product v

-- @[simp] theorem add_dot_product [semiring α] (u v w : m → α) :
--   dot_product (u + v) w = dot_product u w + dot_product v w :=
-- by simp [dot_product, add_mul, finset.sum_add_distrib]

-- @[simp] theorem dot_product_add [semiring α] (u v w : m → α) :
--   dot_product u (v + w) = dot_product u v + dot_product u w :=
-- by simp [dot_product, mul_add, finset.sum_add_distrib]

-- @[simp] theorem diagonal_dot_product [decidable_eq m] [semiring α] (v w : m → α) (i : m) :
--   dot_product (diagonal v i) w = v i * w i :=
-- have ∀ j ≠ i, diagonal v i j * w j = 0 := λ j hij, by simp [diagonal_apply_ne' hij],
-- by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

-- @[simp] theorem dot_product_diagonal [decidable_eq m] [semiring α] (v w : m → α) (i : m) :
--   dot_product v (diagonal w i) = v i * w i :=
-- have ∀ j ≠ i, v j * diagonal w i j = 0 := λ j hij, by simp [diagonal_apply_ne' hij],
-- by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

-- @[simp] theorem dot_product_diagonal' [decidable_eq m] [semiring α] (v w : m → α) (i : m) :
--   dot_product v (λ j, diagonal w j i) = v i * w i :=
-- have ∀ j ≠ i, v j * diagonal w j i = 0 := λ j hij, by simp [diagonal_apply_ne hij],
-- by convert finset.sum_eq_single i (λ j _, this j) _ using 1; simp

-- @[simp] theorem neg_dot_product [ring α] (v w : m → α) : dot_product (-v) w = - dot_product v w :=
-- by simp [dot_product]

-- @[simp] theorem dot_product_neg [ring α] (v w : m → α) : dot_product v (-w) = - dot_product v w :=
-- by simp [dot_product]

-- @[simp] theorem smul_dot_product [monoid R] [semiring α] [distrib_mul_action R α]
--   [is_scalar_tower R α α] (x : R) (v w : m → α) :
--   dot_product (x • v) w = x • dot_product v w :=
-- by simp [dot_product, finset.smul_sum, smul_mul_assoc]

-- @[simp] theorem dot_product_smul [monoid R] [semiring α] [distrib_mul_action R α]
--   [smul_comm_class R α α] (x : R) (v w : m → α) :
--   dot_product v (x • w) = x • dot_product v w :=
-- by simp [dot_product, finset.smul_sum, mul_smul_comm]

-- end dot_product

-- /-- `M ⬝ N` is the usual product of matrices `M` and `N`, i.e. we have that
--     `(M ⬝ N) i k` is the dot product of the `i`-th row of `M` by the `k`-th column of `Ǹ`. -/
-- protected def mul [has_mul α] [add_comm_monoid α] (M : Matrix l m α) (N : Matrix m n α) :
--   Matrix l n α :=
-- λ i k, dot_product (λ j, M i j) (λ j, N j k)

-- localized "infixl ` ⬝ `:75 := Matrix.mul" in Matrix

-- theorem mul_apply [has_mul α] [add_comm_monoid α] {M : Matrix l m α} {N : Matrix m n α} {i k} :
--   (M ⬝ N) i k = ∑ j, M i j * N j k := rfl

-- instance [has_mul α] [add_comm_monoid α] : has_mul (Matrix n n α) := ⟨Matrix.mul⟩

-- @[simp] theorem mul_eq_mul [has_mul α] [add_comm_monoid α] (M N : Matrix n n α) :
--   M * N = M ⬝ N := rfl

-- theorem mul_apply' [has_mul α] [add_comm_monoid α] {M N : Matrix n n α} {i k} :
--   (M ⬝ N) i k = dot_product (λ j, M i j) (λ j, N j k) := rfl

-- section semigroup
-- variables [semiring α]

-- protected theorem mul_assoc (L : Matrix l m α) (M : Matrix m n α) (N : Matrix n o α) :
--   (L ⬝ M) ⬝ N = L ⬝ (M ⬝ N) :=
-- by { ext, apply dot_product_assoc }

-- instance : semigroup (Matrix n n α) :=
-- { mul_assoc := Matrix.mul_assoc, ..Matrix.has_mul }

-- end semigroup

-- @[simp] theorem diagonal_neg [decidable_eq n] [add_group α] (d : n → α) :
--   -diagonal d = diagonal (λ i, -d i) :=
-- by ext i j; by_cases i = j; simp [h]

-- section semiring
-- variables [semiring α]

-- @[simp] protected theorem mul_zero (M : Matrix m n α) : M ⬝ (0 : Matrix n o α) = 0 :=
-- by { ext i j, apply dot_product_zero }

-- @[simp] protected theorem zero_mul (M : Matrix m n α) : (0 : Matrix l m α) ⬝ M = 0 :=
-- by { ext i j, apply zero_dot_product }

-- protected theorem mul_add (L : Matrix m n α) (M N : Matrix n o α) : L ⬝ (M + N) = L ⬝ M + L ⬝ N :=
-- by { ext i j, apply dot_product_add }

-- protected theorem add_mul (L M : Matrix l m α) (N : Matrix m n α) : (L + M) ⬝ N = L ⬝ N + M ⬝ N :=
-- by { ext i j, apply add_dot_product }

-- @[simp] theorem diagonal_mul [decidable_eq m]
--   (d : m → α) (M : Matrix m n α) (i j) : (diagonal d).mul M i j = d i * M i j :=
-- diagonal_dot_product _ _ _

-- @[simp] theorem mul_diagonal [decidable_eq n]
--   (d : n → α) (M : Matrix m n α) (i j) : (M ⬝ diagonal d) i j = M i j * d j :=
-- by { rw ← diagonal_transpose, apply dot_product_diagonal }

-- @[simp] protected theorem one_mul [decidable_eq m] (M : Matrix m n α) :
--   (1 : Matrix m m α) ⬝ M = M :=
-- by ext i j; rw [← diagonal_one, diagonal_mul, one_mul]

-- @[simp] protected theorem mul_one [decidable_eq n] (M : Matrix m n α) :
--   M ⬝ (1 : Matrix n n α) = M :=
-- by ext i j; rw [← diagonal_one, mul_diagonal, mul_one]

-- instance [decidable_eq n] : monoid (Matrix n n α) :=
-- { one_mul := Matrix.one_mul,
--   mul_one := Matrix.mul_one,
--   ..Matrix.has_one, ..Matrix.semigroup }

-- instance [decidable_eq n] : semiring (Matrix n n α) :=
-- { mul_zero := Matrix.mul_zero,
--   zero_mul := Matrix.zero_mul,
--   left_distrib := Matrix.mul_add,
--   right_distrib := Matrix.add_mul,
--   ..Matrix.add_comm_monoid,
--   ..Matrix.monoid }

-- @[simp] theorem diagonal_mul_diagonal [decidable_eq n] (d₁ d₂ : n → α) :
--   (diagonal d₁) ⬝ (diagonal d₂) = diagonal (λ i, d₁ i * d₂ i) :=
-- by ext i j; by_cases i = j; simp [h]

-- theorem diagonal_mul_diagonal' [decidable_eq n] (d₁ d₂ : n → α) :
--   diagonal d₁ * diagonal d₂ = diagonal (λ i, d₁ i * d₂ i) :=
-- diagonal_mul_diagonal _ _

-- @[simp]
-- theorem map_mul {L : Matrix m n α} {M : Matrix n o α} [semiring β] {f : α →+* β} :
--   (L ⬝ M).map f = L.map f ⬝ M.map f :=
-- by { ext, simp [mul_apply, ring_hom.map_sum], }

-- theorem is_add_monoid_hom_mul_left (M : Matrix l m α) :
--   is_add_monoid_hom (λ x : Matrix m n α, M ⬝ x) :=
-- { to_is_add_hom := ⟨Matrix.mul_add _⟩, map_zero := Matrix.mul_zero _ }

-- theorem is_add_monoid_hom_mul_right (M : Matrix m n α) :
--   is_add_monoid_hom (λ x : Matrix l m α, x ⬝ M) :=
-- { to_is_add_hom := ⟨λ _ _, Matrix.add_mul _ _ _⟩, map_zero := Matrix.zero_mul _ }

-- protected theorem sum_mul (s : finset β) (f : β → Matrix l m α)
--   (M : Matrix m n α) : (∑ a in s, f a) ⬝ M = ∑ a in s, f a ⬝ M :=
-- (@finset.sum_hom _ _ _ _ _ s f (λ x, x ⬝ M) M.is_add_monoid_hom_mul_right).symm

-- protected theorem mul_sum (s : finset β) (f : β → Matrix m n α)
--   (M : Matrix l m α) : M ⬝ ∑ a in s, f a = ∑ a in s, M ⬝ f a :=
-- (@finset.sum_hom _ _ _ _ _ s f (λ x, M ⬝ x) M.is_add_monoid_hom_mul_left).symm

-- @[simp]
-- theorem row_mul_col_apply (v w : m → α) (i j) : (row v ⬝ col w) i j = dot_product v w :=
-- rfl

-- end semiring

-- section homs

-- -- TODO: there should be a way to avoid restating these for each `foo_hom`.
-- /-- A version of `one_map` where `f` is a ring hom. -/
-- @[simp] theorem ring_hom_map_one [decidable_eq n] [semiring α] [semiring β] (f : α →+* β) :
--   (1 : Matrix n n α).map f = 1 :=
-- one_map f.map_zero f.map_one

-- /-- A version of `one_map` where `f` is a `ring_equiv`. -/
-- @[simp] theorem ring_equiv_map_one [decidable_eq n]  [semiring α] [semiring β] (f : α ≃+* β) :
--   (1 : Matrix n n α).map f = 1 :=
-- one_map f.map_zero f.map_one

-- /-- A version of `map_zero` where `f` is a `zero_hom`. -/
-- @[simp] theorem zero_hom_map_zero [has_zero α] [has_zero β] (f : zero_hom α β) :
--   (0 : Matrix n n α).map f = 0 :=
-- map_zero f.map_zero

-- /-- A version of `map_zero` where `f` is a `add_monoid_hom`. -/
-- @[simp] theorem add_monoid_hom_map_zero [add_monoid α] [add_monoid β] (f : α →+ β) :
--   (0 : Matrix n n α).map f = 0 :=
-- map_zero f.map_zero

-- /-- A version of `map_zero` where `f` is a `add_equiv`. -/
-- @[simp] theorem add_equiv_map_zero [add_monoid α] [add_monoid β] (f : α ≃+ β) :
--   (0 : Matrix n n α).map f = 0 :=
-- map_zero f.map_zero

-- /-- A version of `map_zero` where `f` is a `linear_map`. -/
-- @[simp] theorem linear_map_map_zero [semiring R] [add_comm_monoid α] [add_comm_monoid β]
--   [module R α] [module R β] (f : α →ₗ[R] β) :
--   (0 : Matrix n n α).map f = 0 :=
-- map_zero f.map_zero

-- /-- A version of `map_zero` where `f` is a `linear_equiv`. -/
-- @[simp] theorem linear_equiv_map_zero [semiring R] [add_comm_monoid α] [add_comm_monoid β]
--   [module R α] [module R β] (f : α ≃ₗ[R] β) :
--   (0 : Matrix n n α).map f = 0 :=
-- map_zero f.map_zero

-- /-- A version of `map_zero` where `f` is a `ring_hom`. -/
-- @[simp] theorem ring_hom_map_zero [semiring α] [semiring β] (f : α →+* β) :
--   (0 : Matrix n n α).map f = 0 :=
-- map_zero f.map_zero

-- /-- A version of `map_zero` where `f` is a `ring_equiv`. -/
-- @[simp] theorem ring_equiv_map_zero [semiring α] [semiring β] (f : α ≃+* β) :
--   (0 : Matrix n n α).map f = 0 :=
-- map_zero f.map_zero

-- end homs

-- end Matrix

-- /-- The `ring_hom` between spaces of square matrices induced by a `ring_hom` between their
-- coefficients. -/
-- @[simps]
-- def ring_hom.map_Matrix [decidable_eq m] [semiring α] [semiring β] (f : α →+* β) :
--   Matrix m m α →+* Matrix m m β :=
-- { to_fun := λ M, M.map f,
--   map_one' := by simp,
--   map_mul' := λ L M, Matrix.map_mul,
--   ..(f.to_add_monoid_hom).map_Matrix }

-- open_locale Matrix

-- namespace Matrix

-- section ring
-- variables [ring α]

-- @[simp] theorem neg_mul (M : Matrix m n α) (N : Matrix n o α) :
--   (-M) ⬝ N = -(M ⬝ N) :=
-- by { ext, apply neg_dot_product }

-- @[simp] theorem mul_neg (M : Matrix m n α) (N : Matrix n o α) :
--   M ⬝ (-N) = -(M ⬝ N) :=
-- by { ext, apply dot_product_neg }

-- protected theorem sub_mul (M M' : Matrix m n α) (N : Matrix n o α) :
--   (M - M') ⬝ N = M ⬝ N - M' ⬝ N :=
-- by rw [sub_eq_add_neg, Matrix.add_mul, neg_mul, sub_eq_add_neg]

-- protected theorem mul_sub (M : Matrix m n α) (N N' : Matrix n o α) :
--   M ⬝ (N - N') = M ⬝ N - M ⬝ N' :=
-- by rw [sub_eq_add_neg, Matrix.mul_add, mul_neg, sub_eq_add_neg]

-- end ring

-- instance [decidable_eq n] [ring α] : ring (Matrix n n α) :=
-- { ..Matrix.semiring, ..Matrix.add_comm_group }

-- section semiring
-- variables [semiring α]

-- theorem smul_eq_diagonal_mul [decidable_eq m] (M : Matrix m n α) (a : α) :
--   a • M = diagonal (λ _, a) ⬝ M :=
-- by { ext, simp }

-- @[simp] theorem smul_mul [monoid R] [distrib_mul_action R α] [is_scalar_tower R α α]
--   (a : R) (M : Matrix m n α) (N : Matrix n l α) :
--   (a • M) ⬝ N = a • M ⬝ N :=
-- by { ext, apply smul_dot_product }

-- /-- This instance enables use with `smul_mul_assoc`. -/
-- instance semiring.is_scalar_tower [decidable_eq n] [monoid R] [distrib_mul_action R α]
--   [is_scalar_tower R α α] :
--   is_scalar_tower R (Matrix n n α) (Matrix n n α) :=
-- ⟨λ r m n, Matrix.smul_mul r m n⟩

-- @[simp] theorem mul_smul [monoid R] [distrib_mul_action R α] [smul_comm_class R α α]
--   (M : Matrix m n α) (a : R) (N : Matrix n l α) : M ⬝ (a • N) = a • M ⬝ N :=
-- by { ext, apply dot_product_smul }

-- /-- This instance enables use with `mul_smul_comm`. -/
-- instance semiring.smul_comm_class [decidable_eq n] [monoid R] [distrib_mul_action R α]
--   [smul_comm_class R α α] :
--   smul_comm_class R (Matrix n n α) (Matrix n n α) :=
-- ⟨λ r m n, (Matrix.mul_smul m r n).symm⟩

-- @[simp] theorem mul_mul_left (M : Matrix m n α) (N : Matrix n o α) (a : α) :
--   (λ i j, a * M i j) ⬝ N = a • (M ⬝ N) :=
-- smul_mul a M N

-- /--
-- The ring homomorphism `α →+* Matrix n n α`
-- sending `a` to the diagonal Matrix with `a` on the diagonal.
-- -/
-- def scalar (n : Type u) [decidable_eq n] [Fintype n] : α →+* Matrix n n α :=
-- { to_fun := λ a, a • 1,
--   map_one' := by simp,
--   map_mul' := by { intros, ext, simp [mul_assoc], },
--   .. (smul_add_hom α _).flip (1 : Matrix n n α) }

-- section scalar

-- variable [decidable_eq n]

-- @[simp] theorem coe_scalar : (scalar n : α → Matrix n n α) = λ a, a • 1 := rfl

-- theorem scalar_apply_eq (a : α) (i : n) :
--   scalar n a i i = a :=
-- by simp only [coe_scalar, smul_eq_mul, mul_one, one_apply_eq, pi.smul_apply]

-- theorem scalar_apply_ne (a : α) (i j : n) (h : i ≠ j) :
--   scalar n a i j = 0 :=
-- by simp only [h, coe_scalar, one_apply_ne, ne.def, not_false_iff, pi.smul_apply, smul_zero]

-- theorem scalar_inj [nonempty n] {r s : α} : scalar n r = scalar n s ↔ r = s :=
-- begin
--   split,
--   { intro h,
--     inhabit n,
--     rw [← scalar_apply_eq r (arbitrary n), ← scalar_apply_eq s (arbitrary n), h] },
--   { rintro rfl, refl }
-- end

-- end scalar

-- end semiring

-- section comm_semiring
-- variables [comm_semiring α]

-- theorem smul_eq_mul_diagonal [decidable_eq n] (M : Matrix m n α) (a : α) :
--   a • M = M ⬝ diagonal (λ _, a) :=
-- by { ext, simp [mul_comm] }

-- @[simp] theorem mul_mul_right (M : Matrix m n α) (N : Matrix n o α) (a : α) :
--   M ⬝ (λ i j, a * N i j) = a • (M ⬝ N) :=
-- mul_smul M a N

-- theorem scalar.commute [decidable_eq n] (r : α) (M : Matrix n n α) : commute (scalar n r) M :=
-- by simp [commute, semiconj_by]

-- end comm_semiring

-- section semiring
-- variables [semiring α]

-- /-- For two vectors `w` and `v`, `vec_mul_vec w v i j` is defined to be `w i * v j`.
--     Put another way, `vec_mul_vec w v` is exactly `col w ⬝ row v`. -/
-- def vec_mul_vec (w : m → α) (v : n → α) : Matrix m n α
-- | x y := w x * v y

-- /-- `mul_vec M v` is the Matrix-vector product of `M` and `v`, where `v` is seen as a column Matrix.
--     Put another way, `mul_vec M v` is the vector whose entries
--     are those of `M ⬝ col v` (see `col_mul_vec`). -/
-- def mul_vec (M : Matrix m n α) (v : n → α) : m → α
-- | i := dot_product (λ j, M i j) v

-- /-- `vec_mul v M` is the vector-Matrix product of `v` and `M`, where `v` is seen as a row Matrix.
--     Put another way, `vec_mul v M` is the vector whose entries
--     are those of `row v ⬝ M` (see `row_vec_mul`). -/
-- def vec_mul (v : m → α) (M : Matrix m n α) : n → α
-- | j := dot_product v (λ i, M i j)

-- instance mul_vec.is_add_monoid_hom_left (v : n → α) :
--   is_add_monoid_hom (λM:Matrix m n α, mul_vec M v) :=
-- { map_zero := by ext; simp [mul_vec]; refl,
--   map_add :=
--   begin
--     intros x y,
--     ext m,
--     apply add_dot_product
--   end }

-- theorem mul_vec_diagonal [decidable_eq m] (v w : m → α) (x : m) :
--   mul_vec (diagonal v) w x = v x * w x :=
-- diagonal_dot_product v w x

-- theorem vec_mul_diagonal [decidable_eq m] (v w : m → α) (x : m) :
--   vec_mul v (diagonal w) x = v x * w x :=
-- dot_product_diagonal' v w x

-- @[simp] theorem mul_vec_one [decidable_eq m] (v : m → α) : mul_vec 1 v = v :=
-- by { ext, rw [←diagonal_one, mul_vec_diagonal, one_mul] }

-- @[simp] theorem vec_mul_one [decidable_eq m] (v : m → α) : vec_mul v 1 = v :=
-- by { ext, rw [←diagonal_one, vec_mul_diagonal, mul_one] }

-- @[simp] theorem mul_vec_zero (A : Matrix m n α) : mul_vec A 0 = 0 :=
-- by { ext, simp [mul_vec] }

-- @[simp] theorem vec_mul_zero (A : Matrix m n α) : vec_mul 0 A = 0 :=
-- by { ext, simp [vec_mul] }

-- @[simp] theorem vec_mul_vec_mul (v : m → α) (M : Matrix m n α) (N : Matrix n o α) :
--   vec_mul (vec_mul v M) N = vec_mul v (M ⬝ N) :=
-- by { ext, apply dot_product_assoc }

-- @[simp] theorem mul_vec_mul_vec (v : o → α) (M : Matrix m n α) (N : Matrix n o α) :
--   mul_vec M (mul_vec N v) = mul_vec (M ⬝ N) v :=
-- by { ext, symmetry, apply dot_product_assoc }

-- theorem vec_mul_vec_eq (w : m → α) (v : n → α) :
--   vec_mul_vec w v = (col w) ⬝ (row v) :=
-- by { ext i j, simp [vec_mul_vec, mul_apply], refl }

-- theorem smul_mul_vec_assoc (A : Matrix m n α) (b : n → α) (a : α) :
--   (a • A).mul_vec b = a • (A.mul_vec b) :=
-- by { ext, apply smul_dot_product }

-- theorem mul_vec_add (A : Matrix m n α) (x y : n → α) :
--   A.mul_vec (x + y) = A.mul_vec x + A.mul_vec y :=
-- by { ext, apply dot_product_add }

-- theorem add_mul_vec (A B : Matrix m n α) (x : n → α) :
--   (A + B).mul_vec x = A.mul_vec x + B.mul_vec x :=
-- by { ext, apply add_dot_product }

-- theorem vec_mul_add (A B : Matrix m n α) (x : m → α) :
--   vec_mul x (A + B) = vec_mul x A + vec_mul x B :=
-- by { ext, apply dot_product_add }

-- theorem add_vec_mul (A : Matrix m n α) (x y : m → α) :
--   vec_mul (x + y) A = vec_mul x A + vec_mul y A :=
-- by { ext, apply add_dot_product }

-- variables [decidable_eq m] [decidable_eq n]

-- /--
-- `std_basis_Matrix i j a` is the Matrix with `a` in the `i`-th row, `j`-th column,
-- and zeroes elsewhere.
-- -/
-- def std_basis_Matrix (i : m) (j : n) (a : α) : Matrix m n α :=
-- (λ i' j', if i' = i ∧ j' = j then a else 0)

-- @[simp] theorem smul_std_basis_Matrix (i : m) (j : n) (a b : α) :
-- b • std_basis_Matrix i j a = std_basis_Matrix i j (b • a) :=
-- by { unfold std_basis_Matrix, ext, simp }

-- @[simp] theorem std_basis_Matrix_zero (i : m) (j : n) :
-- std_basis_Matrix i j (0 : α) = 0 :=
-- by { unfold std_basis_Matrix, ext, simp }

-- theorem std_basis_Matrix_add (i : m) (j : n) (a b : α) :
-- std_basis_Matrix i j (a + b) = std_basis_Matrix i j a + std_basis_Matrix i j b :=
-- begin
--   unfold std_basis_Matrix, ext,
--   split_ifs with h; simp [h],
-- end

-- theorem Matrix_eq_sum_std_basis (x : Matrix n m α) :
--   x = ∑ (i : n) (j : m), std_basis_Matrix i j (x i j) :=
-- begin
--   ext, symmetry,
--   iterate 2 { rw finset.sum_apply },
--   convert Fintype.sum_eq_single i _,
--   { simp [std_basis_Matrix] },
--   { intros j hj,
--     simp [std_basis_Matrix, hj.symm] }
-- end

-- -- TODO: tie this up with the `basis` machinery of linear algebra
-- -- this is not completely trivial because we are indexing by two types, instead of one

-- -- TODO: add `std_basis_vec`
-- theorem std_basis_eq_basis_mul_basis (i : m) (j : n) :
-- std_basis_Matrix i j 1 = vec_mul_vec (λ i', ite (i = i') 1 0) (λ j', ite (j = j') 1 0) :=
-- begin
--   ext, norm_num [std_basis_Matrix, vec_mul_vec],
--   split_ifs; tauto,
-- end

-- @[elab_as_eliminator] protected theorem induction_on'
--   {X : Type*} [semiring X] {M : Matrix n n X → Prop} (m : Matrix n n X)
--   (h_zero : M 0)
--   (h_add : ∀p q, M p → M q → M (p + q))
--   (h_std_basis : ∀ i j x, M (std_basis_Matrix i j x)) :
--   M m :=
-- begin
--   rw [Matrix_eq_sum_std_basis m, ← finset.sum_product'],
--   apply finset.sum_induction _ _ h_add h_zero,
--   { intros, apply h_std_basis, }
-- end

-- @[elab_as_eliminator] protected theorem induction_on
--   [nonempty n] {X : Type*} [semiring X] {M : Matrix n n X → Prop} (m : Matrix n n X)
--   (h_add : ∀p q, M p → M q → M (p + q))
--   (h_std_basis : ∀ i j x, M (std_basis_Matrix i j x)) :
--   M m :=
-- Matrix.induction_on' m
-- begin
--   have i : n := classical.choice (by assumption),
--   simpa using h_std_basis i i 0,
-- end
-- h_add h_std_basis

-- end semiring

-- section ring

-- variables [ring α]

-- theorem neg_vec_mul (v : m → α) (A : Matrix m n α) : vec_mul (-v) A = - vec_mul v A :=
-- by { ext, apply neg_dot_product }

-- theorem vec_mul_neg (v : m → α) (A : Matrix m n α) : vec_mul v (-A) = - vec_mul v A :=
-- by { ext, apply dot_product_neg }

-- theorem neg_mul_vec (v : n → α) (A : Matrix m n α) : mul_vec (-A) v = - mul_vec A v :=
-- by { ext, apply neg_dot_product }

-- theorem mul_vec_neg (v : n → α) (A : Matrix m n α) : mul_vec A (-v) = - mul_vec A v :=
-- by { ext, apply dot_product_neg }

-- end ring

-- section comm_semiring

-- variables [comm_semiring α]

-- theorem mul_vec_smul_assoc (A : Matrix m n α) (b : n → α) (a : α) :
--   A.mul_vec (a • b) = a • (A.mul_vec b) :=
-- by { ext, apply dot_product_smul }

-- theorem mul_vec_transpose (A : Matrix m n α) (x : m → α) :
--   mul_vec Aᵀ x = vec_mul x A :=
-- by { ext, apply dot_product_comm }

-- theorem vec_mul_transpose (A : Matrix m n α) (x : n → α) :
--   vec_mul x Aᵀ = mul_vec A x :=
-- by { ext, apply dot_product_comm }

-- end comm_semiring

-- section transpose

-- open_locale Matrix

-- /--
--   Tell `simp` what the entries are in a transposed Matrix.
--   Compare with `mul_apply`, `diagonal_apply_eq`, etc.
-- -/
-- @[simp] theorem transpose_apply (M : Matrix m n α) (i j) : M.transpose j i = M i j := rfl

-- @[simp] theorem transpose_transpose (M : Matrix m n α) :
--   Mᵀᵀ = M :=
-- by ext; refl

-- @[simp] theorem transpose_zero [has_zero α] : (0 : Matrix m n α)ᵀ = 0 :=
-- by ext i j; refl

-- @[simp] theorem transpose_one [decidable_eq n] [has_zero α] [has_one α] : (1 : Matrix n n α)ᵀ = 1 :=
-- begin
--   ext i j,
--   unfold has_one.one transpose,
--   by_cases i = j,
--   { simp only [h, diagonal_apply_eq] },
--   { simp only [diagonal_apply_ne h, diagonal_apply_ne (λ p, h (symm p))] }
-- end

-- @[simp] theorem transpose_add [has_add α] (M : Matrix m n α) (N : Matrix m n α) :
--   (M + N)ᵀ = Mᵀ + Nᵀ  :=
-- by { ext i j, simp }

-- @[simp] theorem transpose_sub [add_group α] (M : Matrix m n α) (N : Matrix m n α) :
--   (M - N)ᵀ = Mᵀ - Nᵀ  :=
-- by { ext i j, simp }

-- @[simp] theorem transpose_mul [comm_semiring α] (M : Matrix m n α) (N : Matrix n l α) :
--   (M ⬝ N)ᵀ = Nᵀ ⬝ Mᵀ  :=
-- begin
--   ext i j,
--   apply dot_product_comm
-- end

-- @[simp] theorem transpose_smul [semiring α] (c : α) (M : Matrix m n α) :
--   (c • M)ᵀ = c • Mᵀ :=
-- by { ext i j, refl }

-- @[simp] theorem transpose_neg [has_neg α] (M : Matrix m n α) :
--   (- M)ᵀ = - Mᵀ  :=
-- by ext i j; refl

-- theorem transpose_map {f : α → β} {M : Matrix m n α} : Mᵀ.map f = (M.map f)ᵀ :=
-- by { ext, refl }

-- end transpose

-- section star_ring
-- variables [decidable_eq n] [semiring α] [star_ring α]

-- /--
-- When `R` is a `*`-(semi)ring, `Matrix n n R` becomes a `*`-(semi)ring with
-- the star operation given by taking the conjugate, and the star of each entry.
-- -/
-- instance : star_ring (Matrix n n α) :=
-- { star := λ M, M.transpose.map star,
--   star_involutive := λ M, by { ext, simp, },
--   star_add := λ M N, by { ext, simp, },
--   star_mul := λ M N, by { ext, simp [mul_apply], }, }

-- @[simp] theorem star_apply (M : Matrix n n α) (i j) : star M i j = star (M j i) := rfl

-- theorem star_mul (M N : Matrix n n α) : star (M ⬝ N) = star N ⬝ star M := star_mul _ _

-- end star_ring

-- /-- `M.minor row col` is the Matrix obtained by reindexing the rows and the lines of
--     `M`, such that `M.minor row col i j = M (row i) (col j)`. Note that the total number
--     of row/colums doesn't have to be preserved. -/
-- def minor (A : Matrix m n α) (row : l → m) (col : o → n) : Matrix l o α :=
-- λ i j, A (row i) (col j)

-- @[simp] theorem minor_apply (A : Matrix m n α) (row : l → m) (col : o → n) (i j) :
--   A.minor row col i j = A (row i) (col j) := rfl

-- @[simp] theorem minor_id_id (A : Matrix m n α) :
--   A.minor id id = A :=
-- ext $ λ _ _, rfl

-- @[simp] theorem minor_minor {l₂ o₂ : Type*} [Fintype l₂] [Fintype o₂] (A : Matrix m n α)
--   (row₁ : l → m) (col₁ : o → n) (row₂ : l₂ → l) (col₂ : o₂ → o) :
--   (A.minor row₁ col₁).minor row₂ col₂ = A.minor (row₁ ∘ row₂) (col₁ ∘ col₂) :=
-- ext $ λ _ _, rfl

-- @[simp] theorem transpose_minor (A : Matrix m n α) (row : l → m) (col : o → n) :
--   (A.minor row col)ᵀ = Aᵀ.minor col row :=
-- ext $ λ _ _, rfl

-- theorem minor_add [has_add α] (A B : Matrix m n α) :
--   ((A + B).minor : (l → m) → (o → n) → Matrix l o α) = A.minor + B.minor := rfl

-- theorem minor_neg [has_neg α] (A : Matrix m n α) :
--   ((-A).minor : (l → m) → (o → n) → Matrix l o α) = -A.minor := rfl

-- theorem minor_sub [has_sub α] (A B : Matrix m n α) :
--   ((A - B).minor : (l → m) → (o → n) → Matrix l o α) = A.minor - B.minor := rfl

-- @[simp]
-- theorem minor_zero [has_zero α] :
--   ((0 : Matrix m n α).minor : (l → m) → (o → n) → Matrix l o α) = 0 := rfl

-- theorem minor_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α] (r : R)
--   (A : Matrix m n α) :
--   ((r • A : Matrix m n α).minor : (l → m) → (o → n) → Matrix l o α) = r • A.minor := rfl

-- /-- If the minor doesn't repeat elements, then when applied to a diagonal Matrix the result is
-- diagonal. -/
-- theorem minor_diagonal [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α) (e : l → m)
--   (he : function.injective e) :
--   (diagonal d).minor e e = diagonal (d ∘ e) :=
-- ext $ λ i j, begin
--   rw minor_apply,
--   by_cases h : i = j,
--   { rw [h, diagonal_apply_eq, diagonal_apply_eq], },
--   { rw [diagonal_apply_ne h, diagonal_apply_ne (he.ne h)], },
-- end

-- theorem minor_one [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l → m)
--   (he : function.injective e) :
--   (1 : Matrix m m α).minor e e = 1 :=
-- minor_diagonal _ e he

-- theorem minor_mul [semiring α] {p q : Type*} [Fintype p] [Fintype q]
--   (M : Matrix m n α) (N : Matrix n p α)
--   (e₁ : l → m) (e₂ : o → n) (e₃ : q → p) (he₂ : function.bijective e₂) :
--   (M ⬝ N).minor e₁ e₃ = (M.minor e₁ e₂) ⬝ (N.minor e₂ e₃) :=
-- ext $ λ _ _, (he₂.sum_comp _).symm

-- /-! `simp` theorems for `Matrix.minor`s interaction with `Matrix.diagonal`, `1`, and `Matrix.mul` for
-- when the mappings are bundled. -/

-- @[simp]
-- theorem minor_diagonal_embedding [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α)
--   (e : l ↪ m) :
--   (diagonal d).minor e e = diagonal (d ∘ e) :=
-- minor_diagonal d e e.injective

-- @[simp]
-- theorem minor_diagonal_equiv [has_zero α] [decidable_eq m] [decidable_eq l] (d : m → α)
--   (e : l ≃ m) :
--   (diagonal d).minor e e = diagonal (d ∘ e) :=
-- minor_diagonal d e e.injective

-- @[simp]
-- theorem minor_one_embedding [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l ↪ m) :
--   (1 : Matrix m m α).minor e e = 1 :=
-- minor_one e e.injective

-- @[simp]
-- theorem minor_one_equiv [has_zero α] [has_one α] [decidable_eq m] [decidable_eq l] (e : l ≃ m) :
--   (1 : Matrix m m α).minor e e = 1 :=
-- minor_one e e.injective

-- theorem minor_mul_equiv [semiring α] {p q : Type*} [Fintype p] [Fintype q]
--   (M : Matrix m n α) (N : Matrix n p α) (e₁ : l → m) (e₂ : o ≃ n) (e₃ : q → p)  :
--   (M ⬝ N).minor e₁ e₃ = (M.minor e₁ e₂) ⬝ (N.minor e₂ e₃) :=
-- minor_mul M N e₁ e₂ e₃ e₂.bijective

-- /-- The natural map that reindexes a Matrix's rows and columns with equivalent types is an
-- equivalence. -/
-- def reindex (eₘ : m ≃ l) (eₙ : n ≃ o) : Matrix m n α ≃ Matrix l o α :=
-- { to_fun    := λ M, M.minor eₘ.symm eₙ.symm,
--   inv_fun   := λ M, M.minor eₘ eₙ,
--   left_inv  := λ M, by simp,
--   right_inv := λ M, by simp, }

-- @[simp] theorem reindex_apply (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
--   reindex eₘ eₙ M = M.minor eₘ.symm eₙ.symm :=
-- rfl

-- @[simp] theorem reindex_refl_refl (A : Matrix m n α) :
--   reindex (equiv.refl _) (equiv.refl _) A = A :=
-- A.minor_id_id

-- @[simp] theorem reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
--   (reindex eₘ eₙ).symm = (reindex eₘ.symm eₙ.symm : Matrix l o α ≃ _) :=
-- rfl

-- @[simp] theorem reindex_trans {l₂ o₂ : Type*} [Fintype l₂] [Fintype o₂]
--   (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂) (eₙ₂ : o ≃ o₂) :
--   (reindex eₘ eₙ).trans (reindex eₘ₂ eₙ₂) =
--     (reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) : Matrix m n α ≃ _) :=
-- equiv.ext $ λ A, (A.minor_minor eₘ.symm eₙ.symm eₘ₂.symm eₙ₂.symm : _)

-- theorem transpose_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
--   (reindex eₘ eₙ M)ᵀ = (reindex eₙ eₘ Mᵀ) :=
-- rfl

-- /-- The left `n × l` part of a `n × (l+r)` Matrix. -/
-- @[reducible]
-- def sub_left {m l r : nat} (A : Matrix (fin m) (fin (l + r)) α) : Matrix (fin m) (fin l) α :=
-- minor A id (fin.cast_add r)

-- /-- The right `n × r` part of a `n × (l+r)` Matrix. -/
-- @[reducible]
-- def sub_right {m l r : nat} (A : Matrix (fin m) (fin (l + r)) α) : Matrix (fin m) (fin r) α :=
-- minor A id (fin.nat_add l)

-- /-- The top `u × n` part of a `(u+d) × n` Matrix. -/
-- @[reducible]
-- def sub_up {d u n : nat} (A : Matrix (fin (u + d)) (fin n) α) : Matrix (fin u) (fin n) α :=
-- minor A (fin.cast_add d) id

-- /-- The bottom `d × n` part of a `(u+d) × n` Matrix. -/
-- @[reducible]
-- def sub_down {d u n : nat} (A : Matrix (fin (u + d)) (fin n) α) : Matrix (fin d) (fin n) α :=
-- minor A (fin.nat_add u) id

-- /-- The top-right `u × r` part of a `(u+d) × (l+r)` Matrix. -/
-- @[reducible]
-- def sub_up_right {d u l r : nat} (A: Matrix (fin (u + d)) (fin (l + r)) α) :
--   Matrix (fin u) (fin r) α :=
-- sub_up (sub_right A)

-- /-- The bottom-right `d × r` part of a `(u+d) × (l+r)` Matrix. -/
-- @[reducible]
-- def sub_down_right {d u l r : nat} (A : Matrix (fin (u + d)) (fin (l + r)) α) :
--   Matrix (fin d) (fin r) α :=
-- sub_down (sub_right A)

-- /-- The top-left `u × l` part of a `(u+d) × (l+r)` Matrix. -/
-- @[reducible]
-- def sub_up_left {d u l r : nat} (A : Matrix (fin (u + d)) (fin (l + r)) α) :
--   Matrix (fin u) (fin (l)) α :=
-- sub_up (sub_left A)

-- /-- The bottom-left `d × l` part of a `(u+d) × (l+r)` Matrix. -/
-- @[reducible]
-- def sub_down_left {d u l r : nat} (A: Matrix (fin (u + d)) (fin (l + r)) α) :
--   Matrix (fin d) (fin (l)) α :=
-- sub_down (sub_left A)

-- section row_col
-- /-!
-- ### `row_col` section
-- Simplification theorems for `Matrix.row` and `Matrix.col`.
-- -/
-- open_locale Matrix

-- @[simp] theorem col_add [semiring α] (v w : m → α) : col (v + w) = col v + col w := by { ext, refl }
-- @[simp] theorem col_smul [semiring α] (x : α) (v : m → α) : col (x • v) = x • col v :=
-- by { ext, refl }
-- @[simp] theorem row_add [semiring α] (v w : m → α) : row (v + w) = row v + row w := by { ext, refl }
-- @[simp] theorem row_smul [semiring α] (x : α) (v : m → α) : row (x • v) = x • row v :=
-- by { ext, refl }

-- @[simp] theorem col_apply (v : m → α) (i j) : Matrix.col v i j = v i := rfl
-- @[simp] theorem row_apply (v : m → α) (i j) : Matrix.row v i j = v j := rfl

-- @[simp]
-- theorem transpose_col (v : m → α) : (Matrix.col v).transpose = Matrix.row v := by {ext, refl}
-- @[simp]
-- theorem transpose_row (v : m → α) : (Matrix.row v).transpose = Matrix.col v := by {ext, refl}

-- theorem row_vec_mul [semiring α] (M : Matrix m n α) (v : m → α) :
--   Matrix.row (Matrix.vec_mul v M) = Matrix.row v ⬝ M := by {ext, refl}
-- theorem col_vec_mul [semiring α] (M : Matrix m n α) (v : m → α) :
--   Matrix.col (Matrix.vec_mul v M) = (Matrix.row v ⬝ M)ᵀ := by {ext, refl}
-- theorem col_mul_vec [semiring α] (M : Matrix m n α) (v : n → α) :
--   Matrix.col (Matrix.mul_vec M v) = M ⬝ Matrix.col v := by {ext, refl}
-- theorem row_mul_vec [semiring α] (M : Matrix m n α) (v : n → α) :
--   Matrix.row (Matrix.mul_vec M v) = (M ⬝ Matrix.col v)ᵀ := by {ext, refl}

-- end row_col

-- section update

-- /-- Update, i.e. replace the `i`th row of Matrix `A` with the values in `b`. -/
-- def update_row [decidable_eq n] (M : Matrix n m α) (i : n) (b : m → α) : Matrix n m α :=
-- function.update M i b

-- /-- Update, i.e. replace the `j`th column of Matrix `A` with the values in `b`. -/
-- def update_column [decidable_eq m] (M : Matrix n m α) (j : m) (b : n → α) : Matrix n m α :=
-- λ i, function.update (M i) j (b i)

-- variables {M : Matrix n m α} {i : n} {j : m} {b : m → α} {c : n → α}

-- @[simp] theorem update_row_self [decidable_eq n] : update_row M i b i = b :=
-- function.update_same i b M

-- @[simp] theorem update_column_self [decidable_eq m] : update_column M j c i j = c i :=
-- function.update_same j (c i) (M i)

-- @[simp] theorem update_row_ne [decidable_eq n] {i' : n} (i_ne : i' ≠ i) :
--   update_row M i b i' = M i' := function.update_noteq i_ne b M

-- @[simp] theorem update_column_ne [decidable_eq m] {j' : m} (j_ne : j' ≠ j) :
--   update_column M j c i j' = M i j' := function.update_noteq j_ne (c i) (M i)

-- theorem update_row_apply [decidable_eq n] {i' : n} :
--   update_row M i b i' j = if i' = i then b j else M i' j :=
-- begin
--   by_cases i' = i,
--   { rw [h, update_row_self, if_pos rfl] },
--   { rwa [update_row_ne h, if_neg h] }
-- end

-- theorem update_column_apply [decidable_eq m] {j' : m} :
--   update_column M j c i j' = if j' = j then c i else M i j' :=
-- begin
--   by_cases j' = j,
--   { rw [h, update_column_self, if_pos rfl] },
--   { rwa [update_column_ne h, if_neg h] }
-- end

-- theorem update_row_transpose [decidable_eq m] : update_row Mᵀ j c = (update_column M j c)ᵀ :=
-- begin
--   ext i' j,
--   rw [transpose_apply, update_row_apply, update_column_apply],
--   refl
-- end

-- theorem update_column_transpose [decidable_eq n] : update_column Mᵀ i b = (update_row M i b)ᵀ :=
-- begin
--   ext i' j,
--   rw [transpose_apply, update_row_apply, update_column_apply],
--   refl
-- end

-- @[simp] theorem update_row_eq_self [decidable_eq m]
--   (A : Matrix m n α) {i : m} :
--   A.update_row i (A i) = A :=
-- function.update_eq_self i A

-- @[simp] theorem update_column_eq_self [decidable_eq n]
--   (A : Matrix m n α) {i : n} :
--   A.update_column i (λ j, A j i) = A :=
-- funext $ λ j, function.update_eq_self i (A j)

-- end update

-- section block_matrices

-- /-- We can form a single large Matrix by flattening smaller 'block' matrices of compatible
-- dimensions. -/
-- def from_blocks (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
--   Matrix (n ⊕ o) (l ⊕ m) α :=
-- sum.elim (λ i, sum.elim (A i) (B i))
--          (λ i, sum.elim (C i) (D i))

-- @[simp] theorem from_blocks_apply₁₁
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : n) (j : l) :
--   from_blocks A B C D (sum.inl i) (sum.inl j) = A i j :=
-- rfl

-- @[simp] theorem from_blocks_apply₁₂
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : n) (j : m) :
--   from_blocks A B C D (sum.inl i) (sum.inr j) = B i j :=
-- rfl

-- @[simp] theorem from_blocks_apply₂₁
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : o) (j : l) :
--   from_blocks A B C D (sum.inr i) (sum.inl j) = C i j :=
-- rfl

-- @[simp] theorem from_blocks_apply₂₂
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) (i : o) (j : m) :
--   from_blocks A B C D (sum.inr i) (sum.inr j) = D i j :=
-- rfl

-- /-- Given a Matrix whose row and column indexes are sum types, we can extract the corresponding
-- "top left" subMatrix. -/
-- def to_blocks₁₁ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix n l α :=
-- λ i j, M (sum.inl i) (sum.inl j)

-- /-- Given a Matrix whose row and column indexes are sum types, we can extract the corresponding
-- "top right" subMatrix. -/
-- def to_blocks₁₂ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix n m α :=
-- λ i j, M (sum.inl i) (sum.inr j)

-- /-- Given a Matrix whose row and column indexes are sum types, we can extract the corresponding
-- "bottom left" subMatrix. -/
-- def to_blocks₂₁ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix o l α :=
-- λ i j, M (sum.inr i) (sum.inl j)

-- /-- Given a Matrix whose row and column indexes are sum types, we can extract the corresponding
-- "bottom right" subMatrix. -/
-- def to_blocks₂₂ (M : Matrix (n ⊕ o) (l ⊕ m) α) : Matrix o m α :=
-- λ i j, M (sum.inr i) (sum.inr j)

-- theorem from_blocks_to_blocks (M : Matrix (n ⊕ o) (l ⊕ m) α) :
--   from_blocks M.to_blocks₁₁ M.to_blocks₁₂ M.to_blocks₂₁ M.to_blocks₂₂ = M :=
-- begin
--   ext i j, rcases i; rcases j; refl,
-- end

-- @[simp] theorem to_blocks_from_blocks₁₁
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
--   (from_blocks A B C D).to_blocks₁₁ = A :=
-- rfl

-- @[simp] theorem to_blocks_from_blocks₁₂
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
--   (from_blocks A B C D).to_blocks₁₂ = B :=
-- rfl

-- @[simp] theorem to_blocks_from_blocks₂₁
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
--   (from_blocks A B C D).to_blocks₂₁ = C :=
-- rfl

-- @[simp] theorem to_blocks_from_blocks₂₂
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
--   (from_blocks A B C D).to_blocks₂₂ = D :=
-- rfl

-- theorem from_blocks_transpose
--   (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
--   (from_blocks A B C D)ᵀ = from_blocks Aᵀ Cᵀ Bᵀ Dᵀ :=
-- begin
--   ext i j, rcases i; rcases j; simp [from_blocks],
-- end

-- /-- Let `p` pick out certain rows and `q` pick out certain columns of a Matrix `M`. Then
--   `to_block M p q` is the corresponding block Matrix. -/
-- def to_block (M : Matrix m n α) (p : m → Prop) [decidable_pred p]
--   (q : n → Prop) [decidable_pred q] : Matrix {a // p a} {a // q a} α := M.minor coe coe

-- @[simp] theorem to_block_apply (M : Matrix m n α) (p : m → Prop) [decidable_pred p]
--   (q : n → Prop) [decidable_pred q] (i : {a // p a}) (j : {a // q a}) :
--   to_block M p q i j = M ↑i ↑j := rfl

-- /-- Let `b` map rows and columns of a square Matrix `M` to blocks. Then
--   `to_square_block M b k` is the block `k` Matrix. -/
-- def to_square_block (M : Matrix m m α) {n : nat} (b : m → fin n) (k : fin n) :
--   Matrix {a // b a = k} {a // b a = k} α := M.minor coe coe

-- @[simp] theorem to_square_block_def (M : Matrix m m α) {n : nat} (b : m → fin n) (k : fin n) :
--   to_square_block M b k = λ i j, M ↑i ↑j := rfl

-- /-- Alternate version with `b : m → nat`. Let `b` map rows and columns of a square Matrix `M` to
--   blocks. Then `to_square_block' M b k` is the block `k` Matrix. -/
-- def to_square_block' (M : Matrix m m α) (b : m → nat) (k : nat) :
--   Matrix {a // b a = k} {a // b a = k} α := M.minor coe coe

-- @[simp] theorem to_square_block_def' (M : Matrix m m α) (b : m → nat) (k : nat) :
--   to_square_block' M b k = λ i j, M ↑i ↑j := rfl

-- /-- Let `p` pick out certain rows and columns of a square Matrix `M`. Then
--   `to_square_block_prop M p` is the corresponding block Matrix. -/
-- def to_square_block_prop (M : Matrix m m α) (p : m → Prop) [decidable_pred p] :
--   Matrix {a // p a} {a // p a} α := M.minor coe coe

-- @[simp] theorem to_square_block_prop_def (M : Matrix m m α) (p : m → Prop) [decidable_pred p] :
--   to_square_block_prop M p = λ i j, M ↑i ↑j := rfl

-- variables [semiring α]

-- theorem from_blocks_smul
--   (x : α) (A : Matrix n l α) (B : Matrix n m α) (C : Matrix o l α) (D : Matrix o m α) :
--   x • (from_blocks A B C D) = from_blocks (x • A) (x • B) (x • C) (x • D) :=
-- begin
--   ext i j, rcases i; rcases j; simp [from_blocks],
-- end

-- theorem from_blocks_add
--   (A  : Matrix n l α) (B  : Matrix n m α) (C  : Matrix o l α) (D  : Matrix o m α)
--   (A' : Matrix n l α) (B' : Matrix n m α) (C' : Matrix o l α) (D' : Matrix o m α) :
--   (from_blocks A B C D) + (from_blocks A' B' C' D') =
--   from_blocks (A + A') (B + B')
--               (C + C') (D + D') :=
-- begin
--   ext i j, rcases i; rcases j; refl,
-- end

-- theorem from_blocks_multiply {p q : Type*} [Fintype p] [Fintype q]
--   (A  : Matrix n l α) (B  : Matrix n m α) (C  : Matrix o l α) (D  : Matrix o m α)
--   (A' : Matrix l p α) (B' : Matrix l q α) (C' : Matrix m p α) (D' : Matrix m q α) :
--   (from_blocks A B C D) ⬝ (from_blocks A' B' C' D') =
--   from_blocks (A ⬝ A' + B ⬝ C') (A ⬝ B' + B ⬝ D')
--               (C ⬝ A' + D ⬝ C') (C ⬝ B' + D ⬝ D') :=
-- begin
--   ext i j, rcases i; rcases j;
--   simp only [from_blocks, mul_apply, Fintype.sum_sum_type, sum.elim_inl, sum.elim_inr,
--     pi.add_apply],
-- end

-- variables [decidable_eq l] [decidable_eq m]

-- @[simp] theorem from_blocks_diagonal (d₁ : l → α) (d₂ : m → α) :
--   from_blocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (sum.elim d₁ d₂) :=
-- begin
--   ext i j, rcases i; rcases j; simp [diagonal],
-- end

-- @[simp] theorem from_blocks_one : from_blocks (1 : Matrix l l α) 0 0 (1 : Matrix m m α) = 1 :=
-- by { ext i j, rcases i; rcases j; simp [one_apply] }

-- end block_matrices

-- section block_diagonal

-- variables (M N : o → Matrix m n α) [decidable_eq o]

-- section has_zero

-- variables [has_zero α]

-- /-- `Matrix.block_diagonal M` turns a homogenously-indexed collection of matrices
-- `M : o → Matrix m n α'` into a `m × o`-by-`n × o` block Matrix which has the entries of `M` along
-- the diagonal and zero elsewhere.
-- See also `Matrix.block_diagonal'` if the matrices may not have the same size everywhere.
-- -/
-- def block_diagonal : Matrix (m × o) (n × o) α
-- | ⟨i, k⟩ ⟨j, k'⟩ := if k = k' then M k i j else 0

-- theorem block_diagonal_apply (ik jk) :
--   block_diagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 :=
-- by { cases ik, cases jk, refl }

-- @[simp]
-- theorem block_diagonal_apply_eq (i j k) :
--   block_diagonal M (i, k) (j, k) = M k i j :=
-- if_pos rfl

-- theorem block_diagonal_apply_ne (i j) {k k'} (h : k ≠ k') :
--   block_diagonal M (i, k) (j, k') = 0 :=
-- if_neg h

-- @[simp] theorem block_diagonal_transpose :
--   (block_diagonal M)ᵀ = block_diagonal (λ k, (M k)ᵀ) :=
-- begin
--   ext,
--   simp only [transpose_apply, block_diagonal_apply, eq_comm],
--   split_ifs with h,
--   { rw h },
--   { refl }
-- end

-- @[simp] theorem block_diagonal_zero :
--   block_diagonal (0 : o → Matrix m n α) = 0 :=
-- by { ext, simp [block_diagonal_apply] }

-- @[simp] theorem block_diagonal_diagonal [decidable_eq m] (d : o → m → α) :
--   block_diagonal (λ k, diagonal (d k)) = diagonal (λ ik, d ik.2 ik.1) :=
-- begin
--   ext ⟨i, k⟩ ⟨j, k'⟩,
--   simp only [block_diagonal_apply, diagonal],
--   split_ifs; finish
-- end

-- @[simp] theorem block_diagonal_one [decidable_eq m] [has_one α] :
--   block_diagonal (1 : o → Matrix m m α) = 1 :=
-- show block_diagonal (λ (_ : o), diagonal (λ (_ : m), (1 : α))) = diagonal (λ _, 1),
-- by rw [block_diagonal_diagonal]

-- end has_zero

-- @[simp] theorem block_diagonal_add [add_monoid α] :
--   block_diagonal (M + N) = block_diagonal M + block_diagonal N :=
-- begin
--   ext,
--   simp only [block_diagonal_apply, add_apply],
--   split_ifs; simp
-- end

-- @[simp] theorem block_diagonal_neg [add_group α] :
--   block_diagonal (-M) = - block_diagonal M :=
-- begin
--   ext,
--   simp only [block_diagonal_apply, neg_apply],
--   split_ifs; simp
-- end

-- @[simp] theorem block_diagonal_sub [add_group α] :
--   block_diagonal (M - N) = block_diagonal M - block_diagonal N :=
-- by simp [sub_eq_add_neg]

-- @[simp] theorem block_diagonal_mul {p : Type*} [Fintype p] [semiring α] (N : o → Matrix n p α) :
--   block_diagonal (λ k, M k ⬝ N k) = block_diagonal M ⬝ block_diagonal N :=
-- begin
--   ext ⟨i, k⟩ ⟨j, k'⟩,
--   simp only [block_diagonal_apply, mul_apply, ← finset.univ_product_univ, finset.sum_product],
--   split_ifs with h; simp [h]
-- end

-- @[simp] theorem block_diagonal_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α]
--   (x : R) : block_diagonal (x • M) = x • block_diagonal M :=
-- by { ext, simp only [block_diagonal_apply, pi.smul_apply], split_ifs; simp }

-- end block_diagonal

-- section block_diagonal'

-- variables (M N : Π i, Matrix (m' i) (n' i) α) [decidable_eq o]

-- section has_zero

-- variables [has_zero α]

-- /-- `Matrix.block_diagonal' M` turns `M : Π i, Matrix (m i) (n i) α` into a
-- `Σ i, m i`-by-`Σ i, n i` block Matrix which has the entries of `M` along the diagonal
-- and zero elsewhere.
-- This is the dependently-typed version of `Matrix.block_diagonal`. -/
-- def block_diagonal' : Matrix (Σ i, m' i) (Σ i, n' i) α
-- | ⟨k, i⟩ ⟨k', j⟩ := if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0

-- theorem block_diagonal'_eq_block_diagonal (M : o → Matrix m n α) {k k'} (i j) :
--   block_diagonal M (i, k) (j, k') = block_diagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
-- rfl

-- theorem block_diagonal'_minor_eq_block_diagonal (M : o → Matrix m n α) :
--   (block_diagonal' M).minor (prod.to_sigma ∘ prod.swap) (prod.to_sigma ∘ prod.swap) =
--     block_diagonal M :=
-- Matrix.ext $ λ ⟨k, i⟩ ⟨k', j⟩, rfl

-- theorem block_diagonal'_apply (ik jk) :
--   block_diagonal' M ik jk = if h : ik.1 = jk.1 then
--     M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 :=
-- by { cases ik, cases jk, refl }

-- @[simp]
-- theorem block_diagonal'_apply_eq (k i j) :
--   block_diagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
-- dif_pos rfl

-- theorem block_diagonal'_apply_ne {k k'} (i j) (h : k ≠ k') :
--   block_diagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
-- dif_neg h

-- @[simp] theorem block_diagonal'_transpose :
--   (block_diagonal' M)ᵀ = block_diagonal' (λ k, (M k)ᵀ) :=
-- begin
--   ext ⟨ii, ix⟩ ⟨ji, jx⟩,
--   simp only [transpose_apply, block_diagonal'_apply, eq_comm],
--   dsimp only,
--   split_ifs with h₁ h₂ h₂,
--   { subst h₁, refl, },
--   { exact (h₂ h₁.symm).elim },
--   { exact (h₁ h₂.symm).elim },
--   { refl }
-- end

-- @[simp] theorem block_diagonal'_zero :
--   block_diagonal' (0 : Π i, Matrix (m' i) (n' i) α) = 0 :=
-- by { ext, simp [block_diagonal'_apply] }

-- @[simp] theorem block_diagonal'_diagonal [∀ i, decidable_eq (m' i)] (d : Π i, m' i → α) :
--   block_diagonal' (λ k, diagonal (d k)) = diagonal (λ ik, d ik.1 ik.2) :=
-- begin
--   ext ⟨i, k⟩ ⟨j, k'⟩,
--   simp only [block_diagonal'_apply, diagonal],
--   split_ifs; finish
-- end

-- @[simp] theorem block_diagonal'_one [∀ i, decidable_eq (m' i)] [has_one α] :
--   block_diagonal' (1 : Π i, Matrix (m' i) (m' i) α) = 1 :=
-- show block_diagonal' (λ (i : o), diagonal (λ (_ : m' i), (1 : α))) = diagonal (λ _, 1),
-- by rw [block_diagonal'_diagonal]

-- end has_zero

-- @[simp] theorem block_diagonal'_add [add_monoid α] :
--   block_diagonal' (M + N) = block_diagonal' M + block_diagonal' N :=
-- begin
--   ext,
--   simp only [block_diagonal'_apply, add_apply],
--   split_ifs; simp
-- end

-- @[simp] theorem block_diagonal'_neg [add_group α] :
--   block_diagonal' (-M) = - block_diagonal' M :=
-- begin
--   ext,
--   simp only [block_diagonal'_apply, neg_apply],
--   split_ifs; simp
-- end

-- @[simp] theorem block_diagonal'_sub [add_group α] :
--   block_diagonal' (M - N) = block_diagonal' M - block_diagonal' N :=
-- by simp [sub_eq_add_neg]

-- @[simp] theorem block_diagonal'_mul {p : o → Type*} [Π i, Fintype (p i)] [semiring α]
--   (N : Π i, Matrix (n' i) (p i) α) :
--     block_diagonal' (λ k, M k ⬝ N k) = block_diagonal' M ⬝ block_diagonal' N :=
-- begin
--   ext ⟨k, i⟩ ⟨k', j⟩,
--   simp only [block_diagonal'_apply, mul_apply, ← finset.univ_sigma_univ, finset.sum_sigma],
--   rw Fintype.sum_eq_single k,
--   { split_ifs; simp },
--   { intros j' hj', exact finset.sum_eq_zero (λ _ _, by rw [dif_neg hj'.symm, zero_mul]) },
-- end

-- @[simp] theorem block_diagonal'_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α]
--   (x : R) : block_diagonal' (x • M) = x • block_diagonal' M :=
-- by { ext, simp only [block_diagonal'_apply, pi.smul_apply], split_ifs; simp }

-- end block_diagonal'

-- end Matrix

-- namespace ring_hom
-- variables [semiring α] [semiring β]

-- theorem map_Matrix_mul (M : Matrix m n α) (N : Matrix n o α) (i : m) (j : o) (f : α →+* β) :
--   f (Matrix.mul M N i j) = Matrix.mul (λ i j, f (M i j)) (λ i j, f (N i j)) i j :=
-- by simp [Matrix.mul_apply, ring_hom.map_sum]

-- end ring_hom
