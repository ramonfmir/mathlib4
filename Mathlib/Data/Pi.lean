
import Mathlib.Algebra.Group.Defs

universes u v₁ v₂ v₃
variable {I : Type u}     -- The indexing type
-- The families of types already equipped with instances
variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}
variable (x y : ∀ i, f i) (i : I)

namespace Pi

instance Zero [∀ i, Zero $ f i] :
  Zero (∀ i : I, f i) :=
⟨fun _ => 0⟩

instance One [∀ i, One $ f i] :
  One (∀ i : I, f i) :=
⟨fun _ => 1⟩

end Pi
