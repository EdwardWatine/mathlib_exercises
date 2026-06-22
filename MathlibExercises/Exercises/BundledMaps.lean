import Mathlib

/-!
# Bundled maps

-/

namespace Exercises.BundledMaps

/-! ## `Equiv`

-/

theorem forall_nonneg_shift_iff_forall_ge_five (P : ℤ → Prop) :
    (∀ m : ℤ, 0 ≤ m → P (m + 5)) ↔ ∀ n : ℤ, 5 ≤ n → P n := by sorry

/-! ## `LinearMap`

Scaling by a nonzero constant `c` is an injective linear map, so its kernel
is trivial.
-/

def scaleLM (c : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun x := c * x
  map_add' x y := by ring
  map_smul' r x := by simp only [smul_eq_mul, RingHom.id_apply]; ring

theorem scaleLM_ker_eq_bot {c : ℝ} (hc : c ≠ 0) : LinearMap.ker (scaleLM c) = ⊥ := by sorry

/-! ## `AddMonoidHom`

The range of the doubling map on `ℤ` is exactly the even integers.
-/

def doubleHom : ℤ →+ ℤ where
  toFun n := 2 * n
  map_zero' := by ring
  map_add' x y := by ring

theorem doubleHom_range_eq_even : Set.range doubleHom = {n : ℤ | Even n} := by sorry

end Exercises.BundledMaps
