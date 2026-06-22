import Mathlib

/-!
# Bundled maps

-/

namespace Solutions.BundledMaps

/-! ## `Equiv`

`Equiv.forall_congr` transfers a `∀`-statement across a bijection: given
`e : α ≃ β` and a pointwise correspondence between predicates `p` and `q`,
a fact about all of `α` becomes a fact about all of `β`. Using the
pre-existing shift equivalence `Equiv.addRight 5` on `ℤ`, a statement about
every integer `≥ 5` reindexes to a statement about every *nonnegative*
integer — exactly the "shift the induction to start at 0" move.
-/

theorem forall_nonneg_shift_iff_forall_ge_five (P : ℤ → Prop) :
    (∀ m : ℤ, 0 ≤ m → P (m + 5)) ↔ ∀ n : ℤ, 5 ≤ n → P n := by
  -- simp -- This doesn't work!
  apply (Equiv.addRight (5 : ℤ)).forall_congr
  simp -- this does!

/-! ## `LinearMap`

Scaling by a nonzero constant `c` is an injective linear map, so its kernel
is trivial.
-/

def scaleLM (c : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun x := c * x
  map_add' x y := by ring
  map_smul' r x := by simp only [smul_eq_mul, RingHom.id_apply]; ring

theorem scaleLM_ker_eq_bot {c : ℝ} (hc : c ≠ 0) : LinearMap.ker (scaleLM c) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro x y hxy
  simpa [scaleLM, hc] using hxy

/-! ## `AddMonoidHom`

The range of the doubling map on `ℤ` is exactly the even integers.
-/

def doubleHom : ℤ →+ ℤ where
  toFun n := 2 * n
  map_zero' := by ring
  map_add' x y := by ring

theorem doubleHom_range_eq_even : Set.range doubleHom = {n : ℤ | Even n} := by
  ext n
  simp only [Set.mem_range, Set.mem_setOf_eq]
  simp only [Even, ← two_mul, @eq_comm _ _ n]
  rfl

end Solutions.BundledMaps
