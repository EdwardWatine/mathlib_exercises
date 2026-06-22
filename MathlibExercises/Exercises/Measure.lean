import Mathlib

/-!
# Measure theory
-/

namespace Exercises.Measure

open MeasureTheory
open scoped ENNReal

/-! ## Law of total probability

If a finite family of pairwise-disjoint measurable sets `A i` covers a
measurable `B` (not necessarily the whole space), then the measure of `B`
splits as the sum of the measures of its pieces inside each `A i`.
-/

theorem total_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι : Type*} (s : Finset ι) (A : ι → Set Ω) (B : Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hB : MeasurableSet B)
    (hdisj : (s : Set ι).PairwiseDisjoint A)
    (hcover : B ⊆ ⋃ i ∈ s, A i) :
    μ B = ∑ i ∈ s, μ (B ∩ A i) := by sorry

/-! ## Markov's inequality

For a nonnegative measurable `f` and `ε > 0`, the measure of `{f ≥ ε}`
times `ε` is bounded by the total integral of `f`.
-/

theorem markov_inequality {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ {x | ε ≤ f x} ≤ ∫⁻ a, f a ∂μ := by sorry

/-! ## Area of a right triangle

The right triangle with legs `a` and `b` along the axes is the region
between the constant function `0` and the line `b * (1 - x / a)` over
`x ∈ [0, a]`; its Lebesgue measure works out to `a * b / 2`.
-/

theorem area_right_triangle (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (volume.prod volume)
      (regionBetween (fun _ => (0 : ℝ)) (fun x => b * (1 - x / a)) (Set.Icc 0 a))
      = ENNReal.ofReal (a * b / 2) := by sorry

end Exercises.Measure
