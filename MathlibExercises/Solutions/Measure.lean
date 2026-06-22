import Mathlib

/-!
# Measure theory

Three concrete results: the law of total probability for a finite
partition, the area of a right triangle as a Lebesgue measure, and (as a
bonus) Markov's inequality, each derived from more primitive measure-theory
facts rather than cited outright.
-/

namespace Solutions.Measure

open MeasureTheory
open scoped ENNReal

/-! ## Law of total probability

If a finite family of pairwise-disjoint measurable sets `A i` covers a
measurable `B`, then the measure of `B`
splits as the sum of the measures of its pieces in `A i`.
-/

theorem total_probability {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ι : Type*} (s : Finset ι) (A : ι → Set Ω) (B : Set Ω)
    (hA : ∀ i ∈ s, MeasurableSet (A i)) (hB : MeasurableSet B)
    (hdisj : (s : Set ι).PairwiseDisjoint A)
    (hcover : B ⊆ ⋃ i ∈ s, A i) :
    μ B = ∑ i ∈ s, μ (B ∩ A i) := by
  have hcover' : B = ⋃ i ∈ s, B ∩ A i := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hx
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hcover hx)
      exact ⟨i, hi, hx, hxi⟩
    · rintro ⟨i, _, hx, _⟩
      exact hx
  calc μ B = μ (⋃ i ∈ s, B ∩ A i) := by rw [← hcover']
    _ = ∑ i ∈ s, μ (B ∩ A i) :=
      measure_biUnion_finset (hdisj.mono fun _ => Set.inter_subset_right)
        fun i hi => hB.inter (hA i hi)

/-! ## Markov's inequality

For a nonnegative measurable `f` and `ε > 0`, the measure of `{f ≥ ε}`
times `ε` is bounded by the total integral of `f`.
-/

theorem markov_inequality {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ {x | ε ≤ f x} ≤ ∫⁻ a, f a ∂μ := by
  have hset : MeasurableSet {x | ε ≤ f x} := measurableSet_le measurable_const hf
  calc
    ε * μ {x | ε ≤ f x} = ∫⁻ _a in {x | ε ≤ f x}, ε ∂μ := (setLIntegral_const _ _).symm
    _ = ∫⁻ a, {x | ε ≤ f x}.indicator (fun _ => ε) a ∂μ := (lintegral_indicator hset _).symm
    _ ≤ ∫⁻ a, f a ∂μ := by
        apply lintegral_mono
        intro a
        by_cases ha : a ∈ {x | ε ≤ f x}
        · simpa [Set.indicator_of_mem ha] using ha
        · simp [Set.indicator_of_notMem ha]

/-! ## Area of a right triangle

The right triangle with legs `a` and `b` along the axes is the region
between the constant function `0` and the line `b * (1 - x / a)` over
`x ∈ [0, a]`; its Lebesgue measure works out to `a * b / 2`.
-/

theorem area_right_triangle (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (volume.prod volume)
      (regionBetween (fun _ => (0 : ℝ)) (fun x => b * (1 - x / a)) (Set.Icc 0 a))
      = ENNReal.ofReal (a * b / 2) := by
  have hg : Continuous fun x : ℝ => b * (1 - x / a) := by fun_prop
  have hint : (∫ y in Set.Icc (0 : ℝ) a,
      ((fun x : ℝ => b * (1 - x / a)) - (fun _ : ℝ => (0 : ℝ))) y)
      = a * b / 2 := by
    simp only [Pi.sub_apply, sub_zero]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha.le]
    have heq : ∀ x : ℝ, b * (1 - x / a) = b - b / a * x := fun x => by ring
    simp_rw [heq]
    have hf1 : Continuous fun _ : ℝ => b := continuous_const
    have hf2 : Continuous fun x : ℝ => b / a * x := by fun_prop
    rw [intervalIntegral.integral_sub (hf1.intervalIntegrable 0 a) (hf2.intervalIntegrable 0 a)]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    field_simp
    ring
  have hfg : ∀ x ∈ Set.Icc (0 : ℝ) a, (fun _ : ℝ => (0 : ℝ)) x ≤ (fun x => b * (1 - x / a)) x := by
    rintro x ⟨hx0, hxa⟩
    have hxa' : x / a ≤ 1 := (div_le_one ha).mpr hxa
    nlinarith
  rw [volume_regionBetween_eq_integral continuous_const.integrableOn_Icc hg.integrableOn_Icc
    measurableSet_Icc hfg, hint]

end Solutions.Measure
