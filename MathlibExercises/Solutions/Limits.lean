import Mathlib

/-!
# Limits

Three concrete results: combining `Eventually` facts with `filter_upwards`,
a one-sided/punctured limit phrased with `nhdsWithin`, and a squeeze-theorem
application, each worked out from more primitive facts rather than cited
outright.
-/

namespace Solutions.Limits

open Filter Topology

/-! ## `filter_upwards`

`filter_upwards [h₁, h₂, ...] with x hx₁ hx₂` combines several `Eventually`
hypotheses into the single eventual fact you actually need, one bound per
named witness.
-/

theorem eventually_le_of_le_of_le {f g : ℕ → ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ g n)
    (hg : ∀ᶠ n in atTop, g n ≤ 5) :
    ∀ᶠ n in atTop, f n ≤ 5 := by
  filter_upwards [hfg, hg] with n hfgn hgn
  linarith

/-! ## A limit at a point via `nhdsWithin`

The difference quotient `(x^2 - 4) / (x - 2)` is undefined at `x = 2`, so we
can't talk about continuity there — but it still has a limit as `x → 2`
through the *punctured* neighbourhood `𝓝[≠] 2`.
-/

theorem tendsto_removable_singularity :
    Tendsto (fun x : ℝ => (x ^ 2 - 4) / (x - 2)) (𝓝[≠] (2 : ℝ)) (𝓝 4) := by
  have heq : (fun x : ℝ => (x ^ 2 - 4) / (x - 2)) =ᶠ[𝓝[≠] (2 : ℝ)] (fun x => x + 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx2 : x - 2 ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring
  have hcont : Tendsto (fun x : ℝ => x + 2) (𝓝[≠] (2 : ℝ)) (𝓝 4) := by
    have hc : Continuous fun x : ℝ => x + 2 := by fun_prop
    have h2 : Tendsto (fun x : ℝ => x + 2) (𝓝 (2 : ℝ)) (𝓝 4) := by
      have h := hc.tendsto 2
      norm_num at h
      exact h
    exact h2.mono_left nhdsWithin_le_nhds
  exact hcont.congr' heq.symm

/-! ## A squeeze-theorem application

`sin n / n → 0`: the numerator is bounded while the denominator grows
without bound, made precise by sandwiching `‖sin n / n‖` between `0` and
`1 / n`.
-/

theorem tendsto_sin_div_atTop :
    Tendsto (fun n : ℕ => Real.sin n / n) atTop (𝓝 0) := by
  apply squeeze_zero_norm (a := fun n : ℕ => 1 / (n : ℝ))
  · intro n
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
    gcongr
    exact Real.abs_sin_le_one _
  · exact tendsto_one_div_atTop_nhds_zero_nat

end Solutions.Limits
