import Mathlib

/-!
# Limits

Limits are expressed using `Filter.Tendsto f l₁ l₂`, read as `f` tends to `l₂` along `l₁`.
This encodes all(?) useful limits, such as tending to ∞, -∞, a point (careful, see below!), or
unbounded.
-/

namespace Exercises.Limits

open Filter Topology

/-! ## `filter_upwards`

`filter_upwards [h₁, h₂, ...] with x hx₁ hx₂` combines several `Eventually`
hypotheses into the single eventual fact you actually need, one bound per
named witness.
-/

theorem eventually_le_of_le_of_le {f g : ℕ → ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ g n)
    (hg : ∀ᶠ n in atTop, g n ≤ 5) :
    ∀ᶠ n in atTop, f n ≤ 5 := by sorry

/-! ## A limit at a point via `nhdsWithin`

The difference quotient `(x^2 - 4) / (x - 2)` is undefined at `x = 2`, so we
can't talk about continuity there — but it still has a limit as `x → 2`
through the *punctured* neighbourhood `𝓝[≠] 2`.
-/

theorem tendsto_removable_singularity :
    Tendsto (fun x : ℝ => (x ^ 2 - 4) / (x - 2)) (𝓝[≠] (2 : ℝ)) (𝓝 4) := by sorry

/-! ## A squeeze-theorem application
-/

theorem tendsto_sin_div_atTop :
    Tendsto (fun n : ℕ => Real.sin n / n) atTop (𝓝 0) := by sorry

end Exercises.Limits
