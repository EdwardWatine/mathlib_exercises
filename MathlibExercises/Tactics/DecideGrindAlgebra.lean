import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# The `decide` tactic

`decide` closes a goal by evaluating its `Decidable` instance to `isTrue`.
It works on any decidable proposition with no hypotheses needed, but can be
slow (or get stuck) if the instance has to do real computation.
-/

example : (12 : ℕ) % 5 = 2 := by decide

example : ¬ (5 ∣ 12 : Prop) := by decide

example : (3 : ℕ) < 7 ∧ (7 : ℕ) ≠ 3 := by decide

example : Nat.Prime 131 := by decide

/-!
# The `norm_num` tactic

`norm_num` is a closing tactic for numerical goals — arithmetic,
(in)equalities, divisibility, primality — and unlike `decide` it normalizes
through casts between numeric types (`ℕ`, `ℤ`, `ℚ`, `ℝ`, ...) instead of
getting stuck on them.
-/

example : (2 : ℕ) + 2 = 4 := by norm_num

example : (37 : ℕ).Prime := by norm_num

-- Casts get pushed through the arithmetic automatically.
example : ((2 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) = 5 := by norm_num

example (n : ℕ) : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_num

example : ((7 : ℤ) : ℚ) / 2 < 4 := by norm_num

/-!
# The `grind` tactic

`grind` is a general-purpose closing tactic: it combines congruence closure,
case splitting, and arithmetic/`simp`-like normalization to discharge a goal
in one step, without you naming any lemmas.
-/

example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by grind

example (p q : Prop) (h : p ↔ q) (hp : p) : q := by grind

example (a b c : ℤ) (hab : a < b) (hbc : b < c) : a < c := by grind

/-!
# `ring`, `abel`, and `group`

These are decision procedures for equalities in specific algebraic
structures — each normalizes both sides and checks they agree, so a
correct equation in the right structure closes in one line.
-/

-- `ring`: commutative (semi)rings.
example (a b : ℤ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring

example (a b c : ℤ) : a * (b + c) = a * b + a * c := by ring

-- `abel`: additive commutative groups (handles `+`, `-`, `neg`, `zsmul`).
example {G : Type*} [AddCommGroup G] (a b : G) : a + b - b = a := by abel

example {G : Type*} [AddCommGroup G] (a b c : G) : a + b + c = c + (b + a) := by abel

-- `group`: (possibly non-abelian) groups, normalizing `*`, `⁻¹`, and `zpow`.
example {G : Type*} [Group G] (a b : G) : a * b * b⁻¹ * a⁻¹ = 1 := by group

example {G : Type*} [Group G] (a : G) : a * a⁻¹ * a = a := by group
