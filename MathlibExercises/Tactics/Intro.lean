import Mathlib.Data.Nat.Notation

/-!
# The `intro` tactic

`intro` moves a hypothesis (or universally quantified variable) from the goal
into the local context. Compare the proof state by clicking your cursor before,
and then after, the `intro` tactic --/

example (p q : Prop) : p → q → p := by
  intro hp hq
  sorry -- If you have a hypothsis named `x` which matches the goal
        -- `exact x` will close the goal

example (n : ℕ) : n = n → True := by
  intro h
  sorry

example : ∀ n : ℕ, n + 0 = n := by
  intro n
  sorry

example (p q r : Prop) : (p → q → r) → p → q → r := by
  intro hpqr hp hq
  sorry

/-!
# The `rintro` tactic

`rintro` is `intro` combined with `rcases` pattern-matching, so a hypothesis
can be destructured the moment it enters the context.
-/

-- `⟨_, _⟩` destructures an `And` (or any arbitrary structure)
-- straight away.
example (p q : Prop) : p ∧ q → p := by
  rintro ⟨hp, _hq⟩
  sorry

-- `(_ | _)` destructures an `Or` (or any inductive type), giving one goal per case.
example (p q r : Prop) : p ∨ q → (p → r) → (q → r) → r := by
  rintro (hp | hq) hpr hqr
  all_goals sorry

-- Example of the above with an inductive type
example : (n : ℕ) → n = 0 ∨ n > 0 := by
  rintro (_ | x)
  all_goals sorry

-- `⟨_, _⟩` also destructures an `Exists`.
example : (∃ n : ℕ, n + 1 = 2) → ∃ n : ℕ, n + 2 = 3 := by
  rintro ⟨n, hn⟩
  sorry

-- Patterns nest, and `rfl` immediately substitutes an equality.
example (p : ℕ → Prop) : (∃ n, n = 0 ∧ p n) → p 0 := by
  rintro ⟨n, rfl, hpn⟩
  sorry
