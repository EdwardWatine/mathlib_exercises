import Mathlib.Data.Nat.Basic

/-!
# The `have` tactic

`have` proves an auxiliary fact and adds it to the local context under a
name (or as `this` if unnamed); it doesn't touch the goal itself.
-/

example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  have hq : q := hpq hp
  sorry

-- `have` can also be proved with a tactic block instead of a term.
example (a b c : ℕ) (hab : a = b) (hbc : b = c) : a + c = b + b := by
  have hac : a = c := by rw [hab, hbc]
  sorry

-- Leaving off the name binds the fact to `this`.
example (p : Prop) (hp : p) : p ∧ p := by
  have : p := hp
  sorry

example (n : ℕ) : 0 < n + 1 := by
  have h : 0 < n + 1 := Nat.succ_pos n
  sorry

/-!
# The `let` tactic

`let` adds a local *definition* to the context (not just a proof), and —
unlike `have` — keeps it definitionally transparent: anything provably equal
to it by unfolding can be matched with `show` or `change`.
-/

-- `s` is defeq to `a + b`, so `show` can restate the goal in terms of it.
example (a b : ℕ) : (a + b) + (a + b) = 2 * (a + b) := by
  let s := a + b
  change s + s = 2 * s
  sorry

example (n : ℕ) (h : 0 < n) : n - 1 + 1 = n := by
  let m := n - 1
  change m + 1 = n
  sorry

-- A `let`-bound value can supply a witness for an existential.
example (n : ℕ) : ∃ k, k + k = n + n := by
  let k := n
  refine ⟨k, ?_⟩
  sorry

/-!
# The `obtain` tactic

`obtain` is `rcases`-style pattern matching applied to a hypothesis (or any
term) already at hand, rather than something being introduced — the
hypothesis-side counterpart to `rintro`.
-/

example (p q : Prop) (h : p ∧ q) : p := by
  obtain ⟨hp, hq⟩ := h
  sorry

example (n : ℕ) (h : ∃ k, n = 2 * k) : ∃ k, n = k + k := by
  obtain ⟨k, hk⟩ := h
  sorry

-- `(_ | _)` splits an `Or` hypothesis into one goal per case.
example (p q r : Prop) (h : p ∨ q) (hp : p → r) (hq : q → r) : r := by
  obtain hp' | hq' := h
  · sorry
  · sorry

-- Patterns nest, and `rfl` immediately substitutes an equality, just as
-- with `rintro`.
example (p : ℕ → Prop) (h : ∃ n, n = 0 ∧ p n) : p 0 := by
  obtain ⟨n, rfl, hp⟩ := h
  sorry
