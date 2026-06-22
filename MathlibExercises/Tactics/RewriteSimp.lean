import Mathlib.Data.Nat.Prime.Basic

/-!
# The `rw` tactic

`rw` rewrites the goal using an equality (or `Iff`), left-to-right by
default. Compare the proof state by clicking your cursor before, and then
after, the individual theorems used for the `rw` tactic. This is also seen
as `rewrite`, but `rw` adds an `rfl` tactic afterwards for free.
-/

-- The substitution alone doesn't finish the goal, so there's still work left.
example (a b c : ℕ) (h : a = b) (hbc : b + c = 10) : a + c = 10 := by
  rw [h]
  sorry

-- Several lemmas can be chained in one `rw`, applied in order.
example (a b c d : ℕ) (hab : a = b) (hbc : b = c) (hcd : c + 1 = d) : a + 1 = d := by
  rw [hab, hbc]
  sorry

-- `rw [← h]` rewrites right-to-left.
example (a b : ℕ) (h : a = b) (ha : a + 1 = 5) : b + 1 = 5 := by
  rw [← h]
  sorry

-- `rw` works with `Iff` too, rewriting the goal's propositional shape.
example (p q : Prop) (h : p ↔ q) (hp : p) : q := by
  rw [h] at hp
  sorry

example (a b : ℕ) : a + b = b + a := by
  rw [Nat.add_comm]

/-!
# The `simp` tactic

`simp` rewrites repeatedly using a curated set of `@[simp]` lemmas (and any
extra ones you supply) until nothing more applies.
-/

example (n : ℕ) : n + 0 = n := by
  simp

-- Extra lemmas/hypotheses can be added to the simp set for this call only.
example (p q : Prop) (h : p ↔ q) (hp : p) : q := by
  simp [h] at hp
  sorry



-- `simp only [...]` restricts simp to exactly the given lemmas, no defaults.
-- Writing `simp?` will suggest a corresponding `simp only` statement to replace it
example (l : List ℕ) (h : l.length = 3) : (l ++ []).length = 3 := by
  simp only [List.append_nil]
  sorry
