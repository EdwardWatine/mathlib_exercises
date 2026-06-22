import Mathlib.Data.Nat.Prime.Basic

/-!
# The `apply` tactic

`apply` matches the goal's conclusion against the conclusion of a term/lemma,
leaving any unmet hypotheses as new goals. Compare the proof state by
clicking your cursor before, and then after, the `apply` tactic.
-/

example (p q : Prop) (h : p → q) (hp : p) : q := by
  apply h
  sorry

example (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  apply le_trans hab
  sorry

-- `apply` can leave more than one goal when the lemma takes several
-- hypotheses that aren't already in context.
example (p q r : Prop) (hp : p) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  apply hqr
  apply hpq
  sorry

example (n : ℕ) : n ≤ n + 1 := by
  apply Nat.le_succ_of_le
  sorry

/-!
# The `refine` tactic

`refine` is `exact` with holes: write out as much of the proof term as you
already know, and mark the missing pieces with `?_` to turn them into new
goals.
-/

-- `?_` inside an anonymous constructor leaves one goal per component.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  refine ⟨hp, ?_⟩
  sorry

-- `refine` can supply the witness for an `Exists` while deferring the proof.
example : ∃ n : ℕ, n > 3 := by
  refine ⟨4, ?_⟩
  sorry

-- Several holes at once, including a nested structure.
example (p q r : Prop) : p → q → r → p ∧ (q ∧ r) := by
  intro hp hq hr
  refine ⟨?_, ?_, ?_⟩
  all_goals sorry

-- `refine` also accepts a partially-applied term, deferring just the tail.
example (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  refine le_trans hab ?_
  sorry

/-!
# The `constructor` tactic

`constructor` applies the (unique, or first matching) constructor of the
goal's inductive type, turning each of its arguments into a new goal. It's
the tactic form of leaving every slot of `refine ⟨?_, ?_, ...⟩` as a hole.
-/

-- For `And`, `constructor` is `refine ⟨?_, ?_⟩`.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  all_goals sorry

-- `Iff` also has a single constructor, splitting into `mp` and `mpr`.
example (p : Prop) : p ↔ p := by
  constructor
  all_goals sorry

-- `Exists` has a constructor too, but now the witness itself becomes a goal.
example : ∃ n : ℕ, n > 3 := by
  constructor
  all_goals sorry

-- Combine with `intro` as usual: introduce the hypotheses first, then split.
example (p q r : Prop) : p → (q ∧ r) → p ∧ q ∧ r := by
  intro hp hqr
  constructor
  all_goals sorry
