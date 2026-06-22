import Mathlib.Data.Nat.Prime.Basic

/-!
# The `all_goals` combinator

`all_goals tac` runs `tac` on every remaining goal, and fails if `tac` fails
on any of them.
-/

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  all_goals sorry

-- `all_goals` fails as a whole if even one goal can't be discharged, so it's
-- often paired with a tactic that's expected to work everywhere, like `sorry`
-- here, or `assumption` once every piece is in context.
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  refine ⟨?_, ?_, ?_⟩
  all_goals sorry

/-!
# The `any_goals` combinator

`any_goals tac` runs `tac` on every remaining goal, but only fails if `tac`
fails on *all* of them — goals it can't make progress on are simply left
behind.
-/

-- `assumption` only succeeds on the goal that has a matching hypothesis;
-- `any_goals` lets the other one survive instead of aborting.
example (p q : Prop) (hp : p) : p ∧ q := by
  constructor
  any_goals assumption
  sorry

-- With three goals and only one matching hypothesis, two survive for you
-- to fill in.
example (p q r : Prop) (hq : q) : p ∧ q ∧ r := by
  refine ⟨?_, ?_, ?_⟩
  any_goals assumption
  all_goals sorry

/-!
# The `<;>` combinator

`tac₁ <;> tac₂` runs `tac₁`, then runs `tac₂` on *every* goal it produces.
-/

-- Split, then immediately try the same closing tactic on both halves.
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> sorry

-- Chains compose: split the conjunction, then split each `Or` it exposes.
example (p q r s : Prop) (hpq : p ∨ q) (hrs : r ∨ s) : (p ∨ q) ∧ (r ∨ s) := by
  constructor <;> [exact hpq; exact hrs]
