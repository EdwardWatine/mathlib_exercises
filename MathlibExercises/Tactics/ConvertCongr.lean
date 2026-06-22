import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# The `congr` tactic

`congr` splits a goal of the form `f a₁ ... aₙ = f b₁ ... bₙ` into one goal
`aᵢ = bᵢ` per argument, closing any that already match by `rfl`.
-/

-- `congr` is strong enough to discharge a matching hypothesis on its own;
-- here it closes the goal outright.
example (a b : ℕ) (h : a = b) : (a, 1) = (b, 1) := by
  congr 1

-- When the available hypothesis doesn't match syntactically, `congr` still
-- leaves the residual goal for you to finish.
example (a b : ℕ) (h : a + 1 = b + 1) : (a, 1) = (b, 1) := by
  congr 1
  sorry

-- With several mismatched arguments, only the ones it can't close on its
-- own survive.
example (a b c d : ℕ) (hac : a = c) (hdb : d = b) : (a, b) = (c, d) := by
  congr 1
  sorry

-- `congr 1` only peels off one layer of application.
example (f : ℕ → ℕ) (a b : ℕ) (hba : b = a) : f a = f b := by
  congr 1
  sorry

-- `congr` also works on the lengths of equal lists.
example (l₁ l₂ : List ℕ) (h : l₂ = l₁) : l₁.length = l₂.length := by
  congr 1
  sorry

/-!
# The `convert` tactic

`convert e` behaves like `exact e`, but where the goal and the type of `e`
don't match up syntactically, it leaves the mismatched pieces as new
equality goals instead of failing outright.
-/

-- The shapes mostly agree; only the mismatched argument becomes a goal.
example (P : ℕ → Prop) (a b : ℕ) (h : a = b) (hp : P a) : P b := by
  convert hp
  sorry

-- `using n` controls how deep `convert` is allowed to look before giving up
-- and turning the remainder into an equality goal.
example (a b : ℕ) (h : a = b) : (a, 1) = (b, 1) := by
  convert rfl using 2
  sorry

-- `convert` can leave more than one residual goal at once.
example (a b c d : ℕ) (hac : a = c) (hbd : b = d) : (a, b) = (c, d) := by
  convert rfl using 2
  all_goals sorry
