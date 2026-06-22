import Mathlib.Data.Nat.Notation
import Mathlib.Tactic

/-!
# Natural number induction
The `induction` tactic may help!
-/

namespace Exercises.Induction

/-! ## Pattern matching

`fib` is defined by matching on three shapes of its argument at once
(`0`, `1`, `n + 2`). Use the decision procedure `decide`.
-/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib n + fib (n + 1)

theorem fib_ten : fib 10 = 55 := by sorry

def sumTo : ℕ → ℕ
  | 0 => 0
  | (n + 1) => sumTo n + (n + 1)

theorem sumTo_formula : ∀ n, 2 * sumTo n = n * (n + 1) := by sorry

theorem self_lt_two_pow (n : ℕ) : n < 2 ^ n := by sorry

end Exercises.Induction
