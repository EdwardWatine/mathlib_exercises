import Mathlib.Data.Nat.Notation
import Mathlib.Tactic

/-!
# Natural number induction

-/

namespace Solutions.Induction

/-! ## Pattern matching

`fib` is defined by matching on three shapes of its argument at once
(`0`, `1`, `n + 2`). Once it's defined this way, a *concrete* instance of
the Fibonacci recurrence is just a computation: no induction is needed to
check one specific numeral.
-/

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib n + fib (n + 1)

theorem fib_ten : fib 10 = 55 := by decide

/-! ## Recursion

`sumTo n` adds up `0 + 1 + ... + n`, defined by structural recursion. We
prove the closed-form formula by writing the proof itself as a
recursive function on `n`.
-/

def sumTo : ℕ → ℕ
  | 0 => 0
  | (n + 1) => sumTo n + (n + 1)

theorem sumTo_formula : ∀ n, 2 * sumTo n = n * (n + 1)
  | 0 => rfl
  | (n + 1) => by
      change 2 * (sumTo n + (n + 1)) = (n + 1) * (n + 2)
      rw [Nat.mul_add, sumTo_formula n]
      ring

/-! ## Induction
-/

theorem self_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
    rw [pow_succ]
    omega

end Solutions.Induction
