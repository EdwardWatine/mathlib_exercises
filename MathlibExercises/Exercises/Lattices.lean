import Mathlib

/-!
# Lattices

-/

namespace Exercises.Lattices

/-! ## Absorption

`a ⊓ (a ⊔ b) = a` holds in any lattice at all — no distributivity needed.
-/

theorem inf_sup_self {α : Type*} [Lattice α] (a b : α) : a ⊓ (a ⊔ b) = a := by sorry

/-! ## The one-sided distributive inequality

Lattices aren't always distributive, but the inequality
`(a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)` always holds;
-/

theorem sup_inf_le_inf_sup {α : Type*} [Lattice α] (a b c : α) :
    a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c) := by sorry

/-! ## A concrete instance: the divisibility order on `ℕ`

`gcd` and `lcm` play the role of `⊓` and `⊔` for the divisibility order on
`ℕ`.
-/

theorem gcd_lcm_self (n m : ℕ) : Nat.gcd n (Nat.lcm n m) = n := by sorry

end Exercises.Lattices
