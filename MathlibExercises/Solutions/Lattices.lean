import Mathlib

/-!
# Lattices

Three concrete results: the absorption law that holds in *every* lattice,
the one-directional distributive inequality that holds even when a lattice
isn't distributive, and a divisibility-order instance of the absorption
law for natural numbers.
-/

namespace Solutions.Lattices

/-! ## Absorption

`a ⊓ (a ⊔ b) = a` holds in any lattice at all — no distributivity needed.
-/

theorem inf_sup_self {α : Type*} [Lattice α] (a b : α) : a ⊓ (a ⊔ b) = a := by
  apply le_antisymm inf_le_left
  exact le_inf le_rfl le_sup_left

/-! ## The one-sided distributive inequality

Lattices aren't always distributive, but the inequality
`(a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c)` always holds; it becomes an equality
precisely in the distributive ones.
-/

theorem sup_inf_le_inf_sup {α : Type*} [Lattice α] (a b c : α) :
    a ⊓ b ⊔ a ⊓ c ≤ a ⊓ (b ⊔ c) := by
  apply sup_le
  · exact le_inf inf_le_left (inf_le_right.trans le_sup_left)
  · exact le_inf inf_le_left (inf_le_right.trans le_sup_right)

/-! ## A concrete instance: the divisibility order on `ℕ`

`gcd` and `lcm` play the role of `⊓` and `⊔` for the divisibility order on
`ℕ`. The absorption law's proof replays exactly, with `≤` swapped for `∣`:
`gcd n (lcm n m) = n`.
-/

theorem gcd_lcm_self (n m : ℕ) : Nat.gcd n (Nat.lcm n m) = n := by
  apply Nat.dvd_antisymm (Nat.gcd_dvd_left _ _)
  exact Nat.dvd_gcd dvd_rfl (Nat.dvd_lcm_left n m)

end Solutions.Lattices
