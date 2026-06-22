import Mathlib

/-!
# Finite types

Types that reason about finiteness in some way. `Finite α` is a typeclass
expressing that `α` is finite, which is not covered in this file.
-/

namespace Solutions.FiniteTypes

/-! ## `Finset`

A finset's cardinality splits into the cardinalities of the elements
satisfying a predicate and those that don't.
-/
open Classical in -- This theorem is only true in classical logic
theorem card_filter_add_card_filter_not {α : Type*} (s : Finset α) (p : α → Prop)
    [DecidablePred p] [∀ x, Decidable ¬ p x] :
    (s.filter p).card + (s.filter fun a => ¬ p a).card = s.card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not s s p),
    Finset.filter_union_filter_not_eq]

/-! ## `Fin`

Reversing the indices of a `Fin n`-indexed sum doesn't change its value:
reversal is just a reindexing by a bijection.
-/

theorem sum_rev_eq_sum (n : ℕ) : ∑ i : Fin n, (Fin.revPerm i : ℕ) = ∑ i : Fin n, (i : ℕ) :=
  Equiv.sum_comp Fin.revPerm (fun i : Fin n => (i : ℕ))

/-! ## `Finsupp`

`p : ℕ →₀ ℤ` below is the finitely-supported function representing
`1 - x` (coefficient `1` at degree `0`, coefficient `-1` at degree `1`).
Evaluating it at `x = 2` via `Finsupp.sum` gives `1 - 2 = -1`.
This is how polynomials are implemented in Mathlib.
-/

-- Finitely supported functions are noncomutable (sadly)
noncomputable def p : ℕ →₀ ℤ := Finsupp.single 0 1 + Finsupp.single 1 (-1)

theorem p_eval_two : p.sum (fun n c => c * 2 ^ n) = -1 := by
  rw [p, Finsupp.sum_add_index' (by simp) (by intros; ring)]
  rw [Finsupp.sum_single_index (by ring), Finsupp.sum_single_index (by ring)]
  ring

end Solutions.FiniteTypes
