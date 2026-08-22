import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

noncomputable section

open Filter BigOperators

namespace AdaptiveADMM_Convergence_Proof

/-- A finite product of real factors bounded below by one is bounded by its
infinite product.  This is the real-valued replacement for the more general
`Multipliable.prod_le_tprod`, whose global ordered-monoid assumption is false
for `ℝ` because multiplication by a negative number reverses inequalities. -/
lemma real_finset_prod_le_tprod_of_one_le
    (f : ℕ → ℝ) (s : Finset ℕ)
    (h_one_le : ∀ n, 1 ≤ f n)
    (h_mult : Multipliable f) :
    (∏ n ∈ s, f n) ≤ ∏' n, f n := by
  classical
  have h_prod_one_le : ∀ u : Finset ℕ, 1 ≤ ∏ n ∈ u, f n := by
    intro u
    induction u using Finset.induction_on with
    | empty => simp
    | @insert a u ha ih =>
        rw [Finset.prod_insert ha]
        nlinarith [h_one_le a, ih]
  have h_mono : Monotone (fun u : Finset ℕ => ∏ n ∈ u, f n) := by
    intro u v huv
    have hu_nonneg : 0 ≤ ∏ n ∈ u, f n :=
      le_trans zero_le_one (h_prod_one_le u)
    calc
      (∏ n ∈ u, f n) = 1 * ∏ n ∈ u, f n := by ring
      _ ≤ (∏ n ∈ v \ u, f n) * ∏ n ∈ u, f n := by
        exact mul_le_mul_of_nonneg_right (h_prod_one_le (v \ u)) hu_nonneg
      _ = ∏ n ∈ v, f n := by
        rw [← Finset.prod_union Finset.sdiff_disjoint]
        rw [Finset.sdiff_union_of_subset huv]
  apply ge_of_tendsto h_mult.hasProd
  filter_upwards [eventually_ge_atTop s] with u hu
  exact h_mono hu

end AdaptiveADMM_Convergence_Proof
