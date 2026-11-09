import Mathlib

/-!
# Monotone relations in a real Hilbert space

This file defines monotone relations (set-valued operators) `A : E → Set E` on a real inner
product space and their maximality, together with basic resolvent facts.

Main definitions:

* `IsMonotoneRel A` : for any two graph points `(x, a)`, `(y, b)` we have
  `0 ≤ ⟪x - y, a - b⟫_ℝ`.
* `IsMaximalMonotoneRel A` : `A` is monotone and any point compatible with the whole graph
  already lies on the graph.

Main results:

* `IsMonotoneRel.resolvent_unique` : the equation `(1/t) • (p - x) ∈ A x` has at most
  one solution `x` for each `p` and `t > 0` (unique resolvent value).
-/

open scoped InnerProductSpace

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A relation `A : E → Set E` is *monotone* if for all graph points `(x, a)` and `(y, b)`
(with `a ∈ A x`, `b ∈ A y`) we have `0 ≤ ⟪x - y, a - b⟫_ℝ`. -/
def IsMonotoneRel (A : E → Set E) : Prop :=
  ∀ x a y b, a ∈ A x → b ∈ A y → 0 ≤ ⟪x - y, a - b⟫_ℝ

/-- A relation `A : E → Set E` is *maximally monotone* if it is monotone and every point
`(x, a)` compatible with all graph points already lies on the graph. -/
def IsMaximalMonotoneRel (A : E → Set E) : Prop :=
  IsMonotoneRel A ∧
    ∀ x a, (∀ y b, b ∈ A y → 0 ≤ ⟪x - y, a - b⟫_ℝ) → a ∈ A x

variable {A : E → Set E}

/-- Uniqueness of the resolvent: for a monotone relation and `t > 0`, the point `x` with
`(1/t) • (p - x) ∈ A x` is unique. -/
theorem IsMonotoneRel.resolvent_unique (hA : IsMonotoneRel A) {t : ℝ} (ht : 0 < t) {p x y : E}
    (hx : (1 / t) • (p - x) ∈ A x) (hy : (1 / t) • (p - y) ∈ A y) : x = y := by
  have hmono : 0 ≤ ⟪x - y, (1 / t) • (p - x) - (1 / t) • (p - y)⟫_ℝ :=
    hA x _ y _ hx hy
  have hsub : (1 / t) • (p - x) - (1 / t) • (p - y) = (1 / t) • (y - x) := by
    rw [smul_sub]
    module
  rw [hsub] at hmono
  have h1 : ⟪x - y, (1 / t) • (y - x)⟫_ℝ = (1 / t) * ⟪x - y, y - x⟫_ℝ := by
    rw [real_inner_smul_right]
  rw [h1] at hmono
  have h2 : ⟪x - y, y - x⟫_ℝ = -‖x - y‖ ^ 2 := by
    rw [show y - x = -(x - y) from by module]
    rw [inner_neg_right, real_inner_self_eq_norm_sq]
  rw [h2] at hmono
  have h3 : (1 / t) * ‖x - y‖ ^ 2 ≤ 0 := by
    have : (1 / t) * (-‖x - y‖ ^ 2) ≥ 0 := by linarith
    nlinarith [abs_nonneg ((1 / t) * ‖x - y‖ ^ 2)]
  by_contra hxy
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hp : 0 < (1 / t) * ‖x - y‖ ^ 2 := mul_pos (one_div_pos.mpr ht) (sq_pos_of_pos hn)
  exact (not_lt_of_ge h3) hp

/-- The Cayley transform of the resolvent: if `a ∈ A x` and `b ∈ A y` are the residual values
from the resolvent equation (i.e. `x + t • a` and `y + t • b` are the given points), then the map
`(x, a) ↦ x - t • a` is `1`-Lipschitz on such pairs. In particular, for resolvent pairs
`(p, x)`, `(q, y)` with `(p - x)/t ∈ A x`, `(q - y)/t ∈ A y` we get
`‖(x - t • a) - (y - t • b)‖ ≤ ‖p - q‖` where `a = (p - x)/t`, `b = (q - y)/t`. -/
theorem IsMonotoneRel.cayley_nonexpansive (hA : IsMonotoneRel A) {t : ℝ} (ht : 0 < t)
    {p q x y : E} {a b : E} (ha : a ∈ A x) (hb : b ∈ A y)
    (hpx : p = x + t • a) (hqy : q = y + t • b) :
    ‖(x - t • a) - (y - t • b)‖ ≤ ‖p - q‖ := by
  have hmono : 0 ≤ ⟪x - y, a - b⟫_ℝ := hA x a y b ha hb
  have hcross : 0 ≤ ⟪x - y, t • (a - b)⟫_ℝ := by
    rw [real_inner_smul_right]
    exact mul_nonneg ht.le hmono
  have hxsub : (x - t • a) - (y - t • b) = (x - y) - t • (a - b) := by
    module
  have hqsub : p - q = (x - y) + t • (a - b) := by
    rw [hpx, hqy]
    module
  rw [hxsub, hqsub]
  have hsq : ‖x - y - t • (a - b)‖ ^ 2 ≤ ‖x - y + t • (a - b)‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    linarith [hcross]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

end DRS
