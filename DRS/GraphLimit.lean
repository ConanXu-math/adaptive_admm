import DRS.Iteration
import DRS.WeakSubsequence

/-!
# The joint weak limit lies in the solution set

If along a subsequence graph points of `A` weakly tend to `(z, -w)` and graph points of
`B` weakly tend to `(z, w)`, and the sum of the pairing terms `⟪v n, a n⟫ + ⟪u n, b n⟫`
tends to zero, then maximality of both relations gives `-w ∈ A z` and `w ∈ B z`.
-/

open Filter
open scoped InnerProductSpace Topology

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A B : E → Set E}

theorem extendedSolution_of_weak_graph_limit
    (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    (v a u b : ℕ → E) (z w : E)
    (hva : ∀ n, a n ∈ A (v n)) (hub : ∀ n, b n ∈ B (u n))
    (hv : WeaklyTendsTo v z) (ha : WeaklyTendsTo a (-w))
    (hu : WeaklyTendsTo u z) (hb : WeaklyTendsTo b w)
    (hcross : Tendsto (fun n => ⟪v n, a n⟫_ℝ + ⟪u n, b n⟫_ℝ) atTop (𝓝 0)) :
    ExtendedSolution A B z w := by
  have h1 : 0 < (1 : ℝ) := by norm_num
  let x := hA.resolvent h1 (z - w)
  let y := hB.resolvent h1 (z + w)
  let α := z - w - x
  let β := z + w - y
  have hx : α ∈ A x := by simpa [α, x] using hA.resolvent_mem h1 (z - w)
  have hy : β ∈ B y := by simpa [β, y] using hB.resolvent_mem h1 (z + w)
  have hα : Tendsto (fun _ : ℕ => ⟪x, α⟫_ℝ) atTop (𝓝 ⟪x, α⟫_ℝ) := tendsto_const_nhds
  have hβ : Tendsto (fun _ : ℕ => ⟪y, β⟫_ℝ) atTop (𝓝 ⟪y, β⟫_ℝ) := tendsto_const_nhds
  have hlim := ((((((hcross.sub (hv α)).sub (ha x)).add hα).sub (hu β)).sub (hb y)).add hβ)
  have hfun : (fun n => (⟪v n, a n⟫_ℝ + ⟪u n, b n⟫_ℝ) -
      ⟪v n, α⟫_ℝ - ⟪a n, x⟫_ℝ + ⟪x, α⟫_ℝ -
      ⟪u n, β⟫_ℝ - ⟪b n, y⟫_ℝ + ⟪y, β⟫_ℝ) =
      (fun n => ⟪v n - x, a n - α⟫_ℝ + ⟪u n - y, b n - β⟫_ℝ) := by
    funext n
    simp only [inner_sub_left, inner_sub_right]
    rw [real_inner_comm (a n) x, real_inner_comm (b n) y]
    ring
  rw [hfun] at hlim
  have hL := ge_of_tendsto' hlim fun n =>
    add_nonneg (hA.1 (v n) (a n) x α (hva n) hx) (hB.1 (u n) (b n) y β (hub n) hy)
  have heq : (0 - ⟪z, α⟫_ℝ - ⟪-w, x⟫_ℝ + ⟪x, α⟫_ℝ -
      ⟪z, β⟫_ℝ - ⟪w, y⟫_ℝ + ⟪y, β⟫_ℝ) =
      ⟪z - x, -w - α⟫_ℝ + ⟪z - y, w - β⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right]
    rw [real_inner_comm w x, real_inner_comm w y]
    ring
  rw [heq, show -w - α = -(z - x) by dsimp [α]; module,
    show w - β = -(z - y) by dsimp [β]; module] at hL
  simp only [inner_neg_right, real_inner_self_eq_norm_sq] at hL
  have hnx : ‖z - x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z - x‖, sq_nonneg ‖z - y‖]
  have hny : ‖z - y‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z - x‖, sq_nonneg ‖z - y‖]
  have hxz : z = x := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnx))
  have hyz : z = y := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hny))
  have hαw : α = -w := by dsimp [α]; rw [← hxz]; module
  have hβw : β = w := by dsimp [β]; rw [← hyz]; module
  exact ⟨by simpa only [hαw, ← hxz] using hx, by simpa only [hβw, ← hyz] using hy⟩

end DRS
