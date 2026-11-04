import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/- 本文件保存 Codex 提供的有界性证明帮助。 -/

namespace PDALCodexHelp

theorem sqrtBoundOfDivLe (r β A : ℝ) (hβ : 0 < β)
    (h : r ^ 2 / (2 * β) ≤ A) : r ≤ Real.sqrt (2 * β * A) := by
  apply Real.le_sqrt_of_sq_le
  calc
    r ^ 2 ≤ A * (2 * β) := (div_le_iff₀ (by positivity)).mp h
    _ = 2 * β * A := by ring

#print axioms sqrtBoundOfDivLe

theorem boundedPairsOfSquareBounds {X Y : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y]
    (x : ℕ → X) (y : ℕ → Y) (xref : X) (yref : Y)
    (β A : ℝ) (hβ : 0 < β)
    (hx : ∀ k ≥ 1, ‖x k - xref‖ ^ 2 / 2 ≤ A)
    (hy : ∀ k ≥ 1, ‖y k - yref‖ ^ 2 / (2 * β) ≤ A) :
    Bornology.IsBounded (Set.range fun k => (x k, y k)) := by
  have hxroot : ∀ k ≥ 1, ‖x k - xref‖ ≤ Real.sqrt (2 * A) := by
    intro k hk
    have h := sqrtBoundOfDivLe ‖x k - xref‖ 1 A (by norm_num)
      (by simpa using hx k hk)
    simpa using h
  have hyroot : ∀ k ≥ 1, ‖y k - yref‖ ≤ Real.sqrt (2 * β * A) := by
    intro k hk
    exact sqrtBoundOfDivLe _ β A hβ (hy k hk)
  rw [Metric.isBounded_iff_subset_closedBall (xref, yref)]
  refine ⟨max (max (Real.sqrt (2 * A)) (Real.sqrt (2 * β * A)))
    (max ‖x 0 - xref‖ ‖y 0 - yref‖), ?_⟩
  rintro p ⟨k, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def]
  change max ‖x k - xref‖ ‖y k - yref‖ ≤ _
  by_cases hk : k = 0
  · subst k
    exact le_max_right _ _
  · have hk1 : k ≥ 1 := by omega
    exact (max_le_max (hxroot k hk1) (hyroot k hk1)).trans (le_max_left _ _)

#print axioms boundedPairsOfSquareBounds

end PDALCodexHelp
