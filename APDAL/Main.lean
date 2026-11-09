import APDAL.Averages

/-!
# Theorem 4 的两条速率

从原始 `Params` 与 `states` 直接构造。初始点 `p.x0` 不要求属于有效域，
试探选择器保持 `Params` 中的任意合法形式。用两个明确非负常数对每个 `N ≥ 1`
给出 `‖x_N - x̂‖ = O(1/N)` 与 `G(X_N, Y_N) = O(1/N²)`。
-/

open scoped BigOperators InnerProduct

namespace APDAL

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable {K : X →L[ℝ] Y} {g : ProperConvex X} {h : ProperConvex Y}

theorem main_rate (p : Params X Y) (sp : SaddlePoint K g h) (hs : StrongSupport g p.gamma) :
    let s := states K g h p
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ N : ℕ, 1 ≤ N →
      ‖(s N).x - sp.xhat‖ ≤ C₁ / (N : ℝ) ∧
      avgX s N ∈ g.dom ∧ avgY s N ∈ h.dom ∧
      0 ≤ pd_gap K g h (avgX s N) (avgY s N) sp.xhat sp.yhat ∧
      pd_gap K g h (avgX s N) (avgY s N) sp.xhat sp.yhat ≤ C₂ / (N : ℝ)^2 := by
  let s := states K g h p
  let C := max (energy sp s 1) (arbitraryConstant sp s)
  have hC : 0 ≤ C := (energy_nonneg sp s 1).trans (le_max_left _ _)
  obtain ⟨b, d, hb, hd, hgrowth⟩ := quadratic_growth K g h p
  have hE (N : ℕ) (hN : 1 ≤ N) : energy sp s N ≤ C := by
    cases N with
    | zero => omega
    | succ n =>
      cases n with
      | zero => exact le_max_left _ _
      | succ m =>
        have hbound := joint_bound_arbitrary p sp hs m
        have hG := (averaged_gap_le_sum p sp m).2.2.1
        have hnon : 0 ≤ sumSigma s (m + 1) *
            pd_gap K g h (avgX s (m + 1)) (avgY s (m + 1)) sp.xhat sp.yhat :=
          mul_nonneg (sumSigma_pos s (Nat.succ_pos m)).le hG
        exact ((le_add_of_nonneg_right hnon).trans hbound).trans (le_max_right _ _)
  refine ⟨Real.sqrt (2 * C / b), C / d, Real.sqrt_nonneg _, div_nonneg hC hd.le, ?_⟩
  intro N hN
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdist : (s N).beta * ‖(s N).x - sp.xhat‖^2 ≤ 2 * C := by
    have he := hE N hN
    unfold energy at he
    nlinarith only [he, sq_nonneg ‖(s (N - 1)).y - sp.yhat‖]
  have hβ : b * (N : ℝ)^2 ≤ (s N).beta := by
    apply le_trans _ (hgrowth N).1
    apply mul_le_mul_of_nonneg_left _ hb.le
    exact (sq_le_sq₀ hNpos.le (by positivity)).2 (by linarith)
  have hsq : (‖(s N).x - sp.xhat‖ * (N : ℝ))^2 ≤ 2 * C / b := by
    apply (le_div_iff₀ hb).2
    calc
      _ = (b * (N : ℝ)^2) * ‖(s N).x - sp.xhat‖^2 := by ring
      _ ≤ (s N).beta * ‖(s N).x - sp.xhat‖^2 :=
        mul_le_mul_of_nonneg_right hβ (sq_nonneg _)
      _ ≤ _ := hdist
  have hprimal := (le_div_iff₀ hNpos).2 (Real.le_sqrt_of_sq_le hsq)
  refine ⟨hprimal, ?_⟩
  cases N with
  | zero => omega
  | succ m =>
    obtain ⟨hx, hy, hG, _⟩ := averaged_gap_le_sum p sp m
    have hbound := joint_bound_arbitrary p sp hs m
    have hn : 0 < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    let G := pd_gap K g h (avgX s (m + 1)) (avgY s (m + 1)) sp.xhat sp.yhat
    have hsg : sumSigma s (m + 1) * G ≤ C := by
      calc
        _ ≤ energy sp s (m + 2) + sumSigma s (m + 1) * G :=
          le_add_of_nonneg_left (energy_nonneg sp s (m + 2))
        _ ≤ arbitraryConstant sp s := hbound
        _ ≤ C := le_max_right _ _
    have hprod : G * (((m + 1 : ℕ) : ℝ)^2 * d) ≤ C := by
      calc
        _ = (d * ((m + 1 : ℕ) : ℝ)^2) * G := by ring
        _ ≤ sumSigma s (m + 1) * G := mul_le_mul_of_nonneg_right (hgrowth (m + 1)).2 hG
        _ ≤ C := hsg
    refine ⟨hx, hy, hG, ?_⟩
    apply (le_div_iff₀ (pow_pos hn 2)).2
    apply (le_div_iff₀ hd).2
    simpa only [mul_assoc] using hprod

end APDAL
