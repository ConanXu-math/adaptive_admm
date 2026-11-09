import Mathlib

/-!
# 标量增长定理

若 β₀ > 0、γ > 0、c > 0，且序列 β 满足 β_{n+1} ≥ β_n + γ c √β_n，
则取 b = min(β₀, (γc/3)²) > 0，对所有 n 有 β_n ≥ b (n+1)²。
-/

namespace APDAL

theorem scalar_growth (β : ℕ → ℝ) {γ c : ℝ}
    (hγ : 0 < γ) (hc : 0 < c) (hβ : 0 < β 0)
    (hstep : ∀ n, β n + γ * c * Real.sqrt (β n) ≤ β (n + 1)) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, b * ((n : ℝ) + 1)^2 ≤ β n := by
  let b : ℝ := min (β 0) ((γ * c / 3)^2)
  have hthird : 0 < γ * c / 3 := div_pos (mul_pos hγ hc) (by norm_num)
  have hb : 0 < b := lt_min hβ (pow_pos hthird 2)
  have hcap : Real.sqrt b ≤ γ * c / 3 := by
    calc
      Real.sqrt b ≤ Real.sqrt ((γ * c / 3)^2) :=
        Real.sqrt_le_sqrt (min_le_right _ _)
      _ = γ * c / 3 := Real.sqrt_sq hthird.le
  have hthree : 3 * Real.sqrt b ≤ γ * c := by linarith only [hcap]
  refine ⟨b, hb, ?_⟩
  intro n
  induction n with
  | zero =>
    have h0 : b * ((0 : ℕ) + 1)^2 ≤ β 0 := by
      have : b * ((0 : ℕ) + 1)^2 = b := by norm_num [b]
      rw [this]
      exact min_le_left (β 0) ((γ * c / 3)^2)
    simpa using h0
  | succ n ih =>
    let m : ℝ := (n : ℝ) + 1
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hm : 1 ≤ m := by dsimp [m]; linarith only [hn]
    have hms : 0 ≤ m := zero_le_one.trans hm
    have hs : Real.sqrt b * m ≤ Real.sqrt (β n) := by
      calc
        Real.sqrt b * m = Real.sqrt (b * m^2) := by
          rw [Real.sqrt_mul hb.le, Real.sqrt_sq hms]
        _ ≤ Real.sqrt (β n) := Real.sqrt_le_sqrt ih
    have hi : 3 * b * m ≤ γ * c * Real.sqrt (β n) := by
      calc
        3 * b * m = 3 * (Real.sqrt b)^2 * m := by rw [Real.sq_sqrt hb.le]
        _ = (3 * Real.sqrt b) * (Real.sqrt b * m) := by ring
        _ ≤ γ * c * Real.sqrt (β n) :=
          mul_le_mul hthree hs (mul_nonneg (Real.sqrt_nonneg _) hms) (mul_pos hγ hc).le
    have hlast : b * (m + 1)^2 ≤ b * m^2 + 3 * b * m := by
      calc
        b * (m + 1)^2 = b * m^2 + 3 * b * m - b * (m - 1) := by ring
        _ ≤ _ := sub_le_self _ (mul_nonneg hb.le (sub_nonneg.mpr hm))
    have hnext : b * (m + 1)^2 ≤ β (n + 1) :=
      hlast.trans ((add_le_add ih hi).trans (hstep n))
    simpa only [Nat.cast_succ, m] using hnext

end APDAL
