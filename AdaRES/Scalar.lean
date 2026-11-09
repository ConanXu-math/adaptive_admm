import Mathlib

namespace AdaRES

noncomputable def accelInv : ℕ → ℝ
  | 0 => 1
  | n + 1 => (1 + Real.sqrt (1 + 4 * (accelInv n)^2)) / 2

theorem accelInv_pos (n : ℕ) : 0 < accelInv n := by
  cases n with
  | zero => norm_num [accelInv]
  | succ n =>
    rw [accelInv]
    have h := Real.sqrt_nonneg (1 + 4 * (accelInv n)^2)
    linarith only [h]

theorem accelInv_identity (n : ℕ) : (accelInv (n + 1))^2 - accelInv (n + 1) = (accelInv n)^2 := by
  rw [accelInv]
  have hs := Real.sq_sqrt (show 0 ≤ 1 + 4 * (accelInv n)^2 by positivity)
  nlinarith only [hs]

theorem accelInv_growth (n : ℕ) : 1 + (n : ℝ) / 2 ≤ accelInv n := by
  induction n with
  | zero => norm_num [accelInv]
  | succ n ih =>
    have hsq : (2 * accelInv n)^2 ≤ 1 + 4 * (accelInv n)^2 := by nlinarith
    have hs := Real.le_sqrt_of_sq_le hsq
    rw [accelInv, Nat.cast_succ]
    linarith only [ih, hs]

noncomputable def theta (n : ℕ) : ℝ := (accelInv n)⁻¹

@[simp] theorem theta_zero : theta 0 = 1 := by norm_num [theta, accelInv]

theorem theta_pos (n : ℕ) : 0 < theta n := inv_pos.mpr (accelInv_pos n)

theorem theta_le_one (n : ℕ) : theta n ≤ 1 := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have ha : 1 ≤ accelInv n := by linarith only [accelInv_growth n, hn]
  unfold theta
  rw [← one_div, div_le_iff₀ (accelInv_pos n), one_mul]
  exact ha

theorem theta_potential_identity (n : ℕ) :
    (1 - theta (n + 1)) / (theta (n + 1))^2 = 1 / (theta n)^2 := by
  unfold theta
  have h₀ := (accelInv_pos n).ne'
  have h₁ := (accelInv_pos (n + 1)).ne'
  field_simp [h₀, h₁]
  nlinarith only [accelInv_identity n]

theorem theta_bound (n : ℕ) : theta n ≤ 2 / ((n : ℝ) + 2) := by
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hd : 0 < (n : ℝ) + 2 := by linarith only [hn]
  unfold theta
  rw [← one_div, div_le_div_iff₀ (accelInv_pos n) hd, one_mul]
  linarith only [accelInv_growth n]

end AdaRES
