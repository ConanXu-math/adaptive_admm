import Mathlib

namespace UFGM

theorem power_increment {A a H D p : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (hH : 0 < H) (hD : 0 < D) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hroot : H * a^2 = A + a) (hbound : H * (a / (A + a))^p ≤ D) :
    let γ := 1 / (2 - p)
    D^(-γ) / 2 ≤ (A + a)^γ - A^γ := by
  let B := A + a
  let γ := 1 / (2 - p)
  have hB : 0 < B := add_pos_of_nonneg_of_pos hA ha
  have hden : 0 < 2 - p := by linarith only [hp₁]
  have hg : 0 < γ := one_div_pos.mpr hden
  have hgl : 1 / 2 ≤ γ := (le_div_iff₀ hden).2 (by linarith only [hp₀])
  have hgu : γ ≤ 1 := (div_le_one hden).2 (by linarith only [hp₁])
  have hge : (2 - p) * γ = 1 := by
    dsimp only [γ]
    field_simp [hden.ne']
  have he : H * (a / B)^p = B^(1 - p) / a^(2 - p) := by
    apply (eq_div_iff (Real.rpow_pos_of_pos ha _).ne').2
    rw [Real.div_rpow ha.le hB.le]
    calc
      _ = H * (a^p * a^(2 - p)) / B^p := by ring
      _ = H * a^2 / B^p := by
        rw [← Real.rpow_add ha, show p + (2 - p) = (2 : ℝ) from by ring, Real.rpow_two]
      _ = _ := by
        change H * a^2 / B^p = B^(1 - p)
        rw [show H * a^2 = B from hroot, Real.rpow_sub hB, Real.rpow_one]
  have hbpos : 0 < H * (a / B)^p := mul_pos hH (Real.rpow_pos_of_pos (div_pos ha hB) _)
  have hneg := Real.rpow_le_rpow_of_nonpos hbpos hbound (neg_nonpos.mpr hg.le)
  have hscaled : D^(-γ) ≤ a * B^(γ - 1) := by
    have h₁ : (1 - p) * (-γ) = γ - 1 := by nlinarith only [hge]
    have h₂ : (2 - p) * (-γ) = -1 := by nlinarith only [hge]
    rw [he, Real.div_rpow (Real.rpow_nonneg hB.le _) (Real.rpow_nonneg ha.le _),
      ← Real.rpow_mul hB.le, ← Real.rpow_mul ha.le, h₁, h₂, Real.rpow_neg_one] at hneg
    simpa only [div_eq_mul_inv, inv_inv, mul_comm] using hneg
  have ham := Real.geom_mean_le_arith_mean2_weighted hg.le (sub_nonneg.mpr hgu)
    hA hB.le (by ring)
  have hpB : B * B^(γ - 1) = B^γ := by
    calc
      _ = B^(1 : ℝ) * B^(γ - 1) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hB, show 1 + (γ - 1) = γ from by ring]
  have hA' : A = B - a := by dsimp [B]; ring
  have hstep : A^γ ≤ B^γ - γ * a * B^(γ - 1) := by
    calc
      _ = (A^γ * B^(1 - γ)) * B^(γ - 1) := by
        rw [mul_assoc, ← Real.rpow_add hB, show (1 - γ) + (γ - 1) = 0 from by ring,
          Real.rpow_zero, mul_one]
      _ ≤ (γ * A + (1 - γ) * B) * B^(γ - 1) :=
        mul_le_mul_of_nonneg_right ham (Real.rpow_nonneg hB.le _)
      _ = B * B^(γ - 1) - γ * a * B^(γ - 1) := by rw [hA']; ring
      _ = _ := by rw [hpB]
  have hgD := mul_le_mul_of_nonneg_right hgl (Real.rpow_nonneg hD.le (-γ))
  have hga := mul_le_mul_of_nonneg_left hscaled hg.le
  change D^(-γ) / 2 ≤ B^γ - A^γ
  nlinarith only [hgD, hga, hstep]

theorem accumulate_power {A : ℕ → ℝ} {D γ : ℝ} (hD : 0 < D) (hg : 0 < γ)
    (hA₀ : A 0 = 0) (hA : ∀ n, 0 ≤ A n)
    (hstep : ∀ n, D^(-γ) / 2 ≤ (A (n + 1))^γ - (A n)^γ) (n : ℕ) :
    ((n : ℝ) / 2)^(1 / γ) / D ≤ A n := by
  have hs (m : ℕ) : (m : ℝ) / 2 * D^(-γ) ≤ (A m)^γ := by
    induction m with
    | zero => rw [hA₀, Real.zero_rpow hg.ne']; norm_num
    | succ m ih =>
      rw [Nat.cast_succ]
      nlinarith only [ih, hstep m]
  have hn : 0 ≤ (n : ℝ) / 2 := by positivity
  have hR : 0 ≤ ((n : ℝ) / 2)^(1 / γ) / D :=
    div_nonneg (Real.rpow_nonneg hn _) hD.le
  apply (Real.rpow_le_rpow_iff hR (hA n) hg).1
  calc
    _ = (n : ℝ) / 2 * D^(-γ) := by
      rw [Real.div_rpow (Real.rpow_nonneg hn _) hD.le, ← Real.rpow_mul hn,
        one_div_mul_cancel hg.ne', Real.rpow_one, Real.rpow_neg hD.le,
        div_eq_mul_inv ((n : ℝ) / 2) (D^γ)]
    _ ≤ _ := hs n

end UFGM
