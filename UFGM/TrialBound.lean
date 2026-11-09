import UFGM.TrialScalar
import UFGM.ModelBound

namespace UFGM

noncomputable section

def scaledTrial (A H p : ℝ) : ℝ := H * (trialRatio A H)^p

theorem scaledTrial_formula {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (p : ℝ) :
    scaledTrial A H p = H^(1 - p / 2) * (A + trialWeight A H)^(-(p / 2)) := by
  let a := trialWeight A H
  let B := A + a
  let τ := trialRatio A H
  have ha : 0 < a := trialWeight_pos hH
  have hB : 0 < B := add_pos_of_nonneg_of_pos hA ha
  have ht : 0 < τ := (trialRatio_range hA hH).1
  have hroot : H * a^2 = B := trialWeight_eq hA hH
  have hsq : τ^2 = 1 / (H * B) := by
    change (a / B)^2 = _
    rw [div_pow]
    apply (div_eq_div_iff (pow_ne_zero 2 hB.ne') (mul_ne_zero hH.ne' hB.ne')).2
    calc
      _ = (H * a^2) * B := by ring
      _ = _ := by rw [hroot]; ring
  have he : τ^p = (τ^2)^(p / 2) := by
    rw [← Real.rpow_two τ, ← Real.rpow_mul ht.le, show 2 * (p / 2) = p from by ring]
  change H * τ^p = H^(1 - p / 2) * B^(-(p / 2))
  rw [he, hsq, one_div, Real.inv_rpow (mul_nonneg hH.le hB.le),
    ← Real.rpow_neg (mul_nonneg hH.le hB.le), Real.mul_rpow hH.le hB.le]
  calc
    _ = (H^(1 : ℝ) * H^(-(p / 2))) * B^(-(p / 2)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [← Real.rpow_add hH, sub_eq_add_neg]

theorem scaledTrial_lower {A H p : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (hp : p ≤ 1) :
    1 / trialWeight A H ≤ scaledTrial A H p := by
  have ht := trialRatio_range hA hH
  have h := Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 hp
  rw [Real.rpow_one] at h
  unfold scaledTrial
  calc
    _ = H * trialRatio A H := by
      rw [trialRatio_reciprocal hA hH]
      field_simp [hH.ne', (trialWeight_pos (A := A) hH).ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hH.le

theorem threshold_candidate_exists {A L p C : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hp : p ≤ 1)
    (hC : 0 ≤ C) : ∃ i : ℕ, C ≤ scaledTrial A ((2 : ℝ)^i * L) p := by
  let η := 1 / (C + 1)
  have hc1 : 0 < C + 1 := by positivity
  have hη : 0 < η := one_div_pos.mpr hc1
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (R := ℝ)
    ((A / η^2 + 1 / η) / L) (show (1 : ℝ) < 2 by norm_num)
  let H := (2 : ℝ)^i * L
  have hH : 0 < H := mul_pos (pow_pos (by norm_num) _) hL
  have hlarge : A / η^2 + 1 / η < H := (div_lt_iff₀ hL).1 hi
  have ha := trialWeight_small hA hH hη hlarge
  have hl : 1 / η < 1 / trialWeight A H := one_div_lt_one_div_of_lt (trialWeight_pos hH) ha
  have he : 1 / η = C + 1 := by dsimp [η]; rw [one_div_one_div]
  refine ⟨i, ?_⟩
  change C ≤ scaledTrial A H p
  rw [he] at hl
  exact (show C ≤ 1 / trialWeight A H by linarith only [hl]).trans (scaledTrial_lower hA hH hp)

theorem scaledTrial_first_monotone {A₀ H₀ A₁ H₁ p : ℝ}
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hH₀ : 0 < H₀) (hH₁ : 0 < H₁)
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hH : H₁ ≤ H₀)
    (hB : A₀ + trialWeight A₀ H₀ ≤ A₁ + trialWeight A₁ H₁) :
    scaledTrial A₁ H₁ p ≤ scaledTrial A₀ H₀ p := by
  have hB₀ := add_pos_of_nonneg_of_pos hA₀ (trialWeight_pos (A := A₀) hH₀)
  have hB₁ := add_pos_of_nonneg_of_pos hA₁ (trialWeight_pos (A := A₁) hH₁)
  rw [scaledTrial_formula hA₁ hH₁, scaledTrial_formula hA₀ hH₀]
  apply mul_le_mul
  · exact Real.rpow_le_rpow hH₁.le hH (by linarith only [hp₁])
  · exact Real.rpow_le_rpow_of_nonpos hB₀ hB (by linarith only [hp₀])
  · exact Real.rpow_nonneg hB₁.le _
  · exact Real.rpow_nonneg hH₀.le _

end
end UFGM
