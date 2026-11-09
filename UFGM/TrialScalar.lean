import Mathlib

namespace UFGM

noncomputable section

def trialWeight (A H : ℝ) : ℝ := (1 + Real.sqrt (1 + 4 * H * A)) / (2 * H)

def trialRatio (A H : ℝ) : ℝ := trialWeight A H / (A + trialWeight A H)

theorem trialWeight_pos {A H : ℝ} (hH : 0 < H) : 0 < trialWeight A H := by
  unfold trialWeight
  positivity

theorem trialWeight_eq {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) :
    H * (trialWeight A H)^2 = A + trialWeight A H := by
  let a := trialWeight A H
  let r := Real.sqrt (1 + 4 * H * A)
  have hr : r^2 = 1 + 4 * H * A := Real.sq_sqrt (by positivity)
  have ha : 2 * H * a = 1 + r := by
    change 2 * H * ((1 + r) / (2 * H)) = 1 + r
    field_simp [hH.ne']
  have hp : (1 + r)^2 = 2 * (1 + r) + 4 * H * A := by nlinarith only [hr]
  have he : (2 * H * a)^2 = 2 * (2 * H * a) + 4 * H * A := by rw [ha]; exact hp
  have hz : (4 * H) * (H * a^2 - (A + a)) = 0 := by nlinarith only [he]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (by positivity)))

theorem trialWeight_unique {A H b : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (hb : 0 < b)
    (he : H * b^2 = A + b) : b = trialWeight A H := by
  let a := trialWeight A H
  have ha : 0 < a := trialWeight_pos hH
  have haa : H * a^2 = A + a := trialWeight_eq hA hH
  have hbase : 1 ≤ H * a := by
    apply (mul_le_mul_right ha).1
    nlinarith only [haa, hA]
  have hp : 0 < H * (b + a) - 1 := by nlinarith only [hbase, mul_pos hH hb]
  have hfac : (b - a) * (H * (b + a) - 1) = 0 := by nlinarith only [he, haa]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hp.ne')

theorem trialRatio_range {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) :
    0 < trialRatio A H ∧ trialRatio A H ≤ 1 := by
  have ha : 0 < trialWeight A H := trialWeight_pos hH
  have hB := add_pos_of_nonneg_of_pos hA ha
  unfold trialRatio
  exact ⟨div_pos ha hB, (div_le_one hB).2 (le_add_of_nonneg_left hA)⟩

theorem trialRatio_reciprocal {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) :
    trialRatio A H = 1 / (H * trialWeight A H) := by
  have ha := trialWeight_pos (A := A) hH
  unfold trialRatio
  rw [← trialWeight_eq hA hH]
  field_simp [hH.ne', ha.ne'] <;> ring

theorem trialRatio_formula {A H : ℝ} (hA : 0 ≤ A) (hH : 0 < H) :
    trialRatio A H = 2 / (1 + Real.sqrt (1 + 4 * H * A)) := by
  rw [trialRatio_reciprocal hA hH]
  have hs : 0 < 1 + Real.sqrt (1 + 4 * H * A) := by positivity
  unfold trialWeight
  field_simp [hH.ne', hs.ne'] <;> ring

theorem trialRatio_antitone {A H₁ H₂ : ℝ} (hA : 0 ≤ A) (h₁ : 0 < H₁) (hle : H₁ ≤ H₂) :
    trialRatio A H₂ ≤ trialRatio A H₁ := by
  rw [trialRatio_formula hA h₁, trialRatio_formula hA (h₁.trans_le hle)]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  apply add_le_add_left
  apply Real.sqrt_le_sqrt
  nlinarith only [mul_le_mul_of_nonneg_right hle hA]

theorem trialWeight_small {A H η : ℝ} (hA : 0 ≤ A) (hH : 0 < H) (hη : 0 < η)
    (hlarge : A / η^2 + 1 / η < H) : trialWeight A H < η := by
  let a := trialWeight A H
  have ha : 0 < a := trialWeight_pos hH
  have he : H * a^2 = A + a := trialWeight_eq hA hH
  have hH' : H = A / a^2 + 1 / a := by
    field_simp [ha.ne']
    nlinarith only [he]
  by_contra! hn
  have hs : η^2 ≤ a^2 := (sq_le_sq₀ hη.le ha.le).2 hn
  have h₁ := div_le_div_of_nonneg_left hA (pow_pos hη 2) hs
  have h₂ := one_div_le_one_div_of_le hη hn
  change η ≤ a at hn
  linarith only [hlarge, hH', h₁, h₂]

end
end UFGM
