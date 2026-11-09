import UFGM.Holder
import UFGM.TrialScalar

namespace UFGM

noncomputable section

def holderPower (ν : ℝ) : ℝ := (1 - ν) / (1 + ν)

def smoothConstant (ν M ε : ℝ) : ℝ := M^(2 / (1 + ν)) * ε^(-holderPower ν)

theorem holderPower_range {ν : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) :
    0 ≤ holderPower ν ∧ holderPower ν ≤ 1 := by
  have hp : 0 < 1 + ν := by linarith
  exact ⟨div_nonneg (sub_nonneg.mpr hν') hp.le, (div_le_one hp).2 (by linarith)⟩

theorem smoothConstant_nonneg {ν M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    0 ≤ smoothConstant ν M ε := by
  unfold smoothConstant
  positivity

theorem young_holder {ν M δ r : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1)
    (hM : 0 ≤ M) (hδ : 0 < δ) (hr : 0 ≤ r) :
    M / (1 + ν) * r^(1 + ν) ≤ smoothConstant ν M δ * r^2 / 2 + δ / 2 := by
  let α := (1 + ν) / 2
  let β := (1 - ν) / 2
  let p := holderPower ν
  let C := smoothConstant ν M δ
  let u := C * r^2
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := div_nonneg (sub_nonneg.mpr hν') (by norm_num)
  have hsum : α + β = 1 := by dsimp [α, β]; ring
  have hden : 0 < 1 + ν := by positivity
  have hu : 0 ≤ u := mul_nonneg (smoothConstant_nonneg hM hδ) (sq_nonneg _)
  have hαM : (2 / (1 + ν)) * α = 1 := by dsimp [α]; field_simp [hden.ne'] <;> ring
  have hβδ : (-p) * α + β = 0 := by dsimp [p, holderPower, α, β]; field_simp [hden.ne'] <;> ring
  have hαr : 2 * α = 1 + ν := by dsimp [α]; ring
  have hproduct : u^α * δ^β = M * r^(1 + ν) := by
    change (C * r^2)^α * δ^β = _
    rw [Real.mul_rpow (smoothConstant_nonneg hM hδ) (sq_nonneg r), ← Real.rpow_two r,
      ← Real.rpow_mul hr, hαr]
    change (((M^(2 / (1 + ν))) * δ^(-p))^α) * r^(1 + ν) * δ^β = _
    rw [Real.mul_rpow (Real.rpow_nonneg hM _) (Real.rpow_nonneg hδ.le _),
      ← Real.rpow_mul hM, ← Real.rpow_mul hδ.le, hαM, Real.rpow_one]
    calc
      _ = M * r^(1 + ν) * (δ^((-p) * α) * δ^β) := by ring
      _ = _ := by rw [← Real.rpow_add hδ, hβδ, Real.rpow_zero, mul_one]
  have ham := Real.geom_mean_le_arith_mean2_weighted hα.le hβ hu hδ.le hsum
  rw [hproduct] at ham
  have hβ' : β ≤ α := by dsimp [α, β]; linarith
  have hc : M / (1 + ν) * r^(1 + ν) ≤ (α * u + α * δ) / (1 + ν) := by
    apply (le_div_iff₀ hden).2
    calc
      _ = M * r^(1 + ν) := by field_simp [hden.ne'] <;> ring
      _ ≤ _ := ham.trans (add_le_add_left (mul_le_mul_of_nonneg_right hβ' hδ.le) _)
  refine hc.trans_eq ?_
  change (α * (C * r^2) + α * δ) / (1 + ν) = C * r^2 / 2 + δ / 2
  dsimp only [α]
  field_simp [hden.ne'] <;> ring

theorem tolerance_model {ν M ε τ H r : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1)
    (hM : 0 ≤ M) (hε : 0 < ε) (hτ : 0 < τ) (hr : 0 ≤ r)
    (hH : smoothConstant ν M ε ≤ H * τ^(holderPower ν)) :
    M / (1 + ν) * r^(1 + ν) ≤ H * r^2 / 2 + ε * τ / 2 := by
  have hp : 0 < τ^(holderPower ν) := Real.rpow_pos_of_pos hτ _
  have he : smoothConstant ν M (ε * τ) = smoothConstant ν M ε / τ^(holderPower ν) := by
    unfold smoothConstant
    simp only [Real.mul_rpow hε.le hτ.le, Real.rpow_neg hτ.le, div_eq_mul_inv, mul_assoc]
  have hc : smoothConstant ν M (ε * τ) ≤ H := by
    rw [he]
    exact (div_le_iff₀ hp).2 hH
  exact (young_holder hν hν' hM (mul_pos hε hτ) hr).trans
    (add_le_add_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg r)) (by norm_num)) _)

end
end UFGM
