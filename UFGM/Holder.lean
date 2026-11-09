import Mathlib

open Filter Topology Set

namespace UFGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Oracle (Q : Set E) where
  value : E → ℝ
  grad : E → E →L[ℝ] ℝ
  support : ∀ x ∈ Q, ∀ y ∈ Q, value x + grad x (y - x) ≤ value y

def Holder {Q : Set E} (o : Oracle Q) (ν M : ℝ) : Prop :=
  ∀ x ∈ Q, ∀ y ∈ Q, ‖o.grad x - o.grad y‖ ≤ M * ‖x - y‖^ν

theorem holder_model {Q : Set E} (hQ : Convex ℝ Q) (o : Oracle Q)
    {ν M : ℝ} (hν : 0 ≤ ν) (hM : 0 ≤ M) (hh : Holder o ν M)
    (x y : E) (hx : x ∈ Q) (hy : y ∈ Q) :
    o.value y ≤ o.value x + o.grad x (y - x) + M / (1 + ν) * ‖y - x‖^(1 + ν) := by
  have hq : 0 < 1 + ν := by linarith only [hν]
  by_cases hxy : x = y
  · subst y
    simp [Real.zero_rpow hq.ne']
  by_cases hν₀ : ν = 0
  · subst ν
    have h := o.support y hy x hx
    rw [show x - y = -(y - x) from by abel, map_neg] at h
    have hp := hh y hy x hx
    simp only [Real.rpow_zero, mul_one] at hp
    have hs : o.grad y (y - x) - o.grad x (y - x) ≤ M * ‖y - x‖ := by
      change (o.grad y - o.grad x) (y - x) ≤ _
      have hop : |(o.grad y - o.grad x) (y - x)| ≤ ‖o.grad y - o.grad x‖ * ‖y - x‖ := by
        simpa only [Real.norm_eq_abs] using (o.grad y - o.grad x).le_opNorm (y - x)
      exact (le_abs_self _).trans (hop.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _)))
    simp only [add_zero, div_one, Real.rpow_one]
    linarith only [h, hs]
  have hνp : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν₀)
  let I := Icc (0 : ℝ) 1
  let d := y - x
  let z := fun t : ℝ => x + t • d
  let F := fun t : ℝ => o.value (z t)
  let a := fun t : ℝ => o.grad (z t) d
  let C := M * ‖d‖^(1 + ν)
  have hd : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hxy h.symm))
  have hz (t : ℝ) (ht : t ∈ I) : z t ∈ Q := by
    have hmem := hQ hx hy (sub_nonneg.mpr ht.2) ht.1 (show (1 - t) + t = 1 by ring)
    have he : (1 - t) • x + t • y = z t := by dsimp [z, d]; rw [sub_smul, one_smul, smul_sub]; abel
    rwa [he] at hmem
  have hzd (u t : ℝ) : z u - z t = (u - t) • d := by
    dsimp only [z]
    rw [sub_smul]
    abel
  have ha (u t : ℝ) (hu : u ∈ I) (ht : t ∈ I) : |a u - a t| ≤ C * |u - t|^ν := by
    calc
      _ = ‖(o.grad (z u) - o.grad (z t)) d‖ := by
        simp only [a, Real.norm_eq_abs, ContinuousLinearMap.sub_apply]
      _ ≤ ‖o.grad (z u) - o.grad (z t)‖ * ‖d‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M * ‖z u - z t‖^ν) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (hh (z u) (hz u hu) (z t) (hz t ht)) (norm_nonneg _)
      _ = (M * (‖d‖ * ‖d‖^ν)) * |u - t|^ν := by
        rw [hzd, norm_smul, Real.norm_eq_abs, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
        ring
      _ = _ := by
        dsimp only [C]
        have he : ‖d‖ * ‖d‖^ν = ‖d‖^(1 + ν) := by rw [Real.rpow_add hd, Real.rpow_one]
        rw [he]
  have hslope (u t : ℝ) (hu : u ∈ I) (ht : t ∈ I) (hne : u ≠ t) :
      |slope F t u - a t| ≤ C * |u - t|^ν := by
    have htU := o.support (z t) (hz t ht) (z u) (hz u hu)
    have huT := o.support (z u) (hz u hu) (z t) (hz t ht)
    rw [hzd, map_smul, smul_eq_mul] at htU huT
    change F t + (u - t) * a t ≤ F u at htU
    change F u + (t - u) * a u ≤ F t at huT
    let R := F u - F t - a t * (u - t)
    have hR : 0 ≤ R := by dsimp [R]; nlinarith only [htU]
    have hRu : R ≤ (a u - a t) * (u - t) := by dsimp [R]; nlinarith only [huT]
    have he : slope F t u - a t = R / (u - t) := by
      rw [slope_def_field]
      dsimp only [R]
      field_simp [sub_ne_zero.mpr hne] <;> ring
    rw [he, abs_div, abs_of_nonneg hR]
    apply (div_le_iff₀ (abs_pos.mpr (sub_ne_zero.mpr hne))).2
    calc
      _ ≤ (a u - a t) * (u - t) := hRu
      _ ≤ |a u - a t| * |u - t| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ _ := mul_le_mul_of_nonneg_right (ha u t hu ht) (abs_nonneg _)
  have hdF (t : ℝ) (ht : t ∈ I) : HasDerivWithinAt F (a t) I t := by
    apply hasDerivWithinAt_iff_tendsto_slope.2
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hc : ContinuousAt (fun u : ℝ => |u - t|) t := (continuous_id.sub continuous_const).abs.continuousAt
    have hlim : Tendsto (fun u : ℝ => |u - t|) (𝓝[I \ {t}] t) (𝓝 0) := by
      simpa only [sub_self, abs_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    have hp : Tendsto (fun u : ℝ => |u - t|^ν) (𝓝[I \ {t}] t) (𝓝 0) := by
      simpa only [Real.zero_rpow hν₀] using hlim.rpow_const (Or.inr hν)
    have hCp : Tendsto (fun u : ℝ => C * |u - t|^ν) (𝓝[I \ {t}] t) (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hp
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hCp
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hne : u ≠ t := fun h => hu.2 (by simp [h])
    simpa only [Real.norm_eq_abs] using hslope u t hu.1 ht hne
  let G := fun t : ℝ => F t - F 0 - a 0 * t - (C / (1 + ν)) * t^(1 + ν)
  have hCF : ContinuousOn F I := fun t ht => (hdF t ht).continuousWithinAt
  have hCp : Continuous (fun t : ℝ => (C / (1 + ν)) * t^(1 + ν)) :=
    continuous_const.mul (continuous_id.rpow_const fun _ => Or.inr hq.le)
  have hCG : ContinuousOn G I :=
    ((hCF.sub continuousOn_const).sub (continuous_const.mul continuous_id).continuousOn).sub hCp.continuousOn
  have hG (t : ℝ) (ht : t ∈ interior I) : HasDerivWithinAt G (a t - a 0 - C * t^ν) (interior I) t := by
    have hF := (hdF t (interior_subset ht)).mono interior_subset
    have hp := (Real.hasDerivAt_rpow_const (x := t) (p := 1 + ν)
      (Or.inr (by linarith only [hν]))).hasDerivWithinAt (s := interior I)
    have ha0 := ((hasDerivAt_id t).const_mul (a 0)).hasDerivWithinAt (s := interior I)
    have H := ((hF.sub_const (F 0)).sub ha0).sub (hp.const_mul (C / (1 + ν)))
    convert H using 1
    simp only [show 1 + ν - 1 = ν from by ring, mul_one, one_mul]
    field_simp [hq.ne'] <;> ring
  have hGn (t : ℝ) (ht : t ∈ interior I) : a t - a 0 - C * t^ν ≤ 0 := by
    have htI := interior_subset ht
    have h0 : (0 : ℝ) ∈ I := by norm_num [I]
    have H := ha t 0 htI h0
    rw [sub_zero, abs_of_nonneg htI.1] at H
    linarith only [H, le_abs_self (a t - a 0)]
  have hmono := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (0 : ℝ) 1) hCG hG hGn
  have H := hmono (show (0 : ℝ) ∈ I by norm_num [I]) (show (1 : ℝ) ∈ I by norm_num [I]) zero_le_one
  have hz₀ : z 0 = x := by simp [z]
  have hz₁ : z 1 = y := by simp [z, d]
  simp only [G, F, a, hz₀, hz₁, Real.zero_rpow hq.ne', Real.one_rpow, mul_zero, mul_one,
    sub_self, sub_zero] at H
  dsimp only [d, C] at H
  have he : (M * ‖y - x‖^(1 + ν)) / (1 + ν) = M / (1 + ν) * ‖y - x‖^(1 + ν) := by ring
  rw [he] at H
  linarith only [H]

end UFGM
