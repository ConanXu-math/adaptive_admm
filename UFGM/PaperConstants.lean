import UFGM.Main

namespace UFGM

theorem paper_rate_coeff_eq {ν M ε k : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1)
    (hM : 0 ≤ M) (hε : 0 < ε) (hk : 0 < k) :
    2 * smoothConstant ν M ε / (k / 2)^(1 / ratePower ν) =
      (((2 : ℝ)^(2 + 4 * ν) * M^2) / (ε^(1 - ν) * k^(1 + 3 * ν)))^(1 / (1 + ν)) := by
  let r := 1 + ν
  let t := 1 / r
  let q := (1 + 3 * ν) / r
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < 1 + 3 * ν := by positivity
  have hq : 1 / ratePower ν = q := by
    simp only [ratePower_eq hν hν', one_div_div, q, r]
  have ht₁ : (2 + 4 * ν) * t = 1 + q := by
    dsimp only [t, q]
    field_simp [hr.ne'] <;> dsimp [r] <;> ring
  have ht₂ : 2 * t = 2 / (1 + ν) := by dsimp [t, r]; ring
  have ht₃ : (1 - ν) * t = holderPower ν := by dsimp [t, r, holderPower]; ring
  have ht₄ : (1 + 3 * ν) * t = q := by dsimp [t, q]; ring
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hnum : ((2 : ℝ)^(2 + 4 * ν) * M^2)^t = (2 : ℝ)^(1 + q) * M^(2 / (1 + ν)) := by
    rw [Real.mul_rpow (Real.rpow_nonneg htwo.le _) (sq_nonneg M), ← Real.rpow_two M,
      ← Real.rpow_mul htwo.le, ← Real.rpow_mul hM, ht₁, ht₂]
  have hden : (ε^(1 - ν) * k^(1 + 3 * ν))^t = ε^(holderPower ν) * k^q := by
    rw [Real.mul_rpow (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hk.le _),
      ← Real.rpow_mul hε.le, ← Real.rpow_mul hk.le, ht₃, ht₄]
  change 2 * smoothConstant ν M ε / (k / 2)^(1 / ratePower ν) =
    (((2 : ℝ)^(2 + 4 * ν) * M^2) / (ε^(1 - ν) * k^(1 + 3 * ν)))^t
  rw [Real.div_rpow (mul_nonneg (Real.rpow_nonneg htwo.le _) (sq_nonneg M))
      (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg hk.le _)), hnum, hden,
    hq, Real.div_rpow hk.le htwo.le, smoothConstant, Real.rpow_neg hε.le,
    Real.rpow_add htwo, Real.rpow_one]
  field_simp [(Real.rpow_pos_of_pos hε (holderPower ν)).ne',
    (Real.rpow_pos_of_pos hk q).ne', (Real.rpow_pos_of_pos htwo q).ne'] <;> ring

theorem paper_round_threshold_eq {ν M ε ξ : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1)
    (hM : 0 ≤ M) (hε : 0 < ε) (hξ : 0 ≤ ξ) :
    2 * (4 * smoothConstant ν M ε * ξ / ε)^(ratePower ν) =
      (((2 : ℝ)^((3 + 5 * ν) / 2) * M) / ε)^(2 / (1 + 3 * ν)) * ξ^(ratePower ν) := by
  let γ := ratePower ν
  let p := holderPower ν
  let m := 2 / (1 + ν)
  let b := 2 / (1 + 3 * ν)
  let c := (3 + 5 * ν) / 2
  let C := smoothConstant ν M ε
  have h₁ : 0 < 1 + ν := by positivity
  have h₃ : 0 < 1 + 3 * ν := by positivity
  have hg : γ = (1 + ν) / (1 + 3 * ν) := ratePower_eq hν hν'
  have hm : m * γ = b := by
    dsimp only [m, b]
    rw [hg]
    field_simp [h₁.ne', h₃.ne'] <;> ring
  have he : (-p) * γ - γ = -b := by
    dsimp only [p, b, holderPower]
    rw [hg]
    field_simp [h₁.ne', h₃.ne'] <;> ring
  have hc : c * b = 1 + 2 * γ := by
    dsimp only [c, b]
    rw [hg]
    field_simp [h₃.ne'] <;> ring
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have hC : 0 ≤ C := smoothConstant_nonneg hM hε
  have h4pow : (4 : ℝ)^γ = (2 : ℝ)^(2 * γ) := by
    calc
      _ = ((2 : ℝ)^(2 : ℝ))^γ := by rw [Real.rpow_two]; norm_num
      _ = _ := (Real.rpow_mul h2.le 2 γ).symm
  have h2pow : 2 * (2 : ℝ)^(2 * γ) = (2 : ℝ)^(c * b) := by
    rw [hc, Real.rpow_add h2, Real.rpow_one]
  have hεpow : ε^((-p) * γ) / ε^γ = (ε^b)⁻¹ := by
    rw [← Real.rpow_sub hε, he, Real.rpow_neg hε.le]
  have hCpow : C^γ = M^b * ε^((-p) * γ) := by
    change (M^m * ε^(-p))^γ = _
    rw [Real.mul_rpow (Real.rpow_nonneg hM _) (Real.rpow_nonneg hε.le _),
      ← Real.rpow_mul hM, ← Real.rpow_mul hε.le, hm]
  have hright : (((2 : ℝ)^c * M) / ε)^b = (2 : ℝ)^(c * b) * M^b / ε^b := by
    rw [Real.div_rpow (mul_nonneg (Real.rpow_nonneg h2.le _) hM) hε.le,
      Real.mul_rpow (Real.rpow_nonneg h2.le _) hM, ← Real.rpow_mul h2.le]
  change 2 * (4 * C * ξ / ε)^γ = (((2 : ℝ)^c * M) / ε)^b * ξ^γ
  rw [Real.div_rpow (mul_nonneg (mul_nonneg h4 hC) hξ) hε.le,
    Real.mul_rpow (mul_nonneg h4 hC) hξ, Real.mul_rpow h4 hC,
    h4pow, hCpow, hright]
  calc
    _ = (2 * (2 : ℝ)^(2 * γ)) * M^b * ξ^γ * (ε^((-p) * γ) / ε^γ) := by ring
    _ = _ := by rw [h2pow, hεpow, div_eq_mul_inv]; ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem paper_rate (p : Problem E) (h : HasHolder p)
    {ν M : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M) (hh : Holder p.oracle ν M)
    (hL : p.L0 ≤ 2 * smoothConstant ν M p.ε)
    (w : E) (hw : w ∈ p.regularizer.dom) (n : ℕ) (hn : 1 ≤ n) :
    objective p (states p h n).y - objective p w ≤
      (((2 : ℝ)^(2 + 4 * ν) * M^2) / (p.ε^(1 - ν) * (n : ℝ)^(1 + 3 * ν)))^(1 / (1 + ν)) *
        bregman p.kernel p.x0 w + p.ε / 2 := by
  let ξ := bregman p.kernel p.x0 w
  let R := ((n : ℝ) / 2)^(1 / ratePower ν)
  have hD : rateScale p ν M = 2 * smoothConstant ν M p.ε := max_eq_right hL
  have H := (main_rate p h hν hν' hM hh w hw n hn).2.2
  change objective p (states p h n).y - objective p w ≤ p.ε / 2 + rateScale p ν M * ξ / R at H
  rw [hD] at H
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have he := paper_rate_coeff_eq hν hν' hM p.ε_pos hn'
  change 2 * smoothConstant ν M p.ε / R = _ at he
  calc
    _ ≤ _ := H
    _ = (2 * smoothConstant ν M p.ε / R) * ξ + p.ε / 2 := by ring
    _ = _ := by rw [he]

theorem paper_rounds (p : Problem E) {ν M : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M)
    (hL : p.L0 ≤ 2 * smoothConstant ν M p.ε) (w : E) (hw : w ∈ p.regularizer.dom) :
    sufficientRounds p ν M w = max 1
      ⌈((((2 : ℝ)^((3 + 5 * ν) / 2) * M) / p.ε)^(2 / (1 + 3 * ν))) *
        (bregman p.kernel p.x0 w)^((1 + ν) / (1 + 3 * ν))⌉₊ := by
  let C := smoothConstant ν M p.ε
  let ξ := bregman p.kernel p.x0 w
  have hξ : 0 ≤ ξ := (by positivity : 0 ≤ ‖w - p.x0‖^2 / 2).trans
    (bregman_lower p.kernel p.x0_mem (p.regularizer.subset hw))
  have hD : rateScale p ν M = 2 * C := max_eq_right hL
  unfold sufficientRounds
  rw [hD, show 2 * (2 * C) * ξ / p.ε = 4 * C * ξ / p.ε from by ring]
  rw [paper_round_threshold_eq hν hν' hM p.ε_pos hξ, ratePower_eq hν hν']

theorem paper_target_accuracy (p : Problem E) (h : HasHolder p)
    {ν M : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M) (hh : Holder p.oracle ν M)
    (hL : p.L0 ≤ 2 * smoothConstant ν M p.ε) (w : E) (hw : w ∈ p.regularizer.dom)
    (n : ℕ) (hn : max 1
      ⌈((((2 : ℝ)^((3 + 5 * ν) / 2) * M) / p.ε)^(2 / (1 + 3 * ν))) *
        (bregman p.kernel p.x0 w)^((1 + ν) / (1 + 3 * ν))⌉₊ ≤ n) :
    objective p (states p h n).y - objective p w ≤ p.ε := by
  apply target_accuracy p h hν hν' hM hh w hw n
  rw [paper_rounds p hν hν' hM hL w hw]
  exact hn

end UFGM
