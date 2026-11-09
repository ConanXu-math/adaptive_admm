import UFGM.Estimate

namespace UFGM

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def rateScale (p : Problem E) (ν M : ℝ) : ℝ := max p.L0 (2 * smoothConstant ν M p.ε)

def ratePower (ν : ℝ) : ℝ := 1 / (2 - holderPower ν)

theorem rateScale_pos (p : Problem E) (ν M : ℝ) : 0 < rateScale p ν M :=
  p.L0_pos.trans_le (le_max_left _ _)

theorem ratePower_pos {ν : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) : 0 < ratePower ν :=
  one_div_pos.mpr (by linarith only [(holderPower_range hν hν').2])

theorem ratePower_eq {ν : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) :
    ratePower ν = (1 + ν) / (1 + 3 * ν) := by
  have h₁ : 0 < 1 + ν := by positivity
  have he : 2 - holderPower ν = (1 + 3 * ν) / (1 + ν) := by
    unfold holderPower
    apply (eq_div_iff h₁.ne').2
    rw [sub_mul, div_mul_cancel₀ _ h₁.ne']
    ring
  rw [ratePower, he, one_div_div]

theorem states_A_pos (p : Problem E) (h : HasHolder p) (n : ℕ) (hn : 1 ≤ n) :
    0 < (states p h n).A := by
  cases n with
  | zero => omega
  | succ n => exact next_A_pos p h (states p h n)

theorem gap_le_estimate (p : Problem E) (h : HasHolder p) (w : E) (hw : w ∈ p.regularizer.dom)
    (n : ℕ) (hn : 1 ≤ n) :
    objective p (states p h n).y - objective p w ≤
      p.ε / 2 + bregman p.kernel p.x0 w / (states p h n).A := by
  let s := states p h n
  have hA : 0 < s.A := states_A_pos p h n hn
  have hwD : w ∈ estimateDomain p s := by simpa only [estimateDomain, if_neg hA.ne'] using hw
  have hmin := (isMinOn_iff.1 (estimateMin_spec p s).2) w hwD
  have hlo := estimate_lower p h n
  change s.A * (objective p s.y - p.ε / 2) ≤ estimateFun p s (estimateMin p s) at hlo
  have hhi := estimate_upper p h w hw n
  have hall := hlo.trans (hmin.trans hhi)
  have hmul : (objective p s.y - objective p w - p.ε / 2) * s.A ≤ bregman p.kernel p.x0 w := by
    change s.A * (objective p s.y - p.ε / 2) ≤ bregman p.kernel p.x0 w + s.A * objective p w at hall
    nlinarith only [hall]
  have hdiv := (le_div_iff₀ hA).2 hmul
  change objective p s.y - objective p w ≤ p.ε / 2 + bregman p.kernel p.x0 w / s.A
  linarith only [hdiv]

theorem main_rate (p : Problem E) (h : HasHolder p)
    {ν M : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M) (hh : Holder p.oracle ν M)
    (w : E) (hw : w ∈ p.regularizer.dom) (n : ℕ) (hn : 1 ≤ n) :
    let s := states p h n
    let D := rateScale p ν M
    let γ := ratePower ν
    s.y ∈ p.regularizer.dom ∧
    ((n : ℝ) / 2)^(1 / γ) / D ≤ s.A ∧
    objective p s.y - objective p w ≤ p.ε / 2 +
      D * bregman p.kernel p.x0 w / ((n : ℝ) / 2)^(1 / γ) := by
  let s := states p h n
  let D := rateScale p ν M
  let γ := ratePower ν
  let R := ((n : ℝ) / 2)^(1 / γ)
  let ξ := bregman p.kernel p.x0 w
  have hA := states_A_pos p h n hn
  have hD := rateScale_pos p ν M
  have hg : R / D ≤ s.A := states_growth p h hν hν' hM hh n
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hR : 0 < R := Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ) / 2) _
  have hξ : 0 ≤ ξ := (by positivity : 0 ≤ ‖w - p.x0‖^2 / 2).trans
    (bregman_lower p.kernel p.x0_mem (p.regularizer.subset hw))
  refine ⟨s.y_dom hA, hg, ?_⟩
  have hgap := gap_le_estimate p h w hw n hn
  calc
    _ ≤ p.ε / 2 + ξ / s.A := hgap
    _ ≤ p.ε / 2 + ξ / (R / D) :=
      add_le_add_left (div_le_div_of_nonneg_left hξ (div_pos hR hD) hg) _
    _ = _ := by change _ = p.ε / 2 + D * ξ / R; rw [div_div_eq_mul_div, mul_comm ξ D]

def sufficientRounds (p : Problem E) (ν M : ℝ) (w : E) : ℕ :=
  max 1 ⌈2 * (2 * rateScale p ν M * bregman p.kernel p.x0 w / p.ε)^(ratePower ν)⌉₊

theorem target_accuracy (p : Problem E) (h : HasHolder p)
    {ν M : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M) (hh : Holder p.oracle ν M)
    (w : E) (hw : w ∈ p.regularizer.dom) (n : ℕ) (hn : sufficientRounds p ν M w ≤ n) :
    objective p (states p h n).y - objective p w ≤ p.ε := by
  let s := states p h n
  let D := rateScale p ν M
  let γ := ratePower ν
  let ξ := bregman p.kernel p.x0 w
  let X := 2 * D * ξ / p.ε
  have hD := rateScale_pos p ν M
  have hγ := ratePower_pos hν hν'
  have hξ : 0 ≤ ξ := (by positivity : 0 ≤ ‖w - p.x0‖^2 / 2).trans
    (bregman_lower p.kernel p.x0_mem (p.regularizer.subset hw))
  have hX : 0 ≤ X := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD.le) hξ) p.ε_pos.le
  have hn₁ : 1 ≤ n := (le_max_left _ _).trans hn
  have hn₂ : 2 * X^γ ≤ (n : ℝ) := by
    have hcast : (⌈2 * X^γ⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show ⌈2 * X^γ⌉₊ ≤ n from (le_max_right _ _).trans hn)
    exact (Nat.le_ceil _).trans hcast
  have hle : X^γ ≤ (n : ℝ) / 2 := by linarith only [hn₂]
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hX _) hle (one_div_pos.mpr hγ).le
  rw [← Real.rpow_mul hX, mul_one_div_cancel hγ.ne', Real.rpow_one] at hpow
  have hAg : 2 * ξ / p.ε ≤ s.A := by
    calc
      _ = X / D := by
        apply (eq_div_iff (show D ≠ 0 from hD.ne')).2
        dsimp only [X]
        ring
      _ ≤ ((n : ℝ) / 2)^(1 / γ) / D := div_le_div_of_nonneg_right hpow hD.le
      _ ≤ _ := states_growth p h hν hν' hM hh n
  have hA := states_A_pos p h n hn₁
  have hsmall : ξ / s.A ≤ p.ε / 2 := by
    apply (div_le_iff₀ hA).2
    have hh' := (div_le_iff₀ p.ε_pos).1 hAg
    nlinarith only [hh']
  have hgap := gap_le_estimate p h w hw n hn₁
  change objective p s.y - objective p w ≤ p.ε
  linarith only [hgap, hsmall]

end
end UFGM
