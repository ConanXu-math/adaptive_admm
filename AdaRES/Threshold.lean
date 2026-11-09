import AdaRES.Scalar

namespace AdaRES

noncomputable section

def period (μ : ℝ) : ℕ := max 1 ⌈2 * Real.sqrt (Real.exp 1 / μ) - 1⌉₊

theorem period_pos (μ : ℝ) : 0 < period μ :=
  Nat.zero_lt_one.trans_le (le_max_left _ _)

def phaseFactor (μ : ℝ) : ℝ := (theta (period μ - 1))^2 / μ

theorem phaseFactor_nonneg {μ : ℝ} (hμ : 0 < μ) : 0 ≤ phaseFactor μ :=
  div_nonneg (sq_nonneg _) hμ.le

theorem phaseFactor_le {μ : ℝ} (hμ : 0 < μ) : phaseFactor μ ≤ Real.exp (-1) := by
  let K := period μ
  let s := Real.sqrt (Real.exp 1 / μ)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos (Real.exp_pos _) hμ)
  have hs2 : s^2 = Real.exp 1 / μ := Real.sq_sqrt (div_nonneg (Real.exp_nonneg _) hμ.le)
  have hK : 1 ≤ K := le_max_left _ _
  have hbound : 2 * s ≤ (K : ℝ) + 1 := by
    have hc : 2 * s - 1 ≤ (⌈2 * s - 1⌉₊ : ℝ) := Nat.le_ceil _
    have hkc : (⌈2 * s - 1⌉₊ : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (show ⌈2 * s - 1⌉₊ ≤ K from le_max_right _ _)
    linarith only [hc, hkc]
  have hθ := theta_bound (K - 1)
  have he : ((K - 1 : ℕ) : ℝ) + 2 = (K : ℝ) + 1 := by
    rw [Nat.cast_sub hK, Nat.cast_one]
    ring
  rw [he] at hθ
  have hd : 0 < (K : ℝ) + 1 := by positivity
  have ht := theta_pos (K - 1)
  have hm := (le_div_iff₀ hd).1 hθ
  have hm' := (mul_le_mul_of_nonneg_left hbound ht.le).trans hm
  have hsmall : theta (K - 1) * s ≤ 1 := by nlinarith only [hm']
  have hsq := (sq_le_sq₀ (mul_nonneg ht.le hs.le) zero_le_one).2 hsmall
  rw [mul_pow, hs2, one_pow] at hsq
  change (theta (K - 1))^2 / μ ≤ Real.exp (-1)
  rw [Real.exp_neg, ← one_div]
  apply (le_div_iff₀ (Real.exp_pos 1)).2
  calc
    _ = (theta (K - 1))^2 * (Real.exp 1 / μ) := by ring
    _ ≤ _ := hsq

def expRounds (A ε : ℝ) : ℕ :=
  if A = 0 then 1 else max 1 ⌈Real.log (A / ε)⌉₊

theorem expRounds_pos (A ε : ℝ) : 0 < expRounds A ε := by
  unfold expRounds
  split_ifs
  · exact Nat.zero_lt_one
  · exact Nat.zero_lt_one.trans_le (le_max_left _ _)

theorem expRounds_bound {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    A * Real.exp (-(expRounds A ε : ℝ)) ≤ ε := by
  by_cases hzero : A = 0
  · simp [hzero, hε.le]
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
    have hround : Real.log (A / ε) ≤ (expRounds A ε : ℝ) := by
      have h := Nat.le_ceil (Real.log (A / ε))
      have h' : ⌈Real.log (A / ε)⌉₊ ≤ expRounds A ε := by
        simp only [expRounds, if_neg hzero]
        exact le_max_right _ _
      exact h.trans (by exact_mod_cast h')
    have hdiv := (Real.log_le_iff_le_exp (div_pos hAp hε)).1 hround
    have he := (div_le_iff₀ hε).1 hdiv
    calc
      _ ≤ (Real.exp (expRounds A ε : ℝ) * ε) * Real.exp (-(expRounds A ε : ℝ)) :=
        mul_le_mul_of_nonneg_right he (Real.exp_nonneg _)
      _ = ε * (Real.exp (expRounds A ε : ℝ) * Real.exp (-(expRounds A ε : ℝ))) := by ring
      _ = ε := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem phaseFactor_pow_le {μ : ℝ} (hμ : 0 < μ) (n : ℕ) :
    (phaseFactor μ)^n ≤ Real.exp (-(n : ℝ)) := by
  calc
    _ ≤ (Real.exp (-1))^n := pow_le_pow_left₀ (phaseFactor_nonneg hμ) (phaseFactor_le hμ) _
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

def estimate (μ0 : ℝ) (s : ℕ) : ℝ := μ0 / (2 : ℝ)^s

theorem estimate_pos {μ0 : ℝ} (hμ0 : 0 < μ0) (s : ℕ) : 0 < estimate μ0 s :=
  div_pos hμ0 (pow_pos (by norm_num) s)

def goodStage (μ0 μF : ℝ) : ℕ := ⌈Real.log (μ0 / μF) / Real.log 2⌉₊

theorem goodStage_iff {μ0 μF : ℝ} (hμ0 : 0 < μ0) (hμF : 0 < μF) (s : ℕ) :
    goodStage μ0 μF ≤ s ↔ estimate μ0 s ≤ μF := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hp := pow_pos htwo s
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [goodStage, Nat.ceil_le, div_le_iff₀ hlog, ← Real.log_pow,
    Real.log_le_log_iff (div_pos hμ0 hμF) hp, div_le_iff₀ hμF, estimate, div_le_iff₀ hp]
  rw [mul_comm μF]

end
end AdaRES
