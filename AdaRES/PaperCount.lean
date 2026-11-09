import AdaRES.Count

open scoped BigOperators

namespace AdaRES

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {data : Smooth E} {ψ : ProperConvex E}

theorem callCount_eq34 (opt : Minimum data ψ) (p : RestartParams E) (h0 : p.x0 ∈ ψ.dom)
    {μF : ℝ} (hF : 0 < μF) (hq : LocalGrowth opt p.x0 μF)
    (hterm : ∃ s, stageSuccess data ψ p s) (hle : p.μ0 ≤ μF)
    (hraw : p.μ0 < 4 * Real.exp 1) (hΔ : 0 < gap opt p.x0)
    (hV : 1 ≤ ⌈Real.log (2 * gap opt p.x0 / p.ε)⌉₊) :
    callCount p hterm ≤ ⌈2 * Real.sqrt (Real.exp 1 / p.μ0) - 1⌉₊ *
      ⌈Real.log (2 * gap opt p.x0 / p.ε)⌉₊ + 2 := by
  have hs := goodStage_zero p.μ0_pos hF hle
  have hk := (period_original p.μ0_pos hraw).1
  have hv : goodRounds (gap opt p.x0) p.ε = ⌈Real.log (2 * gap opt p.x0 / p.ε)⌉₊ :=
    expRounds_original (by positivity) hV
  have H := callCount_bound opt p h0 hF hq hterm
  simp only [hs, Finset.range_zero, Finset.sum_empty, Nat.add_zero, estimate, pow_zero, div_one, hk, hv] at H
  rw [Nat.mul_comm]
  omega

theorem callCount_eq35 (opt : Minimum data ψ) (p : RestartParams E) (h0 : p.x0 ∈ ψ.dom)
    {μF : ℝ} (hF : 0 < μF) (hq : LocalGrowth opt p.x0 μF)
    (hterm : ∃ s, stageSuccess data ψ p s) (hgt : μF < p.μ0)
    (hraw : p.μ0 < 4 * Real.exp 1) (hΔ : 0 < gap opt p.x0)
    (hU : 1 ≤ ⌈Real.log ((32 * gap opt p.x0 / μF) / p.ε)⌉₊)
    (hV : 1 ≤ ⌈Real.log (2 * gap opt p.x0 / p.ε)⌉₊) :
    let S := goodStage p.μ0 μF
    let U := ⌈Real.log ((32 * gap opt p.x0 / μF) / p.ε)⌉₊
    let V := ⌈Real.log (2 * gap opt p.x0 / p.ε)⌉₊
    (callCount p hterm : ℝ) ≤ 1 + (S : ℝ)
      + (2 * Real.sqrt (Real.exp 1) / (Real.sqrt 2 - 1) *
        (Real.sqrt (2 / μF) - Real.sqrt (1 / p.μ0))) * (U : ℝ)
      + (⌈2 * Real.sqrt (2 * Real.exp 1 / μF)⌉₊ : ℝ) * (V : ℝ) := by
  let S := goodStage p.μ0 μF
  let U := ⌈Real.log ((32 * gap opt p.x0 / μF) / p.ε)⌉₊
  let V := ⌈Real.log (2 * gap opt p.x0 / p.ε)⌉₊
  let K := fun s => period (estimate p.μ0 s)
  let J := ⌈2 * Real.sqrt (2 * Real.exp 1 / μF)⌉₊
  have hu : earlyRounds (gap opt p.x0) μF p.ε = U := expRounds_original (by positivity) hU
  have hv : goodRounds (gap opt p.x0) p.ε = V := expRounds_original (by positivity) hV
  have H := callCount_bound opt p h0 hF hq hterm
  change callCount p hterm ≤
    1 + (∑ s ∈ Finset.range S, (earlyRounds (gap opt p.x0) μF p.ε * K s + 1))
      + (goodRounds (gap opt p.x0) p.ε * K S + 1) at H
  rw [hu, hv] at H
  have Hc : (callCount p hterm : ℝ) ≤
    ((1 + (∑ s ∈ Finset.range S, (U * K s + 1)) + (V * K S + 1) : ℕ) : ℝ) := by exact_mod_cast H
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sum, Nat.cast_mul] at Hc
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at Hc
  have hone : (∑ _s ∈ Finset.range S, (1 : ℝ)) = (S : ℝ) := by simp
  rw [hone] at Hc
  have hs := sum_period_bound p.μ0_pos hF hgt hraw
  have hsu := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg U)
  have hm := estimate_at_goodStage_lower p.μ0_pos hF hgt
  have hroot : Real.sqrt (Real.exp 1 / estimate p.μ0 S) ≤ Real.sqrt (2 * Real.exp 1 / μF) := by
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ Real.exp 1 / (μF / 2) := div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hm.le
      _ = _ := by field_simp [hF.ne'] <;> ring
  have hK : K S + 1 ≤ J := by
    have horig := (period_original (estimate_pos p.μ0_pos S)
      ((estimate_le_initial p.μ0_pos S).trans_lt hraw)).2.2
    exact horig.trans_le (Nat.ceil_le_ceil (mul_le_mul_of_nonneg_left hroot (by norm_num)))
  have htail : V * K S + 1 ≤ V * J := by
    calc
      _ ≤ V * K S + V := Nat.add_le_add_left hV _
      _ = V * (K S + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ ≤ _ := Nat.mul_le_mul_left V hK
  have ht : (V : ℝ) * (K S : ℝ) + 1 ≤ (V : ℝ) * (J : ℝ) := by exact_mod_cast htail
  change (callCount p hterm : ℝ) ≤ 1 + (S : ℝ)
    + (2 * Real.sqrt (Real.exp 1) / (Real.sqrt 2 - 1) *
        (Real.sqrt (2 / μF) - Real.sqrt (1 / p.μ0))) * (U : ℝ)
    + (J : ℝ) * (V : ℝ)
  nlinarith only [Hc, hsu, ht]

end
end AdaRES
