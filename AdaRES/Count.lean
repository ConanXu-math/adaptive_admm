import AdaRES.Restart

open scoped BigOperators

namespace AdaRES

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {data : Smooth E} {ψ : ProperConvex E}

def earlyRounds (Δ μF ε : ℝ) : ℕ := expRounds (32 * Δ / μF) ε
def goodRounds (Δ ε : ℝ) : ℕ := expRounds (2 * Δ) ε

theorem early_blocks_bound (opt : Minimum data ψ) (p : RestartParams E)
    (h0 : p.x0 ∈ ψ.dom) {μF : ℝ} (hF : 0 < μF) (s : ℕ)
    (hs : s < goodStage p.μ0 μF) : stageBlocks data ψ p s ≤ earlyRounds (gap opt p.x0) μF p.ε := by
  let prev := previous data ψ p s
  let μ := estimate p.μ0 s
  let U := earlyRounds (gap opt p.x0) μF p.ε
  have hm := estimate_pos p.μ0_pos s
  have hμ : μF < μ := lt_of_not_ge (fun h => (not_le_of_gt hs) ((goodStage_iff p.μ0_pos hF s).2 h))
  have hprev := previous_invariant data ψ p h0 s
  have hg : gap opt prev ≤ gap opt p.x0 := sub_le_sub_right hprev.2 _
  have hR := residual_le_gap opt prev hprev.1
  have hΔ := gap_nonneg opt p.x0 h0
  have hc : phaseConstant data ψ prev μ ≤ 32 * gap opt p.x0 / μF := by
    unfold phaseConstant
    calc
      _ ≤ (32 * gap opt p.x0) / μ :=
        div_le_div_of_nonneg_right (by linarith only [hR, hg]) hm.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hF hμ.le
  have hu : 0 < U := expRounds_pos _ _
  have ht : phaseConstant data ψ prev μ * Real.exp (-(U : ℝ)) ≤ p.ε :=
    (mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)).trans
      (expRounds_bound (by positivity) p.ε_pos)
  exact firstBlocks_le data ψ prev hm p.ε_pos hu (blockStop_of_threshold_le data ψ prev hm ht)

theorem good_blocks_bound (opt : Minimum data ψ) (p : RestartParams E)
    (h0 : p.x0 ∈ ψ.dom) {μF : ℝ} (hF : 0 < μF) (hq : LocalGrowth opt p.x0 μF)
    (s : ℕ) (hs : estimate p.μ0 s ≤ μF) : stageBlocks data ψ p s ≤ goodRounds (gap opt p.x0) p.ε := by
  let prev := previous data ψ p s
  let μ := estimate p.μ0 s
  let V := goodRounds (gap opt p.x0) p.ε
  have hm := estimate_pos p.μ0_pos s
  have hprev := previous_invariant data ψ p h0 s
  have hv : 0 < V := expRounds_pos _ _
  have hΔ := gap_nonneg opt p.x0 h0
  have hR := good_residual_bound opt p.x0 hF hq hm hs prev hprev.1 hprev.2 V
  have hstop : blockStop data ψ prev μ p.ε V :=
    Or.inr (hR.trans (expRounds_bound (by positivity) p.ε_pos))
  exact firstBlocks_le data ψ prev hm p.ε_pos hv hstop

theorem cached_block_count (K t : ℕ) (hK : 0 < K) (ht : 0 < t) :
    K + (t - 1) * (1 + (K - 1)) + 1 = t * K + 1 := by
  have hk' : 1 + (K - 1) = K := by omega
  have ht' : t - 1 + 1 = t := by omega
  rw [hk']
  calc
    _ = (t - 1 + 1) * K + 1 := by rw [Nat.add_mul, Nat.one_mul, add_comm K]
    _ = _ := by rw [ht']

theorem callCount_bound (opt : Minimum data ψ) (p : RestartParams E) (h0 : p.x0 ∈ ψ.dom)
    {μF : ℝ} (hF : 0 < μF) (hq : LocalGrowth opt p.x0 μF)
    (hterm : ∃ s, stageSuccess data ψ p s) :
    let S := goodStage p.μ0 μF
    let U := earlyRounds (gap opt p.x0) μF p.ε
    let V := goodRounds (gap opt p.x0) p.ε
    callCount p hterm ≤ 1 + (∑ s ∈ Finset.range S, (U * period (estimate p.μ0 s) + 1))
      + (V * period (estimate p.μ0 S) + 1) := by
  let S := goodStage p.μ0 μF
  let U := earlyRounds (gap opt p.x0) μF p.ε
  let V := goodRounds (gap opt p.x0) p.ε
  let B := fun s => stageBlocks data ψ p s * period (estimate p.μ0 s) + 1
  let L := fun s => U * period (estimate p.μ0 s) + 1
  let stop := firstStage p hterm
  have hle : stop ≤ S := (result_spec opt p h0 hF hq hterm).1
  have hB (s : ℕ) (hs : s < S) : B s ≤ L s :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (early_blocks_bound opt p h0 hF s hs)) 1
  have hsum (n : ℕ) (hn : n ≤ S) : (∑ s ∈ Finset.range n, B s) ≤ ∑ s ∈ Finset.range S, L s := by
    calc
      _ ≤ ∑ s ∈ Finset.range n, L s :=
        Finset.sum_le_sum (fun s hs => hB s ((Finset.mem_range.mp hs).trans_le hn))
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun _ _ _ => Nat.zero_le _)
  change 1 + (∑ s ∈ Finset.range (stop + 1), B s) ≤
    1 + (∑ s ∈ Finset.range S, L s) + (V * period (estimate p.μ0 S) + 1)
  rcases lt_or_eq_of_le hle with hlt | heq
  · have H := hsum (stop + 1) (by omega)
    omega
  · rw [heq, Finset.sum_range_succ]
    have H := hsum S le_rfl
    have hgood := (goodStage_iff p.μ0_pos hF S).1 le_rfl
    have htail : B S ≤ V * period (estimate p.μ0 S) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (good_blocks_bound opt p h0 hF hq S hgood)) 1
    omega

theorem estimate_le_initial {μ0 : ℝ} (hμ0 : 0 < μ0) (s : ℕ) : estimate μ0 s ≤ μ0 :=
  div_le_self hμ0.le (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num))

theorem period_original {μ : ℝ} (hμ : 0 < μ) (hu : μ < 4 * Real.exp 1) :
    period μ = ⌈2 * Real.sqrt (Real.exp 1 / μ) - 1⌉₊ ∧
      (period μ : ℝ) ≤ 2 * Real.sqrt (Real.exp 1 / μ) ∧
      period μ + 1 = ⌈2 * Real.sqrt (Real.exp 1 / μ)⌉₊ := by
  let a := 2 * Real.sqrt (Real.exp 1 / μ) - 1
  have hs : (1 / 2 : ℝ) < Real.sqrt (Real.exp 1 / μ) := by
    apply Real.lt_sqrt_of_sq_lt
    apply (lt_div_iff₀ hμ).2
    linarith only [hu]
  have ha : 0 < a := by dsimp [a]; linarith only [hs]
  have hceil : 1 ≤ ⌈a⌉₊ := Nat.lt_ceil.2 (by simpa only [Nat.cast_zero] using ha)
  have hK : period μ = ⌈a⌉₊ := max_eq_right hceil
  have he : a + 1 = 2 * Real.sqrt (Real.exp 1 / μ) := by dsimp [a]; ring
  refine ⟨hK, ?_, ?_⟩
  · rw [hK, ← he]
    exact (Nat.ceil_lt_add_one ha.le).le
  · rw [hK, ← he, Nat.ceil_add_one ha.le]

theorem expRounds_original {A ε : ℝ} (hA : 0 < A)
    (hr : 1 ≤ ⌈Real.log (A / ε)⌉₊) : expRounds A ε = ⌈Real.log (A / ε)⌉₊ := by
  simp only [expRounds, if_neg hA.ne', max_eq_right hr]

theorem goodStage_zero {μ0 μF : ℝ} (hμ0 : 0 < μ0) (hF : 0 < μF) (hle : μ0 ≤ μF) :
    goodStage μ0 μF = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (goodStage_iff hμ0 hF 0).2
  simpa [estimate] using hle

theorem estimate_at_goodStage_lower {μ0 μF : ℝ} (hμ0 : 0 < μ0) (hF : 0 < μF) (hgt : μF < μ0) :
    μF / 2 < estimate μ0 (goodStage μ0 μF) := by
  let S := goodStage μ0 μF
  have hp : 0 < S := by
    by_contra! hz
    have h := (goodStage_iff hμ0 hF 0).1 hz
    simp only [estimate, pow_zero, div_one] at h
    exact (not_le_of_gt hgt) h
  have hs : S - 1 < S := by omega
  have hbefore : μF < estimate μ0 (S - 1) :=
    lt_of_not_ge (fun h => (not_le_of_gt hs) ((goodStage_iff hμ0 hF _).2 h))
  have he : S - 1 + 1 = S := by omega
  have hnext : estimate μ0 S = estimate μ0 (S - 1) / 2 := by
    unfold estimate
    rw [div_div, ← pow_succ, he]
  rw [hnext]
  exact div_lt_div_of_pos_right hbefore (by norm_num)

theorem sqrt_two_pow (s : ℕ) : Real.sqrt ((2 : ℝ)^s) = (Real.sqrt (2 : ℝ))^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _), ih, pow_succ]

theorem sqrt_estimate {μ0 : ℝ} (hμ0 : 0 < μ0) (s : ℕ) :
    Real.sqrt (Real.exp 1 / estimate μ0 s) =
      Real.sqrt (Real.exp 1 / μ0) * (Real.sqrt (2 : ℝ))^s := by
  have he : Real.exp 1 / estimate μ0 s = (Real.exp 1 / μ0) * (2 : ℝ)^s := by
    unfold estimate
    rw [div_div_eq_mul_div, div_mul_eq_mul_div]
  rw [he, Real.sqrt_mul (div_nonneg (Real.exp_nonneg _) hμ0.le), sqrt_two_pow]

theorem sum_period_bound {μ0 μF : ℝ} (hμ0 : 0 < μ0) (hF : 0 < μF)
    (hgt : μF < μ0) (hraw : μ0 < 4 * Real.exp 1) :
    let S := goodStage μ0 μF
    (∑ s ∈ Finset.range S, (period (estimate μ0 s) : ℝ)) ≤
      2 * Real.sqrt (Real.exp 1) / (Real.sqrt 2 - 1) *
        (Real.sqrt (2 / μF) - Real.sqrt (1 / μ0)) := by
  let S := goodStage μ0 μF
  let a := Real.sqrt (Real.exp 1 / μ0)
  let q := Real.sqrt (2 : ℝ)
  have hq : 1 < q := Real.lt_sqrt_of_sq_lt (by norm_num)
  have hden : 0 < q - 1 := sub_pos.mpr hq
  have hμS := estimate_at_goodStage_lower hμ0 hF hgt
  have hsmall : Real.sqrt (Real.exp 1 / estimate μ0 S) ≤ Real.sqrt (2 * Real.exp 1 / μF) := by
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ Real.exp 1 / (μF / 2) :=
        div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity) hμS.le
      _ = _ := by field_simp [hF.ne'] <;> ring
  have he₁ : Real.sqrt (2 * Real.exp 1 / μF) = Real.sqrt (Real.exp 1) * Real.sqrt (2 / μF) := by
    rw [show 2 * Real.exp 1 / μF = Real.exp 1 * (2 / μF) from by ring,
      Real.sqrt_mul (Real.exp_nonneg _)]
  have he₂ : a = Real.sqrt (Real.exp 1) * Real.sqrt (1 / μ0) := by
    dsimp [a]
    rw [show Real.exp 1 / μ0 = Real.exp 1 * (1 / μ0) from by ring,
      Real.sqrt_mul (Real.exp_nonneg _)]
  change (∑ s ∈ Finset.range S, (period (estimate μ0 s) : ℝ)) ≤
      2 * Real.sqrt (Real.exp 1) / (q - 1) * (Real.sqrt (2 / μF) - Real.sqrt (1 / μ0))
  calc
    _ ≤ ∑ s ∈ Finset.range S, (2 * a) * q^s := by
      apply Finset.sum_le_sum
      intro s hs
      have hb := (period_original (estimate_pos hμ0 s) ((estimate_le_initial hμ0 s).trans_lt hraw)).2.1
      rw [sqrt_estimate hμ0 s] at hb
      simpa only [a, q, mul_assoc] using hb
    _ = (2 * a) * ((q^S - 1) / (q - 1)) := by rw [← Finset.mul_sum, geom_sum_eq hq.ne' S]
    _ = 2 * (Real.sqrt (Real.exp 1 / estimate μ0 S) - a) / (q - 1) := by
      rw [sqrt_estimate hμ0 S]
      dsimp [a, q]
      ring
    _ ≤ 2 * (Real.sqrt (2 * Real.exp 1 / μF) - a) / (q - 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hsmall _) (by norm_num)) hden.le
    _ = _ := by rw [he₁, he₂]; ring

end
end AdaRES
