import AdaRES.Stages

open scoped BigOperators

namespace AdaRES

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {data : Smooth E} {ψ : ProperConvex E}

theorem phase_gap_decay (opt : Minimum data ψ) (x0 : E) {μF μ : ℝ}
    (hF : 0 < μF) (hq : LocalGrowth opt x0 μF) (hμ : 0 < μ) (hle : μ ≤ μF)
    (prev : E) (hp : prev ∈ ψ.dom) (hl : objective data ψ prev ≤ objective data ψ x0)
    (t : ℕ) : gap opt (phasePoint data ψ prev μ t) ≤ (phaseFactor μ)^t * gap opt (step data ψ prev) := by
  induction t with
  | zero => simp [phasePoint]
  | succ t ih =>
    let x := phasePoint data ψ prev μ t
    have hx := phase_invariant data ψ prev hp μ t
    have hK : period μ - 1 + 1 = period μ := by have := period_pos μ; omega
    have hf := fista_gap_bound opt x0 hF hq x hx.1 (hx.2.trans hl) (period μ - 1)
    rw [hK] at hf
    have hqle : (theta (period μ - 1))^2 / μF ≤ phaseFactor μ :=
      div_le_div_of_nonneg_left (sq_nonneg _) hμ hle
    change gap opt (fista data ψ x (period μ)) ≤ (phaseFactor μ)^(t + 1) * gap opt (step data ψ prev)
    calc
      _ ≤ phaseFactor μ * gap opt x := hf.trans (mul_le_mul_of_nonneg_right hqle (gap_nonneg opt x hx.1))
      _ ≤ phaseFactor μ * ((phaseFactor μ)^t * gap opt (step data ψ prev)) :=
        mul_le_mul_of_nonneg_left ih (phaseFactor_nonneg hμ)
      _ = _ := by rw [pow_succ]; ring

theorem good_threshold (opt : Minimum data ψ) (x0 : E) {μF μ : ℝ}
    (hF : 0 < μF) (hq : LocalGrowth opt x0 μF) (hμ : 0 < μ) (hle : μ ≤ μF)
    (prev : E) (hp : prev ∈ ψ.dom) (hl : objective data ψ prev ≤ objective data ψ x0)
    (t : ℕ) : residual data ψ (phasePoint data ψ prev μ t) ≤
      phaseConstant data ψ prev μ * (phaseFactor μ)^t := by
  have hx := (phase_invariant data ψ prev hp μ t).1
  have hR := residual_le_gap opt _ hx
  have hd := phase_gap_decay opt x0 hF hq hμ hle prev hp hl t
  have h0 := gap_step_le_residual opt x0 hF hq prev hp hl
  have hRn : 0 ≤ residual data ψ prev := by unfold residual; positivity
  have h0' : gap opt (step data ψ prev) ≤ 8 * residual data ψ prev / μ :=
    h0.trans (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hRn) hμ hle)
  calc
    _ ≤ 2 * gap opt (phasePoint data ψ prev μ t) := hR
    _ ≤ 2 * ((phaseFactor μ)^t * gap opt (step data ψ prev)) :=
      mul_le_mul_of_nonneg_left hd (by norm_num)
    _ ≤ 2 * ((phaseFactor μ)^t * (8 * residual data ψ prev / μ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h0' (pow_nonneg (phaseFactor_nonneg hμ) _))
        (by norm_num)
    _ = _ := by unfold phaseConstant; ring

theorem good_residual_bound (opt : Minimum data ψ) (x0 : E) {μF μ : ℝ}
    (hF : 0 < μF) (hq : LocalGrowth opt x0 μF) (hμ : 0 < μ) (hle : μ ≤ μF)
    (prev : E) (hp : prev ∈ ψ.dom) (hl : objective data ψ prev ≤ objective data ψ x0)
    (t : ℕ) : residual data ψ (phasePoint data ψ prev μ t) ≤
      (2 * gap opt x0) * Real.exp (-(t : ℝ)) := by
  have hx := (phase_invariant data ψ prev hp μ t).1
  have hR := residual_le_gap opt _ hx
  have hd := phase_gap_decay opt x0 hF hq hμ hle prev hp hl t
  have h0 := (phase_invariant data ψ prev hp μ 0).2.trans hl
  have h0' : gap opt (step data ψ prev) ≤ gap opt x0 := by
    change objective data ψ (step data ψ prev) ≤ objective data ψ x0 at h0
    exact sub_le_sub_right h0 _
  have he := mul_le_mul (phaseFactor_pow_le hμ t) h0'
    (gap_nonneg opt _ (step_dom data ψ prev)) (Real.exp_nonneg _)
  calc
    _ ≤ 2 * gap opt (phasePoint data ψ prev μ t) := hR
    _ ≤ 2 * ((phaseFactor μ)^t * gap opt (step data ψ prev)) :=
      mul_le_mul_of_nonneg_left hd (by norm_num)
    _ ≤ 2 * (Real.exp (-(t : ℝ)) * gap opt x0) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

theorem good_stage_succeeds (opt : Minimum data ψ) (p : RestartParams E)
    (h0 : p.x0 ∈ ψ.dom) {μF : ℝ} (hF : 0 < μF) (hq : LocalGrowth opt p.x0 μF)
    (s : ℕ) (hs : estimate p.μ0 s ≤ μF) : stageSuccess data ψ p s := by
  let prev := previous data ψ p s
  let μ := estimate p.μ0 s
  let t := stageBlocks data ψ p s
  have hm := estimate_pos p.μ0_pos s
  have hprev := previous_invariant data ψ p h0 s
  have hbound := good_threshold opt p.x0 hF hq hm hs prev hprev.1 hprev.2 t
  have hstop : blockStop data ψ prev μ p.ε t := firstBlocks_spec data ψ prev hm p.ε_pos
  change residual data ψ (phasePoint data ψ prev μ t) ≤ p.ε
  rcases hstop with h | h
  · exact False.elim ((not_lt_of_ge hbound) h)
  · exact h

theorem stage_exists (opt : Minimum data ψ) (p : RestartParams E)
    (h0 : p.x0 ∈ ψ.dom) {μF : ℝ} (hF : 0 < μF) (hq : LocalGrowth opt p.x0 μF) :
    ∃ s, stageSuccess data ψ p s := by
  let S := goodStage p.μ0 μF
  exact ⟨S, good_stage_succeeds opt p h0 hF hq S ((goodStage_iff p.μ0_pos hF S).1 le_rfl)⟩

def firstStage (p : RestartParams E) (hterm : ∃ s, stageSuccess data ψ p s) : ℕ := by
  classical
  exact Nat.find hterm

def resultPoint (p : RestartParams E) (hterm : ∃ s, stageSuccess data ψ p s) : E :=
  step data ψ (previous data ψ p (firstStage p hterm + 1))

def callCount (p : RestartParams E) (hterm : ∃ s, stageSuccess data ψ p s) : ℕ :=
  1 + ∑ s ∈ Finset.range (firstStage p hterm + 1),
    (stageBlocks data ψ p s * period (estimate p.μ0 s) + 1)

theorem result_spec (opt : Minimum data ψ) (p : RestartParams E) (h0 : p.x0 ∈ ψ.dom)
    {μF : ℝ} (hF : 0 < μF) (hq : LocalGrowth opt p.x0 μF)
    (hterm : ∃ s, stageSuccess data ψ p s) :
    let s := firstStage p hterm
    let x := resultPoint p hterm
    s ≤ goodStage p.μ0 μF ∧
    (∀ j < s, ¬stageSuccess data ψ p j) ∧
    stageSuccess data ψ p s ∧ x ∈ ψ.dom ∧ residual data ψ x ≤ p.ε ∧ gap opt x ≤ 8 * p.ε / μF := by
  classical
  let s := firstStage p hterm
  let prev := previous data ψ p (s + 1)
  let x := step data ψ prev
  let S := goodStage p.μ0 μF
  have hS := good_stage_succeeds opt p h0 hF hq S ((goodStage_iff p.μ0_pos hF S).1 le_rfl)
  have hs : s ≤ S := Nat.find_min' hterm hS
  have hsuccess : stageSuccess data ψ p s := Nat.find_spec hterm
  have hr : residual data ψ prev ≤ p.ε := hsuccess
  have hnexp := step_nonexpansive data ψ (step data ψ prev) prev
  have hxR : residual data ψ x ≤ residual data ψ prev :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnexp
  have hp := previous_invariant data ψ p h0 (s + 1)
  have hgap := gap_step_le_residual opt p.x0 hF hq prev hp.1 hp.2
  refine ⟨hs, fun j hj => Nat.find_min hterm hj, hsuccess, step_dom data ψ prev, hxR.trans hr, ?_⟩
  exact hgap.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by norm_num)) hF.le)

end
end AdaRES
