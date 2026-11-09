import AdaRES.ErrorBounds
import AdaRES.Threshold

namespace AdaRES

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure RestartParams (E : Type*) where
  x0 : E
  μ0 : ℝ
  ε : ℝ
  μ0_pos : 0 < μ0
  ε_pos : 0 < ε

def phasePoint (data : Smooth E) (ψ : ProperConvex E) (prev : E) (μ : ℝ) : ℕ → E :=
  Nat.rec (step data ψ prev) (fun _ x => fista data ψ x (period μ))

def phaseConstant (data : Smooth E) (ψ : ProperConvex E) (prev : E) (μ : ℝ) : ℝ :=
  16 * residual data ψ prev / μ

def blockStop (data : Smooth E) (ψ : ProperConvex E) (prev : E) (μ ε : ℝ) (t : ℕ) : Prop :=
  phaseConstant data ψ prev μ * (phaseFactor μ)^t < residual data ψ (phasePoint data ψ prev μ t)
    ∨ residual data ψ (phasePoint data ψ prev μ t) ≤ ε

theorem phaseConstant_nonneg (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    {μ : ℝ} (hμ : 0 < μ) : 0 ≤ phaseConstant data ψ prev μ := by
  unfold phaseConstant residual
  positivity

theorem blockStop_of_threshold_le (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    {μ ε : ℝ} (hμ : 0 < μ) {t : ℕ}
    (ht : phaseConstant data ψ prev μ * Real.exp (-(t : ℝ)) ≤ ε) :
    blockStop data ψ prev μ ε t := by
  unfold blockStop
  by_cases hr : residual data ψ (phasePoint data ψ prev μ t) ≤ ε
  · exact Or.inr hr
  · have hc := mul_le_mul_of_nonneg_left (phaseFactor_pow_le hμ t)
      (phaseConstant_nonneg data ψ prev hμ)
    exact Or.inl (lt_of_le_of_lt (hc.trans ht) (lt_of_not_ge hr))

theorem blockStop_exists (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) :
    ∃ t : ℕ, blockStop data ψ prev μ ε (t + 1) := by
  let C := phaseConstant data ψ prev μ
  let T := expRounds C ε
  have hp : 0 < T := expRounds_pos C ε
  have he : T - 1 + 1 = T := by omega
  refine ⟨T - 1, ?_⟩
  rw [he]
  exact blockStop_of_threshold_le data ψ prev hμ
    (expRounds_bound (phaseConstant_nonneg data ψ prev hμ) hε)

def firstBlocks (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) : ℕ := by
  classical
  exact Nat.find (blockStop_exists data ψ prev hμ hε) + 1

theorem firstBlocks_pos (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) : 0 < firstBlocks data ψ prev hμ hε := by
  unfold firstBlocks
  exact Nat.succ_pos _

theorem firstBlocks_spec (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) :
    blockStop data ψ prev μ ε (firstBlocks data ψ prev hμ hε) := by
  classical
  exact Nat.find_spec (blockStop_exists data ψ prev hμ hε)

theorem firstBlocks_minimal (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) {t : ℕ}
    (ht : 0 < t) (hlt : t < firstBlocks data ψ prev hμ hε) : ¬ blockStop data ψ prev μ ε t := by
  classical
  cases t with
  | zero => omega
  | succ t =>
    apply Nat.find_min (blockStop_exists data ψ prev hμ hε)
    exact Nat.lt_of_succ_lt_succ hlt

theorem firstBlocks_le (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) {t : ℕ}
    (ht : 0 < t) (hstop : blockStop data ψ prev μ ε t) : firstBlocks data ψ prev hμ hε ≤ t := by
  by_contra! hlt
  exact (firstBlocks_minimal data ψ prev hμ hε ht hlt) hstop

theorem phase_invariant (data : Smooth E) (ψ : ProperConvex E) (prev : E)
    (hp : prev ∈ ψ.dom) (μ : ℝ) (t : ℕ) :
    phasePoint data ψ prev μ t ∈ ψ.dom ∧
      objective data ψ (phasePoint data ψ prev μ t) ≤ objective data ψ prev := by
  induction t with
  | zero =>
    have h := step_descent data ψ prev hp
    have hn : 0 ≤ ‖step data ψ prev - prev‖^2 / 2 := by positivity
    exact ⟨step_dom data ψ prev, (le_add_of_nonneg_right hn).trans h⟩
  | succ t ih =>
    let x := phasePoint data ψ prev μ t
    change fista data ψ x (period μ) ∈ ψ.dom ∧
      objective data ψ (fista data ψ x (period μ)) ≤ objective data ψ prev
    exact ⟨fista_x_dom data ψ x ih.1 _, (fista_descent data ψ x ih.1 _).trans ih.2⟩

def previous (data : Smooth E) (ψ : ProperConvex E) (p : RestartParams E) : ℕ → E
  | 0 => p.x0
  | s + 1 =>
    let prev := previous data ψ p s
    let μ := estimate p.μ0 s
    let t := firstBlocks data ψ prev (estimate_pos p.μ0_pos s) p.ε_pos
    phasePoint data ψ prev μ t

def stageBlocks (data : Smooth E) (ψ : ProperConvex E) (p : RestartParams E) (s : ℕ) : ℕ :=
  firstBlocks data ψ (previous data ψ p s) (estimate_pos p.μ0_pos s) p.ε_pos

def stageSuccess (data : Smooth E) (ψ : ProperConvex E) (p : RestartParams E) (s : ℕ) : Prop :=
  residual data ψ (previous data ψ p (s + 1)) ≤ p.ε

theorem previous_invariant (data : Smooth E) (ψ : ProperConvex E) (p : RestartParams E)
    (h0 : p.x0 ∈ ψ.dom) (s : ℕ) :
    previous data ψ p s ∈ ψ.dom ∧ objective data ψ (previous data ψ p s) ≤ objective data ψ p.x0 := by
  induction s with
  | zero => exact ⟨h0, le_rfl⟩
  | succ s ih =>
    let prev := previous data ψ p s
    have H := phase_invariant data ψ prev ih.1 (estimate p.μ0 s) (stageBlocks data ψ p s)
    exact ⟨H.1, H.2.trans ih.2⟩

end
end AdaRES
