import PDAL.Definitions

/-!
# Algorithm 2 的递归构造与局部规格

状态编号 n 存放 x_n、y_{n+1}、τ_n、β_n、θ_n。初始 y₁ 无需在有效域。
本轮只核查递归构造与接受规格，不涉及能量、平均或最终速率。
-/

open scoped InnerProduct

namespace APDAL

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

structure State (X Y : Type*) where
  x : X
  y : Y
  tau : ℝ
  beta : ℝ
  theta : ℝ
  trial : ℝ
  index : ℕ
  tau_pos : 0 < tau
  beta_pos : 0 < beta
  theta_nonneg : 0 ≤ theta

def betaNext (gamma : ℝ) (s : State X Y) : ℝ :=
  s.beta * (1 + gamma * s.tau)

lemma betaNext_pos {gamma : ℝ} (hg : 0 < gamma) (s : State X Y) :
    0 < betaNext gamma s := by
  have ht := s.tau_pos
  have hb := s.beta_pos
  unfold betaNext
  positivity

noncomputable def trialLower (gamma : ℝ) (s : State X Y) : ℝ :=
  s.tau * Real.sqrt (s.beta / betaNext gamma s)

lemma trialLower_pos {gamma : ℝ} (hg : 0 < gamma) (s : State X Y) :
    0 < trialLower gamma s :=
  mul_pos s.tau_pos (Real.sqrt_pos.mpr (div_pos s.beta_pos (betaNext_pos hg s)))

structure Params (X Y : Type*) where
  x0 : X
  y1 : Y
  tau0 : ℝ
  beta0 : ℝ
  mu : ℝ
  gamma : ℝ
  tau0_pos : 0 < tau0
  beta0_pos : 0 < beta0
  mu_range : 0 < mu ∧ mu < 1
  gamma_pos : 0 < gamma
  selectTrial : ℕ → State X Y → X → ℝ
  trial_range : ∀ j s x,
    trialLower gamma s ≤ selectTrial j s x ∧
      selectTrial j s x ≤ trialLower gamma s * Real.sqrt (1 + s.theta)

def initial (p : Params X Y) : State X Y where
  x := p.x0
  y := p.y1
  tau := p.tau0
  beta := p.beta0
  theta := 1
  trial := p.tau0
  index := 0
  tau_pos := p.tau0_pos
  beta_pos := p.beta0_pos
  theta_nonneg := zero_le_one

noncomputable def primalNext (K : X →L[ℝ] Y) (g : ProperConvex X)
    (s : State X Y) : X :=
  prox g s.tau s.tau_pos (s.x - s.tau • (K†) s.y)

noncomputable def trial (K : X →L[ℝ] Y) (g : ProperConvex X)
    (p : Params X Y) (j : ℕ) (s : State X Y) : ℝ :=
  p.selectTrial j s (primalNext K g s)

lemma trial_pos (K : X →L[ℝ] Y) (g : ProperConvex X)
    (p : Params X Y) (j : ℕ) (s : State X Y) : 0 < trial K g p j s :=
  (trialLower_pos p.gamma_pos s).trans_le (p.trial_range j s _).1

noncomputable def candidateTau (K : X →L[ℝ] Y) (g : ProperConvex X)
    (p : Params X Y) (j : ℕ) (s : State X Y) (i : ℕ) : ℝ :=
  trial K g p j s * p.mu ^ i

lemma candidateTau_pos (K : X →L[ℝ] Y) (g : ProperConvex X)
    (p : Params X Y) (j : ℕ) (s : State X Y) (i : ℕ) :
    0 < candidateTau K g p j s i :=
  mul_pos (trial_pos K g p j s) (pow_pos p.mu_range.1 i)

noncomputable def candidateY (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y) (i : ℕ) : Y :=
  let t := candidateTau K g p j s i
  let beta := betaNext p.gamma s
  let x := primalNext K g s
  prox h (beta * t) (mul_pos (betaNext_pos p.gamma_pos s) (candidateTau_pos K g p j s i))
    (s.y + (beta * t) • K (x + (t / s.tau) • (x - s.x)))

noncomputable def acceptedIndex (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y) : ℕ :=
  min_accept_index K g h (primalNext K g s) s.x s.y s.tau (trial K g p j s)
    (betaNext p.gamma s) 1 p.mu s.tau_pos (trial_pos K g p j s)
    (betaNext_pos p.gamma_pos s) zero_lt_one p.mu_range

noncomputable def next (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y) : State X Y :=
  let i := acceptedIndex K g h p j s
  let t := candidateTau K g p j s i
  let ht := candidateTau_pos K g p j s i
  { x := primalNext K g s
    y := candidateY K g h p j s i
    tau := t
    beta := betaNext p.gamma s
    theta := t / s.tau
    trial := trial K g p j s
    index := i
    tau_pos := ht
    beta_pos := betaNext_pos p.gamma_pos s
    theta_nonneg := div_nonneg ht.le s.tau_pos.le }

theorem next_accept (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y) :
    let t := next K g h p j s
    accept_cond K t.beta 1 t.tau s.y t.y := by
  exact (min_accept_index_accept K g h (primalNext K g s) s.x s.y s.tau
    (trial K g p j s) (betaNext p.gamma s) 1 p.mu s.tau_pos
    (trial_pos K g p j s) (betaNext_pos p.gamma_pos s) zero_lt_one p.mu_range).2

theorem next_minimal (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y)
    (i : ℕ) (hi : i < (next K g h p j s).index) :
    ¬accept_cond K (betaNext p.gamma s) 1 (candidateTau K g p j s i)
      s.y (candidateY K g h p j s i) := by
  intro ha
  exact min_accept_index_minimal K g h (primalNext K g s) s.x s.y s.tau
    (trial K g p j s) (betaNext p.gamma s) 1 p.mu s.tau_pos
    (trial_pos K g p j s) (betaNext_pos p.gamma_pos s) zero_lt_one p.mu_range i hi
      ⟨candidateTau_pos K g p j s i, ha⟩

noncomputable def states (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) : ℕ → State X Y :=
  Nat.rec (initial p) (fun n s => next K g h p (n + 1) s)

@[simp] theorem states_zero (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) : states K g h p 0 = initial p := rfl

theorem states_succ (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (n : ℕ) :
    states K g h p (n + 1) = next K g h p (n + 1) (states K g h p n) := rfl

theorem next_primal (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y) :
    prox_scale g s.tau (s.x - s.tau • (K†) s.y) (next K g h p j s).x :=
  prox_spec g s.tau s.tau_pos _

theorem next_dual (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y) :
    let t := next K g h p j s
    prox_scale h (t.beta * t.tau) (s.y + (t.beta * t.tau) • K
      (t.x + t.theta • (t.x - s.x))) t.y :=
  prox_spec h _ (mul_pos (next K g h p j s).beta_pos (next K g h p j s).tau_pos) _

/-- K = 0 时每个候选都接受：接受条件左端为零。 -/
theorem accept_cond_of_K_zero (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y)
    (hK : K = 0) (i : ℕ) :
    accept_cond K (betaNext p.gamma s) 1 (candidateTau K g p j s i)
      s.y (candidateY K g h p j s i) := by
  subst hK
  simp only [accept_cond]
  have hnorm : ∀ v : Y, ‖((0 : X →L[ℝ] Y)†) v‖ = 0 := by
    intro v
    simp
  rw [hnorm _, mul_zero]
  exact mul_nonneg zero_le_one (norm_nonneg _)

/-- 候选对偶增量为零时该候选接受：此时接受条件右端为零。 -/
theorem accept_cond_of_zero_dual (K : X →L[ℝ] Y) (g : ProperConvex X)
    (h : ProperConvex Y) (p : Params X Y) (j : ℕ) (s : State X Y) (i : ℕ)
    (hz : (candidateY K g h p j s i) - s.y = 0) :
    accept_cond K (betaNext p.gamma s) 1 (candidateTau K g p j s i)
      s.y (candidateY K g h p j s i) := by
  simp only [accept_cond]
  rw [hz]
  simp

end APDAL
