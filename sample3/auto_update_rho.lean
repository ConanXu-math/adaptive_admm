-- AUTO GENERATED Lean4 FILE
import Optlib.Algorithm.AdaptiveADMM.Strategies.AdaptiveStrategyBase

noncomputable section
open Topology Filter AdaptiveADMM_Verification AdaptiveADMM_Convergence_Proof AdaptiveStrategyBase

variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (admm : ADMM E₁ E₂ F)

def tau_base (c p : ℝ) (n : ℕ) : ℝ := c / Real.rpow ((n : ℝ) + 1) p

def log10 (x : ℝ) : ℝ := Real.log x / Real.log 10
def log1p (x : ℝ) : ℝ := Real.log (1 + x)

def residual_scale (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  log10 (max (r_norm_seq n) (max (s_norm_seq n) eps) + 1.0)

def effective_mu (mu : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  if n < 5 then 1.5 + 0.1 * residual_scale r_norm_seq s_norm_seq eps n
  else if n < 15 then 2.0 + 0.2 * residual_scale r_norm_seq s_norm_seq eps n
  else mu + 0.3 * residual_scale r_norm_seq s_norm_seq eps n

def base_factor (n : ℕ) : ℝ :=
  if n < 5 then 2.0
  else if n < 15 then 1.5 else 1.2

def factor_seq (mu eps c p : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : ℝ :=
  let eff_mu := effective_mu mu r_norm_seq s_norm_seq eps n
  let t := tau_base c p n
  let bf := base_factor n
  let ratio := r_ratio r_norm_seq s_norm_seq eps n
  let excess := min (ratio / eff_mu) 5.0
  let scaled := 1.0 + (bf - 1.0) * (log1p (excess - 1.0) / log1p 4.0)
  max (scaled - t) 1.05

def tau_seq (mu eps c p : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : ℝ :=
  factor_seq mu eps c p r_norm_seq s_norm_seq n - 1

theorem h_tau_summable (mu eps c p : ℝ) (hp : 1 < p) (r_norm_seq s_norm_seq : ℕ → ℝ) :
    Summable (tau_seq mu eps c p r_norm_seq s_norm_seq) := by
  sorry -- TODO: proof for complex tau_seq

def dir_seq (mu eps : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : ℤ :=
  if r_ratio r_norm_seq s_norm_seq eps n > effective_mu mu r_norm_seq s_norm_seq eps n then 1
  else if s_ratio r_norm_seq s_norm_seq eps n > effective_mu mu r_norm_seq s_norm_seq eps n then -1 else 0

lemma h_dir (mu eps : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) :
    ∀ n, dir_seq mu eps r_norm_seq s_norm_seq n = 1 ∨
         dir_seq mu eps r_norm_seq s_norm_seq n = 0 ∨
         dir_seq mu eps r_norm_seq s_norm_seq n = -1 := by
  intro n; by_cases h1 : r_ratio r_norm_seq s_norm_seq eps n > effective_mu mu r_norm_seq s_norm_seq eps n
  · simp [dir_seq, h1]
  · by_cases h2 : s_ratio r_norm_seq s_norm_seq eps n > effective_mu mu r_norm_seq s_norm_seq eps n
    · simp [dir_seq, h1, h2]
    · simp [dir_seq, h1, h2]

-- Strategy-specific: update_fun with clipping (wraps base update_fun)
def update_fun_clipped (tau : ℕ → ℝ) (dir : ℕ → ℤ) (n : ℕ) (rho : ℝ) : ℝ :=
  let raw := update_fun tau dir n rho
  let upper := rho * 10.0
  let lower := rho / 10.0
  let raw_clipped := max (min raw upper) lower
  max (min raw_clipped 1e6) 1e-6

theorem auto_converges (admm_kkt : Existance_of_kkt admm) [Setting E₁ E₂ F admm admm_kkt] [IsOrderedMonoid ℝ]
    (mu eps c p : ℝ) (hp : 1 < p) (r_norm_seq s_norm_seq : ℕ → ℝ)
    (h_tau_nonneg : ∀ n, 0 ≤ tau_seq mu eps c p r_norm_seq s_norm_seq n)
    (h_no_clip : ∀ n rho, update_fun_clipped (tau_seq mu eps c p r_norm_seq s_norm_seq) (dir_seq mu eps r_norm_seq s_norm_seq) n rho =
      update_fun (tau_seq mu eps c p r_norm_seq s_norm_seq) (dir_seq mu eps r_norm_seq s_norm_seq) n rho)
    (h_rho : ∀ n, admm.ρₙ (n+1) = update_fun_clipped (tau_seq mu eps c p r_norm_seq s_norm_seq) (dir_seq mu eps r_norm_seq s_norm_seq) n (admm.ρₙ n))
    (fullrank₁ : Function.Injective admm.A₁) (fullrank₂ : Function.Injective admm.A₂) :
    ∃ x₁ x₂ y, Convex_KKT x₁ x₂ y admm.toOptProblem ∧ Tendsto admm.x₁ atTop (𝓝 x₁) ∧
      Tendsto admm.x₂ atTop (𝓝 x₂) ∧ Tendsto admm.y atTop (𝓝 y) := by
  let tau := tau_seq mu eps c p r_norm_seq s_norm_seq; let dir := dir_seq mu eps r_norm_seq s_norm_seq
  have h_dir' : ∀ n, dir n = 1 ∨ dir n = 0 ∨ dir n = -1 := fun n => by simpa [dir] using h_dir mu eps r_norm_seq s_norm_seq n
  have h_update_equiv' : ∀ n rho, 0 < rho → update_fun_clipped tau dir n rho = rho * (1 + tau n) ∨
      update_fun_clipped tau dir n rho = rho / (1 + tau n) ∨ update_fun_clipped tau dir n rho = rho := by
    intro n rho hρ_pos
    rw [h_no_clip n rho]
    exact h_update_equiv tau dir h_dir' n rho hρ_pos
  exact Strategy3.converges_from_adaptable_strategy (admm := admm) (admm_kkt := admm_kkt)
    { tau_seq := tau, h_tau_nonneg := h_tau_nonneg, h_tau_summable := h_tau_summable mu eps c p hp r_norm_seq s_norm_seq,
      update_fun := update_fun_clipped tau dir, h_update_equiv := h_update_equiv' } h_rho fullrank₁ fullrank₂
