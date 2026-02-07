-- AUTO GENERATED Lean4 FILE
import Optlib.Algorithm.AdaptiveADMM.Strategies.Adaptive_Strategy_Convergence
import Optlib.Algorithm.AdaptiveADMM.Strategies.VerificationLib

noncomputable section

open Topology Filter
open AdaptiveADMM_Convergence_Proof
open AdaptiveADMM_Verification

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

variable (admm : ADMM E₁ E₂ F)

def tau_seq (c p : ℝ) (n : ℕ) : ℝ := c / Real.rpow ((n : ℝ) + 1) p

theorem h_tau_summable (c p : ℝ) (hp : 1 < p) : Summable (tau_seq c p) := by
  simpa [tau_seq] using p_series_summable_template c p hp

def dir_seq (mu eps : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : ℤ :=
  if r_norm_seq n > mu * max (s_norm_seq n) eps then 1
  else if s_norm_seq n > mu * max (r_norm_seq n) eps then -1 else 0

lemma h_dir (mu eps : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) :
    ∀ n, dir_seq mu eps r_norm_seq s_norm_seq n = 1 ∨
         dir_seq mu eps r_norm_seq s_norm_seq n = 0 ∨
         dir_seq mu eps r_norm_seq s_norm_seq n = -1 := by
  intro n
  by_cases h1 : r_norm_seq n > mu * max (s_norm_seq n) eps
  · simp [dir_seq, h1]
  · by_cases h2 : s_norm_seq n > mu * max (r_norm_seq n) eps
    · simp [dir_seq, h1, h2]
    · simp [dir_seq, h1, h2]

def update_fun (tau : ℕ → ℝ) (dir : ℕ → ℤ) (n : ℕ) (rho : ℝ) : ℝ :=
  if dir n = (-1 : ℤ) then
    rho / (1 + tau n)
  else if dir n = (1 : ℤ) then
    rho * (1 + tau n)
  else
    rho

lemma h_update_equiv (tau : ℕ → ℝ) (dir : ℕ → ℤ)
    (h_dir : ∀ n, dir n = 1 ∨ dir n = 0 ∨ dir n = -1) :
    ∀ n rho, 0 < rho →
      update_fun tau dir n rho = rho * (1 + tau n) ∨
      update_fun tau dir n rho = rho / (1 + tau n) ∨
      update_fun tau dir n rho = rho := by
  intro n rho hρ_pos
  rcases h_dir n with h | h | h
  · simp [update_fun, h]
  · simp [update_fun, h]
  · simp [update_fun, h]

theorem auto_converges
    (admm_kkt : Existance_of_kkt admm)
    [Setting E₁ E₂ F admm admm_kkt]
    [IsOrderedMonoid ℝ]
    (mu eps c p : ℝ)
    (hp : 1 < p)
    (r_norm_seq s_norm_seq : ℕ → ℝ)
    (h_tau_nonneg : ∀ n, 0 ≤ tau_seq c p n)
    (h_rho : ∀ n, admm.ρₙ (n+1) = update_fun (tau_seq c p) (dir_seq mu eps r_norm_seq s_norm_seq) n (admm.ρₙ n))
    (fullrank₁ : Function.Injective admm.A₁)
    (fullrank₂ : Function.Injective admm.A₂) :
    ∃ x₁ x₂ y,
  Convex_KKT x₁ x₂ y admm.toOptProblem ∧
  Tendsto admm.x₁ atTop (𝓝 x₁) ∧
  Tendsto admm.x₂ atTop (𝓝 x₂) ∧
  Tendsto admm.y atTop (𝓝 y) := by
  let tau := tau_seq c p
  let dir := dir_seq mu eps r_norm_seq s_norm_seq
  have h_dir' : ∀ n, dir n = 1 ∨ dir n = 0 ∨ dir n = -1 := by
    intro n; simpa [dir] using h_dir mu eps r_norm_seq s_norm_seq n
  let s : AdaptableStrategy (admm := admm) (admm_kkt := admm_kkt) :=
    { tau_seq := tau
      h_tau_nonneg := h_tau_nonneg
      h_tau_summable := h_tau_summable c p hp
      update_fun := update_fun tau dir
      h_update_equiv := h_update_equiv tau dir h_dir' }
  apply Strategy3.converges_from_adaptable_strategy (admm := admm) (admm_kkt := admm_kkt) s h_rho fullrank₁ fullrank₂