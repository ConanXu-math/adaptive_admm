-- Manually maintained Lean proof example (ResearchCandidate.lean style)
import Optlib.Algorithm.AdaptiveADMM

noncomputable section
open Topology Filter AdaptiveADMM AdaptiveADMM_Verification AdaptiveADMM_Convergence_Proof AdaptiveStrategyBase

variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (admm : ADMM E₁ E₂ F)

theorem auto_converges (reference : KKTPoint admm)
    (c p : ℝ) (hp1 : 1 < p) (hp2 : 1 < p + 0.5)
    (action : ℕ → RhoAction)
    (h_tau_nonneg : ∀ n, 0 ≤ (fun n : ℕ => tau_seq_shifted (c * 0.8) p 1 n + (tau_seq_shifted (c * 0.2) (p + 0.5) 1 n)) n)
    (h_rho : ∀ n, admm.ρₙ (n+1) =
      (action n).update ((fun n : ℕ => tau_seq_shifted (c * 0.8) p 1 n + (tau_seq_shifted (c * 0.2) (p + 0.5) 1 n)) n) (admm.ρₙ n))
    (fullrank₁ : Function.Injective admm.A₁) (fullrank₂ : Function.Injective admm.A₂) :
    ∃ x₁ x₂ y, Convex_KKT x₁ x₂ y admm.toOptProblem ∧ Tendsto admm.x₁ atTop (𝓝 x₁) ∧
      Tendsto admm.x₂ atTop (𝓝 x₂) ∧ Tendsto admm.y atTop (𝓝 y) := by
  let tau : CertifiedTau :=
    { seq := (fun n : ℕ => tau_seq_shifted (c * 0.8) p 1 n + (tau_seq_shifted (c * 0.2) (p + 0.5) 1 n)), nonneg := h_tau_nonneg, summable := ((h_tau_summable_shifted (c * 0.8) p 1 hp1 (by norm_num)).add (h_tau_summable_shifted (c * 0.2) (p + 0.5) 1 hp2 (by norm_num))) }
  let policy : StrategyPolicy :=
    { tau := tau, action := action }
  exact Strategy3.converges_from_policy (admm := admm) reference policy
    (by
      intro n
      simpa [policy, tau, StrategyPolicy.updateRho] using h_rho n)
    fullrank₁
    fullrank₂
