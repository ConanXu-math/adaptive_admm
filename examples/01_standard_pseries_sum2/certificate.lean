-- Manually maintained Lean proof example (ResearchCandidate.lean style)
import Optlib.Algorithm.AdaptiveADMM

noncomputable section
open Topology Filter AdaptiveADMM AdaptiveADMM_Verification AdaptiveADMM_Convergence_Proof AdaptiveStrategyBase

variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable (admm : ADMM E₁ E₂ F)

theorem auto_converges (reference : KKTPoint admm)
    (c1 p1 c2 p2 : ℝ) (hp1 : 1 < p1) (hp2 : 1 < p2)
    (action : ℕ → RhoAction)
    (h_tau_nonneg : ∀ n, 0 ≤ tau_seq_sum2 c1 p1 c2 p2 n)
    (h_rho : ∀ n, admm.ρₙ (n+1) =
      (action n).update (tau_seq_sum2 c1 p1 c2 p2 n) (admm.ρₙ n))
    (fullrank₁ : Function.Injective admm.A₁) (fullrank₂ : Function.Injective admm.A₂) :
    ∃ x₁ x₂ y, Convex_KKT x₁ x₂ y admm.toOptProblem ∧ Tendsto admm.x₁ atTop (𝓝 x₁) ∧
      Tendsto admm.x₂ atTop (𝓝 x₂) ∧ Tendsto admm.y atTop (𝓝 y) := by
  let tau : CertifiedTau :=
    { seq := tau_seq_sum2 c1 p1 c2 p2, nonneg := h_tau_nonneg, summable := h_tau_summable_sum2 c1 p1 c2 p2 hp1 hp2 }
  let policy : StrategyPolicy :=
    { tau := tau, action := action }
  exact Strategy3.converges_from_policy (admm := admm) reference policy
    (by
      intro n
      simpa [policy, tau, StrategyPolicy.updateRho] using h_rho n)
    fullrank₁
    fullrank₂
