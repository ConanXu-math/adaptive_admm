-- Base library for adaptive ADMM strategies
-- Contains all FIXED components that don't change across different strategies
import Optlib.Algorithm.AdaptiveADMM.Strategies.Adaptive_Strategy_Convergence
import Optlib.Algorithm.AdaptiveADMM.Strategies.VerificationLib

noncomputable section

namespace AdaptiveStrategyBase
open Topology Filter AdaptiveADMM_Verification AdaptiveADMM_Convergence_Proof

variable {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

variable (admm : ADMM E₁ E₂ F)


def update_fun (tau : ℕ → ℝ) (dir : ℕ → ℤ) (n : ℕ) (rho : ℝ) : ℝ :=
  if dir n = (-1 : ℤ) then rho / (1 + tau n)
  else if dir n = (1 : ℤ) then rho * (1 + tau n)
  else rho

def r_ratio (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  r_norm_seq n / max (s_norm_seq n) eps
def s_ratio (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  s_norm_seq n / max (r_norm_seq n) eps

lemma h_update_equiv (tau : ℕ → ℝ) (dir : ℕ → ℤ)
    (h_dir : ∀ n, dir n = 1 ∨ dir n = 0 ∨ dir n = -1) :
    ∀ n rho, 0 < rho → update_fun tau dir n rho = rho * (1 + tau n) ∨
      update_fun tau dir n rho = rho / (1 + tau n) ∨ update_fun tau dir n rho = rho := by
  intro n rho _; rcases h_dir n with h | h | h
  · left; simp [update_fun, h]
  · right; right; simp [update_fun, h]
  · right; left; simp [update_fun, h]

end AdaptiveStrategyBase
