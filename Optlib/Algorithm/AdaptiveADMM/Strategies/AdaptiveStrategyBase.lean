-- Base library for adaptive ADMM strategies
-- Contains all FIXED components that don't change across different strategies
import Optlib.Algorithm.AdaptiveADMM.Strategies.Adaptive_Strategy_Convergence
import Optlib.Algorithm.AdaptiveADMM.Strategies.VerificationLib

noncomputable section

namespace AdaptiveStrategyBase
open AdaptiveADMM

def r_ratio (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  r_norm_seq n / max (s_norm_seq n) eps

def s_ratio (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  s_norm_seq n / max (r_norm_seq n) eps

/-- Standard residual-balancing branch selector used by generated certificates. -/
def residualBalanceAction
    (mu eps : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : RhoAction :=
  if r_ratio r_norm_seq s_norm_seq eps n > mu then .increase
  else if s_ratio r_norm_seq s_norm_seq eps n > mu then .decrease
  else .keep

/-- Compatibility update for historical certificates that encoded actions as integers. -/
def update_fun (tau : ℕ → ℝ) (dir : ℕ → ℤ) (n : ℕ) (rho : ℝ) : ℝ :=
  if dir n = (-1 : ℤ) then rho / (1 + tau n)
  else if dir n = (1 : ℤ) then rho * (1 + tau n)
  else rho

lemma h_update_equiv (tau : ℕ → ℝ) (dir : ℕ → ℤ)
    (h_dir : ∀ n, dir n = 1 ∨ dir n = 0 ∨ dir n = -1) :
    ∀ n rho, 0 < rho → update_fun tau dir n rho = rho * (1 + tau n) ∨
      update_fun tau dir n rho = rho / (1 + tau n) ∨ update_fun tau dir n rho = rho := by
  intro n rho _; rcases h_dir n with h | h | h
  · left; simp [update_fun, h]
  · right; right; simp [update_fun, h]
  · right; left; simp [update_fun, h]

end AdaptiveStrategyBase
