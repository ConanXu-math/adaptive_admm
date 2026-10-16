-- Base library for adaptive ADMM strategies
-- Contains reusable residual-based action selectors.
import Optlib.Algorithm.AdaptiveADMM.Strategies.StrategyPolicy
import Optlib.Algorithm.AdaptiveADMM.Strategies.VerificationLib

noncomputable section

namespace AdaptiveStrategyBase
open AdaptiveADMM

def r_ratio (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  r_norm_seq n / max (s_norm_seq n) eps

def s_ratio (r_norm_seq s_norm_seq : ℕ → ℝ) (eps : ℝ) (n : ℕ) : ℝ :=
  s_norm_seq n / max (r_norm_seq n) eps

/-- Standard residual-balancing branch selector reused by research proofs. -/
def residualBalanceAction
    (mu eps : ℝ) (r_norm_seq s_norm_seq : ℕ → ℝ) (n : ℕ) : RhoAction :=
  if r_ratio r_norm_seq s_norm_seq eps n > mu then .increase
  else if s_ratio r_norm_seq s_norm_seq eps n > mu then .decrease
  else .keep

end AdaptiveStrategyBase
