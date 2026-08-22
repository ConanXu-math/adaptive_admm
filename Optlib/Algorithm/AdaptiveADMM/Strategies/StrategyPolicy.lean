import Mathlib.Analysis.PSeries

noncomputable section

namespace AdaptiveADMM

/-- The three updates admitted by the current Strategy3 convergence theorem. -/
inductive RhoAction where
  | increase
  | decrease
  | keep
  deriving DecidableEq, Repr

namespace RhoAction

def update (action : RhoAction) (tau rho : ℝ) : ℝ :=
  match action with
  | increase => rho * (1 + tau)
  | decrease => rho / (1 + tau)
  | keep => rho

end RhoAction

/-- A modulation sequence bundled with exactly the facts needed by Strategy3. -/
structure CertifiedTau where
  seq : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ seq n
  summable : Summable seq

/-- Typed public policy for canonical Strategy3 certificates. -/
structure StrategyPolicy where
  tau : CertifiedTau
  action : ℕ → RhoAction

namespace StrategyPolicy

def updateRho (policy : StrategyPolicy) (n : ℕ) (rho : ℝ) : ℝ :=
  (policy.action n).update (policy.tau.seq n) rho

lemma updateRho_cases (policy : StrategyPolicy) (n : ℕ) (rho : ℝ) :
    policy.updateRho n rho = rho * (1 + policy.tau.seq n) ∨
    policy.updateRho n rho = rho / (1 + policy.tau.seq n) ∨
    policy.updateRho n rho = rho := by
  cases h : policy.action n <;>
    simp [updateRho, RhoAction.update, h]

end StrategyPolicy

end AdaptiveADMM
