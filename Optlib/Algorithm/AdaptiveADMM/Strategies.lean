import Optlib.Algorithm.AdaptiveADMM.Compatibility
import Optlib.Algorithm.AdaptiveADMM.Strategies.AdaptiveStrategyBase
import Optlib.Algorithm.AdaptiveADMM.Strategies.Adaptive_Strategy_Convergence
import Optlib.Algorithm.AdaptiveADMM.Strategies.StrategyPolicy
import Optlib.Algorithm.AdaptiveADMM.Strategies.ClippedPolicy
import Optlib.Algorithm.AdaptiveADMM.Strategies.TauTemplates
import Optlib.Algorithm.AdaptiveADMM.Strategies.VerificationLib

/-!
Stable public facade for manually written adaptive-ADMM candidate proofs.

Candidate proofs should import this module rather than proof-internal C1 files.
-/
