from pathlib import Path
from lean_interact import LeanREPLConfig, LeanServer, LocalProject, FileCommand

# optlib 项目根（含 lakefile.lean），从 lean_admm 向上一级
_optlib_root = Path(__file__).resolve().parent.parent
project = LocalProject(directory=str(_optlib_root))
config = LeanREPLConfig(project=project)
server = LeanServer(config=config)
response = server.run(FileCommand(path="Optlib/Algorithm/AdaptiveADMM/Strategies/Strategy3_Convergence.lean"))
print(response)


'''
class Strategy3 [Setting E₁ E₂ F admm admm_kkt][IsOrderedMonoid ℝ] where
  tau_seq : ℕ → ℝ
  h_tau_nonneg : ∀ n, 0 ≤ tau_seq n
  h_tau_summable : Summable tau_seq
  h_rho_update : ∀ n,
    admm.ρₙ (n+1) = admm.ρₙ n * (1 + tau_seq n) ∨
    admm.ρₙ (n+1) = admm.ρₙ n / (1 + tau_seq n) ∨
    admm.ρₙ (n+1) = admm.ρₙ n
'''