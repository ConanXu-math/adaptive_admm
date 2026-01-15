-- AUTO GENERATED Lean4 FILE
import Optlib.Algorithm.AdaptiveADMM.Strategies.Adaptive_Strategy_Convergence
noncomputable section

def update_fun (n : ℕ) (rho : ℝ) : ℝ :=
  match n with
  | 0 => rho * (2.0 : ℝ)
  | 1 => rho / (2.0 : ℝ)
  | 2 => rho * (2.0 : ℝ)
  | 3 => rho * (2.0 : ℝ)
  | 4 => rho / (2.0 : ℝ)
  | 5 => rho / (2.0 : ℝ)
  | 6 => rho

def tau_seq (n : ℕ) : ℝ :=
  match n with
  | 0 => 1 / ((n : ℝ) + 2)^2
  | 1 => 1 / ((n : ℝ) + 2)^2
  | 2 => 1 / ((n : ℝ) + 2)^2
  | 3 => 1 / ((n : ℝ) + 2)^2
  | 4 => 1 / ((n : ℝ) + 2)^2
  | 5 => 1 / ((n : ℝ) + 2)^2
  | 6 => 0

def choice_seq (n : ℕ) : Strategy3.RhoUpdateRule :=
  match n with
  | 0 => .increase
  | 1 => .decrease
  | 2 => .increase
  | 3 => .increase
  | 4 => .decrease
  | 5 => .decrease
  | 6 => .keep

def adaptable_strategy_auto : GeneralAdapter.AdaptableStrategy :=
{
  update_fun := update_fun,
  tau_seq := tau_seq,
  choice_seq := choice_seq,
  h_tau_nonneg := by intro n; dsimp [tau_seq]; apply zero_le_one_div,
  h_tau_summable := by apply summable_one_div_nat_pow.mpr (by norm_num),
  h_update_equiv := by
    intros n rho hρ_pos; dsimp [update_fun, tau_seq, choice_seq];
    admit
}

variable (fullrank₁ : Function.Injective base_admm_real.A₁)
variable (fullrank₂ : Function.Injective base_admm_real.A₂)

theorem auto_converges : ∃ x₁ x₂ y,
  let final_admm := { base_admm_real with
    ρₙ := fun n => Nat.rec ({admm_name}.ρₙ 0) (fun k ρ => update_fun k ρ) n
  }
  Convex_KKT x₁ x₂ y final_admm.toOptProblem ∧
  Tendsto final_admm.x₁ atTop (𝓝 x₁) ∧
  Tendsto final_admm.x₂ atTop (𝓝 x₂) ∧
  Tendsto final_admm.y atTop (𝓝 y) := by
  apply GeneralAdapter.converges_from_adaptable_strategy base_admm_real base_admm_kkt_real adaptable_strategy_auto fullrank₁ fullrank₂