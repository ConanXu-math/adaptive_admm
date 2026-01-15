import Optlib.Algorithm.AdaptiveADMM.AdaptiveScheme
import Optlib.Algorithm.AdaptiveADMM.AdaptiveLemmas
import Optlib.Algorithm.AdaptiveADMM.AdaptiveCondition1
import Optlib.Algorithm.AdaptiveADMM.AdaptiveCondition2
import Optlib.Algorithm.AdaptiveADMM.AdaptiveTheorem_converge_c1
import Optlib.Algorithm.AdaptiveADMM.AdaptiveTheorem_converge_c2

noncomputable section

open Set InnerProductSpace Topology Filter Real
open AdaptiveADMM_Convergence_Proof

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

variable (admm : ADMM E₁ E₂ F)
variable (admm_kkt : Existance_of_kkt admm)

/-
## Strategy 3 定义
-/
class Strategy3 [Setting E₁ E₂ F admm admm_kkt][IsOrderedMonoid ℝ] where
  tau_seq : ℕ → ℝ
  h_tau_nonneg : ∀ n, 0 ≤ tau_seq n
  h_tau_summable : Summable tau_seq
  h_rho_update : ∀ n,
    admm.ρₙ (n+1) = admm.ρₙ n * (1 + tau_seq n) ∨
    admm.ρₙ (n+1) = admm.ρₙ n / (1 + tau_seq n) ∨
    admm.ρₙ (n+1) = admm.ρₙ n

namespace Strategy3

variable [Setting E₁ E₂ F admm admm_kkt]
variable [IsOrderedMonoid ℝ]
variable [s3 : Strategy3 admm admm_kkt]

local notation "τ" => s3.tau_seq
local notation "h_tau_summable" => s3.h_tau_summable
local notation "h_tau_nonneg" => s3.h_tau_nonneg
/-
### 辅助引理
-/
lemma bound_summable :Summable (fun n => 2 * τ n + (τ n)^2) := by
  apply Summable.add
  · -- 2 * τ is summable
    apply Summable.mul_left
    exact h_tau_summable
  · -- τ^2 is summable
    have h_lim : Tendsto τ atTop (𝓝 0) := h_tau_summable.tendsto_atTop_zero
    -- 使用 refine 显式提供上界序列，并转换滤波器类型
    refine Summable.of_norm_bounded_eventually  h_tau_summable ?_
    -- 将目标中的 cofinite 转换为 atTop，以便使用 h_lim
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [h_lim (Metric.ball_mem_nhds 0 zero_lt_one)] with n hn
    -- Proof: |τ_n^2| = |τ_n|^2 ≤ |τ_n| when |τ_n| < 1
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (h_tau_nonneg n)] at *
    simp at hn
    -- Use: x^2 = x * x ≤ x * 1 = x when 0 ≤ x ≤ 1
    rw [sq]
    have h_le : 0 ≤ τ n := h_tau_nonneg n
    have h_lt : τ n < 1 := by
      exact lt_of_abs_lt hn
    exact mul_le_of_le_one_left h_le (le_of_lt h_lt)
/-
### 1. 证明 Strategy3 满足 Condition C1
-/

lemma eta_sq_bound_s3 (n : ℕ) : (η_k (admm := admm) n)^2 ≤ 2 * τ n + (τ n)^2 := by
  dsimp [η_k]
  split_ifs with h_zero h_inc
  · -- n=0
    simp; apply add_nonneg
    have h_zero : 0 ≤ τ n := h_tau_nonneg n
    · apply mul_nonneg (by norm_num) h_zero
    · apply sq_nonneg
  · -- ρ_{n+1} > ρ_n (增长情况)
    -- 根据 S3 定义，ρ 变大只能是 ρ_{n+1} = ρ_n * (1 + τ) 这一种情况
    have h_update_true : admm.ρₙ (n+1) = admm.ρₙ n * (1 + τ n) := by
      cases s3.h_rho_update n with
      | inl h_mul => exact h_mul
      | inr h_rest =>
        cases h_rest with
        | inl h_div =>
          -- 如果是除法 ρ_{n+1} = ρ_n / (1+τ)
          -- 因为 τ ≥ 0 => 1+τ ≥ 1 => ρ_{n+1} ≤ ρ_n，与 h_inc (ρ_{n+1} > ρ_n) 矛盾
          have h_le : admm.ρₙ (n+1) ≤ admm.ρₙ n := by
            rw [h_div]
            apply div_le_self (le_of_lt (admm.hρₙ_pos n))
            linarith [h_tau_nonneg n]
          linarith [h_inc, h_le]
        | inr h_eq =>
          -- 如果相等，与 h_inc 矛盾
          linarith [h_inc, h_eq]
    -- 计算 η_k^2 = (ρ_{n+1}/ρ_n)^2 - 1
    rw [Real.sq_sqrt]
    · -- 内部化简：((ρ(1+τ)/ρ)^2 - 1) = (1+τ)^2 - 1 = 2τ + τ^2
      rw [h_update_true]
      have h_rho_pos : admm.ρₙ n > 0 := admm.hρₙ_pos n
      field_simp [ne_of_gt h_rho_pos]
      ring_nf
      apply le_refl
    · -- 证明根号内非负
      rw [h_update_true]
      have h_rho_pos : admm.ρₙ n > 0 := admm.hρₙ_pos n
      field_simp [ne_of_gt h_rho_pos]
      rw [sub_nonneg, one_le_sq_iff_one_le_abs]
      rw [abs_of_nonneg (add_nonneg zero_le_one (h_tau_nonneg n))]
      linarith [h_tau_nonneg n]
  · -- 其他情况 (减少或不变)，η = 0
    simp
    apply add_nonneg
    · apply mul_nonneg (by norm_num) (h_tau_nonneg n)
    · apply sq_nonneg



lemma summable_eta_sq : Summable (fun n => (η_k (admm := admm) n)^2) := by
  apply summable_of_nonneg_of_le
  · intro n; apply sq_nonneg
  · intro n; exact eta_sq_bound_s3 admm admm_kkt n
  · exact bound_summable admm admm_kkt

lemma multipliable_one_eta_sq : Multipliable (fun n => 1 + (η_k (admm := admm) n)^2) := by
  let f := fun n => (η_k (admm := admm) n)^2
  have h_sum : Summable f := summable_eta_sq admm admm_kkt
  have h_nonneg : ∀ n, 0 ≤ f n := fun n => sq_nonneg _
  exact Real.multipliable_one_add_of_summable h_sum

-- 实例化 Condition_C1
instance strategy3_satisfies_C1 [Setting E₁ E₂ F admm admm_kkt] [s3 : Strategy3 admm admm_kkt] : Condition_C1 admm admm_kkt where
  eta_square_summable' := summable_eta_sq admm admm_kkt
  eta_square_summable := by
    obtain ⟨S, hS⟩ := summable_eta_sq admm admm_kkt
    use S + 1
    constructor
    · have h_nonneg : ∀ n, 0 ≤ (η_k (admm := admm) n)^2 := fun n => sq_nonneg _
      have : S ≥ 0 := by
        exact HasSum.nonneg h_nonneg hS
      linarith
    · have h_tsum_eq := hS.tsum_eq
      linarith

  one_eta_square_multipliable := multipliable_one_eta_sq admm admm_kkt

  one_eta_square_multipliable' := by
    obtain ⟨P, hP⟩ := multipliable_one_eta_sq admm admm_kkt
    use P + 1
    constructor
    · -- 1. 证明每一项都 >= 1
      have h_one_le : ∀ n, 1 ≤ 1 + (η_k (admm := admm) n)^2 :=
        fun n => le_add_of_nonneg_right (sq_nonneg _)
      -- 2. 证明任意有限子集的乘积 >= 1 (匹配 HasProd 的定义)
      have h_finset_ge_one : ∀ s : Finset ℕ, 1 ≤ ∏ i ∈ s, (1 + (η_k (admm := admm) i)^2) := by
        intro s
        apply Finset.one_le_prod'
        intro i _
        exact h_one_le i
      -- 3. 应用极限保序性，P >= 1
      have hP_ge_one : 1 ≤ P := ge_of_tendsto' hP h_finset_ge_one
      linarith
    · rw [hP.tprod_eq]
      linarith
/-
### 3. Strategy3 收敛性定理
-/
omit s3 in
theorem strategy3_converges
    [Strategy3 admm admm_kkt]
    [IsOrderedMonoid ℝ]
    (fullrank₁ : Function.Injective admm.A₁)
    (fullrank₂ : Function.Injective admm.A₂) :
    ∃ (x₁_star : E₁) (x₂_star : E₂) (y_star : F),
      Convex_KKT x₁_star x₂_star y_star admm.toOptProblem ∧
      (Tendsto admm.x₁ atTop (𝓝 x₁_star) ∧
       Tendsto admm.x₂ atTop (𝓝 x₂_star) ∧
       Tendsto admm.y atTop (𝓝 y_star)) := by
  haveI : Setting E₁ E₂ F admm (admm_kkt_c1 fullrank₁ fullrank₂ (admm_kkt := admm_kkt) (_s := ⟨⟩)) := {}
  apply adaptive_admm_convergence_c1
end Strategy3

structure AdaptableStrategy
    [Setting E₁ E₂ F admm admm_kkt]
    [IsOrderedMonoid ℝ] where
  tau_seq : ℕ → ℝ
  h_tau_nonneg : ∀ n, 0 ≤ tau_seq n
  h_tau_summable : Summable tau_seq
  update_fun : ℕ → ℝ → ℝ
  h_update_equiv :
    ∀ n rho, 0 < rho →
      update_fun n rho = rho * (1 + tau_seq n) ∨
      update_fun n rho = rho / (1 + tau_seq n) ∨
      update_fun n rho = rho

/-
## AdaptableStrategy → Strategy3
-/
noncomputable def Strategy3.ofAdaptableStrategy
    [Setting E₁ E₂ F admm admm_kkt]
    [IsOrderedMonoid ℝ]
    (s : AdaptableStrategy (admm := admm) (admm_kkt := admm_kkt))
    (hρ : ∀ n, admm.ρₙ (n+1) = s.update_fun n (admm.ρₙ n)) :
    Strategy3 admm admm_kkt :=
{
  tau_seq := s.tau_seq
  h_tau_nonneg := s.h_tau_nonneg
  h_tau_summable := s.h_tau_summable
  h_rho_update := by
    intro n
    have h :=
      s.h_update_equiv n (admm.ρₙ n) (admm.hρₙ_pos n)
    rcases h with h | h | h
    · left
      simpa [hρ] using h
    · right; left
      simpa [hρ] using h
    · right; right
      simpa [hρ] using h
}
