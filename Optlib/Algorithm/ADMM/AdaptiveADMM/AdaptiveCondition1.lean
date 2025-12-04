import Optlib.Algorithm.ADMM.AdaptiveADMM.AdaptiveScheme
import Optlib.Algorithm.ADMM.AdaptiveADMM.AdaptiveLemmas

noncomputable section

open Set InnerProductSpace Topology Filter Bornology Metric Real

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

variable(admm : ADMM E₁ E₂ F)

namespace AdaptiveADMM_Convergence_Proof

variable {admm admm_kkt}

local notation "f₁" => admm.f₁
local notation "f₂" => admm.f₂
local notation "A₁" => admm.A₁
local notation "A₂" => admm.A₂
local notation "x₁" => admm.x₁
local notation "x₂" => admm.x₂
local notation "b" => admm.b
local notation "y"  => admm.y
local notation "τ"  => admm.τ
local notation "ρₙ" => admm.ρₙ
local notation "ρmin" => admm.ρmin

local notation "x₁'" => admm_kkt.x₁
local notation "x₂'" => admm_kkt.x₂
local notation "y'"  => admm_kkt.y

local notation "A₁†" => ContinuousLinearMap.adjoint A₁
local notation "A₂†" => ContinuousLinearMap.adjoint A₂
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

-- ==========================

def η_k [Setting E₁ E₂ F admm admm_kkt] : ℕ → ℝ :=
  fun n => if n = 0 then 0
           else if ρₙ (n+1) > ρₙ n then
            Real.sqrt ((ρₙ (n+1) / ρₙ n)^2 - 1)
           else 0
#check η_k
def θ_k [Setting E₁ E₂ F admm admm_kkt] : ℕ → ℝ :=
  fun n => if ρₙ (n+1) < ρₙ n then
            Real.sqrt (1 - (ρₙ n / ρₙ (n+1))^2)
           else 0
def h1 [Setting E₁ E₂ F admm admm_kkt] (n : ℕ) := - g1 (n+1) + (1 + (η_k n)^2)* (g1 n)
-- Condition C1: 增长情况下的收敛条件
class Condition_C1 {E₁ E₂ F : outParam Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (admm : outParam (ADMM E₁ E₂ F))
    (admm_kkt : outParam (Existance_of_kkt admm))
    extends Setting E₁ E₂ F admm admm_kkt where
  eta_square_summable : ∃ S > 0, ∑' n : ℕ, (η_k n)^2 ≤ S
  eta_square_summable' : Summable (f := fun n :ℕ  => (η_k n)^2)
  one_eta_square_multipliable':
    ∃ S > 0 , ∏' n : ℕ, (1 + (η_k n)^2) ≤ S
  one_eta_square_multipliable : Multipliable (f := fun n :ℕ  => (1 + (η_k n)^2))


-- Condition C2: 减小情况下的收敛条件
class Condition_C2 {E₁ E₂ F : outParam Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (admm : outParam (ADMM E₁ E₂ F)) (admm_kkt : outParam (Existance_of_kkt admm))
    extends Setting E₁ E₂ F admm admm_kkt where
  -- Σ θₖ² < ∞ (θ平方和有限)
  theta_square_summable : ∃ S, ∑' n : ℕ+, (θ_k n)^2 ≤ S


lemma HWY_thm4_1_ineq [Setting E₁ E₂ F admm admm_kkt] :T_HWY - τ >0 := by
   rw[eq4']
   have hpos : 0 < (τ^2 - 3*τ + 3 : ℝ) := by
      have : (τ^2 - 3*τ + 3 : ℝ) = (τ - (3/2))^2 + (3/4) := by ring
      have hsq : 0 ≤ (τ - (3/2))^2 := by exact sq_nonneg _
      have h34 : 0 < (3/4 : ℝ) := by norm_num
      have h:= add_pos_of_nonneg_of_pos hsq h34
      rw [this]
      exact h
   linarith
lemma HWY_thm4_1_ineq'[Setting E₁ E₂ F admm admm_kkt] :∀ n : ℕ,τ * (T_HWY - τ) * ρₙ n^2  ≥ 0 := by
   intro n
   have h1:= admm.htau.1
   have h2:= HWY_thm4_1_ineq
   have h3:= sq_pos_of_pos (admm.hρₙ_pos n)
   have h4:= mul_pos h1 h2
   have := mul_pos h4 h3
   linarith[this]

lemma HWY_eq_bounded_below [Setting E₁ E₂ F admm admm_kkt] :
    ∀ n : ℕ+,
        0 ≤ ‖ey n‖^2    + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
        intro n
        have h:  0 ≤ ‖ey n‖^2 := by exact sq_nonneg ‖ey ↑n‖
        have := sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
        have h1: 0 ≤ τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by exact mul_nonneg  (HWY_thm4_1_ineq' n) this
        linarith

lemma rho_square_ratio_bound [Setting E₁ E₂ F admm admm_kkt] (n : ℕ+) :
    (ρₙ (n+1))^2 / (ρₙ n)^2 ≤ 1 + (η_k n)^2 := by
  by_cases h : ρₙ (n+1) > ρₙ n
  ·
    simp [η_k, h]
    have h5: (ρₙ (n+1) / ρₙ n)^2 - 1 ≥ 0 := by
      field_simp
      have h3:(ρₙ n)  ≥ 0 := by linarith [admm.hρₙ_pos n]
      have h3':(ρₙ (n+1))  ≥  0 := by linarith [admm.hρₙ_pos (n+1)]
      have h2: (0 : ℝ) < (1 : ℝ)  := by linarith
      have h1: (ρₙ n) ^2 > 0 := by
         refine sq_pos_of_pos ?ha
         linarith [admm.hρₙ_pos n]
      simp
      have h2:= div_pos (admm.hρₙ_pos (n+1)) (admm.hρₙ_pos n)
      have h4:= Bound.one_lt_div_of_pos_of_lt (admm.hρₙ_pos n) h
      have h5 := (sq_lt_sq₀ h3 h3').mpr h
      -- have h6:= pow_le_pow_left' h4 2
      rw[one_le_div]
      linarith
      linarith
    have h6: Real.sqrt ((ρₙ (n+1) / (ρₙ n))^2-1) ^2 =  (ρₙ (n+1)/ (ρₙ n))^2-1 := by
      exact Real.sq_sqrt h5
    rw[h6]
    simp
    ring_nf
    linarith
  · -- 当 ρₙ 不增长时
    simp [η_k,h]
    have pos1 : 0 ≤  ρₙ n := by linarith [admm.hρₙ_pos n]
    have pos2 : 0 ≤  ρₙ (n+1) := by linarith [admm.hρₙ_pos (n+1)]
    rw [div_le_one]
    have := le_of_not_gt h
    have h6:= (sq_le_sq₀  pos2 pos1).2 this
    linarith[h6]
    exact sq_pos_of_pos (admm.hρₙ_pos n)


lemma HWY_Convergence_1_1_1 [Setting E₁ E₂ F admm admm_kkt] (n : ℕ) : 1 ≤ 1 + (η_k n)^2 := by
 norm_num
 exact sq_nonneg (η_k n)

#check Bound.one_lt_div_of_pos_of_lt

lemma HWY_Convergence_1_1 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+,
       ‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
+ τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
≤ ‖ey n‖^2 + τ * (ρₙ (n+1)^2 / ρₙ (n)^2) *  ρₙ (n)^2 * ‖A₂ (e₂ n)‖^2
+ τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
- (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
      intro n
      have h1:= HWY_Theorem_3_1 n
      have h : (ρₙ (n+1)^2 / ρₙ (n)^2) *  ρₙ (n)^2 = ρₙ (n+1)^2 := by
       refine div_mul_cancel₀ (ADMM.ρₙ E₁ E₂ F (↑n + 1) ^ 2) ?h
       have := sq_pos_of_pos (admm.hρₙ_pos n)
       linarith
      -- 统一乘法结合律的括号，以匹配目标中的形态
      have hmul : τ * ((ρₙ (n+1)^2 / ρₙ (n)^2) * ρₙ (n)^2) = τ * (ρₙ (n+1)^2 / ρₙ (n)^2) * ρₙ (n)^2 := by
        ring
      nth_rw 3 [← h] at h1
      linarith[h1]

lemma HWY_Convergence_1_2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+,
      ‖ey n‖^2 + τ * (ρₙ (n+1)^2/ ρₙ (n)^2) *  ρₙ (n)^2  * ‖A₂ (e₂ n)‖^2
      + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
         (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2)
      ≤ ‖ey n‖^2 + τ * (1 + (η_k n)^2) * ρₙ (n)^2  * ‖A₂ (e₂ n)‖^2
      + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
         (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := by
         intro n
         simp
         gcongr
         · linarith [admm.htau.1]
         · exact rho_square_ratio_bound n

lemma HWY_Convergence_1_3 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+,
‖ey n‖^2 + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
         (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2)
      ≤ (1 + (η_k n)^2)*
      (‖ey n‖^2 + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2)
      - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
         (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := by
         intro n
         simp
         have h : 1 ≤ 1 + (η_k n)^2 := by
            norm_num
            exact sq_nonneg (η_k n)
         have := mul_le_mul_of_nonneg_left h (HWY_eq_bounded_below n)
         linarith

lemma HWY_ineq_51 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+,
‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
+ τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
≤ (1 + (η_k n)^2)*
(‖ey n‖^2 + τ * ρₙ (n)^2  * ‖A₂ (e₂ n)‖^2
+ τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2)
- (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
   (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
     intro n
     have := HWY_Convergence_1_1 n
     have := HWY_Convergence_1_3 n
     have := HWY_Convergence_1_2 n
     linarith
lemma  HWY_ineq_51' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
 -(1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
   (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) ≤   0 := by
   intro n
   have h1:= admm.htau.1
   have h2:=admm.htau_range
   have h3:= sq_pos_of_pos (admm.hρₙ_pos (n+1))
   have h4:= mul_pos h1 h2
   have h5:= mul_pos h4 h3
   have :(1 + τ - τ^2) * τ * ρₙ (n+1)^2 ≥ 0 := by linarith[h5]
   have h6:= sq_nonneg ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖
   have h7:= sq_nonneg ‖A₂ (x₂ n - x₂ (n+1))‖
   have h8:= add_nonneg h6 h7
   have h9:= mul_nonneg this h8
   linarith

lemma HWY_ineq_52_0 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
+ τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
≤ (1 + (η_k n)^2)*
(‖ey n‖^2 + τ * ρₙ (n)^2  * ‖A₂ (e₂ n)‖^2
+ τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) := by
   intro n
   have h := HWY_ineq_51 n
   have hneg := HWY_ineq_51' n
   linarith

-- lemma HWY_ineq_52_0_nat [Condition_C1 admm admm_kkt]: ∀ n : ℕ,
-- ‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
-- + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
-- ≤ (1 + (η_k n)^2)*
-- (‖ey n‖^2 + τ * ρₙ (n)^2  * ‖A₂ (e₂ n)‖^2
-- + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) := by
--    intro n
--    have : ‖ey (1)‖^2 + τ * ρₙ (1)^2 * ‖A₂ (e₂ (1))‖^2
--    + τ * (T_HWY - τ) * ρₙ (1)^2 * ‖A₁ (x₁ (1)) + A₂ (x₂ (1)) - b‖ ^ 2
--    ≤(1 + (η_k 0)^2) *
--    (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
--    + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2):= by
--          have h1 : (η_k 0) = 0 := by simp [η_k]
--          rw [h1]
--          simp
--    induction' n with k h
--    ·
--       have : ‖ey (1)‖^2 + τ * ρₙ (1)^2 * ‖A₂ (e₂ (1))‖^2 + τ * (T_HWY - τ) * ρₙ (1)^2 * ‖A₁ (x₁ (1)) + A₂ (x₂ (1)) - b‖ ^ 2 ≤ (1 + (η_k 0)^2) *
--    (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
--    + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2):= by
--          have h1 : (η_k 0) = 0 := by simp [η_k]
--          rw [h1]
--          simp
--       simp
--       exact this
-- lemma HWY_ineq_52_0_nat [Condition_C1 admm admm_kkt]: ∀ n : ℕ,
-- ‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
-- + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
-- ≤ (1 + (η_k n)^2)*
-- (‖ey n‖^2 + τ * ρₙ (n)^2  * ‖A₂ (e₂ n)‖^2
-- + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) := by
--    intro n
--    cases n with
--    | zero =>
--       sorry
--    | succ k =>
--       -- n = k + 1 的情况 (k ≥ 0, 即 n ≥ 1)
--       -- 这里可以直接调用已有的 ℕ+ 版本
--       let n_pnat : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
--       have h := HWY_ineq_51 n_pnat
--       have hneg := HWY_ineq_51' n_pnat
--       -- 转换类型以匹配目标
--       have h_idx : (n_pnat : ℕ) = k + 1 := rfl
--       simp only [h_idx] at h hneg
--       linarith
#check Finset.Icc 1 4
lemma HWY_ineq_52_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ,
  ‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
  + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
  ≤ (∏ k ∈ Finset.range (n+1), (1 + (η_k k)^2)) *
  (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2) := by
  intro n
  have : ‖ey (1)‖^2 + τ * ρₙ (1)^2 * ‖A₂ (e₂ (1))‖^2
  + τ * (T_HWY - τ) * ρₙ (1)^2 * ‖A₁ (x₁ (1)) + A₂ (x₂ (1)) - b‖ ^ 2
  ≤(1 + (η_k 0)^2) *
  (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2):= by
      have h1 : (η_k 0) = 0 := by simp [η_k]
      rw [h1]
      simp
  induction' n with k h
  ·   simp
      linarith
  ·   by_cases hh : k = 0
      ·  simp [hh]
         simp [Finset.range]
         have h2 := HWY_ineq_52_0 1
         simp at h2
         have h1 : (η_k 0) = 0 := by simp [η_k]
         rw [h1]
         simp
         exact h2
      ·  push_neg at hh
         have k_pos : k > 0 := by apply Nat.pos_of_ne_zero hh
         have h2 := HWY_ineq_52_0 ((k.toPNat k_pos)+1)
         have h1 : ‖ey ((k.toPNat k_pos+1))‖^2 + τ * ρₙ ((k.toPNat k_pos+1))^2 * ‖A₂ (e₂ ((k.toPNat k_pos+1)))‖^2
         + τ * (T_HWY - τ) * ρₙ ((k.toPNat k_pos+1))^2 * ‖A₁ (x₁ ((k.toPNat k_pos+1))) + A₂ (x₂ ((k.toPNat k_pos+1))) - b‖ ^ 2
         ≤ (∏ m ∈ Finset.range ((k.toPNat k_pos+1)), (1 + (η_k m)^2)) *
         (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
         + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2):= by
            exact h
         show ‖ey ((k.toPNat k_pos+1)+1)‖^2 + τ * ρₙ ((k.toPNat k_pos+1)+1)^2 * ‖A₂ (e₂ ((k.toPNat k_pos+1)+1))‖^2
         + τ * (T_HWY - τ) * ρₙ ((k.toPNat k_pos+1)+1)^2 * ‖A₁ (x₁ ((k.toPNat k_pos+1)+1)) + A₂ (x₂ ((k.toPNat k_pos+1)+1)) - b‖ ^ 2
         ≤ (∏ m ∈ Finset.range ((k.toPNat k_pos+1)+1), (1 + (η_k m)^2)) *
         (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
         + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2)
         simp at h2
         have h3 : (∏ m ∈ Finset.range ((k.toPNat k_pos+1)+1), (1 + (η_k m)^2)) =
            (1 + (η_k ((k.toPNat k_pos+1)) )^2) * ( ∏ m ∈ Finset.range ((k.toPNat k_pos+1)), (1 + (η_k m)^2)) := by
               rw [Finset.prod_range_succ]
               ring
         have hnonneg : 0 ≤ 1 + (η_k ((k.toPNat k_pos+1)))^2 := by apply add_nonneg; norm_num; apply sq_nonneg
         have h4 : _ := mul_le_mul_of_nonneg_left h1 hnonneg
         rw [← mul_assoc, ← h3] at h4
         linarith
         -- exact le_trans h2 h4 --为什么linarith 不行？？？？？？？？？？？ 还得是Claude 解我心头之患 --后续 绷不住 原来是版本问题.。。。

-- def Cp [Condition_C1 admm admm_kkt] : ℝ :=  ∏' n : ℕ, (1 + (η_k n )^2)
lemma HWY_ineq_52_ [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ]: ∀ n : ℕ,
  ∏ k ∈  Finset.range (n+1), (1 + (η_k k)^2) ≤ ∏' k : ℕ, (1 + (η_k k)^2) := by
   intro n
   have hf_nonneg : ∀ k, 0 ≤ 1 + (η_k k)^2 := by intro k ;linarith [sq_nonneg (η_k k)]
   let f : ℕ → ℝ:= fun k => 1 + (η_k k)^2
   let S : Finset ℕ := Finset.range (n + 1)
   have hmult : Multipliable f := Condition_C1.one_eta_square_multipliable
   have h_ge_one : ∀ i : ℕ, i ∉ S → (1:ℝ) ≤ f i := by
      intro i _
      show (1 : ℝ) ≤ f i
      simp only [f]
      linarith [sq_nonneg (η_k i)]
   -- obtain ⟨a, ah⟩ := Condition_C1.one_eta_square_multipliable
   -- have h1 : HasProd f a := ah
   -- -- calc (∏ k in S, f k : ℝ) ≤ (∏ k in t, f k : ℝ) := by ...
   -- show (∏ k ∈ S, f k:ℝ) ≤ (∏' k : ℕ, f k : ℝ)
   -- -- have := prod_le_tprod S h_ge_one hmult
   -- have h2 : ∏ i ∈  S, f i ≤ a := ge_of_tendsto h1 (eventually_atTop.2
   --   ⟨S, fun _t hst =>
   --  @Finset.prod_le_prod_of_subset_of_one_le' (ι := ℕ) (N := ℝ) (f := f) (s := S) (t := _t) _ _ _ hst
   --        (fun i _ hi => h_ge_one i hi)⟩)
   exact Multipliable.prod_le_tprod S h_ge_one hmult


lemma HWY_ineq_52_2 [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]: ∀ n : ℕ,
  (∏ k ∈ Finset.range (n+1), (1 + (η_k k)^2)) *
  (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2)
  ≤ (∏' k : ℕ, (1 + (η_k k)^2)) *
  (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2) := by
   intro n
   gcongr
   -- have h:  0 ≤ ‖ey 1‖^2 := by exact sq_nonneg ‖ey 1‖
   -- have := sq_nonneg ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖
   -- have h1: 0 ≤ τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2 := by exact mul_nonneg  (HWY_thm4_1_ineq' 1) this
   -- have h2:= admm.htau.1
   -- have h3:= sq_pos_of_pos (admm.hρₙ_pos 1)
   -- have h4 : 0 ≤  τ * ρₙ 1^2 := by linarith[mul_pos h2 h3]
   -- have h5 := sq_nonneg ‖A₂ (e₂ 1)‖
   -- have h6 : 0 ≤ τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2 := by exact mul_nonneg h4 h5
   linarith[HWY_ineq_52_ n]
   -- have h:= HWY_Convergence_1_1_1 n
   -- exact HWY_ineq_52_0 n

lemma HWY_ineq_52_3 [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]: ∀ n : ℕ,
  ‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
  + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
  ≤ (∏' k : ℕ, (1 + (η_k k)^2)) *
  (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2)
  := by
  intro n
  have h1 := HWY_ineq_52_2 n
  have h2 := HWY_ineq_52_ n
  have h3 := HWY_ineq_52_1 n
  linarith

lemma HWY_ineq_52_4 [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]:  (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2) ≥ 0 := by
   have h1 : 0 ≤ ‖ey 1‖^2 := by exact sq_nonneg ‖ey 1‖
   have := sq_nonneg ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖
   have h1: 0 ≤ τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2 := by exact mul_nonneg  (HWY_thm4_1_ineq' 1) this
   have h2:= admm.htau.1
   have h3:= sq_pos_of_pos (admm.hρₙ_pos 1)
   have h4 : 0 ≤  τ * ρₙ 1^2 := by linarith[mul_pos h2 h3]
   have h5 := sq_nonneg ‖A₂ (e₂ 1)‖
   have h6 : 0 ≤ τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2 := by exact mul_nonneg h4 h5
   linarith

lemma HWY_ineq_52 [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]: ∃ P >0 , ∀ n : ℕ, ‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
  + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
  ≤ P * (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2):= by
   obtain ⟨P, hP_pos, hP⟩ := Condition_C1.one_eta_square_multipliable'
   use P
   constructor
   · exact hP_pos
   intro n
   have h1 := HWY_ineq_52_3 n
   have h2 : (∏' k : ℕ, (1 + (η_k k)^2)) * (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2) ≤ P * (‖ey 1‖^2 + τ * ρₙ (1)^2  * ‖A₂ (e₂ 1)‖^2
  + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2):= by
      exact mul_le_mul_of_nonneg_right hP HWY_ineq_52_4
   exact le_trans h1 h2

lemma HWY_ineq_53 [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]: ∃ C > 0, ∀ n : ℕ+,
‖ey n‖^2 + τ * ρₙ n^2 * ‖A₂ (e₂ n)‖^2
  + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 ≤ C := by
   obtain ⟨C, hC_pos, hC⟩ := HWY_ineq_52
   use C * (‖ey 1‖^2 + τ * ρₙ 1^2 * ‖A₂ (e₂ 1)‖^2 + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2) + 1
   constructor
   ·  apply add_pos_of_nonneg_of_pos
      have := HWY_ineq_52_4
      have:= mul_nonneg (le_of_lt hC_pos) this
      linarith
      norm_num
   ·  intro n
      have h1 := hC (n - 1)
      have h_sub : (↑n : ℕ) - 1 + 1 = (↑n : ℕ) := PNat.natPred_add_one n
      rw [h_sub] at h1
      have h2 := hC n
      linarith
   -- intro n
   -- have h1 := HWY_ineq_52 (n - 1)
   -- have h_sub : (↑n : ℕ) - 1 + 1 = (↑n : ℕ) := PNat.natPred_add_one n
   -- obtain ⟨P, hP_pos, hP⟩ := h1
   -- use P * (‖ey 1‖^2 + τ * ρₙ 1^2 * ‖A₂ (e₂ 1)‖^2 + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2) + 1
   -- rw [h_sub] at hP
   -- constructor
   -- ·  apply add_pos_of_nonneg_of_pos
   --    exact mul_nonneg (le_of_lt hP_pos) HWY_ineq_52_4
   --    norm_num
   -- ·  calc ‖ey n‖^2 + τ * ρₙ n^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 ≤ P * (‖ey 1‖^2 + τ * ρₙ 1^2 * ‖A₂ (e₂ 1)‖^2 + τ * (T_HWY - τ) * ρₙ 1^2 * ‖A₁ (x₁ 1) + A₂ (x₂ 1) - b‖^2) + 1 := by linarith

-- 扩展到自然数（包括0）

lemma HWY_ineq_53_nat [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]: ∃ C > 0, ∀ n : ℕ,
g1 n ≤ C := by
  obtain ⟨C, hC_pos, hC⟩ := HWY_ineq_53
  -- 取 C' = C + 初始值（n=0时的值），确保对所有 n 都成立
  let C₀ := ‖ey 0‖^2 + τ * ρₙ 0^2 * ‖A₂ (e₂ 0)‖^2 + τ * (T_HWY - τ) * ρₙ 0^2 * ‖A₁ (x₁ 0) + A₂ (x₂ 0) - b‖^2
  use max C C₀ + 1
  constructor
  · apply add_pos_of_pos_of_nonneg
    · apply lt_max_iff.mpr
      left
      exact hC_pos
    · norm_num
  · intro n
    by_cases h : n = 0
    · -- n = 0 的情况
      rw [h]
      calc C₀ ≤ max C C₀ := le_max_right C C₀
        _ ≤ max C C₀ + 1 := by linarith
    · -- n > 0 的情况，使用 HWY_ineq_53
      have n_pos : 0 < n := Nat.pos_of_ne_zero h
      calc ‖ey n‖^2 + τ * ρₙ n^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
        ≤ C := hC ⟨n, n_pos⟩
        _ ≤ max C C₀ := le_max_left C C₀
        _ ≤ max C C₀ + 1 := by linarith


lemma g1_nonneg [Setting E₁ E₂ F admm admm_kkt] (n : ℕ) : 0 ≤ g1 n := by
   unfold g1
   apply add_nonneg
   apply add_nonneg
   apply sq_nonneg ‖ey (n)‖
   apply mul_nonneg
   apply mul_nonneg
   apply le_of_lt admm.htau.1
   apply sq_nonneg (ρₙ (n))
   apply sq_nonneg ‖A₂ (e₂ (n))‖
   apply mul_nonneg
   apply mul_nonneg
   have : 0 ≤ T_HWY - τ := by linarith [T_minus_tau_positive]
   apply mul_nonneg
   apply le_of_lt admm.htau.1
   exact this
   apply sq_nonneg (ρₙ (n))
   apply sq_nonneg ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖

theorem summable_of_nonneg_of_le {β : Type*} {f : β → ℝ} {g : β → ℝ}
(hg : ∀ (n : β), 0 ≤ g n) (hgf : ∀ (n : β), g n ≤ f n) (hf : Summable f) :
Summable g:=by
  rw[← NNReal.summable_mk]
  have f_ge_zero :∀ (n : β), 0 ≤ f n := by
   intro n
   apply le_trans (hg n) (hgf n)
  have :∀ (n : β), (⟨g n, hg n⟩ : NNReal) ≤ ⟨f n , f_ge_zero n⟩ := by
   simp only [Subtype.mk_le_mk]
   apply hgf
  apply NNReal.summable_of_le this
  rw[← NNReal.summable_coe]
  exact hf; grind



lemma HWY_ineq_54_0 [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]: ∀ n : ℕ+,
    (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2)
    ≤ - g1 (n+1)
    + (1 + (η_k n)^2)* g1 n := by
   intro n
   have h1 := HWY_ineq_51 n
   unfold g1
   linarith

lemma HWY_ineq_54_1 [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]: ∀ n : ℕ+,
    (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2)
    ≤ h1 n:= by
   intro n
   have := HWY_ineq_54_0 n
   unfold h1
   linarith

lemma g1_summable_0 [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] :∃ C >0,∀ n : ℕ,
    ∑ i ∈ Finset.range n, (η_k (i+1))^2 * g1 (i+1)
   ≤  ∑ i ∈ Finset.range n, (η_k (i+1)^2) * C := by
  obtain ⟨C, hC_pos, hC⟩ := HWY_ineq_53_nat
  use C
  constructor
  exact hC_pos
  intro n
  apply Finset.sum_le_sum
  intro i hi
  refine mul_le_mul' ?_ ?_
  · exact Std.IsPreorder.le_refl (η_k (i+1) ^ 2)
  · exact hC (i+1)

#check Finset.sum_le_sum
lemma g1_summable_0_sum [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] :∀ n : ℕ,
    ∑ i ∈ Finset.range n, (η_k (i+1))^2 ≤ ∑' i : ℕ, (η_k (i+1))^2:= by
      intro n
      let f : ℕ → ℝ:= fun k => (η_k (k+1))^2
      let S : Finset ℕ := Finset.range n
      apply Summable.sum_le_tsum
      have h_ge_zero : ∀ i : ℕ, i ∉ S → (0:ℝ) ≤ f i := by
        intro i _
        show (0 : ℝ) ≤ f i
        simp only [f]
        linarith [sq_nonneg (η_k (i+1))]
      exact h_ge_zero
      let f':ℕ → ℝ:= fun k => (η_k k)^2
      show Summable (fun i => f' (i + 1))
      rw[summable_nat_add_iff 1]
      exact Condition_C1.eta_square_summable'

lemma eta_square_summable [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] : Summable (fun n ↦ η_k (n+1) ^ 2) := by
   let f':ℕ → ℝ:= fun k => (η_k k)^2
   show Summable (fun i => f' (i + 1))
   rw[summable_nat_add_iff 1]
   exact Condition_C1.eta_square_summable'

lemma eta_square_summable' [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] :
∃ S > 0, ∑' (n : ℕ), η_k (n+1) ^ 2 ≤ S := by
   obtain ⟨C, hC_pos, hC⟩ := Condition_C1.eta_square_summable
   use C
   constructor
   exact hC_pos
   have:∑' (n : ℕ), η_k (n) ^ 2 ≥ ∑' (n : ℕ), η_k (n+1) ^ 2 := by
      rw [tsum_eq_zero_add']
      have h1:= sq_nonneg (η_k 0)
      linarith
      exact eta_square_summable
   calc ∑' (n : ℕ), η_k (n+1) ^ 2
       ≤ ∑' (n : ℕ), η_k n ^ 2 := this
     _ ≤ C := hC




lemma g1_summable_0_sum' [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] :
   ∃ C >0 ,∀ n : ℕ,
   ∑ i ∈ Finset.range n, (η_k (i+1))^2 ≤ C := by
   obtain ⟨C, hC_pos, hC⟩ :=  eta_square_summable'
   use C
   constructor
   ·  exact hC_pos
   ·  intro n
      have h1 := g1_summable_0_sum n
      linarith

lemma g1_summable_1 [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] :∃ C >0,∀ n : ℕ,
    ∑ i ∈ Finset.range n, (η_k (i+1))^2 * g1 (i+1)
   ≤  C := by
   obtain ⟨C1, hC_pos1,hC1⟩ := g1_summable_0
   obtain ⟨C2, hC_pos2, hC2⟩ := g1_summable_0_sum'
   use C1 * C2
   constructor
   exact mul_pos hC_pos1 hC_pos2
   intro n
   have h1 := hC1 n
   have h2 := hC2 n
   have : (∑ i ∈ Finset.range n, (η_k (i+1))^2) * C1 ≤ C2 * C1 := by
      gcongr
   have :(∑ i ∈ Finset.range n, (η_k (i+1))^2) * C1 = ∑ i ∈ Finset.range n, (η_k (i+1))^2 * C1 := by
      rw [Finset.sum_mul]
   linarith

lemma h1_summable_0 [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] : ∀ n : ℕ, ∑ i ∈ Finset.range n, h1 (i+1) = g1 1 - g1 (n+1) + ∑ i ∈ Finset.range n, (η_k (i+1))^2* (g1 (i+1)) := by
   intro n
   calc
      _ = ∑ i ∈ Finset.range n, (- g1 (i+1+1) + (1 + (η_k (i+1))^2)* (g1 (i+1))) := by
         unfold h1
         simp
      _ = ∑ i ∈ Finset.range n, ( g1 (i+1) - g1 (i+1+1) +  (η_k (i+1))^2 * (g1 (i+1))):= by
         congr
         ext i
         ring_nf
      _ = ∑ i ∈ Finset.range n, ( g1 (i+1) - g1 (i+1+1)) + ∑ i ∈ Finset.range n, (η_k (i+1))^2 * (g1 (i+1)) := by
         rw[Finset.sum_add_distrib]
      _ = g1 1 - g1 (n+1) + ∑ i ∈ Finset.range n,  (η_k (i+1))^2 * (g1 (i+1)) := by
         rw[Finset.sum_range_sub']

lemma h1_summable_1 [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] : ∃ C >0,∀ n : ℕ, ∑ i ∈ Finset.range n, h1 (i+1) ≤ C := by
   rcases g1_summable_1 with ⟨C1,hC_pos1,hC1⟩
   rcases HWY_ineq_53_nat with ⟨C2,hC_pos2,hC2⟩
   use 2* C2 + C1
   constructor
   exact add_pos (mul_pos (by norm_num) hC_pos2) hC_pos1
   intro n
   rw [h1_summable_0]
   have := g1_nonneg 1
   have := g1_nonneg (n+1)
   have := hC1 (n)
   have := hC2 (n+1)
   have := hC2 1
   gcongr
   linarith

lemma h1_eq' [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]:∀ n : ℕ+, (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2)
≤ h1 n := by
   intro n
   have h := HWY_ineq_54_0 n
   unfold h1
   linarith

lemma h1_eq'' [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] : ∀ n : ℕ, h1 (n+1) ≥ (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+2)^2 *
   (‖A₁ (x₁ (n+2)) + A₂ (x₂ (n+2)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ (n+2))‖^2) := by
   intro n
   have : n+1>0 := by linarith
   have h := h1_eq' (n+1).toPNat'
   exact h

lemma h1_eq''' [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] : ∀ n : ℕ,(1/3) * (1 + τ - τ^2) * τ * ρₙ (n+2)^2 *
   (‖A₁ (x₁ (n+2)) + A₂ (x₂ (n+2)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ (n+2))‖^2)≥ 0:= by
   intro n
   have h1:= admm.htau.1
   have h2:=admm.htau_range
   have h3:= sq_pos_of_pos (admm.hρₙ_pos (n+2))
   have h4:= mul_pos h1 h2
   have h5:= mul_pos h4 h3
   have :(1 + τ - τ^2) * τ * ρₙ (n+2)^2 ≥ 0 := by linarith[h5]
   have h6:= sq_nonneg ‖A₁ (x₁ (n+2)) + A₂ (x₂ (n+2)) - b‖
   have h7:= sq_nonneg ‖A₂ (x₂ (n+1)- x₂ (n+2))‖
   have h8:= add_nonneg h6 h7
   have h9:= mul_nonneg this h8
   linarith


lemma h1_nonneg [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] : ∀ n : ℕ, h1 (n+1) ≥ 0:= by
   intro n
   have := h1_eq'' n
   have : n+1>0 := by linarith
   have := h1_eq''' n
   linarith

lemma  h1_summable [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ] :  Summable (fun n : ℕ => h1 (n+1)) := by
   rcases h1_summable_1 with ⟨C, hC_pos, hC⟩
   apply summable_of_sum_range_le (c:=C)
   intro n
   have :=h1_nonneg n
   linarith
   intro n
   have := hC n
   linarith

lemma HWY_ineq_54 [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]:∀ (n : ℕ), ∑ i ∈ Finset.range n, (1/3) * (1 + τ - τ^2) * τ * ρₙ (i+1+1)^2 *
   (‖A₁ (x₁ (i+1+1)) + A₂ (x₂ (i+1+1)) - b‖^2 + ‖A₂ (x₂ (i+1) - x₂ (i+1+1))‖^2) ≤
   ∑ i ∈ Finset.range n, h1 (i+1) := by
   intro n
   gcongr with i _
   have : i+1 > 0 := by linarith
   have h1 := HWY_ineq_54_1 (i+1).toPNat'
   exact h1

lemma Summable_1' [Condition_C1 admm admm_kkt][IsOrderedMonoid ℝ]:∀ (i : ℕ),  (1/3) * (1 + τ - τ^2) * τ * ρₙ (i+1+1)^2 *
   (‖A₁ (x₁ (i+1+1)) + A₂ (x₂ (i+1+1)) - b‖^2 + ‖A₂ (x₂ (i+1) - x₂ (i+1+1))‖^2) ≤
   h1 (i+1) := by
   intro i
   have : i+1 > 0 := by linarith
   have h1 := HWY_ineq_54_1 (i+1).toPNat'
   exact h1

lemma Summable_1 [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ]:
   Summable (fun n => (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
   (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n) - x₂ (n+1))‖^2)) := by
   let f := fun n => (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
   (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n) - x₂ (n+1))‖^2)
   show Summable f
   rw[← summable_nat_add_iff 1]
   let fsucc := fun n => (f (n+1))
   show Summable fsucc
   apply summable_of_nonneg_of_le
   unfold fsucc
   unfold f
   intro n
   have := h1_eq''' n
   linarith
   exact Summable_1'
   exact h1_summable

lemma converge_zero [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ]: Tendsto (fun n => (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n) - x₂ (n+1))‖^2)) atTop (nhds 0) := by
  apply Summable.tendsto_atTop_zero Summable_1

-- 主要收敛定理：残差项趋于零
theorem HWY_Convergence_1 [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ]:
    Tendsto (fun n => ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ n)‖^2) atTop (nhds 0) := by
   obtain ⟨ BL, hBL_pos, hBL⟩ := admm.rho_lower_bound
  -- 关于τ的条件
   have htau_pos : 0 < τ := admm.htau.1
   have htau_range := admm.htau_range
   -- 构造常数下界
   have hconst : 0 < (1/3) * (1 + τ - τ^2) * τ * BL^2 := by
      apply mul_pos
      apply mul_pos
      apply mul_pos
      · linarith
      · exact admm.htau_range
      · exact admm.htau.1
      · apply sq_pos_of_pos; exact hBL_pos
   -- 关键：利用范数的对称性
   have norm_symm : ∀ n, ‖A₂ (x₂ (n) - x₂ (n+1))‖ = ‖A₂ (x₂ (n+1) - x₂ n)‖ := by
      intro n
      rw [← norm_neg]
      congr 1
      simp [sub_eq_add_neg, add_comm]
   -- 从converge_zero得到的结论
   have h_conv := converge_zero
   -- 利用夹逼定理
   have h_squeeze : ∀ n, (1/3) * (1 + τ - τ^2) * τ * BL^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ n)‖^2)
                        ≤ (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n) - x₂ (n+1))‖^2) := by
      intro n
      rw [norm_symm n]
      gcongr
      apply hBL (n+1)
   have h_pos : ∀ n, (1/3) * (1 + τ - τ^2) * τ * BL^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ n)‖^2)≥ 0:= by
      intro n
      apply mul_nonneg
      linarith [hconst]
      apply add_nonneg
      apply sq_nonneg
      apply sq_nonneg
   -- 应用夹逼定理得到结论
   have h_lower : Tendsto (fun n => (1/3) * (1 + τ - τ^2) * τ * BL^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ n)‖^2)) atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      exact tendsto_const_nhds
      exact h_conv
      exact h_pos
      exact h_squeeze
   -- 除以正常数不改变极限为零
   rw [show (0 : ℝ) =  ((1/3) * (1 + τ - τ^2) * τ * BL^2 * 0) by simp] at h_lower
   have := Tendsto.const_mul ((1/3) * (1 + τ - τ^2) * τ * BL^2)⁻¹ h_lower
   field_simp at this
   exact this
#check tendsto_add_atTop_iff_nat

-- 第一项：残差项趋于零
theorem HWY_Convergence_1_residual' [IsOrderedMonoid ℝ][Condition_C1 admm admm_kkt][Setting E₁ E₂ F admm admm_kkt]:
    Tendsto (fun n => ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2) atTop (nhds 0) := by
  have h_sum := HWY_Convergence_1
  have h_nonneg : ∀ n, 0 ≤ ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 := by
    intro n
    apply sq_nonneg
  have h_bound : ∀ n, ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
                      ≤ ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ n)‖^2 := by
    intro n
    have h_nonneg2 : 0 ≤ ‖A₂ (x₂ (n+1) - x₂ n)‖^2 := sq_nonneg _
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
  · exact tendsto_const_nhds
  · exact h_sum
  · exact h_nonneg
  · exact h_bound

theorem HWY_Convergence_1_increment [Condition_C1 admm admm_kkt] [IsOrderedMonoid ℝ]:
    Tendsto (fun n => ‖A₂ (x₂ (n+1) - x₂ n)‖^2) atTop (nhds 0) := by
   have h_sum := HWY_Convergence_1
   have h_nonneg : ∀ n, 0 ≤ ‖A₂ (x₂ (n+1) - x₂ n)‖^2 := by
         intro n
         apply sq_nonneg
   have h_bound : ∀ n, ‖A₂ (x₂ (n+1) - x₂ n)‖^2
                        ≤ ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ n)‖^2 := by
         intro n
         have h_nonneg1 : 0 ≤ ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 := sq_nonneg _
         linarith
   apply tendsto_of_tendsto_of_tendsto_of_le_of_le
   · exact tendsto_const_nhds
   · exact h_sum
   · exact h_nonneg
   · exact h_bound

#check inv_mul_cancel_left₀

#check summable_of_nonneg_of_le



end AdaptiveADMM_Convergence_Proof
