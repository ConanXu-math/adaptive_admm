import Optlib.Algorithm.AdaptiveADMM.AdaptiveEnergyIdentities
import Optlib.Algorithm.AdaptiveADMM.SequenceConvergence

noncomputable section
open Set InnerProductSpace Topology Filter InnerProduct
open scoped Pointwise

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F ]

namespace AdaptiveADMM_Convergence_Proof

variable {admm : ADMM E₁ E₂ F} {admm_kkt : KKTPoint admm}

-- shorthand
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

local notation "x₁'" => admm_kkt.x₁
local notation "x₂'" => admm_kkt.x₂
local notation "y'"  => admm_kkt.y

local notation "A₁†" => ContinuousLinearMap.adjoint A₁
local notation "A₂†" => ContinuousLinearMap.adjoint A₂
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

local notation "e₁" => AdaptiveADMM_Convergence_Proof.e₁ admm admm_kkt
local notation "e₂" => AdaptiveADMM_Convergence_Proof.e₂ admm admm_kkt
local notation "ey" => AdaptiveADMM_Convergence_Proof.ey admm admm_kkt
local notation "g1" => AdaptiveADMM_Convergence_Proof.g1 admm admm_kkt
local notation "g2" => AdaptiveADMM_Convergence_Proof.g2 admm admm_kkt
local notation "u" => AdaptiveADMM_Convergence_Proof.u admm admm_kkt
local notation "v" => AdaptiveADMM_Convergence_Proof.v admm admm_kkt
local notation "Ψ" => AdaptiveADMM_Convergence_Proof.Ψ admm admm_kkt
local notation "Φ" => AdaptiveADMM_Convergence_Proof.Φ admm admm_kkt
local notation "T_HWY" => AdaptiveADMM_Convergence_Proof.T_HWY admm
local notation "υ" => AdaptiveADMM_Convergence_Proof.υ admm

set_option maxHeartbeats 200000 in
lemma HWY_eq34 : ∀ n : ℕ+,
       ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 ≥
       ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n+1) - x₂ n)‖^2
       + 2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ A₁ (x₁ n) + A₂ (x₂ n) - b, (A₂ (x₂ n - x₂ (n+1))) ⟫  := by
   intro n
   have h := Φ_isdescending_inequ5 (admm_kkt := admm_kkt) n
   have hτ_pos : 0 < τ := admm.htau.1
   have hρ_pos : 0 < ρₙ (n+1) := admm.hρₙ_pos (n+1)
   have hτρ_ne : τ * ρₙ (n+1) ≠ 0 := mul_ne_zero (ne_of_gt hτ_pos) (ne_of_gt hρ_pos)
   -- Rewrite M(n+1) using HWY_Lemma_3_2.
   have hM : (M admm) (n+1) = (1 - τ) * ρₙ n * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫ := by
     simp [ AdaptiveADMM_Convergence_Proof.M]
   -- Reverse the inner-product arguments.
   have hM' : (M admm) (n+1) = (1 - τ) * ρₙ n * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ (n+1) - x₂ n)) ⟫ := by
     rw [hM, real_inner_comm]
   -- Reverse the subtraction.
   have hM'' : 2 * (M admm) (n+1) = 2 * (1 - τ) * ρₙ n * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (-(A₂ (x₂ n - x₂ (n+1)))) ⟫ := by
     rw [hM']
     have : A₂ (x₂ (n+1) - x₂ n) = -(A₂ (x₂ n - x₂ (n+1))) := by simp
     rw [← this]
     ring

   have hM''' : 2 * (M admm) (n+1) = -2 * (1 - τ) * ρₙ n * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫ := by
     rw [hM'']
     rw [inner_neg_right]
     ring
   -- Multiply both sides by τ * ρₙ(n+1) and expand.
   have h_expand : τ * ρₙ (n+1) * (1 / (τ * ρₙ (n+1)) * (‖ey n‖^2 - ‖ey (n+1)‖^2) - (2 - τ) * ρₙ (n+1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + 2 * (M admm) (n+1) - ρₙ (n+1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 - ρₙ (n+1) * ‖A₂ (e₂ (n+1))‖^2 + ρₙ (n+1) * ‖A₂ (e₂ n)‖^2) ≥ 0 := by
     apply mul_nonneg (mul_nonneg (le_of_lt hτ_pos) (le_of_lt hρ_pos)) h
   -- Substitute the expression for M and simplify.
   calc ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2
     = ‖ey n‖^2 + τ * ρₙ (n+1) * (ρₙ (n+1) * ‖A₂ (e₂ n)‖^2) := by ring
     _ ≥ ‖ey (n+1)‖^2 + τ * ρₙ (n+1) * (ρₙ (n+1) * ‖A₂ (e₂ (n+1))‖^2)
         + τ * ρₙ (n+1) * ((2 - τ) * ρₙ (n+1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2)
         + τ * ρₙ (n+1) * (ρₙ (n+1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2)
         + τ * ρₙ (n+1) * (-2 * (M admm) (n+1)) := by
       field_simp [hτρ_ne] at h_expand
       linarith only [h_expand]
     _ = ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
         + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
         + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n+1) - x₂ n)‖^2
         + 2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫ := by
       simp
       rw [hM''']
       simp
       ring


include admm_kkt in
lemma HWY_Lemma_3_2  :
   ∀ n : ℕ+,
      ρₙ (n+1) * ⟪ (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫
      ≥ (1 - τ) * ρₙ n * ⟪(A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1)))⟫ := by
   intro n
   have h1 :
         ρₙ (n+1) *
         ⟪ (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b), (A₂ (x₂ (n+1) - x₂ n)) ⟫
      ≤ (1 - τ) * ρₙ n *
         ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ (n+1) - x₂ n)) ⟫ := by
      simpa [ AdaptiveADMM_Convergence_Proof.M, real_inner_comm] using Φ_isdescending_inequ3 (admm_kkt := admm_kkt) n
   have key :A₂ (x₂ (n+1) - x₂ n) = - A₂ (x₂ n - x₂ (n+1)) := by
         simp
   rw [key] at h1
   rw [inner_neg_right, inner_neg_right, mul_neg, mul_neg] at h1
   rw [neg_le_neg_iff] at h1
   exact ge_iff_le.1 h1




lemma T_minus_tau_positive : T_HWY - τ ≥ 3/8 := by
   simp only [ AdaptiveADMM_Convergence_Proof.T_HWY]
   have h : 2 - 1/2 * (1 + τ - τ^2) - τ = 1/2 * (τ^2 - 3*τ + 3) := by ring
   rw [h]
   have h2 : τ^2 - 3*τ + 3 = (τ - 3/2)^2 + 3/4 := by ring
   rw [h2]
   have h3 : (τ - 3/2)^2 ≥ 0 := sq_nonneg _
   linarith

lemma HWY_eq35  :
  ∀ n : ℕ+,
    2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫
  ≥ - τ * (T_HWY - τ) * (ρₙ n)^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
    - (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ n - x₂ (n+1))‖^2 := by
  intro n
  -- Simplify notation.
  set residualVec := A₁ (x₁ n) + A₂ (x₂ n) - b
  set incrementVec := A₂ (x₂ n - x₂ (n+1))
  set ε := τ * (T_HWY - τ)
  -- Positivity of the constants.
  have hτ_pos : 0 < τ := admm.htau.1
  have hT_pos : 0 < T_HWY - τ := by linarith [T_minus_tau_positive (admm := admm)]
  have hε_pos : 0 < ε := mul_pos hτ_pos hT_pos
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hsqrtε_ne : (Real.sqrt ε) ≠ 0 := Real.sqrt_ne_zero'.mpr hε_pos

  -- Scaled vectors.
  let xu := (Real.sqrt ε * ρₙ n) • residualVec
  let yv := ((τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1)) • incrementVec

  -- Apply Cauchy-Schwarz to obtain the desired inequality.
  -- 1. ⟪x, y⟫ ≤ ‖x‖‖y‖
  have hCS : |⟪ xu, yv ⟫| ≤ ‖xu‖ * ‖yv‖ := by
    simpa using abs_real_inner_le_norm xu yv

  -- 2. AM-GM: 2‖x‖‖y‖ ≤ ‖x‖² + ‖y‖².
  have hAMGM : 2 * (‖xu‖ * ‖yv‖) ≤ ‖xu‖^2 + ‖yv‖^2 := by
    have := sq_nonneg (‖xu‖ - ‖yv‖)
    ring_nf at this
    linarith

  -- 3. -2⟪x,y⟫ ≤ 2|⟪x,y⟫|
  have hneg : -2 * (⟪ xu, yv ⟫ : ℝ) ≤ 2 * |⟪ xu, yv ⟫| := by
    have : -(⟪ xu, yv ⟫ : ℝ) ≤ |⟪ xu, yv ⟫| := neg_le_abs _
    linarith

  -- 4. Combine the inequalities.
  have base : -2 * ⟪ xu, yv ⟫ ≤ ‖xu‖^2 + ‖yv‖^2 := by
    linarith [hneg, hCS, hAMGM]

  -- Rewrite the left side from inner x y to inner residualVec incrementVec.
  have lhs_eq : 2 * ⟪ xu, yv ⟫ = 2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ residualVec, incrementVec ⟫ := by
    simp only [xu, yv, inner_smul_left, inner_smul_right, starRingEnd_apply]
    field_simp [hsqrtε_ne]
    ring_nf
    simp
    ring_nf
  -- Expand the right side into norm terms.
  have hx_sq : ‖xu‖^2 = ε * (ρₙ n)^2 * ‖residualVec‖^2 := by
   --  have : xu = (Real.sqrt ε * ρₙ n) • residualVec := rfl
    simp only [xu]
    simp only [norm_smul]

    simp only [Real.norm_eq_abs (Real.sqrt ε * ρₙ n)]
    have h1 : |Real.sqrt ε * ρₙ n| = Real.sqrt ε * ρₙ n := by
      apply abs_of_pos
      exact mul_pos (Real.sqrt_pos.mpr hε_pos) (admm.hρₙ_pos n)
    simp only [h1]
    have h2 : (Real.sqrt ε * ρₙ n * ‖residualVec‖)^2 = (Real.sqrt ε * ρₙ n)^2 * ‖residualVec‖^2 := by ring
    simp only [h2]
    have h3 : (Real.sqrt ε * ρₙ n)^2 = (Real.sqrt ε)^2 * (ρₙ n)^2 := by ring
    rw [h3, Real.sq_sqrt hε_nonneg]

  have hy_sq : ‖yv‖^2 = (τ * (1 - τ))^2 / ε * (ρₙ (n+1))^2 * ‖incrementVec‖^2 := by
    simp only [yv, norm_smul]
    simp only [Real.norm_eq_abs ((τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1))]
    have h1 : |(τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1)| ^ 2
        = (τ * (1 - τ))^2 / (Real.sqrt ε)^2 * (ρₙ (n+1))^2 := by
      field_simp [hsqrtε_ne]
      ring_nf
      simp
      ring_nf
      field_simp
    have h2 : (|(τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1)| * ‖incrementVec‖)^2 = |(τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1)|^2 * ‖incrementVec‖^2 := by ring_nf
    simp only [h2]
    rw [h1, Real.sq_sqrt hε_nonneg]
  -- Apply base and rewrite both sides into the required form.
  have h4 : (τ * (1 - τ))^2 / ε * (ρₙ (n+1))^2 * ‖incrementVec‖^2 = (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖incrementVec‖^2 := by
    simp only [ε]
    field_simp
  have h5 : ε * (ρₙ n)^2 * ‖residualVec‖^2 = τ * (T_HWY - τ) * (ρₙ n) ^2 * ‖residualVec‖^2 := by
    simp only [ε]
  have h6 : ⟪ xu, yv ⟫ = ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ residualVec, incrementVec ⟫ := by
    simp only [xu, yv, inner_smul_left, inner_smul_right, starRingEnd_apply]
    field_simp [hsqrtε_ne]
    ring_nf
    simp
    ring_nf
  have := base
  simp only [hx_sq, hy_sq] at this
  rw [h4] at this
  rw [h5] at this
  rw [h6] at this
  rw [← neg_le_neg_iff] at this
  linarith

lemma norm_sq_A₂_increment_symm  : ∀ n : ℕ+,
  ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 = ‖A₂ (x₂ (n+1) - x₂ (n))‖^2 := by
    intro n
    have h : A₂ (x₂ (n) - x₂ (n+1)) = A₂ (x₂ n) - A₂ (x₂ (n+1)) := by
      simp
    have h2 : A₂ (x₂ n) - A₂ (x₂ (n+1))=  - A₂ (x₂ (n+1) - x₂ (n)) := by
      simp
    rw [h]
    rw [h2]
    rw [norm_neg]

lemma energy_step_add_residual  : ∀ n : ℕ+,
 ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2≥
       ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
       + 2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫ + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2:= by
   intro n
   rw [norm_sq_A₂_increment_symm n]
   linarith [HWY_eq34 (admm_kkt := admm_kkt) n]

lemma energy_step_bound_cross_term  : ∀ n : ℕ+,
   ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n)^2 * ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2≥
       ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
       - τ * (T_HWY - τ) * (ρₙ n)^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
    - (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
       + τ * (T_HWY - τ) * ρₙ (n)^2 * ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2:= by
      intro n
      linarith [HWY_eq35 (admm := admm) n, energy_step_add_residual (admm_kkt := admm_kkt) n]
lemma energy_step_with_dissipation  : ∀ n : ℕ+,
      ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n)^2* ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2 ≥
       ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (T_HWY - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 )   := by
      intro n
      calc
         _ ≥‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
         + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
         + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
         - τ * (T_HWY - τ) * (ρₙ n)^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
         + τ * (T_HWY - τ) * ρₙ (n)^2 * ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2 :=by exact energy_step_bound_cross_term n
         _ = ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 ):= by ring_nf
lemma energy_step_le_sub_dissipation   : ∀ n : ℕ+,
      ‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
      + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
      ≤ ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2
      + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      -  τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 ):= by
         intro n
         have h : ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (T_HWY - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 ) ≤ ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n)^2* ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2 := by exact energy_step_with_dissipation n

         linarith

lemma T_sub_tau_eq_quadratic  :T_HWY - τ = 1/2*(τ^2-3*τ+3):= by
      simp only [ AdaptiveADMM_Convergence_Proof.T_HWY]
      ring_nf


lemma one_sub_ratio_eq_quadratic_quotient  :  1 - (1 - τ)^2 / (1/2*(τ^2-3*τ+3)) = (τ^2 -3*τ +3- 2 *(1 - τ)^2) / (τ^2-3*τ+3):= by
   have hpos : 0 < (τ^2 - 3*τ + 3 : ℝ) := by
      have : (τ^2 - 3*τ + 3 : ℝ) = (τ - (3/2))^2 + (3/4) := by ring
      have hsq : 0 ≤ (τ - (3/2))^2 := by exact sq_nonneg _
      have h34 : 0 < (3/4 : ℝ) := by norm_num
      have h:= add_pos_of_nonneg_of_pos hsq h34
      rw [this]
      exact h
   field_simp [hpos]
   refine one_sub_div ?_
   linarith



lemma dissipation_coefficient_eq  : 1 - (1 - τ)^2 / (T_HWY - τ) = (1 + τ - τ ^2) / ( 3 - 3 * τ +τ ^2) := by
    rw [T_sub_tau_eq_quadratic]
    rw [one_sub_ratio_eq_quadratic_quotient]
    ring_nf

lemma tau_quadratic_bounds  :
  3/4 ≤ τ^2 - 3*τ + 3 ∧ τ^2 - 3*τ + 3 ≤ 3 := by
  constructor
  · -- Prove 3/4 ≤ τ^2 - 3*τ + 3.
    have : τ^2 - 3*τ + 3 = (τ - 3/2)^2 + 3/4 := by ring
    rw [this]
    have : 0 ≤ (τ - 3/2)^2 := sq_nonneg _
    linarith
  · have h : τ^2 - 3*τ + 3 = (τ - 3/2)^2 + 3/4 := by ring
    rw [h]
    have : 0 ≤ (τ - 3/2)^2 := sq_nonneg _
    have h1 : 0 < τ := admm.htau.1
    have h2 : τ < (1 + Real.sqrt 5)/2 := admm.htau.2
    -- First prove (1 + √5)/2 ≤ 2.
    have hsqrt : Real.sqrt (5:ℝ) ≤ 3 := by
      have hb : (0:ℝ) ≤ (3:ℝ) := by norm_num
      have h5le9 : (5:ℝ) ≤ (3:ℝ)^2 := by norm_num
      exact (Real.sqrt_le_left hb).mpr h5le9
    have hup : (1 + Real.sqrt (5:ℝ)) / 2 ≤ (2:ℝ) := by
      -- (1 + √5)/2 ≤ 2  ↔  1 + √5 ≤ 4
      have : 1 + Real.sqrt (5:ℝ) ≤ 2 * 2 := by linarith
      linarith

    -- Deduce τ ≤ 2.
    have hτ_le2 : τ ≤ 2 := le_trans (le_of_lt h2) hup

    -- Hence |τ - 3/2| ≤ 3/2.
    have hleft  : -(3/2 : ℝ) ≤ τ - 3/2 := by
      have : (0:ℝ) ≤ τ := le_of_lt h1
      linarith
    have hright : τ - 3/2 ≤ (3/2 : ℝ) := by
      have : τ ≤ 2 := hτ_le2
      linarith
    -- Square and add 3/4 to obtain the upper bound 3.
    have hsq : (τ - 3/2)^2 ≤ (3/2 : ℝ)^2 := by
      exact sq_le_sq' hleft hright
      -- |a| ≤ b ⇒ a^2 ≤ b^2
    have : (τ - 3/2)^2 + 3/4 ≤ (3/2 : ℝ)^2 + 3/4 :=
      add_le_add_right hsq _
    -- (3/2)^2 + 3/4 = 9/4 + 3/4 = 3
    linarith

lemma thm3_1_ineq1  :
  1 - (1 - τ)^2 / (T_HWY - τ) ≥ (1/3 : ℝ) * (1 + τ - τ^2) := by
  rw [dissipation_coefficient_eq]
  rcases tau_quadratic_bounds (admm := admm) with ⟨h1, h2⟩
  -- Let D = τ^2 - 3τ + 3.
  set D : ℝ := τ^2 - 3*τ + 3 with hD

  -- D is positive and bounded above by 3.
  have hD_pos : 0 < D := by
    have : (0 : ℝ) < 3/4 := by norm_num
    exact lt_of_lt_of_le this (by simpa [hD] using h1)
  have hD_le3 : D ≤ 3 := by simpa [hD] using h2

  -- Deduce 1/3 ≤ 1/D.
  have inv_ge : (1/3 : ℝ) ≤ 1 / D := by
    -- one_div_le_one_div_of_le : 0 < a → a ≤ b → 1/b ≤ 1/a
    -- Take a = D and b = 3.
    simpa [one_div] using (one_div_le_one_div_of_le hD_pos hD_le3)

  -- The numerator is nonnegative by weakening the strict inequality.
  have hA_nonneg : 0 ≤ 1 + τ - τ^2 := (admm.htau_range).le

  -- Multiply by the nonnegative numerator.
  have hmul := mul_le_mul_of_nonneg_left inv_ge hA_nonneg
  -- Rearrange into the target form.
  simp only [hD] at hmul
  field_simp at hmul
  field_simp
  have h: 3*(1-τ) + τ^2 = τ*(τ-3) + 3:= by ring
  rw [← h] at hmul
  linarith



lemma thm3_1_eq1  : 2-T_HWY = 1/2*(1+τ-τ^2):= by
  rw [ AdaptiveADMM_Convergence_Proof.T_HWY]
  ring_nf

lemma thm3_1_ineq3  : ∀ n : ℕ+,
   - τ * (ρₙ (n+1))^2 * ((1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) ≤
   - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
         (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := by
   intro n
   have h : τ * (ρₙ (n+1))^2 > 0 := by exact mul_pos (admm.htau.1) (pow_pos (admm.hρₙ_pos (n+1)) 2)
   have hA_nonneg : 0 ≤  1 + τ - τ^2 := (admm.htau_range).le
   have h2 : 1/2*(1+τ-τ^2) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 ≥ 1/3 * (1 + τ - τ^2)* ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2:= by
      gcongr
      norm_num
   have h4 : (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ≥ 1/3 * (1 + τ - τ^2)* ‖A₂ (x₂ n - x₂ (n+1))‖^2:= by
      gcongr
      linarith [thm3_1_ineq1 (admm := admm)]
   have h1 : (1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ≥ (1/3) * (1 + τ - τ^2)*(‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
      linarith [h2, h4]
   have h5 : - ((1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) ≤  -(1/3) * (1 + τ - τ^2)*(‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
      linarith [h1]
   have h6 := mul_le_mul_of_nonneg_left h5 (le_of_lt h)
   linarith [h6]


theorem HWY_Theorem_3_1  : ∀ n : ℕ+,
‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
+ τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
≤ ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2
+ τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
- (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := by
   intro n
   calc _ ≤ ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2 +
      τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) := by exact energy_step_le_sub_dissipation n
       _ = ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2 +
      τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
       - τ * (ρₙ (n+1))^2 * ((1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) := by simp [thm3_1_eq1]
       _ ≤  ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2 +
      τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
         (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
        linarith [thm3_1_ineq3 (admm := admm) n]

lemma HWY_thm4_1_ineq  :T_HWY - τ >0 := by
   rw[T_sub_tau_eq_quadratic]
   have hpos : 0 < (τ^2 - 3*τ + 3 : ℝ) := by
      have : (τ^2 - 3*τ + 3 : ℝ) = (τ - (3/2))^2 + (3/4) := by ring
      have hsq : 0 ≤ (τ - (3/2))^2 := by exact sq_nonneg _
      have h34 : 0 < (3/4 : ℝ) := by norm_num
      have h:= add_pos_of_nonneg_of_pos hsq h34
      rw [this]
      exact h
   linarith


end AdaptiveADMM_Convergence_Proof
