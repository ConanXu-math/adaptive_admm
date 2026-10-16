import Optlib.Algorithm.AdaptiveADMM.ClusterPointC1
noncomputable section

open Set InnerProductSpace Topology Filter Bornology Metric Real

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

variable(admm : ADMM E₁ E₂ F)

namespace AdaptiveADMM_Convergence_Proof

variable {admm} (admm_kkt : KKTPoint admm)

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

include admm_kkt

variable (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂)
-- Subsequence mapping
local notation "φ" => Converge_Subseq_1.φ (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

-- The point of the subsequence convergence
local notation "x₁''" => Converge_Subseq_1.x₁'' (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
local notation "x₂''" => Converge_Subseq_1.x₂'' (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
local notation "y''"  => Converge_Subseq_1.y'' (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

local notation "limitKKT" => admm_kkt_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
local notation "e₁" => AdaptiveADMM_Convergence_Proof.e₁ admm limitKKT
local notation "e₂" => AdaptiveADMM_Convergence_Proof.e₂ admm limitKKT
local notation "ey" => AdaptiveADMM_Convergence_Proof.ey admm limitKKT
local notation "g1" => AdaptiveADMM_Convergence_Proof.g1 admm limitKKT
local notation "g2" => AdaptiveADMM_Convergence_Proof.g2 admm limitKKT
local notation "u" => AdaptiveADMM_Convergence_Proof.u admm limitKKT
local notation "v" => AdaptiveADMM_Convergence_Proof.v admm limitKKT
local notation "Ψ" => AdaptiveADMM_Convergence_Proof.Ψ admm limitKKT
local notation "Φ" => AdaptiveADMM_Convergence_Proof.Φ admm limitKKT
local notation "g1_hat" => AdaptiveADMM_Convergence_Proof.g1_hat admm limitKKT
local notation "T_HWY" => AdaptiveADMM_Convergence_Proof.T_HWY admm
local notation "υ" => AdaptiveADMM_Convergence_Proof.υ admm
local notation "η_k" => AdaptiveADMM_Convergence_Proof.η_k admm
local notation "Q_seq_c1" => AdaptiveADMM_Convergence_Proof.Q_seq_c1 admm

lemma e₁_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (e₁ ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (x₁ ∘ φ) n - x₁'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply x₁_subseq_converge_c1 (admm_kkt := admm_kkt)
   have h₂: (fun n => (x₁ ∘ φ) n - x₁'') = (fun n => e₁ (φ n)) := by
      funext n; rw [ AdaptiveADMM_Convergence_Proof.e₁];simp; simp [admm_kkt_c1];
   rw [h₂] at h₁; apply h₁

-- e₂ (φ n) → 0
-- x₂ (φ n) → (admm_kkt_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂).x₂ = x₂''
lemma e₂_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (e₂ ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (x₂ ∘ φ) n - x₂'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply x₂_subseq_converge_c1 (admm_kkt := admm_kkt)
   have h₂: (fun n => (x₂ ∘ φ) n - x₂'') = (fun n => e₂ (φ n)) := by
      funext n; rw [ AdaptiveADMM_Convergence_Proof.e₂]; simp; simp [admm_kkt_c1]
   rw [h₂] at h₁; apply h₁

-- e₂ (φ n) → 0
-- y (φ n) → (admm_kkt_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂).y = y''
lemma ey_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (ey ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (y ∘ φ) n - y'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply y_subseq_converge_c1 (admm_kkt := admm_kkt)
   have h₂: (fun n => (y ∘ φ) n - y'') = (fun n => ey (φ n)) := by
      funext n; rw [ AdaptiveADMM_Convergence_Proof.ey]; simp; simp [admm_kkt_c1]
   rw [h₂] at h₁; apply h₁

-- ‖ey (φ n)‖ → 0
lemma nrm_ey_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => ‖ey (φ n)‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply ey_subseq_converge_zero_c1 (admm_kkt := admm_kkt)

-- ‖ey (φ n)‖^2 → 0
lemma sqnrm_ey_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => ‖ey (φ n)‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_ey_subseq_converge_zero_c1 (admm_kkt := admm_kkt); linarith

-- A₁ (e₁ (φ n)) → 0
lemma A₁e₁_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => A₁ (e₁ (φ n))) atTop (𝓝 0) := by
   have h₁: Tendsto A₁ (𝓝 0) (𝓝 (A₁ 0)) := by
      apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   simp at h₁; apply Filter.tendsto_iff_seq_tendsto.1 h₁; apply e₁_subseq_converge_zero_c1

-- A₂ (e₂ (φ n)) → 0
lemma A₂e₂_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => A₂ (e₂ (φ n))) atTop (𝓝 0) := by
   have h₁: Tendsto A₂ (𝓝 0) (𝓝 (A₂ 0)) := by
      apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   simp at h₁; apply Filter.tendsto_iff_seq_tendsto.1 h₁; apply e₂_subseq_converge_zero_c1 (admm_kkt := admm_kkt)

-- ‖A₂ (e₂ (φ n))‖ → 0
lemma nrm_A₂e₂_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => ‖A₂ (e₂ (φ n))‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply A₂e₂_subseq_converge_zero_c1 (admm_kkt := admm_kkt)

-- ‖A₂ (e₂ (φ n))‖^2 → 0
lemma sqnrm_A₂e₂_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => ‖A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_A₂e₂_subseq_converge_zero_c1 (admm_kkt := admm_kkt); linarith


-- A₁ (e₁ (φ n)) + A₂ (e₂ (φ n)) → 0
lemma A₁e₁_A₂e₂_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))) atTop (𝓝 0) := by
   rw [← add_zero 0]
   apply Tendsto.add (A₁e₁_subseq_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (A₂e₂_subseq_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

-- ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖ → 0
lemma nrm_A₁e₁_A₂e₂_subseq_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply A₁e₁_A₂e₂_subseq_converge_zero_c1 (admm_kkt := admm_kkt)

-- ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2 → 0
lemma sqnrm_A₁e₁_A₂e₂_subseq_converge_zero_c1[Condition_C1 admm]:
      Tendsto (fun n => ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_A₁e₁_A₂e₂_subseq_converge_zero_c1 (admm_kkt := admm_kkt); linarith



-- Prove g1(φ n) → 0.
lemma g1_subseq_converge_zero
      [Condition_C1 admm] :
      Tendsto (fun n => g1 (φ n)) atTop (nhds 0) := by
   obtain ⟨BU, hBU_pos, hBU⟩ := admm.rho_upper_bound
   have h_rho_sq : ∀ n, ρₙ n ^ 2 ≤ BU ^ 2 := fun n => sq_le_sq' (by linarith [admm.hρₙ_pos n]) (hBU n)
   have h_rho_sq_nonneg : ∀ n, 0 ≤ ρₙ n ^ 2 := fun n => sq_nonneg (ρₙ n)
   have h1 : Tendsto (fun n => ‖ey (φ n)‖^2) atTop (nhds 0) :=
      sqnrm_ey_subseq_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   have h2_inner : Tendsto (fun n => ‖A₂ (e₂ (φ n))‖^2) atTop (nhds 0) :=
      sqnrm_A₂e₂_subseq_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   have h2 : Tendsto (fun n => τ * ρₙ (φ n)^2 * ‖A₂ (e₂ (φ n))‖^2) atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      · exact tendsto_const_nhds -- Constant lower bound zero.
      · -- Upper bound C * ‖A₂e₂‖^2 → 0.
        rw [← mul_zero (τ * BU^2)]
        apply Filter.Tendsto.const_mul (τ * BU^2) h2_inner
      · intro n -- Prove nonnegativity.
        apply mul_nonneg
        apply mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg _)
        apply sq_nonneg
      · intro n -- Prove the upper bound.
        have h_rho_sq_le : ρₙ (φ n) ^ 2 ≤ BU ^ 2 := by exact h_rho_sq (φ n)
        have hscaled : τ * ρₙ (φ n)^2 ≤ τ * BU^2 :=
           mul_le_mul_of_nonneg_left h_rho_sq_le (le_of_lt admm.htau.1)
        exact mul_le_mul_of_nonneg_right hscaled (sq_nonneg _)
   have h3_inner : Tendsto (fun n => ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖^2) atTop (nhds 0) := by
      rw [← zero_pow two_ne_zero]
      apply Tendsto.pow (subconverge_zero₂_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) 2
   have h3 : Tendsto (fun n => τ * (T_HWY - τ) * ρₙ (φ n)^2 * ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖^2) atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      · exact tendsto_const_nhds
      · rw [← mul_zero (τ * (T_HWY - τ) * BU^2)]
        apply Filter.Tendsto.const_mul (τ * (T_HWY - τ) * BU^2) h3_inner
      · intro n
        apply mul_nonneg
        apply mul_nonneg
        apply mul_nonneg (le_of_lt admm.htau.1) (le_of_lt (HWY_thm4_1_ineq (admm := admm)))
        apply sq_nonneg
        apply sq_nonneg
      · intro n
        have hcoef : 0 ≤ τ * (T_HWY - τ) :=
           mul_nonneg (le_of_lt admm.htau.1) (le_of_lt (HWY_thm4_1_ineq (admm := admm)))
        have hscaled :
            τ * (T_HWY - τ) * ρₙ (φ n)^2 ≤
              τ * (T_HWY - τ) * BU^2 :=
           mul_le_mul_of_nonneg_left (h_rho_sq (φ n)) hcoef
        exact mul_le_mul_of_nonneg_right hscaled (sq_nonneg _)
   unfold AdaptiveADMM_Convergence_Proof.g1
   have h_add : Tendsto (fun x => ‖ey (φ x)‖^2 + τ * ρₙ (φ x)^2 * ‖A₂ (e₂ (φ x))‖^2) atTop (𝓝 (0 + 0)) := by
      apply Tendsto.add h1 h2
   have h_add' : Tendsto (fun x => ‖ey (φ x)‖^2 + τ * ρₙ (φ x)^2 * ‖A₂ (e₂ (φ x))‖^2 + τ * (T_HWY - τ) * ρₙ (φ x)^2 * ‖A₁ (x₁ (φ x)) + A₂ (x₂ (φ x)) - b‖^2) atTop (𝓝 (0 + 0 + 0)) := by
      apply Tendsto.add h_add h3
   simp at h_add'
   exact h_add'

lemma g1_hat_tail_antitone [Condition_C1 admm]:
      Antitone (fun n ↦  g1_hat (n + 1)) := by
   apply antitone_nat_of_succ_le
   intro n
   apply g1_hat_succ_le (admm_kkt := limitKKT) (n+1).toPNat'

lemma g1_hat_subseq_converge_zero
       [Condition_C1 admm] :
      Tendsto (fun n => g1_hat (φ n)) atTop (𝓝 0) := by
  simp only [ AdaptiveADMM_Convergence_Proof.g1_hat]
  obtain ⟨P, hP_pos, hQ_conv⟩ := Q_seq_converges_c1 (admm := admm)
  have hQ_sub : Tendsto (fun n => Q_seq_c1 (φ n)) atTop (𝓝 P) :=
    hQ_conv.comp (hphi_StrictMono_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂).tendsto_atTop
  have hg_sub : Tendsto (fun n => g1 (φ n)) atTop (𝓝 0) :=
    g1_subseq_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
  have h_lim := Tendsto.div hg_sub hQ_sub (ne_of_gt hP_pos)
  rw [zero_div] at h_lim
  -- Use convert to reconcile f / g with fun n => f n / g n.
  convert h_lim using 2

lemma g1_hat_converge_zero [Condition_C1 admm]:
      Tendsto g1_hat atTop (𝓝 0) := by
   exact tendsto_zero_of_antitone_tail_of_subseq (g1_hat_is_nonneg (admm_kkt := limitKKT))
     (g1_hat_tail_antitone (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
     (hphi_StrictMono_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
     (g1_hat_subseq_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂)


-- Prove the full sequence g tends to zero.
-- Final conclusion of the Robbins-Siegmund construction.
lemma g1_tendsto_zero
       [Condition_C1 admm]

       :
      Tendsto (fun n => g1 n) atTop (nhds 0) := by
  have h_ghat_zero := g1_hat_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
  obtain ⟨P, hP⟩ := Q_seq_converges_c1 (admm := admm)
  have h_lim_mul := Tendsto.mul h_ghat_zero (hP.2)
  rw [zero_mul] at h_lim_mul
  have h_eq : (fun n => g1 n) = (fun n => g1_hat n * Q_seq_c1 n) := by
    funext n
    dsimp [ AdaptiveADMM_Convergence_Proof.g1_hat]
    have h_Q_pos : Q_seq_c1 n ≠ 0 := by
        apply ne_of_gt
        dsimp [ AdaptiveADMM_Convergence_Proof.Q_seq_c1]
        apply Finset.prod_pos
        intro n _
        linarith [sq_nonneg (η_k n)]
    field_simp
  rw [h_eq]
  exact h_lim_mul

lemma A₂e₂_le_g1 (n : ℕ)  [Condition_C1 admm]
      :
      ‖A₂ (e₂ n)‖ ^ 2 ≤ (1 / (τ * (ρₙ n)^2)) * g1 n := by
   have hτ : 0 < τ := admm.htau.1
   have hρ : 0 < ρₙ n := admm.hρₙ_pos n
   have h_coeff : 0 < τ * (ρₙ n)^2 := mul_pos hτ (sq_pos_of_pos hρ)
   rw [mul_comm (1 / (τ * (ρₙ n)^2)) (g1 n)]
   field_simp
   rw [le_div_iff₀ h_coeff]
   dsimp [ AdaptiveADMM_Convergence_Proof.g1]
   have h_ey_nonneg : 0 ≤ ‖ey n‖^2 := sq_nonneg _
   have h_res_nonneg : 0 ≤ τ * (T_HWY - τ) * ρₙ n ^ 2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg (le_of_lt hτ)
          exact le_of_lt (HWY_thm4_1_ineq (admm := admm))
        · apply sq_nonneg
      · apply sq_nonneg
   linarith [h_ey_nonneg, h_res_nonneg]

lemma A₂e₂_le_g1'  [Condition_C1 admm]
       :
      ∀ n : ℕ, ‖A₂ (e₂ n)‖ ^ 2 ≤ (1 / (τ * (ρₙ n)^2)) * g1 n := by
   intro n
   apply A₂e₂_le_g1 (admm_kkt := admm_kkt)

lemma A₂e₂_pow_converge_zero_c1
       [Condition_C1 admm]
       :
      Tendsto (fun n => ‖A₂ (e₂ n)‖^2) atTop (nhds 0) := by
   obtain ⟨BL, hBL_pos, hBL⟩ := admm.rho_lower_bound
   let C := 1 / (τ * BL^2)
   have hC_pos : C > 0 := by
      apply div_pos zero_lt_one
      apply mul_pos admm.htau.1 (sq_pos_of_pos hBL_pos)
   apply squeeze_zero_norm
   intro n
   have h_bound : τ * BL^2 * ‖A₂ (e₂ n)‖^2 ≤ g1 n := by
      dsimp [ AdaptiveADMM_Convergence_Proof.g1]
      have h_rho : BL^2 ≤ ρₙ n ^ 2 := by
         apply sq_le_sq'
         have h_rho_pos : 0 < ρₙ n := admm.hρₙ_pos n
         linarith
         exact hBL n
      have h_term2 : τ * BL^2 * ‖A₂ (e₂ n)‖^2 ≤ τ * ρₙ n ^ 2 * ‖A₂ (e₂ n)‖^2 := by
         have hscaled : τ * BL^2 ≤ τ * ρₙ n^2 :=
            mul_le_mul_of_nonneg_left h_rho (le_of_lt admm.htau.1)
         exact mul_le_mul_of_nonneg_right hscaled (sq_nonneg _)
      have h_nonneg_rest : 0 ≤ ‖ey n‖^2 + τ * (T_HWY - τ) * ρₙ n ^ 2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
         apply add_nonneg (sq_nonneg _)
         apply mul_nonneg; apply mul_nonneg; apply mul_nonneg
         exact le_of_lt admm.htau.1
         exact le_of_lt (HWY_thm4_1_ineq (admm := admm))
         exact sq_nonneg _
         exact sq_nonneg _
      linarith
   have h_coeff_pos : 0 < τ * BL^2 := mul_pos admm.htau.1 (sq_pos_of_pos hBL_pos)
   have h_bound' : ‖A₂ (e₂ n)‖^2 ≤ C * g1 n := by
      have h_mul_comm : τ * BL^2 * ‖A₂ (e₂ n)‖^2 = ‖A₂ (e₂ n)‖^2 * (τ * BL^2) := by ring
      rw [h_mul_comm] at h_bound
      rw [← le_div_iff₀ h_coeff_pos] at h_bound
      have h_C_eq : C = 1 / (τ * BL^2) := rfl
      rw [h_C_eq]
      field_simp
      exact h_bound
   simp
   -- Convert to ‖A₂e₂‖^2 ≤ C * g n
   let f := fun n => C * g1 n
   have h_f_bound : ‖A₂ (e₂ n)‖^2 ≤ f n := by
      exact h_bound'
   convert h_f_bound
   · rw [← mul_zero C]
     apply Filter.Tendsto.const_mul
     exact g1_tendsto_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂

lemma A₂e₂_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₂ (e₂ n)‖)^2))  atTop (𝓝 √0) := by
      apply Tendsto.sqrt (A₂e₂_pow_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
   rw [Real.sqrt_zero] at this; simp [Real.sqrt_sq] at this; exact this

lemma A₁e₁_converge_zero_c1
       [Condition_C1 admm]
       :
      Tendsto (fun n => ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by
   -- 1. Construct a Condition_C1 instance for the limit point.

   have h (n : ℕ) : ‖A₁ (e₁ n)‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by
      let x := A₁ (e₁ n)
      let xx := A₂ (e₂ n)
      have h1 : ‖x‖ = ‖x + xx - xx‖ := by rw [← add_sub, sub_self, add_zero]
      have h2 : ‖x + xx - xx‖ ≤ ‖x + xx‖ + ‖xx‖ := by apply norm_sub_le
      rw [← h1] at h2
      linarith
   have h' (n : ℕ) : ‖‖A₁ (e₁ n)‖‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by
      have : ‖‖A₁ (e₁ n)‖‖ = ‖A₁ (e₁ n)‖ := by simp only [norm_norm]
      rw [this]
      exact h n
   have h'' : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖) atTop (𝓝 (0 + 0)) := by
      -- These lemmas now use the local inst instance.
      have h_converge_zero₁ : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖) atTop (𝓝 0) := by
         apply converge_zero₁_c1 (admm_kkt := limitKKT)
      have h_A₂e₂_converge_zero : Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
         apply A₂e₂_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
      apply Tendsto.add h_converge_zero₁ h_A₂e₂_converge_zero
   have h''' : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
      have : (0 : ℝ) = 0 + 0 := by norm_num
      rw [this]
      exact h''
   apply squeeze_zero_norm
   apply h'
   exact h'''

lemma A₁e₁_converge_zero'_c1 [Condition_C1 admm]

      :
      Tendsto (fun n => ‖(A₁ ∘ e₁) n‖) atTop (𝓝 0) := by
   have : (fun n => ‖A₁ (e₁ n)‖) = (fun n => ‖(A₁ ∘ e₁) n‖) := by simp only [Function.comp_apply]
   rw [← this]
   apply A₁e₁_converge_zero_c1 (admm_kkt := admm_kkt)

lemma CA₁e₁_converge_zero_c1 [Condition_C1 admm]

      (C : ℝ) :
      Tendsto (fun n => C * ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by apply A₁e₁_converge_zero_c1 (admm_kkt := admm_kkt)
   have h : C * 0 = 0 := by simp only [mul_zero]
   rw[← h]; apply Tendsto.const_mul C this

lemma CA₂e₂_converge_zero_c1 [Condition_C1 admm](C : ℝ) :
      Tendsto (fun n => C * ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by apply A₂e₂_converge_zero_c1 (admm_kkt := admm_kkt)
   have h : C * 0 = 0 := by simp only [mul_zero]
   rw[← h]; apply Tendsto.const_mul C this

lemma e₁_converge_zero_c1 [Condition_C1 admm]:
      Tendsto e₁ atTop (𝓝 0) := by
   have : ∃ C > 0, ∀ n : ℕ, ‖e₁ n‖ ≤ C * ‖A₁ (e₁ n)‖ := open_mapping_e₁_c1 (admm_kkt := limitKKT) fullrank₁
   obtain ⟨C, _, hC⟩ := this
   apply squeeze_zero_norm; intro n; exact hC n; apply CA₁e₁_converge_zero_c1 (admm_kkt := admm_kkt)


lemma e₂_converge_zero_c1 [Condition_C1 admm]:
      Tendsto e₂ atTop (𝓝 0) := by
   have : ∃ C > 0, ∀ n : ℕ, ‖e₂ n‖ ≤ C * ‖A₂ (e₂ n)‖ := open_mapping_e₂_c1 (admm_kkt := limitKKT) fullrank₂
   obtain ⟨C, _, hC⟩ := this
   apply squeeze_zero_norm; intro n; exact hC n; apply CA₂e₂_converge_zero_c1 (admm_kkt := admm_kkt)

lemma ey_sq_le_g1
       [Condition_C1 admm]


      (n : ℕ) :
      ‖ey n‖ ^ 2 ≤ g1 n := by
   dsimp [ AdaptiveADMM_Convergence_Proof.g1]
   have h_A2_nonneg : 0 ≤ τ * (ρₙ n)^2 * ‖A₂ (e₂ n)‖^2 := by
      apply mul_nonneg
      · apply mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg _)
      · apply sq_nonneg
   have h_res_nonneg : 0 ≤ τ * (T_HWY - τ) * (ρₙ n)^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      · apply mul_nonneg
        · apply mul_nonneg (le_of_lt admm.htau.1) (le_of_lt (HWY_thm4_1_ineq (admm := admm)))
        · apply sq_nonneg
      · apply sq_nonneg
   linarith [h_A2_nonneg, h_res_nonneg]


lemma ey_sqnrm_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => ‖ey n‖^2)  atTop (𝓝 0) := by
   apply squeeze_zero_norm
   have (n : ℕ) : ‖‖ey n‖ ^ 2‖ ≤ g1 n := by
     simpa using ey_sq_le_g1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ n
   apply this; apply g1_tendsto_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂

lemma ey_nrm_converge_zero_c1 [Condition_C1 admm]:
      Tendsto (fun n => ‖ey n‖)  atTop (𝓝 0) := by
   rw [← Real.sqrt_zero]
   have : (fun n => ‖ey n‖) = (fun n => √(‖ey n‖^2)) := by funext n; simp [Real.sqrt_sq]
   rw [this]
   apply Filter.Tendsto.sqrt (ey_sqnrm_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

lemma ey_converge_zero_c1 [Condition_C1 admm]:
      Tendsto ey atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2
   apply ey_nrm_converge_zero_c1 (admm_kkt := admm_kkt)

--lim_{ n → ∞} x_n - x = 0 =>  lim_{ n → ∞} x_n  = x
lemma x₁_converge_c1 [Condition_C1 admm]:
      Tendsto x₁ atTop (𝓝 x₁'') := by
   have : e₁ = (fun n => (x₁ n) - x₁''):= rfl
   have h := e₁_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma x₂_converge_c1 [Condition_C1 admm]:
      Tendsto x₂ atTop (𝓝 x₂'') := by
   have : e₂ = (fun n => (x₂ n) - x₂''):= rfl
   have h := e₂_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma y_converge_c1 [Condition_C1 admm]:
      Tendsto y atTop (𝓝 y'') := by
   have : ey = (fun n => (y n) - y''):= rfl
   have h := ey_converge_zero_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

--Adaptive ADMM of condition C1 convergence theorem
include fullrank₁ fullrank₂ in
theorem adaptive_admm_convergence_c1 [Condition_C1 admm]:
      ∃ ( _x₁   : E₁) ( _x₂ : E₂) ( _y : F) , Convex_KKT _x₁ _x₂ _y admm.toOptProblem
      ∧ ( Tendsto x₁ atTop (𝓝 _x₁)∧ Tendsto x₂ atTop (𝓝 _x₂)∧ Tendsto y atTop (𝓝 _y)) :=
   ⟨x₁'',x₂'',y'',Iskktpair_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ ,
   x₁_converge_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ ,x₂_converge_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂,
   y_converge_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂⟩


end AdaptiveADMM_Convergence_Proof
