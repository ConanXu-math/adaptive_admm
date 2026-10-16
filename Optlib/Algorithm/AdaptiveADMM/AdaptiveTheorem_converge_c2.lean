import Optlib.Algorithm.AdaptiveADMM.ClusterPointC2
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
local notation "φ" => Converge_Subseq_2.φ (Subseq_c2 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

-- The point of the subsequence convergence
local notation "x₁''" => Converge_Subseq_2.x₁'' (Subseq_c2 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
local notation "x₂''" => Converge_Subseq_2.x₂'' (Subseq_c2 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
local notation "y''"  => Converge_Subseq_2.y'' (Subseq_c2 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

local notation "limitKKT" => admm_kkt_c2 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
local notation "e₁" => AdaptiveADMM_Convergence_Proof.e₁ admm limitKKT
local notation "e₂" => AdaptiveADMM_Convergence_Proof.e₂ admm limitKKT
local notation "ey" => AdaptiveADMM_Convergence_Proof.ey admm limitKKT
local notation "g1" => AdaptiveADMM_Convergence_Proof.g1 admm limitKKT
local notation "g2" => AdaptiveADMM_Convergence_Proof.g2 admm limitKKT
local notation "u" => AdaptiveADMM_Convergence_Proof.u admm limitKKT
local notation "v" => AdaptiveADMM_Convergence_Proof.v admm limitKKT
local notation "Ψ" => AdaptiveADMM_Convergence_Proof.Ψ admm limitKKT
local notation "Φ" => AdaptiveADMM_Convergence_Proof.Φ admm limitKKT
local notation "g2_hat" => AdaptiveADMM_Convergence_Proof.g2_hat admm limitKKT
local notation "T_HWY" => AdaptiveADMM_Convergence_Proof.T_HWY admm
local notation "υ" => AdaptiveADMM_Convergence_Proof.υ admm
local notation "θ_k" => AdaptiveADMM_Convergence_Proof.θ_k admm
local notation "Q_seq_c2" => AdaptiveADMM_Convergence_Proof.Q_seq_c2 admm

lemma e₁_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (e₁ ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (x₁ ∘ φ) n - x₁'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply x₁_subseq_converge (admm_kkt := admm_kkt)
   have h₂: (fun n => (x₁ ∘ φ) n - x₁'') = (fun n => e₁ (φ n)) := by
      funext n; rw [ AdaptiveADMM_Convergence_Proof.e₁];simp; simp [admm_kkt_c2];
   rw [h₂] at h₁; apply h₁

-- e₂ (φ n) → 0
-- x₂ (φ n) → (admm_kkt_c2 (admm_kkt := admm_kkt) fullrank₁ fullrank₂).x₂ = x₂''
lemma e₂_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (e₂ ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (x₂ ∘ φ) n - x₂'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply x₂_subseq_converge (admm_kkt := admm_kkt)
   have h₂: (fun n => (x₂ ∘ φ) n - x₂'') = (fun n => e₂ (φ n)) := by
      funext n; rw [ AdaptiveADMM_Convergence_Proof.e₂]; simp; simp [admm_kkt_c2]
   rw [h₂] at h₁; apply h₁

-- e₂ (φ n) → 0
-- y (φ n) → (admm_kkt_c2 (admm_kkt := admm_kkt) fullrank₁ fullrank₂).y = y''
lemma ey_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (ey ∘ φ) atTop (𝓝 0) := by
   have h₁: Tendsto (fun n => (y ∘ φ) n - y'') atTop (𝓝 0) := by
      apply tendsto_sub_nhds_zero_iff.2; apply y_subseq_converge (admm_kkt := admm_kkt)
   have h₂: (fun n => (y ∘ φ) n - y'') = (fun n => ey (φ n)) := by
      funext n; rw [ AdaptiveADMM_Convergence_Proof.ey]; simp; simp [admm_kkt_c2]
   rw [h₂] at h₁; apply h₁

-- ‖ey (φ n)‖ → 0
lemma nrm_ey_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => ‖ey (φ n)‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply ey_subseq_converge_zero (admm_kkt := admm_kkt)

-- ‖ey (φ n)‖^2 → 0
lemma sqnrm_ey_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => ‖ey (φ n)‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_ey_subseq_converge_zero (admm_kkt := admm_kkt); linarith

-- A₁ (e₁ (φ n)) → 0
lemma A₁e₁_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => A₁ (e₁ (φ n))) atTop (𝓝 0) := by
   have h₁: Tendsto A₁ (𝓝 0) (𝓝 (A₁ 0)) := by
      apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   simp at h₁; apply Filter.tendsto_iff_seq_tendsto.1 h₁; apply e₁_subseq_converge_zero

-- A₂ (e₂ (φ n)) → 0
lemma A₂e₂_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => A₂ (e₂ (φ n))) atTop (𝓝 0) := by
   have h₁: Tendsto A₂ (𝓝 0) (𝓝 (A₂ 0)) := by
      apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   simp at h₁; apply Filter.tendsto_iff_seq_tendsto.1 h₁; apply e₂_subseq_converge_zero (admm_kkt := admm_kkt)

-- ‖A₂ (e₂ (φ n))‖ → 0
lemma nrm_A₂e₂_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => ‖A₂ (e₂ (φ n))‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply A₂e₂_subseq_converge_zero (admm_kkt := admm_kkt)

-- ‖A₂ (e₂ (φ n))‖^2 → 0
lemma sqnrm_A₂e₂_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => ‖A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_A₂e₂_subseq_converge_zero (admm_kkt := admm_kkt); linarith


-- A₁ (e₁ (φ n)) + A₂ (e₂ (φ n)) → 0
lemma A₁e₁_A₂e₂_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))) atTop (𝓝 0) := by
   rw [← add_zero 0]
   apply Tendsto.add (A₁e₁_subseq_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (A₂e₂_subseq_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

-- ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖ → 0
lemma nrm_A₁e₁_A₂e₂_subseq_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖) atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.1; apply A₁e₁_A₂e₂_subseq_converge_zero (admm_kkt := admm_kkt)

-- ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2 → 0
lemma sqnrm_A₁e₁_A₂e₂_subseq_converge_zero[Condition_C2 admm]:
      Tendsto (fun n => ‖A₁ (e₁ (φ n)) + A₂ (e₂ (φ n))‖^2) atTop (𝓝 0) := by
   rw [← zero_pow]; apply Filter.Tendsto.pow ; apply nrm_A₁e₁_A₂e₂_subseq_converge_zero (admm_kkt := admm_kkt); linarith



-- Prove g2(φ n) → 0.
lemma g2_subseq_converge_zero
      [Condition_C2 admm] :
      Tendsto (fun n => g2 (φ n)) atTop (nhds 0) := by
   obtain ⟨BL, hBL_pos, hBL⟩ := admm.rho_lower_bound
   have h_rho_sq : ∀ n, ρₙ (φ n) ^ 2 ≥  BL ^ 2 := fun n => sq_le_sq' (by linarith [admm.hρₙ_pos (φ n)]) (hBL (φ n))
   have h_rho_sq_nonneg : ∀ n, 0 ≤ ρₙ (φ n) ^ 2 := fun n => sq_nonneg (ρₙ (φ n))
   have h1_inner : Tendsto (fun n => ‖ey (φ n)‖^2) atTop (nhds 0) :=
      sqnrm_ey_subseq_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   have h1 :Tendsto (fun n => 1/ρₙ (φ n) ^ 2 * ‖ey (φ n)‖^2) atTop (nhds 0) :=by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      · exact tendsto_const_nhds -- Constant lower bound zero.
      ·  rw [← mul_zero (1/ BL^2)]
         apply Filter.Tendsto.const_mul (1/ BL^2 ) h1_inner
      ·  intro n
         apply mul_nonneg
         simp [h_rho_sq_nonneg]
         apply sq_nonneg _
      ·  intro n
         simp
         gcongr
         exact hBL (φ n)
   have h2_inner : Tendsto (fun n => ‖A₂ (e₂ (φ n))‖^2) atTop (nhds 0) :=
      sqnrm_A₂e₂_subseq_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   have h2 : Tendsto (fun n => τ * ‖A₂ (e₂ (φ n))‖^2) atTop (nhds 0) := by
      rw [← mul_zero (τ)]
      apply Filter.Tendsto.const_mul (τ) h2_inner
   have h3_inner : Tendsto (fun n => ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖^2) atTop (nhds 0) := by
      rw [← zero_pow two_ne_zero]
      apply Tendsto.pow (subconverge_zero₂ (admm_kkt := admm_kkt) fullrank₁ fullrank₂) 2
   have h3 : Tendsto (fun n => τ * (T_HWY - τ)  * ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖^2) atTop (nhds 0) := by
      rw [← mul_zero (τ * (T_HWY - τ))]
      apply Filter.Tendsto.const_mul (τ * (T_HWY - τ)) h3_inner
   unfold AdaptiveADMM_Convergence_Proof.g2
   have h_add : Tendsto (fun x => 1/ (ρₙ (φ x))^2 * ‖ey (φ x)‖^2 + τ * ‖A₂ (e₂ (φ x))‖^2) atTop (𝓝 (0 + 0)) := by
      apply Tendsto.add h1 h2
   have h_add' : Tendsto (fun x => 1/ (ρₙ (φ x))^2 * ‖ey (φ x)‖^2 + τ * ‖A₂ (e₂ (φ x))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (φ x)) + A₂ (x₂ (φ x)) - b‖^2) atTop (𝓝 (0 + 0 + 0)) := by
      apply Tendsto.add h_add h3
   simp at h_add'
   simp
   exact h_add'




lemma g2_hat_tail_antitone [Condition_C2 admm]:
      Antitone (fun n ↦  g2_hat (n + 1)) := by
   apply antitone_nat_of_succ_le
   intro n
   apply g2_hat_succ_le (admm_kkt := limitKKT) (n+1).toPNat'

lemma g2_hat_subseq_converge_zero
       [Condition_C2 admm] :
      Tendsto (fun n => g2_hat (φ n)) atTop (𝓝 0) := by
  simp only [ AdaptiveADMM_Convergence_Proof.g2_hat]
  obtain ⟨P, hP_pos, hQ_conv⟩ := Q_seq_converges_c2 (admm := admm)
  have hQ_sub : Tendsto (fun n => Q_seq_c2 (φ n)) atTop (𝓝 P) :=
    hQ_conv.comp (hphi_StrictMono (admm_kkt := admm_kkt) fullrank₁ fullrank₂).tendsto_atTop
  have hg_sub : Tendsto (fun n => g2 (φ n)) atTop (𝓝 0) :=
    g2_subseq_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
  have h_lim := Tendsto.div hg_sub hQ_sub (ne_of_gt hP_pos)
  rw [zero_div] at h_lim
  -- Use convert to reconcile f / g with fun n => f n / g n.
  convert h_lim using 2

lemma g2_hat_converge_zero [Condition_C2 admm]:
      Tendsto g2_hat atTop (𝓝 0) := by
   exact tendsto_zero_of_antitone_tail_of_subseq (g2_hat_is_nonneg (admm_kkt := limitKKT))
     (g2_hat_tail_antitone (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
     (hphi_StrictMono (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
     (g2_hat_subseq_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂)


-- Prove the full sequence g tends to zero.
-- Final conclusion of the Robbins-Siegmund construction.
lemma g2_tendsto_zero
       [Condition_C2 admm]

       :
      Tendsto (fun n => g2 n) atTop (nhds 0) := by
  have h_ghat_zero := g2_hat_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
  obtain ⟨P, hP⟩ := Q_seq_converges_c2 (admm := admm)
  have h_lim_mul := Tendsto.mul h_ghat_zero (hP.2)
  rw [zero_mul] at h_lim_mul
  have h_eq : (fun n => g2 n) = (fun n => g2_hat n * Q_seq_c2 n) := by
    funext n
    dsimp [ AdaptiveADMM_Convergence_Proof.g2_hat]
    have h_Q_pos : Q_seq_c2 n ≠ 0 := by
        apply ne_of_gt
        dsimp [ AdaptiveADMM_Convergence_Proof.Q_seq_c2]
        apply Finset.prod_pos
        intro n _
        linarith [sq_nonneg (θ_k n)]
    field_simp
  rw [h_eq]
  exact h_lim_mul

lemma A₂e₂_le_g2 (n : ℕ)  [Condition_C2 admm]
      :
      ‖A₂ (e₂ n)‖ ^ 2 ≤ (1 / τ) * g2 n := by
   have hτ : 0 < τ := admm.htau.1
   rw [mul_comm (1 / τ ) (g2 n)]
   field_simp
   rw [le_div_iff₀ (by linarith [hτ])]
   dsimp [ AdaptiveADMM_Convergence_Proof.g2]
   have h_ey_nonneg : 0 ≤ 1/ (ρₙ n)^2 * ‖ey n‖^2 := by
      have h2': 0 ≤ 1/ρₙ n^2 := by
         apply div_nonneg
         linarith
         linarith [sq_pos_of_pos (admm.hρₙ_pos n)]
      have h2'': 0 ≤ ‖ey n‖^2 := by exact sq_nonneg ‖ey n‖
      exact mul_nonneg h2' h2''
   have h_res_nonneg : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact (le_of_lt hτ)
      linarith [(HWY_thm4_1_ineq (admm := admm))]
      apply sq_nonneg _
   linarith [h_ey_nonneg, h_res_nonneg]

lemma A₂e₂_pow_converge_zero
       [Condition_C2 admm]
       :
      Tendsto (fun n => ‖A₂ (e₂ n)‖^2) atTop (nhds 0) := by
  -- Apply the squeeze theorem to 0 ≤ ‖A₂ (e₂ n)‖^2 ≤ (1/τ) * g2 n.
  apply squeeze_zero
  · -- Lower bound: the squared norm is nonnegative.
    intro n
    apply sq_nonneg
  · -- Upper bound: apply A₂e₂_le_g2 (admm_kkt := admm_kkt).
    intro n
    apply A₂e₂_le_g2 (admm_kkt := admm_kkt)
  · -- Prove that the upper bound tends to zero.
    -- Since g2 n tends to zero, so does (1/τ) * g2 n.
    rw [← mul_zero (1 / τ)]
    apply Tendsto.const_mul
    apply g2_tendsto_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂


lemma A₂e₂_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₂ (e₂ n)‖)^2))  atTop (𝓝 √0) := by
      apply Tendsto.sqrt (A₂e₂_pow_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
   rw [Real.sqrt_zero] at this; simp [Real.sqrt_sq] at this; exact this

lemma A₁e₁_converge_zero
       [Condition_C2 admm]
       :
      Tendsto (fun n => ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by
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
      have h_converge_zero₁ : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖) atTop (𝓝 0) := by
         apply converge_zero₁ (admm_kkt := limitKKT)
      have h_A₂e₂_converge_zero : Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
         apply A₂e₂_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
      apply Tendsto.add h_converge_zero₁ h_A₂e₂_converge_zero
   have h''' : Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
      have : (0 : ℝ) = 0 + 0 := by norm_num
      rw [this]
      exact h''
   apply squeeze_zero_norm
   apply h'
   exact h'''

lemma A₁e₁_converge_zero' [Condition_C2 admm]

      :
      Tendsto (fun n => ‖(A₁ ∘ e₁) n‖) atTop (𝓝 0) := by
   have : (fun n => ‖A₁ (e₁ n)‖) = (fun n => ‖(A₁ ∘ e₁) n‖) := by simp only [Function.comp_apply]
   rw [← this]
   apply A₁e₁_converge_zero (admm_kkt := admm_kkt)

lemma CA₁e₁_converge_zero [Condition_C2 admm]

      (C : ℝ) :
      Tendsto (fun n => C * ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₁ (e₁ n)‖) atTop (𝓝 0) := by apply A₁e₁_converge_zero (admm_kkt := admm_kkt)
   have h : C * 0 = 0 := by simp only [mul_zero]
   rw[← h]; apply Tendsto.const_mul C this

lemma CA₂e₂_converge_zero [Condition_C2 admm](C : ℝ) :
      Tendsto (fun n => C * ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₂ (e₂ n)‖) atTop (𝓝 0) := by apply A₂e₂_converge_zero (admm_kkt := admm_kkt)
   have h : C * 0 = 0 := by simp only [mul_zero]
   rw[← h]; apply Tendsto.const_mul C this

lemma e₁_converge_zero [Condition_C2 admm]:
      Tendsto e₁ atTop (𝓝 0) := by
   have : ∃ C > 0, ∀ n : ℕ, ‖e₁ n‖ ≤ C * ‖A₁ (e₁ n)‖ := open_mapping_e₁ (admm_kkt := limitKKT) fullrank₁
   obtain ⟨C, _, hC⟩ := this
   apply squeeze_zero_norm; intro n; exact hC n; apply CA₁e₁_converge_zero (admm_kkt := admm_kkt)


lemma e₂_converge_zero [Condition_C2 admm]:
      Tendsto e₂ atTop (𝓝 0) := by
   have : ∃ C > 0, ∀ n : ℕ, ‖e₂ n‖ ≤ C * ‖A₂ (e₂ n)‖ := open_mapping_e₂ (admm_kkt := limitKKT) fullrank₂
   obtain ⟨C, _, hC⟩ := this
   apply squeeze_zero_norm; intro n; exact hC n; apply CA₂e₂_converge_zero (admm_kkt := admm_kkt)


lemma ey_sq_le_g
       [Condition_C2 admm]


      (n : ℕ) :
      ‖ey n‖ ^ 2 ≤ ρₙ n^2 * g2 n := by
   -- Expand the definition of g2.
   dsimp [ AdaptiveADMM_Convergence_Proof.g2]
   -- Expand ρₙ n^2 * g2 n into the dual error and scaled residual terms.
   have h1 : ‖ey n‖^2 = ρₙ n^2 * (1 / ρₙ n^2 * ‖ey n‖^2) := by
      have h_ne_zero : ρₙ n^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (admm.hρₙ_pos n))
      have h_ne_zero' : ρₙ n ≠ 0 := ne_of_gt (admm.hρₙ_pos n)
      field_simp [h_ne_zero, h_ne_zero']
   have h2 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by
      apply mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg _)
   have h3 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg (le_of_lt admm.htau.1)
      linarith [(HWY_thm4_1_ineq (admm := admm))]
      apply sq_nonneg
   have h4 : 0 ≤ ρₙ n^2 * (τ * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) := by
      apply mul_nonneg (sq_nonneg _)
      linarith [h2, h3]
   calc ‖ey n‖^2
      = ρₙ n^2 * (1 / ρₙ n^2 * ‖ey n‖^2) := h1
      _ ≤ ρₙ n^2 * (1 / ρₙ n^2 * ‖ey n‖^2) + ρₙ n^2 * (τ * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) := by linarith
      _ = ρₙ n^2 * g2 n := by unfold AdaptiveADMM_Convergence_Proof.g2; ring_nf


lemma ey_sqnrm_converge_zero [Condition_C2 admm]
      :
      Tendsto (fun n => ‖ey n‖^2) atTop (𝓝 0) := by
   -- 1. Obtain the upper bound BU for ρₙ.
   obtain ⟨BU, hBU⟩ := admm.rho_upper_bound
   -- 2. Apply squeeze_zero.
   -- squeeze_zero requires three arguments:
   -- (1) ∀ n, 0 ≤ f n: the lower bound.
   -- (2) ∀ n, f n ≤ g n: the upper bound.
   -- (3) Tendsto g atTop (𝓝 0): convergence of the upper bound.
   apply squeeze_zero
   · -- Branch 1: prove nonnegativity.
     intro n
     exact sq_nonneg _
   · -- Branch 2: prove ‖ey n‖^2 ≤ BU^2 * g2 n.
     intro n
     -- Use the earlier bound ‖ey n‖^2 ≤ ρₙ^2 * g2 n.
     have h_local := ey_sq_le_g (admm_kkt := admm_kkt) fullrank₁ fullrank₂ n
     -- Apply the bounds with calc or gcongr.
     calc ‖ey n‖^2
       _ ≤ ρₙ n^2 * g2 n := h_local
       _ ≤ BU^2 * g2 n   := by
         have h_rho_sq : ρₙ n^2 ≤ BU^2 := by
            apply sq_le_sq'
            · linarith [hBU.1, admm.hρₙ_pos n]
            · exact hBU.2 n
         exact mul_le_mul_of_nonneg_right h_rho_sq ((g2_nonneg (admm := admm) (admm_kkt := limitKKT)) n)
   · -- Branch 3: prove the upper bound tends to zero.
     -- Goal: Tendsto (fun n => BU^2 * g2 n) atTop (𝓝 0).
     rw [← mul_zero (BU^2)] -- Rewrite zero as BU^2 * 0.
     apply Filter.Tendsto.const_mul -- Apply the limit rule for multiplication by a constant.
     apply g2_tendsto_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂ -- Apply convergence of g2 to zero.


lemma ey_nrm_converge_zero [Condition_C2 admm]:
      Tendsto (fun n => ‖ey n‖)  atTop (𝓝 0) := by
   rw [← Real.sqrt_zero]
   have : (fun n => ‖ey n‖) = (fun n => √(‖ey n‖^2)) := by funext n; simp [Real.sqrt_sq]
   rw [this]
   apply Filter.Tendsto.sqrt (ey_sqnrm_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

lemma ey_converge_zero [Condition_C2 admm]:
      Tendsto ey atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2
   apply ey_nrm_converge_zero (admm_kkt := admm_kkt)

--lim_{ n → ∞} x_n - x = 0 =>  lim_{ n → ∞} x_n  = x
lemma x₁_converge [Condition_C2 admm]:
      Tendsto x₁ atTop (𝓝 x₁'') := by
   have : e₁ = (fun n => (x₁ n) - x₁''):= rfl
   have h := e₁_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma x₂_converge [Condition_C2 admm]:
      Tendsto x₂ atTop (𝓝 x₂'') := by
   have : e₂ = (fun n => (x₂ n) - x₂''):= rfl
   have h := e₂_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

lemma y_converge [Condition_C2 admm]:
      Tendsto y atTop (𝓝 y'') := by
   have : ey = (fun n => (y n) - y''):= rfl
   have h := ey_converge_zero (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   rw[this , tendsto_sub_nhds_zero_iff] at h
   exact h

-- Adaptive ADMM convergence under Condition C2.
include fullrank₁ fullrank₂ in
theorem adaptive_admm_convergence [Condition_C2 admm]:
      ∃ ( _x₁   : E₁) ( _x₂ : E₂) ( _y : F) , Convex_KKT _x₁ _x₂ _y admm.toOptProblem
      ∧ ( Tendsto x₁ atTop (𝓝 _x₁)∧ Tendsto x₂ atTop (𝓝 _x₂)∧ Tendsto y atTop (𝓝 _y)) :=
   ⟨x₁'',x₂'',y'',Iskktpair (admm_kkt := admm_kkt) fullrank₁ fullrank₂ ,
   x₁_converge (admm_kkt := admm_kkt) fullrank₁ fullrank₂ ,x₂_converge (admm_kkt := admm_kkt) fullrank₁ fullrank₂,
   y_converge (admm_kkt := admm_kkt) fullrank₁ fullrank₂⟩


end AdaptiveADMM_Convergence_Proof
