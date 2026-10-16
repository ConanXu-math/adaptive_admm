import Optlib.Algorithm.AdaptiveADMM.AdaptiveLemmas
import Optlib.Algorithm.AdaptiveADMM.AdaptiveScheme
import Optlib.Convex.ImageSubgradientClosed
import Optlib.Algorithm.AdaptiveADMM.AdaptiveInv_bounded
import Optlib.Algorithm.AdaptiveADMM.AdaptiveCondition2
import Optlib.Algorithm.AdaptiveADMM.SequenceConvergence
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
local notation "θ_k" => AdaptiveADMM_Convergence_Proof.θ_k admm
def Q_seq_c2 (admm : ADMM E₁ E₂ F) : ℕ → ℝ := fun n => ∏ k ∈ Finset.range n, (1 + (AdaptiveADMM_Convergence_Proof.θ_k admm k)^2)

local notation "Q_seq_c2" => AdaptiveADMM_Convergence_Proof.Q_seq_c2 admm


omit admm_kkt in
lemma Q_seq_mono_c2 : Monotone Q_seq_c2 := by
  apply monotone_nat_of_le_succ
  intro n
  dsimp [ AdaptiveADMM_Convergence_Proof.Q_seq_c2]
  rw [Finset.prod_range_succ]
  have h_factor : 1 ≤ 1 + (θ_k n)^2 := by
    linarith [sq_nonneg (θ_k n)]
  apply le_mul_of_one_le_right
  · apply Finset.prod_nonneg
    intro i _
    linarith [sq_nonneg (θ_k i)]
  · exact h_factor


omit admm_kkt in
lemma Q_seq_converges_c2 [Condition_C2 admm]: ∃ P > 0, Tendsto Q_seq_c2 atTop (𝓝 P) := by
   obtain ⟨S, hS_pos, hS_le⟩ := (Condition_C2.one_theta_square_multipliable' (admm := admm))
   have h_bdd : BddAbove (range Q_seq_c2) := by
      use S
      rintro _ ⟨n, rfl⟩
      apply le_trans _ hS_le
      cases n with
      | zero =>
         simp [ AdaptiveADMM_Convergence_Proof.Q_seq_c2]
         apply le_trans (Q_seq_mono_c2 (admm := admm) (Nat.zero_le 1))
         exact (HWY_ineq_56_1 (admm := admm)) 0
      | succ k =>
         exact (HWY_ineq_56_1 (admm := admm)) k
   have hP := tendsto_atTop_ciSup Q_seq_mono_c2 h_bdd
   use ⨆ i, Q_seq_c2 i
   constructor
   ·  have h0 : Q_seq_c2 0 = 1 := by simp [ AdaptiveADMM_Convergence_Proof.Q_seq_c2]
      have h_le : 1 ≤ ⨆ i, Q_seq_c2 i := le_trans (le_of_eq h0.symm) (le_ciSup h_bdd 0)
      linarith
   ·  exact hP


def g2_hat (admm : ADMM E₁ E₂ F) (reference : KKTPoint admm) : ℕ → ℝ :=
  fun n => AdaptiveADMM_Convergence_Proof.g2 admm reference n / AdaptiveADMM_Convergence_Proof.Q_seq_c2 admm n

local notation "g2_hat" => AdaptiveADMM_Convergence_Proof.g2_hat admm admm_kkt



lemma g2_hat_succ_le : ∀ n : ℕ+, g2_hat (n+1) ≤ g2_hat n := by
   intro n
   dsimp [ AdaptiveADMM_Convergence_Proof.g2_hat]
   have h_Q_pos : 0 < Q_seq_c2 n := by
      apply Finset.prod_pos; intro i _; linarith [sq_nonneg (θ_k i)]
   have h_Q_succ_pos : 0 < Q_seq_c2 (n+1) := by
      apply Finset.prod_pos; intro i _; linarith [sq_nonneg (θ_k  i)]
   -- Use div_le_div_iff₀ with both denominators positive.
   rw [div_le_div_iff₀ h_Q_succ_pos h_Q_pos]
   simp [ AdaptiveADMM_Convergence_Proof.Q_seq_c2]
   rw [Finset.prod_range_succ]
   have h : g2 (n+1) ≤ (1 + (θ_k  n)^2) * g2 n := by
      have := (HWY_ineq_56_0 (admm := admm) (admm_kkt := admm_kkt)) n
      linarith
   have :g2 (n+1) * Q_seq_c2 n
      ≤ ((1 + (θ_k  n)^2) * g2 n) * Q_seq_c2 n := mul_le_mul_of_nonneg_right h (by apply Finset.prod_nonneg; intro i _; linarith [sq_nonneg (θ_k  i)])
   simp [ AdaptiveADMM_Convergence_Proof.Q_seq_c2] at this
   linarith


lemma g2_hat_is_nonneg : ∀ n : ℕ , g2_hat n ≥ 0 := by
   intro n
   dsimp [ AdaptiveADMM_Convergence_Proof.g2_hat]
   have h_Q_pos : 0 < Q_seq_c2 n := by
      apply Finset.prod_pos; intro i _;have h : 0 < 1 + (θ_k i)^2 := by
         linarith [sq_nonneg (θ_k i)]
      exact h
   have h_g_nonneg : 0 ≤ g2 n := by
      apply (g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) n
   exact div_nonneg h_g_nonneg (by linarith [h_Q_pos])

lemma g2_bd_above [Condition_C2 admm]: ∃ C : ℝ, ∀ n : ℕ, g2 n < C := by
   have := (HWY_ineq_55_nat (admm := admm) (admm_kkt := admm_kkt))
   rcases this with ⟨C, hC_pos, hC⟩
   use C + 1
   intro n
   have h := hC n
   linarith

lemma g2_isBounded' [Condition_C2 admm] : ∃ (r : ℝ), (range g2) ⊆ ball 0 r := by
   rcases g2_bd_above (admm_kkt := admm_kkt) with ⟨C,bd⟩
   use C; intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩; rw [← eq, abs_eq_self.2]; exact bd n
   apply (g2_nonneg (admm := admm) (admm_kkt := admm_kkt))

lemma g2_isBounded [Condition_C2 admm]: IsBounded (range g2) := (isBounded_iff_subset_ball 0).2  (g2_isBounded' (admm_kkt := admm_kkt))

lemma ey_isBounded' [Condition_C2 admm]: ∃ (r : ℝ), (range ey) ⊆ ball 0 r := by
   rcases g2_bd_above (admm_kkt := admm_kkt) with ⟨r, h_energy_bound⟩;
   rcases admm.rho_upper_bound with ⟨BU, hBU⟩;
   use √(r*BU^2); intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n, eq⟩; rw [← eq]
   have h1 := (g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) n
   have h2:  0 ≤ τ * ‖ey n‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖ey n‖)
   have h3: 0 ≤ ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by exact sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
   have : 0 ≤ T_HWY - τ := by linarith [(HWY_thm4_1_ineq (admm := admm))]
   have h4 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact le_of_lt admm.htau.1
      exact this
      exact h3
   have h6 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖A₂ (e₂ n)‖)
   have h7 := h_energy_bound n
   have h8: 1/BU^2 * ‖ey n‖^2 ≤ 1/ρₙ n^2 * ‖ey n‖^2 := by
      have h_rho_sq : ρₙ n^2 ≤ BU^2 := by
         apply sq_le_sq'
         · linarith [hBU.1, admm.hρₙ_pos n]
         · exact hBU.2 n
      have h_inv : 1 / BU^2 ≤ 1 / ρₙ n^2 :=
         one_div_le_one_div_of_le (sq_pos_of_pos (admm.hρₙ_pos n)) h_rho_sq
      exact mul_le_mul_of_nonneg_right h_inv (sq_nonneg _)
   have h9: 1/BU^2 * ‖ey n‖^2 ≤ g2 n := by
      simp [ AdaptiveADMM_Convergence_Proof.g2]
      simp at h8
      linarith
   have h10: 1/BU^2 * ‖ey n‖^2 < r := by
      linarith
   have h10': ‖ey n‖^2 / BU^2 < r := by
      rw [div_eq_mul_one_div]
      convert h10 using 1
      ring
   have h11: ‖ey n‖^2 < r * BU^2 := by
      exact (div_lt_iff₀ (sq_pos_of_pos hBU.1)).mp h10'
   have h12: ‖ey n‖ < √(r * BU^2) := by
      have h13 : √(‖ey n‖ ^ 2) = ‖ey n‖ := by rw [pow_two]; apply Real.sqrt_mul_self; apply norm_nonneg
      rw [← h13]
      have : ‖ey n‖ ^ 2 ≥ 0 := by apply pow_two_nonneg
      apply (Real.sqrt_lt_sqrt_iff this).mpr
      exact h11
   exact h12

lemma ey_isBounded [Condition_C2 admm]: IsBounded (range ey ) := (isBounded_iff_subset_ball 0).2  (ey_isBounded' (admm_kkt := admm_kkt))


lemma A₂e₂_isBounded' [Condition_C2 admm]: ∃ (r : ℝ), (range (A₂ ∘ e₂) ) ⊆ ball 0 r := by
   rcases g2_bd_above (admm_kkt := admm_kkt) with ⟨r, h_energy_bound⟩;
   rcases admm.rho_upper_bound with ⟨BU, hBU⟩;
   use √(r/τ); intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n, eq⟩; rw [← eq]
   have h1 := (g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) n
   have h2: 0 ≤ 1/ρₙ n^2 * ‖ey n‖^2 := by
      have h2': 0 ≤ 1/ρₙ n^2 := by
         apply div_nonneg
         linarith
         linarith [sq_pos_of_pos (admm.hρₙ_pos n)]
      have h2'': 0 ≤ ‖ey n‖^2 := by exact sq_nonneg ‖ey n‖
      exact mul_nonneg h2' h2''
   have h3: 0 ≤ ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by exact sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
   have : 0 ≤ T_HWY - τ := by linarith [(HWY_thm4_1_ineq (admm := admm))]
   have h4 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact le_of_lt admm.htau.1
      exact this
      exact h3
   have h6 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖A₂ (e₂ n)‖)
   have h7 := h_energy_bound n
   have h5 :τ * ‖A₂ (e₂ n)‖^2 ≤ g2 n := by
      simp [ AdaptiveADMM_Convergence_Proof.g2]
      simp at h2
      linarith
   have h8:  ‖A₂ (e₂ n)‖^2 * τ< r := by
      linarith
   have h9: ‖A₂ (e₂ n)‖^2 < r / τ := by
      have := (lt_div_iff₀ (admm.htau.1)).mpr h8
      linarith
   have h10: ‖A₂ (e₂ n)‖ < √(r / τ) := by
      have h11: √(‖A₂ (e₂ n)‖ ^ 2) = ‖A₂ (e₂ n)‖ := by rw [pow_two]; apply Real.sqrt_mul_self; apply norm_nonneg
      rw [← h11]
      have : ‖A₂ (e₂ n)‖ ^ 2 ≥ 0 := by apply pow_two_nonneg
      apply (Real.sqrt_lt_sqrt_iff this).mpr
      exact h9
   exact h10

lemma A₂e₂_isBounded [Condition_C2 admm]: IsBounded (range (A₂ ∘ e₂) ) :=
   (isBounded_iff_subset_ball 0).2 (A₂e₂_isBounded' (admm_kkt := admm_kkt))

lemma A₁e₁_A₂e₂_equation_c2 [Condition_C2 admm] : ∀ n : ℕ, ‖A₁ (e₁ n) + A₂ (e₂ n)‖ = ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ := by
   intro n
   have : A₁ (e₁ n) + A₂ (e₂ n) = A₁ (x₁ n) + A₂ (x₂ n) - b := by
      rw [ AdaptiveADMM_Convergence_Proof.e₁, AdaptiveADMM_Convergence_Proof.e₂]; simp
      calc
         _ = A₁ (x₁ n) + A₂ (x₂ n) - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_sub_comm]
         _ = A₁ (x₁ n) + A₂ (x₂ n) - b + b - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_cancel]
         _ = A₁ (x₁ n) + A₂ (x₂ n) - b := by
            rw [admm_kkt.h.eq]; simp
   rw [this]

lemma A₁e₁_A₂e₂_isBounded'[Condition_C2 admm] : ∃ (r : ℝ), (range (A₁ ∘ e₁ + A₂ ∘ e₂) ) ⊆ ball 0 r := by
   rcases g2_bd_above (admm_kkt := admm_kkt) with ⟨r, h_energy_bound⟩;
   rcases admm.rho_upper_bound with ⟨BU, hBU⟩;
   use √(r/(τ * (T_HWY - τ))); intro x hx; simp; rw [range] at hx; simp at hx
   rcases hx with ⟨n, eq⟩; rw [← eq]
   have h1 := (g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) n
   have h2: 0 ≤ 1/ρₙ n^2 * ‖ey n‖^2 := by
      have h2': 0 ≤ 1/ρₙ n^2 := by
         apply div_nonneg
         linarith
         linarith [sq_pos_of_pos (admm.hρₙ_pos n)]
      have h2'': 0 ≤ ‖ey n‖^2 := by exact sq_nonneg ‖ey n‖
      exact mul_nonneg h2' h2''
   have h3: 0 < τ * (T_HWY - τ) := by
      apply mul_pos
      exact admm.htau.1
      linarith [(HWY_thm4_1_ineq (admm := admm))]
   have h4 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact le_of_lt admm.htau.1
      linarith [(HWY_thm4_1_ineq (admm := admm))]
      exact sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
   have h6 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖A₂ (e₂ n)‖)
   have h7 := h_energy_bound n
   have h8 :τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 ≤ g2 n := by
      simp [ AdaptiveADMM_Convergence_Proof.g2]
      simp at h2
      linarith
   have h9: τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 < r := by
      linarith
   have h10: ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 * (τ * (T_HWY - τ)) < r := by
      linarith
   have h11: ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 < r / (τ * (T_HWY - τ)) := by
      have := (lt_div_iff₀ h3).mpr h10
      linarith
   have h12: ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ < √(r / (τ * (T_HWY - τ))) := by
      have h13: √(‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2) = ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ := by rw [pow_two]; apply Real.sqrt_mul_self; apply norm_nonneg
      rw [← h13]
      have : ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 ≥ 0 := by apply pow_two_nonneg
      gcongr
   have h14: ‖A₁ (e₁ n) + A₂ (e₂ n)‖ < √(r / (τ * (T_HWY - τ))) := by
      have h15: ‖A₁ (e₁ n) + A₂ (e₂ n)‖ = ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ := by rw [A₁e₁_A₂e₂_equation_c2 (admm_kkt := admm_kkt)]
      rw [h15]
      exact h12
   exact h14

lemma A₁e₁_A₂e₂_isBounded [Condition_C2 admm]: IsBounded (range (A₁ ∘ e₁ + A₂ ∘ e₂) ) :=
   (isBounded_iff_subset_ball 0).2 (A₁e₁_A₂e₂_isBounded' (admm_kkt := admm_kkt))

lemma A₁e₁_isBounded' [Condition_C2 admm]: ∃ (r : ℝ), range (A₁ ∘ e₁) ⊆ ball 0 r := by

   have h_A₂e₂ : ∃ r1, range (A₂ ∘ e₂) ⊆ ball 0 r1 := by apply A₂e₂_isBounded' (admm_kkt := admm_kkt)
   rcases h_A₂e₂ with ⟨r1, h_A₂e₂⟩

   have h_A₁e₁_A₂e₂ : ∃ r2, range (A₁ ∘ e₁ + A₂ ∘ e₂) ⊆ ball 0 r2 := by apply A₁e₁_A₂e₂_isBounded'
   rcases h_A₁e₁_A₂e₂ with ⟨r2, h_A₁e₁_A₂e₂⟩

   let r := r1 + r2
   have hr : r = r1 + r2 := by rfl
   use r

   intros x hx
   rcases hx with ⟨n, rfl⟩

   have h : ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ < r1 + r2 := by
      have ha : ‖A₂ (e₂ n)‖ < r1 := by
         have haa : A₂ (e₂ n) ∈ range (A₂ ∘ e₂) := by use n; simp
         have ha_in_ball : A₂ (e₂ n) ∈ Metric.ball 0 r1 := by apply h_A₂e₂ haa
         rw [Metric.mem_ball, dist_zero_right] at ha_in_ball
         exact ha_in_ball
      have hb : ‖A₁ (e₁ n) + A₂ (e₂ n)‖ < r2 := by
         have hbb : A₁ (e₁ n) + A₂ (e₂ n) ∈ range (A₁ ∘ e₁ + A₂ ∘ e₂) := by use n; simp
         have hb_in_ball : A₁ (e₁ n) + A₂ (e₂ n) ∈ Metric.ball 0 r2 := by apply h_A₁e₁_A₂e₂ hbb
         rw [Metric.mem_ball, dist_zero_right] at hb_in_ball
         exact hb_in_ball
      linarith

   have h_ineq : ‖A₁ (e₁ n)‖ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := by apply norm_le_add_norm_add

   have h_norm : ‖A₁ (e₁ n)‖ < r := by
      calc ‖A₁ (e₁ n)‖
         _ ≤ ‖A₁ (e₁ n) + A₂ (e₂ n)‖ + ‖A₂ (e₂ n)‖ := h_ineq
         _ < r1 + r2 := h
         _ = r := hr

   have h_dist : dist (A₁ (e₁ n)) 0 < r := by
      rw[← sub_zero (A₁ (e₁ n))] at h_norm
      rw[SeminormedAddGroup.dist_eq (A₁ (e₁ n)) 0]
      exact h_norm

   rw [← Metric.mem_ball] at h_dist
   apply h_dist

lemma A₁e₁_isBounded [Condition_C2 admm]: IsBounded (range (A₁ ∘ e₁) ) :=
   (isBounded_iff_subset_ball 0).2 (A₁e₁_isBounded' (admm_kkt := admm_kkt))

lemma open_mapping_e₁  (fullrank₁: Function.Injective admm.A₁):
      ∃ C > 0, ∀ n : ℕ, ‖e₁ n‖ ≤ C * ‖A₁ (e₁ n)‖ := by
   rcases inv_bounded₂ A₁ fullrank₁ with ⟨C, ⟨C_pos,hh⟩⟩
   use C; constructor
   ·  exact C_pos
   ·  intro n; exact hh (e₁ n)

lemma open_mapping_e₂  (fullrank₂: Function.Injective admm.A₂):
      ∃ C > 0, ∀ n : ℕ, ‖e₂ n‖ ≤ C * ‖A₂ (e₂ n)‖ := by
   rcases inv_bounded₂ A₂ fullrank₂ with ⟨C, ⟨C_pos,hh⟩⟩
   use C; constructor
   ·  exact C_pos
   ·  intro n; exact hh (e₂ n)

  lemma x₁_isBounded' [Condition_C2 admm](fullrank₁: Function.Injective admm.A₁): ∃ (r : ℝ), (range x₁) ⊆ ball 0 r := by
   rcases A₁e₁_isBounded' (admm_kkt := admm_kkt) with ⟨M, h₁⟩
   rcases open_mapping_e₁ (admm_kkt := admm_kkt) fullrank₁ with ⟨C, ⟨C_pos, h₂⟩⟩
   rw [range] at h₁
   use C * M + ‖x₁'‖; intro x hx; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩
   have A₁e₁_bd : ‖A₁ (e₁ n)‖ < M := by
      have : A₁ (e₁ n) ∈ {x | ∃ n, A₁ (e₁ n) = x} := by simp
      have : A₁ (e₁ n) ∈ ball 0 M := by tauto
      simp at this; exact this
   rw [← eq]; simp
   calc
      _ = ‖(x₁ n - x₁') + x₁'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖x₁ n - x₁'‖ + ‖x₁'‖ := by apply norm_add_le
      _ = ‖e₁ n‖ + ‖x₁'‖ := by rw [ AdaptiveADMM_Convergence_Proof.e₁]
      _ ≤ C * ‖A₁ (e₁ n)‖ + ‖x₁'‖ := by linarith [h₂ n]
      _ < C * M + ‖x₁'‖ := by linarith [mul_lt_mul_of_pos_left A₁e₁_bd C_pos]

lemma x₁_isBounded [Condition_C2 admm](fullrank₁: Function.Injective admm.A₁):
      IsBounded (range x₁) :=
   (isBounded_iff_subset_ball 0).2 (x₁_isBounded' (admm_kkt := admm_kkt) fullrank₁)

lemma x₂_isBounded' [Condition_C2 admm] (fullrank₂: Function.Injective admm.A₂):
      ∃ (r : ℝ), (range x₂ ) ⊆ ball 0 r := by
   rcases A₂e₂_isBounded' (admm_kkt := admm_kkt) with ⟨M, h₁⟩
   rcases open_mapping_e₂ (admm_kkt := admm_kkt) fullrank₂ with ⟨C, ⟨C_pos, h₂⟩⟩
   rw [range] at h₁
   use C * M + ‖x₂'‖; intro x hx; rw [range] at hx; simp at hx
   rcases hx with ⟨n,eq⟩
   have A₂e₂_bd : ‖A₂ (e₂ n)‖ < M := by
      have : A₂ (e₂ n) ∈ {x | ∃ n, A₂ (e₂ n) = x} := by simp
      have : A₂ (e₂ n) ∈ ball 0 M := by tauto
      simp at this; exact this
   rw [← eq]; simp
   calc
      _ = ‖(x₂ n - x₂') + x₂'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖x₂ n - x₂'‖ + ‖x₂'‖ := by apply norm_add_le
      _ = ‖e₂ n‖ + ‖x₂'‖ := by rw [ AdaptiveADMM_Convergence_Proof.e₂]
      _ ≤ C * ‖A₂ (e₂ n)‖ + ‖x₂'‖ := by linarith [h₂ n]
      _ < C * M + ‖x₂'‖ := by linarith [mul_lt_mul_of_pos_left A₂e₂_bd C_pos]

lemma x₂_isBounded [Condition_C2 admm] (fullrank₂: Function.Injective admm.A₂):
      IsBounded (range x₂) :=
   (isBounded_iff_subset_ball 0).2 (x₂_isBounded' (admm_kkt := admm_kkt) fullrank₂)

lemma y_isBounded' [Condition_C2 admm] :
      ∃ (r : ℝ), (range y) ⊆ ball 0 r := by
   rcases ey_isBounded' (admm_kkt := admm_kkt) with ⟨M, h⟩
   use M + ‖y'‖; intro x hx; rw [range] at hx h; simp at hx; simp
   rcases hx with ⟨n,eq⟩; rw [← eq]
   have ey_bd : ‖ey n‖ < M := by
      have : ey n ∈ {x | ∃ n, ey n = x} := by simp
      have : ey n ∈ ball 0 M := by tauto
      simp at this; exact this
   calc
      _ = ‖(y n) - y' + y'‖ := by rw [add_comm, add_sub, add_comm, add_sub_assoc, sub_self, add_zero]
      _ ≤ ‖y n - y'‖ + ‖y'‖ := by apply norm_add_le
      _ = ‖ey n‖ + ‖y'‖ := by rw [ AdaptiveADMM_Convergence_Proof.ey]
      _ < M + ‖y'‖ := by linarith

lemma y_isBounded  [Condition_C2 admm]:  IsBounded (range y) :=
   (isBounded_iff_subset_ball 0).2  (y_isBounded' (admm_kkt := admm_kkt))


omit admm_kkt in
lemma times_eq : (range (fun n => (x₁ n,  x₂ n, y n ) ))
⊆  (range x₁) ×ˢ  (range x₂) ×ˢ (range y) := by
   simp [range]
   intro x hx
   dsimp at hx
   simp only [mem_prod, mem_setOf_eq]
   rcases hx with ⟨n , hn⟩
   have h1 : x₁ n = x.1 := hn.symm ▸ rfl
   have h2 : x₂ n = x.2.1 := hn.symm ▸ rfl
   have h3 : y  n = x.2.2 := hn.symm ▸ rfl
   exact ⟨ ⟨ n , h1 ⟩, ⟨ n , h2 ⟩, ⟨ n , h3 ⟩⟩


lemma xy_isBounded [Condition_C2 admm]
      (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂):
      IsBounded (range (fun n => (x₁ n,  x₂ n, y n ) )) := by
   apply IsBounded.subset
   apply IsBounded.prod (x₁_isBounded (admm_kkt := admm_kkt) fullrank₁)
   apply IsBounded.prod (x₂_isBounded (admm_kkt := admm_kkt) fullrank₂) (y_isBounded (admm_kkt := admm_kkt))
   apply times_eq

structure Converge_Subseq_2 where
   x₁'' : E₁
   x₂'' : E₂
   y''  : F
   φ    : ℕ → ℕ
   hphi:StrictMono φ
   hconverge:Tendsto (fun n => (x₁ (φ n),  x₂ (φ n), y (φ n))) atTop (𝓝 (x₁'' , x₂'' , y''))

def Subseq_c2 [Condition_C2 admm]
      (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂): Converge_Subseq_2 (admm := admm) := by
   let x := tendsto_subseq_of_bounded (xy_isBounded (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
      (inSet (fun n => (x₁ n,  x₂ n, y n )) )
   choose x hx using x
   choose φ hphi1 using hx.2
   exact
      {
         x₁'' := x.1
         x₂'' := x.2.1
         y''  := x.2.2
         φ   := φ
         hphi:= hphi1.1
         hconverge:=hphi1.2
      }


end AdaptiveADMM_Convergence_Proof
