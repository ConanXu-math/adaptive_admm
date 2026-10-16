import Optlib.Algorithm.AdaptiveADMM.AdaptiveScheme
import Optlib.Algorithm.AdaptiveADMM.AdaptiveLemmas
import Optlib.Algorithm.AdaptiveADMM.AdaptiveProductBounds

noncomputable section

open Set InnerProductSpace Topology Filter Bornology Metric Real

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

variable(admm : ADMM E₁ E₂ F)

namespace AdaptiveADMM_Convergence_Proof

variable {admm} {admm_kkt : KKTPoint admm}


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

-- ==========================
-- Core definitions for Condition C2.
-- ==========================

-- Definition of θ_k corresponding to Eq. 48, with the sign under the square root adjusted for real values.
-- When rho decreases, ρₙ n / ρₙ (n+1) > 1, so subtract 1 from the squared ratio.
/-- Relative decreases of rho, measured by the inverse squared ratio. -/
def θ_k (admm : ADMM E₁ E₂ F)  : ℕ → ℝ :=
  fun n => if admm.ρₙ (n+1) < admm.ρₙ n then
            Real.sqrt ((admm.ρₙ n / admm.ρₙ (n+1))^2 - 1)
           else 0

-- g2 is defined in AdaptiveLemmas.lean:
-- g2 n = 1 / ρₙ n^2 * ‖ey n‖^2 + τ * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2

-- The auxiliary h2, like h1, describes quasi-monotone decrease.
-- h2 n ≥ 0 means g2(n+1) ≤ (1+θ²)*g2(n).


class Condition_C2 {E₁ E₂ F : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (admm : ADMM E₁ E₂ F)
    : Prop where
   theta_square_summable : ∃ S > 0, ∑' n : ℕ, ((θ_k admm) n)^2 ≤ S
   theta_square_summable' : Summable (f := fun n :ℕ  => ((θ_k admm) n)^2)
   one_theta_square_multipliable':
      ∃ S > 0 , ∏' n : ℕ, (1 + ((θ_k admm) n)^2) ≤ S
   one_theta_square_multipliable : Multipliable (f := fun n :ℕ  => (1 + ((θ_k admm) n)^2))

def h2 (admm : ADMM E₁ E₂ F) (admm_kkt : KKTPoint admm)  (n : ℕ) := - (g2 admm admm_kkt) (n+1) + (1 + ((θ_k admm) n)^2) * (g2 admm admm_kkt) n

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
local notation "H2" => AdaptiveADMM_Convergence_Proof.h2 admm admm_kkt


-- ==========================
-- Core lemmas.
-- ==========================

-- 1. Nonnegativity of g2.
lemma g2_nonneg  (n : ℕ) :
  0 ≤ g2 n := by
   unfold AdaptiveADMM_Convergence_Proof.g2
   apply add_nonneg
   apply add_nonneg
   have h1 : 0 ≤ 1 / (ρₙ n)^2 := by simp; exact sq_nonneg (ρₙ n)
   exact mul_nonneg h1 (sq_nonneg ‖ey n‖)
   have h2 : 0 ≤ τ * ‖A₂ (e₂ n)‖^2 := by exact mul_nonneg (le_of_lt admm.htau.1) (sq_nonneg ‖A₂ (e₂ n)‖)
   linarith
   have h3 : 0 ≤ T_HWY - τ := by linarith [(HWY_thm4_1_ineq (admm := admm))]
   have h4 : 0 ≤ τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      apply mul_nonneg
      apply mul_nonneg
      exact le_of_lt admm.htau.1
      exact h3
      exact sq_nonneg ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖
   linarith

-- 2. Bound on the squared rho ratio.
-- (ρ_n / ρ_{n+1})^2 ≤ 1 + θ_k^2
lemma rho_inv_square_ratio_bound  (n : ℕ) :
    (ρₙ n)^2 / (ρₙ (n+1))^2 ≤ 1 + (θ_k n)^2 := by
  by_cases h : ρₙ (n+1) < ρₙ n
  · simp [ AdaptiveADMM_Convergence_Proof.θ_k, h]
    have h_sub_nonneg : 0 ≤ (ρₙ n / ρₙ (n + 1)) ^ 2 - 1 := by
      rw [sub_nonneg, one_le_sq_iff_one_le_abs]
      -- Remove the absolute value.
      rw [abs_of_nonneg (div_nonneg (le_of_lt (admm.hρₙ_pos n)) (le_of_lt (admm.hρₙ_pos (n + 1))))]
      -- Multiply both sides by ρₙ (n + 1).
      rw [one_le_div (admm.hρₙ_pos (n + 1))]
      exact le_of_lt h
    -- Use (sqrt x)^2 = x.
    rw [Real.sq_sqrt h_sub_nonneg]
    ring_nf
    linarith
  · simp [ AdaptiveADMM_Convergence_Proof.θ_k, h]
    rw [ div_le_one (sq_pos_of_pos (admm.hρₙ_pos (n + 1)))]
    apply sq_le_sq'
    · linarith [admm.hρₙ_pos (n + 1), admm.hρₙ_pos n]
    · linarith


-- 3. Main bounding lemma corresponding to Eq. 55.
-- Goal: g2(n+1) + the residual term ≤ (1+θ²) * g2(n).

lemma HWY_ineq_55_0 : ∀ n : ℕ+,
    1 / ρₙ (n+1)^2 * (‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
      + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2)
      ≤ 1 / ρₙ (n+1)^2 * (‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2
      + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2)) := by
      intro n
      have h_thm := (HWY_Theorem_3_1 (admm := admm) (admm_kkt := admm_kkt)) n
      gcongr


lemma HWY_ineq_55_1 : ∀ n : ℕ+,
     1 / ρₙ (n+1)^2 * ‖ey (n+1)‖^2 + τ * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
     ≤(ρₙ (n)^2 / ρₙ (n+1)^2) * 1 / ρₙ n^2 * ‖ey n‖^2 + τ * ‖A₂ (e₂ n)‖^2 + (ρₙ (n)^2 / ρₙ (n+1)^2) * τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 - (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
   intro n
   have h_thm := (HWY_ineq_55_0 (admm := admm) (admm_kkt := admm_kkt)) n
   have h_rho_n_1_pos : 0 < ρₙ (n+1) := by
      exact admm.hρₙ_pos (n+1)
   have h_rho_n_pos : 0 < ρₙ n := by
      exact admm.hρₙ_pos n
   have h_inv_rho_sq_pos : 0 < 1 / (ρₙ (n+1)^2) := by
      exact div_pos zero_lt_one (pow_pos h_rho_n_1_pos 2)
    -- Final algebraic rearrangement.
   -- Use convert to match h_scaled to the target and expose the remaining equalities.
   -- Using 1 separates the equalities of the left and right sides.
   convert h_thm using 1
   ·field_simp
   ·field_simp

lemma HWY_ineq_55_2 : ∀ n : ℕ+,
     1 / ρₙ (n+1)^2 * ‖ey (n+1)‖^2 + τ * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
     ≤(1 + θ_k n^2) * 1 / ρₙ n^2 * ‖ey n‖^2 + (1 + θ_k n^2)* τ * ‖A₂ (e₂ n)‖^2 + (1 + θ_k n^2) * τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 - (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
      intro n
      have h_thm := (HWY_ineq_55_1 (admm := admm) (admm_kkt := admm_kkt)) n
      have h_ratio := (rho_inv_square_ratio_bound (admm := admm)) n
      have h_theta_nonneg : 0 ≤ θ_k n ^ 2 := sq_nonneg (θ_k n)
      have h_tau_pos : τ ≥  0 := by linarith[admm.htau.1]
      have : (1 + θ_k n^2) ≥ 1 := by
        have h_theta_nonneg : 0 ≤ θ_k n ^ 2 := sq_nonneg (θ_k n)
        linarith
      have : τ ≤  τ * (1 + θ_k n^2) := by
        ring_nf
        simp
        exact Left.mul_nonneg h_tau_pos h_theta_nonneg
      calc
         1 / ρₙ (n+1)^2 * ‖ey (n+1)‖^2 + τ * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
         ≤ (ρₙ (n)^2 / ρₙ (n+1)^2) * 1 / ρₙ n^2 * ‖ey n‖^2 + τ * ‖A₂ (e₂ n)‖^2 + (ρₙ (n)^2 / ρₙ (n+1)^2) * τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 - (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := h_thm
         _ ≤ (1 + θ_k n^2) * 1 / ρₙ n^2 * ‖ey n‖^2 + (1 + θ_k n^2)* τ * ‖A₂ (e₂ n)‖^2 + (1 + θ_k n^2) * τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 - (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := by
            gcongr
            linarith
            linarith [(HWY_thm4_1_ineq (admm := admm))]


lemma HWY_ineq_55_3 : ∀ n : ℕ+,
     1 / ρₙ (n+1)^2 * ‖ey (n+1)‖^2 + τ * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
     ≤(1 + θ_k n^2) * 1 / ρₙ n^2 * ‖ey n‖^2 + (1 + θ_k n^2)* τ * ‖A₂ (e₂ n)‖^2 + (1 + θ_k n^2) * τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 - (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := by
      intro n
      have := (HWY_ineq_55_2 (admm := admm) (admm_kkt := admm_kkt)) n
      linarith

lemma HWY_ineq_55_3' [Condition_C2 admm]: ∀ n : ℕ+,
     1 / ρₙ (n+1)^2 * ‖ey (n+1)‖^2 + τ * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
     ≤(1 + θ_k n^2) * 1 / ρₙ n^2 * ‖ey n‖^2 + (1 + θ_k n^2)* τ * ‖A₂ (e₂ n)‖^2 + (1 + θ_k n^2) * τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
      intro n
      have h_thm := (HWY_ineq_55_2 (admm := admm) (admm_kkt := admm_kkt)) n
      have h_nonneg : (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) ≥ 0 := by
        have h1:= admm.htau.1
        have h2:=admm.htau_range
        have h4:= mul_pos h1 h2
        have h6:= sq_nonneg ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖
        have h7:= sq_nonneg ‖A₂ (x₂ n - x₂ (n+1))‖
        have h8:= add_nonneg h6 h7
        have h9:= mul_nonneg (le_of_lt h4) h8
        linarith
      linarith

lemma HWY_ineq_55_4 : ∀ n : ℕ+,
     1 / ρₙ (n+1)^2 * ‖ey (n+1)‖^2 + τ * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
     ≤(1 + θ_k n^2) * (1 / ρₙ n^2 * ‖ey n‖^2 + τ * ‖A₂ (e₂ n)‖^2 +  τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) - (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
      intro n
      have h_thm := (HWY_ineq_55_3 (admm := admm) (admm_kkt := admm_kkt)) n
      calc 1 / ρₙ (n+1)^2 * ‖ey (n+1)‖^2 + τ * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      ≤(1 + θ_k n^2) * 1 / ρₙ n^2 * ‖ey n‖^2 + (1 + θ_k n^2)* τ * ‖A₂ (e₂ n)‖^2 + (1 + θ_k n^2) * τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2- (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := h_thm
      _ ≤(1 + θ_k n^2) * (1 / ρₙ n^2 * ‖ey n‖^2 + τ * ‖A₂ (e₂ n)‖^2 +  τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) - (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
        ring_nf
        simp

lemma HWY_ineq_56_0' : ∀ n : ℕ+,
    g2 (n+1) ≤ (1 + θ_k n^2) * g2 n - (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
      intro n
      have h_thm := (HWY_ineq_55_4 (admm := admm) (admm_kkt := admm_kkt)) n
      simp only  at h_thm
      unfold AdaptiveADMM_Convergence_Proof.g2
      exact h_thm

lemma HWY_ineq_56_0 : ∀ n : ℕ+,
    g2 (n+1) ≤ (1 + θ_k n^2) * g2 n:= by
      intro n
      have h_thm := (HWY_ineq_56_0' (admm := admm) (admm_kkt := admm_kkt)) n
      unfold AdaptiveADMM_Convergence_Proof.g2 at h_thm
      unfold AdaptiveADMM_Convergence_Proof.g2
      have h_nonneg : (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) ≥ 0 := by
        have h1:= admm.htau.1
        have h2:=admm.htau_range
        have h4:= mul_pos h1 h2
        have h6:= sq_nonneg ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖
        have h7:= sq_nonneg ‖A₂ (x₂ n - x₂ (n+1))‖
        have h8:= add_nonneg h6 h7
        have h9:= mul_nonneg (le_of_lt h4) h8
        linarith
      linarith

lemma HWY_ineq_56_1 [Condition_C2 admm]: ∀ n : ℕ,
  ∏ k ∈  Finset.range (n+1), (1 + (θ_k k)^2) ≤ ∏' k : ℕ, (1 + (θ_k k)^2) := by
   intro n
   let f : ℕ → ℝ:= fun k => 1 + (θ_k k)^2
   let S : Finset ℕ := Finset.range (n + 1)
   have hmult : Multipliable f := (Condition_C2.one_theta_square_multipliable (admm := admm))
   have h_ge_one : ∀ i : ℕ, (1 : ℝ) ≤ f i := by
      intro i
      simp only [f]
      linarith [sq_nonneg (θ_k i)]
   exact real_finset_prod_le_tprod_of_one_le f S h_ge_one hmult


lemma HWY_ineq_56_2 [Condition_C2 admm]: ∀ n : ℕ,
  (∏ k ∈ Finset.range (n+1), (1 + (θ_k k)^2)) * g2 1
  ≤ (∏' k : ℕ, (1 + (θ_k k)^2)) * g2 1 := by
   intro n
   exact mul_le_mul_of_nonneg_right ((HWY_ineq_56_1 (admm := admm)) n) ((g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) 1)
lemma HWY_ineq_56_4 [Condition_C2 admm]: ∀ n : ℕ,
  g2 (n+1)
  ≤ (∏ k ∈ Finset.range (n+1), (1 + (θ_k k)^2)) * g2 1 := by
  intro n
  induction' n with k i
  · simp
    have h_g2_pos : 0 ≤ g2 1 := (g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) 1
    have h_theta_pos : 0 ≤ (θ_k 0)^2 := sq_nonneg _
    nth_rewrite 1 [← one_mul (g2 1)]
    gcongr
    linarith
  ·
    let k_plus_1 : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩
    have h_step := (HWY_ineq_56_0 (admm := admm) (admm_kkt := admm_kkt)) k_plus_1
    rw [Finset.prod_range_succ]
    calc
      g2 (k + 2)
      ≤ (1 + (θ_k (k + 1))^2) * g2 (k + 1) := h_step
      _ ≤ (1 + (θ_k (k + 1))^2) * ((∏ k ∈ Finset.range (k + 1), (1 + (θ_k k)^2)) * g2 1) := by
        gcongr
      _ = ((∏ k ∈ Finset.range (k + 1), (1 + (θ_k k)^2)) * (1 + (θ_k (k + 1))^2)) * g2 1 := by
        ring

lemma HWY_ineq_56_3 [Condition_C2 admm]: ∀ n : ℕ,
   g2 (n+1)
  ≤ (∏' k : ℕ, (1 + (θ_k k)^2)) * g2 1
  := by
  intro n
  have h1 := (HWY_ineq_56_2 (admm := admm) (admm_kkt := admm_kkt)) n
  have h2 := (HWY_ineq_56_1 (admm := admm)) n
  have h3 := (HWY_ineq_56_4 (admm := admm) (admm_kkt := admm_kkt))  n
  linarith

lemma HWY_ineq_56_5 [Condition_C2 admm]: ∃ P >0 , ∀ n : ℕ, g2 (n+1)
  ≤ P * g2 1:= by
   obtain ⟨P, hP_pos, hP⟩ := (Condition_C2.one_theta_square_multipliable' (admm := admm))
   use P
   constructor
   ·exact hP_pos
   intro n
   have h1 := (HWY_ineq_56_3 (admm := admm) (admm_kkt := admm_kkt)) n
   have h2 : (∏' k : ℕ, (1 + (θ_k k)^2)) * g2 1 ≤ P * g2 1:= by
      exact mul_le_mul_of_nonneg_right hP ((g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) 1)
   exact le_trans h1 h2

lemma HWY_ineq_56 [Condition_C2 admm]: ∃ C > 0, ∀ n : ℕ+,
g2 n ≤ C := by
   obtain ⟨C, hC_pos, hC⟩ := (HWY_ineq_56_5 (admm := admm) (admm_kkt := admm_kkt))
   use C * g2 1 + 1
   constructor
   ·  apply add_pos_of_nonneg_of_pos
      exact mul_nonneg (le_of_lt hC_pos) ((g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) 1)
      norm_num
   ·  intro n
      have h1 := hC (n - 1)
      have h_sub : (↑n : ℕ) - 1 + 1 = (↑n : ℕ) := PNat.natPred_add_one n
      rw [h_sub] at h1
      have h2 := hC n
      linarith

lemma HWY_ineq_55_nat [Condition_C2 admm]: ∃ C > 0, ∀ n : ℕ,
g2 n ≤ C := by
   obtain ⟨C, hC_pos, hC⟩ := (HWY_ineq_56 (admm := admm) (admm_kkt := admm_kkt))
   let C₀ := g2 0
   use max C C₀ + 1
   constructor
   ·   apply add_pos_of_pos_of_nonneg
       apply lt_max_iff.2
       left
       exact hC_pos
       norm_num
   ·   intro n
       by_cases h : n = 0
       ·  rw [h]
          calc C₀ ≤ max C C₀ := le_max_right C C₀
          _ ≤ max C C₀ + 1 := by linarith
       ·  have n_pos : 0 < n := Nat.pos_of_ne_zero h
          calc g2 n ≤ C := by exact hC ⟨n, n_pos⟩
          _ ≤ max C C₀ := by exact le_max_left C C₀
          _ ≤ max C C₀ + 1 := by linarith

-- Goal: g2(n+1) + the residual term ≤ (1+θ²) * g2(n).
lemma HWY_ineq_55_5 [Condition_C2 admm]: ∀ n : ℕ+,
    (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2)
    ≤ - g2 (n+1) + (1 + (θ_k n)^2) * g2 n := by
   intro n
   have h_thm := (HWY_ineq_56_0' (admm := admm) (admm_kkt := admm_kkt)) n
   unfold AdaptiveADMM_Convergence_Proof.g2 at h_thm
   unfold AdaptiveADMM_Convergence_Proof.g2
   linarith

lemma HWY_ineq_57_0 [Condition_C2 admm]: ∀ n : ℕ+,
    (1/3) * (1 + τ - τ^2) * τ  * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2)
    ≤ H2 n:= by
   intro n
   have := (HWY_ineq_55_5 (admm := admm) (admm_kkt := admm_kkt)) n
   unfold AdaptiveADMM_Convergence_Proof.h2
   linarith

lemma g2_summable_0 [Condition_C2 admm]  :∃ C >0,∀ n : ℕ,
    ∑ i ∈ Finset.range n, (θ_k (i+1))^2 * g2 (i+1)
   ≤  ∑ i ∈ Finset.range n, (θ_k (i+1)^2) * C := by
   obtain ⟨C, hC_pos, hC⟩ := (HWY_ineq_55_nat (admm := admm) (admm_kkt := admm_kkt))
   use C
   constructor
   exact hC_pos
   intro n
   apply Finset.sum_le_sum
   intro i hi
   exact mul_le_mul_of_nonneg_left (hC (i+1)) (sq_nonneg _)

lemma g2_summable_0_sum [Condition_C2 admm]  :∀ n : ℕ,
    ∑ i ∈ Finset.range n, (θ_k (i+1))^2 ≤ ∑' i : ℕ, (θ_k (i+1))^2:= by
      intro n
      let f : ℕ → ℝ:= fun k => (θ_k (k+1))^2
      let S : Finset ℕ := Finset.range n
      apply Summable.sum_le_tsum
      have h_ge_zero : ∀ i : ℕ, i ∉ S → (0:ℝ) ≤ f i := by
        intro i _
        show (0 : ℝ) ≤ f i
        simp only [f]
        linarith [sq_nonneg (θ_k (i+1))]
      exact h_ge_zero
      let f':ℕ → ℝ:= fun k => (θ_k k)^2
      show Summable (fun i => f' (i + 1))
      rw[summable_nat_add_iff 1]
      exact (Condition_C2.theta_square_summable' (admm := admm))

lemma theta_square_summable [Condition_C2 admm]  : Summable (fun n ↦ θ_k (n+1) ^ 2) := by
   let f':ℕ → ℝ:= fun k => (θ_k k)^2
   show Summable (fun i => f' (i + 1))
   rw[summable_nat_add_iff 1]
   exact (Condition_C2.theta_square_summable' (admm := admm))

lemma theta_square_summable' [Condition_C2 admm]  :
∃ S > 0, ∑' (n : ℕ), θ_k (n+1) ^ 2 ≤ S := by
   obtain ⟨C, hC_pos, hC⟩ := (Condition_C2.theta_square_summable (admm := admm))
   use C
   constructor
   exact hC_pos
   have:∑' (n : ℕ), θ_k (n) ^ 2 ≥ ∑' (n : ℕ), θ_k (n+1) ^ 2 := by
      rw [tsum_eq_zero_add']
      have h1:= sq_nonneg (θ_k 0)
      linarith
      exact (theta_square_summable (admm := admm))
   calc ∑' (n : ℕ), θ_k (n+1) ^ 2
       ≤ ∑' (n : ℕ), θ_k n ^ 2 := this
     _ ≤ C := hC

lemma g2_summable_0_sum' [Condition_C2 admm]  :
   ∃ C >0 ,∀ n : ℕ,
   ∑ i ∈ Finset.range n, (θ_k (i+1))^2 ≤ C := by
   obtain ⟨C, hC_pos, hC⟩ :=  (theta_square_summable' (admm := admm))
   use C
   constructor
   ·  exact hC_pos
   ·  intro n
      have h1 := (g2_summable_0_sum (admm := admm)) n
      linarith


lemma g2_summable_1 [Condition_C2 admm]  :∃ C >0,∀ n : ℕ,
    ∑ i ∈ Finset.range n, (θ_k (i+1))^2 * g2 (i+1)
   ≤  C := by
    obtain ⟨C1, hC_pos1,hC1⟩ := (g2_summable_0 (admm := admm) (admm_kkt := admm_kkt))
    obtain ⟨C2, hC_pos2, hC2⟩ := (g2_summable_0_sum' (admm := admm))
    use C1 * C2
    constructor
    exact mul_pos hC_pos1 hC_pos2
    intro n
    have h1 := hC1 n
    have h2 := hC2 n
    have : (∑ i ∈ Finset.range n, (θ_k (i+1))^2) * C1 ≤ C2 * C1 := by
        gcongr
    have :(∑ i ∈ Finset.range n, (θ_k (i+1))^2) * C1 = ∑ i ∈ Finset.range n, (θ_k (i+1))^2 * C1 := by
        rw [Finset.sum_mul]
    linarith

lemma h2_summable_0 [Condition_C2 admm]  : ∀ n : ℕ, ∑ i ∈ Finset.range n, H2 (i+1) = g2 1 - g2 (n+1) + ∑ i ∈ Finset.range n, (θ_k (i+1))^2* (g2 (i+1)) := by
   intro n
   calc
      _ = ∑ i ∈ Finset.range n, (- g2 (i+1+1) + (1 + (θ_k (i+1))^2)* (g2 (i+1))) := by
         unfold AdaptiveADMM_Convergence_Proof.h2
         simp
      _ = ∑ i ∈ Finset.range n, ( g2 (i+1) - g2 (i+1+1) +  (θ_k (i+1))^2 * (g2 (i+1))):= by
         congr
         ext i
         ring_nf
      _ = ∑ i ∈ Finset.range n, ( g2 (i+1) - g2 (i+1+1)) + ∑ i ∈ Finset.range n, (θ_k (i+1))^2 * (g2 (i+1)) := by
         rw[Finset.sum_add_distrib]
      _ = g2 1 - g2 (n+1) + ∑ i ∈ Finset.range n,  (θ_k (i+1))^2 * (g2 (i+1)) := by
         rw[Finset.sum_range_sub']


lemma h2_summable_1 [Condition_C2 admm]  : ∃ C >0,∀ n : ℕ, ∑ i ∈ Finset.range n, H2 (i+1) ≤ C := by
   rcases (g2_summable_1 (admm := admm) (admm_kkt := admm_kkt)) with ⟨C1,hC_pos1,hC1⟩
   rcases (HWY_ineq_55_nat (admm := admm) (admm_kkt := admm_kkt)) with ⟨C2,hC_pos2,hC2⟩
   use 2* C2 + C1
   constructor
   exact add_pos (mul_pos (by norm_num) hC_pos2) hC_pos1
   intro n
   rw [(h2_summable_0 (admm := admm) (admm_kkt := admm_kkt))]
   have := (g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) 1
   have := (g2_nonneg (admm := admm) (admm_kkt := admm_kkt)) (n+1)
   have := hC1 (n)
   have := hC2 (n+1)
   have := hC2 1; grind

lemma h2_eq'' [Condition_C2 admm]  : ∀ n : ℕ, H2 (n+1) ≥ (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (n+2)) + A₂ (x₂ (n+2)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ (n+2))‖^2):= by
   intro n
   have : n+1>0 := by linarith
   have h := (HWY_ineq_57_0 (admm := admm) (admm_kkt := admm_kkt)) (n+1).toPNat'
   exact h

lemma h2_eq''' [Condition_C2 admm]  : ∀ n : ℕ,(1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (n+2)) + A₂ (x₂ (n+2)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ (n+2))‖^2)≥ 0:= by
    intro n
    have h1:= admm.htau.1
    have h2:=admm.htau_range
    have h3:= sq_pos_of_pos (admm.hρₙ_pos (n+1))
    have h4:= mul_pos h1 h2
    have h5:= mul_pos h4 h3
    have :(1 + τ - τ^2) * τ ≥ 0 := by linarith[h5]
    have h6:= sq_nonneg ‖A₁ (x₁ (n+2)) + A₂ (x₂ (n+2)) - b‖
    have h7:= sq_nonneg ‖A₂ (x₂ (n+1)- x₂ (n+2))‖
    have h8:= add_nonneg h6 h7
    have h9:= mul_nonneg this h8
    linarith
lemma h2_nonneg [Condition_C2 admm]  : ∀ n : ℕ, H2 (n+1) ≥ 0:= by
   intro n
   have := (h2_eq'' (admm := admm) (admm_kkt := admm_kkt)) n
   have : n+1>0 := by linarith
   have := (h2_eq''' (admm := admm)) n
   linarith


lemma  h2_summable [Condition_C2 admm]  :  Summable (fun n : ℕ => H2 (n+1)) := by
   rcases (h2_summable_1 (admm := admm) (admm_kkt := admm_kkt)) with ⟨C, hC_pos, hC⟩
   apply summable_of_sum_range_le (c:=C)
   intro n
   have :=(h2_nonneg (admm := admm) (admm_kkt := admm_kkt)) n
   linarith
   intro n
   have := hC n; grind

lemma HWY_ineq_57 [Condition_C2 admm]:∀ (n : ℕ), ∑ i ∈ Finset.range n, (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (i+2)) + A₂ (x₂ (i+2)) - b‖^2 + ‖A₂ (x₂ (i+1) - x₂ (i+2))‖^2) ≤
   ∑ i ∈ Finset.range n, H2 (i+1) := by
   intro n
   gcongr with i _
   have : i+1 > 0 := by linarith
   have h1 := (HWY_ineq_57_0 (admm := admm) (admm_kkt := admm_kkt)) (i+1).toPNat'
   exact h1

lemma Summable_2' [Condition_C2 admm]:∀ (i : ℕ),  (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (i+2)) + A₂ (x₂ (i+2)) - b‖^2 + ‖A₂ (x₂ (i+1) - x₂ (i+2))‖^2) ≤
   H2 (i+1) := by
   intro i
   have : i+1 > 0 := by linarith
   have h1 := (HWY_ineq_57_0 (admm := admm) (admm_kkt := admm_kkt)) (i+1).toPNat'
   exact h1

include admm_kkt in
lemma Summable_2 [Condition_C2 admm] :
   Summable (fun n => (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n) - x₂ (n+1))‖^2)) := by
   let f := fun n => (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n) - x₂ (n+1))‖^2)
   show Summable f
   rw[← summable_nat_add_iff 1]
   let fsucc := fun n => (f (n+1))
   show Summable fsucc
   apply summable_of_nonneg_of_le
   unfold fsucc
   unfold f
   intro n
   have := (h2_eq''' (admm := admm)) n
   linarith
   exact (Summable_2' (admm := admm) (admm_kkt := admm_kkt))
   exact (h2_summable (admm := admm) (admm_kkt := admm_kkt))

include admm_kkt in
lemma converge_zero_2 [Condition_C2 admm] : Tendsto (fun n => (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n) - x₂ (n+1))‖^2)) atTop (nhds 0) := by
  apply Summable.tendsto_atTop_zero (Summable_2 (admm := admm) (admm_kkt := admm_kkt))

lemma norm_symm [Condition_C2 admm]  : ∀ n : ℕ, ‖A₂ (x₂ (n) - x₂ (n+1))‖ = ‖A₂ (x₂ (n+1) - x₂ n)‖ := by
   intro n
   rw [← norm_neg]
   congr 1
   simp [sub_eq_add_neg, add_comm]

include admm_kkt in
theorem HWY_Convergence_2 [Condition_C2 admm] :
    Tendsto (fun n => ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ n)‖^2) atTop (nhds 0) := by
    have htau_pos : 0 < τ := admm.htau.1
    have htau_range := admm.htau_range
    let c := (1/3) * (1 + τ - τ^2) * τ
    have hconst : 0 < c := by
        apply mul_pos
        apply mul_pos
        apply mul_pos
        linarith
        linarith
        linarith
        linarith
    have h_lim := converge_zero_2 (admm := admm) (admm_kkt := admm_kkt)
    have h_congr : ∀ n, (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) =
                        (1/3) * (1 + τ - τ^2) * τ * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ (n+1) - x₂ n)‖^2) := by
      intro n
      congr 3
      rw [(norm_symm (admm := admm))]
    simp_rw [h_congr] at h_lim
    rw [show (0 : ℝ) = (1/3) * (1 + τ - τ^2) * τ * 0 by ring] at h_lim
    have := Tendsto.const_mul ((1/3) * (1 + τ - τ^2) * τ)⁻¹ h_lim
    field_simp at this
    exact this


include admm_kkt in
theorem HWY_Convergence_2_residual' [Condition_C2 admm]:
    Tendsto (fun n => ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2) atTop (nhds 0) := by
  have h_sum := (HWY_Convergence_2 (admm := admm) (admm_kkt := admm_kkt))
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

include admm_kkt in
theorem HWY_Convergence_2_increment [Condition_C2 admm] :
    Tendsto (fun n => ‖A₂ (x₂ (n+1) - x₂ n)‖^2) atTop (nhds 0) := by
   have h_sum := (HWY_Convergence_2 (admm := admm) (admm_kkt := admm_kkt))
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
end AdaptiveADMM_Convergence_Proof
