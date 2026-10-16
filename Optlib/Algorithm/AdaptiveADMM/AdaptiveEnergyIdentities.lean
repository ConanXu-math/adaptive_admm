import Optlib.Algorithm.AdaptiveADMM.AdaptiveOptimality
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

lemma Φ_isdescending_eq1 : ∀ n , A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b
      = (1 / (τ * ρₙ (n + 1))) • (y (n + 1) - y n):= by
   intro n
   rw [admm.itey n,add_comm (y n)]
   simp only [one_div, mul_inv_rev, add_sub_cancel_right]
   rw [smul_smul, mul_assoc]
   nth_rw 2 [← mul_assoc]
   have htau1 : τ⁻¹ * τ = 1:= by
      refine inv_mul_cancel₀ ?h
      linarith[admm.htau.1];
   have hrho1 :  (ρₙ (n + 1) : ℝ)⁻¹ * (ρₙ (n + 1) : ℝ) = 1:= by
      refine inv_mul_cancel₀ ?h
      linarith[admm.hρₙ_pos (n + 1)];
   rw [htau1 , one_mul, hrho1, one_smul]

lemma Φ_isdescending_eq2 : ∀ n , (1 / (τ * ρₙ (n + 1))) • (y (n + 1) - y n)
      = (1 / (τ * ρₙ (n + 1))) • (ey (n + 1) - ey n):= by
   intro n
   calc
      _ = (1 / (τ * ρₙ (n + 1))) • (y (n + 1) - y' + y' - y n) := by rw [sub_add, sub_self, sub_zero]
      _ = (1 / (τ * ρₙ (n + 1))) • (y (n + 1) - y' - (y n - y')) := by simp only [one_div,
        mul_inv_rev, sub_add_cancel, sub_sub_sub_cancel_right]

lemma Φ_isdescending_eq3  : ∀ n , A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b
      = A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)) := by
   intro n
   calc
      _ = A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - (A₁ x₁' + A₂ x₂') := by rw [admm_kkt.h.eq]
      _ = A₁ (x₁ (n + 1)) - A₁ x₁' + (A₂ (x₂ (n + 1)) - A₂ x₂') :=
         add_sub_add_comm (A₁  (x₁ (n + 1))) (A₂ (x₂ (n + 1))) (A₁  x₁') (A₂ x₂')
      _ = A₁ ((x₁ (n + 1)) - x₁') + A₂ ((x₂ (n + 1)) - x₂') := by simp only [map_sub]
      _ = A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)) := by rw [ AdaptiveADMM_Convergence_Proof.e₁, AdaptiveADMM_Convergence_Proof.e₂]

lemma Φ_isdescending_eq3'  : ∀ n : ℕ+ , A₁ (x₁ n) + A₂ (x₂ n) - b = A₁ (e₁ n) + A₂ (e₂ n) := by
   intro n
   have := Φ_isdescending_eq3 (admm_kkt := admm_kkt) n.natPred
   have h: n = n.natPred + 1 := by simp only [PNat.natPred_add_one]
   rw[← h] at this
   exact this

lemma subgradientAt_mono_u  : ∀ n : ℕ+,
      (0 : ℝ) ≤ ⟪u n + A₁† y', x₁ n - x₁'⟫ := by
   intro n
   calc
      _ = ⟪u n - (- A₁† y'), x₁ n - x₁'⟫ := by
         simp [sub_eq_add_neg]
      _ ≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply u_inthesubgradient
         exact admm_kkt.h.subgrad₁
lemma subgradientAt_mono_v : ∀ n : ℕ+,
      (0 : ℝ) ≤ ⟪v n + A₂† y', x₂ n - x₂'⟫ := by
   intro n
   calc
      _ = ⟪v n - (- A₂† y'), x₂ n - x₂'⟫ := by simp [ AdaptiveADMM_Convergence_Proof.v]
      _ ≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply v_inthesubgradient
         exact admm_kkt.h.subgrad₂


lemma expended_u_gt_zero : ∀ n, (0 : ℝ) ≤
      ⟪( -ey (n + 1) - ((1-τ) * ρₙ (n + 1)) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
      - (ρₙ (n + 1) • (A₂ (x₂ (n) - x₂ (n+1))))), (A₁ (e₁ (n + 1)))⟫ := by
   intro n
   let Ae1 := A₁ (e₁ (n + 1))
   let e' := e₁ (n + 1)
   let block := -ey (n + 1) - ((1-τ) * ρₙ (n + 1)) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
   - (ρₙ (n + 1) • (A₂ (x₂ (n) - x₂ (n+1))))
   let u' := - A₁† (y (n + 1) + ((1-τ) * ρₙ (n + 1)) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
         + (ρₙ (n + 1) • (A₂ (x₂ (n) - x₂ (n+1)))))
   let x_diff := x₁ (n + 1) - x₁'
   let succ_n := Nat.toPNat' (n + 1)
   calc
      _= ⟪block, Ae1⟫ := by rfl
      _= ⟪A₁† block, e'⟫ := by
         simpa [Ae1, e'] using (ContinuousLinearMap.adjoint_inner_left A₁ e' block).symm
      _= ⟪u' + A₁† y', x_diff⟫ := by
         let block₁ := y (n + 1) + ((1-τ) * ρₙ (n + 1)) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))) + (ρₙ (n + 1) • (A₂ (x₂ (n) - x₂ (n+1))))
         have split_block : -block = block₁ - y' := by
            simp[block, block₁]
            have split_ey :  ey (n + 1) = (y (n + 1)) - y' := by rfl
            rw [split_ey]
            simp
            rw [sub_eq_add_neg,neg_sub (y' - y (n + 1)),add_comm,sub_eq_add_neg, neg_sub]
            rw [add_assoc,← smul_add,smul_sub]
            let A := ((1 - τ) * ρₙ (n + 1)) • ((A₁) (e₁ (n + 1)) + (A₂) (e₂ (n + 1)))
            let C := y (n + 1)
            let D := ρₙ (n + 1) • ((A₂) (x₂ n))
            let E := ρₙ (n + 1) • ((A₂) (x₂ (n + 1)))
            change A + (C - y' + (D - E)) = C + A + (D - E) - y'
            rw [← add_assoc,sub_eq_add_neg,← add_assoc,add_comm A C]
            rw [add_assoc,add_comm (-y') (D - E),← add_assoc,← sub_eq_add_neg]
         rw [← neg_neg block,split_block,neg_sub,A₁†.map_sub]
         have u'_eq : - A₁† block₁ = u' := by
            simp[u']
            rw [← A₁†.map_smul, ← A₁†.map_smul,smul_sub,← A₁†.map_smul, ← A₁†.map_smul]
            rw [← A₁†.map_sub,← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg]
            rw [← A₁†.map_add, ← A₁†.map_add, ← A₁†.map_add]
            simp[block₁]
            rw [← smul_neg, neg_sub,smul_sub]
         have Aty'_eq : A₁† y' = A₁† y' := rfl
         rw [← u'_eq, Aty'_eq, add_comm, sub_eq_add_neg]
         simp[e', x_diff]
         rfl
      _= ⟪(u (succ_n) + A₁† y'), (x₁ (succ_n) - x₁')⟫ := by rfl
      _≥ 0 := by apply subgradientAt_mono_u

lemma expended_v_gt_zero : ∀ n,
      ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • ((A₁ (e₁ (n + 1))) + (A₂ (e₂ (n + 1)))) , A₂ (e₂ (n + 1)) ⟫ ≥ (0 : ℝ) := by
   intro n
   let succ_n := Nat.toPNat' (n + 1)
   let ey' := ey (succ_n)
   let e₁' := e₁ (succ_n)
   let e₂' := e₂ (succ_n)
   let y_k_1 := y (succ_n)
   let v_k_1 := v (succ_n)
   let x_diff := x₂ (succ_n) - x₂'
   calc
   _ = ⟪ -ey' - ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂') , A₂ e₂' ⟫ := by rfl
   _ = ⟪ A₂† (-ey' - ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂')) , e₂' ⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_left]
   _ = ⟪ -A₂† (ey' + ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂')) , e₂' ⟫ := by
      rw [sub_eq_add_neg, ← neg_add, A₂†.map_neg]
   _ = ⟪ -A₂† (y_k_1 - y' + ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂')) , e₂' ⟫ := by
      have sub : ey' = y_k_1 - y' := by simp [ey', y_k_1] ; rfl
      rw [sub]
   _ = ⟪ -A₂† (y_k_1 + ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂')) + A₂† y' , e₂' ⟫ := by
      rw [sub_eq_add_neg, add_comm y_k_1, add_assoc, A₂†.map_add]
      simp
   _ = ⟪ v_k_1 + A₂† y' , x_diff ⟫ := by rfl
   _ ≥ (0 : ℝ) := by apply subgradientAt_mono_v


lemma starRingEnd_eq_R (x : ℝ) : (starRingEnd ℝ) x = x := rfl

set_option maxHeartbeats 500000 in
lemma expended_u_v_gt_zero :
∀ n, ⟪ ey (n + 1), -(A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))) ⟫
      - (1 - τ) * ρₙ (n + 1) * ‖A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2
      + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), A₁ (e₁ (n + 1)) ⟫ ≥ 0 := by
  intro n
  set A_e_sum := A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)) with hAes
  set Ae1 := A₁ (e₁ (n + 1)) with hAe1
  set Ae2 := A₂ (e₂ (n + 1)) with hAe2
  have hv : ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum, Ae2 ⟫ ≥ (0 : ℝ) := by
    simpa [A_e_sum, Ae2] using (expended_v_gt_zero (admm:=admm) (admm_kkt:=admm_kkt) n)
  have hu : ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum - ρₙ (n + 1) • A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫ ≥ (0 : ℝ) := by
    simpa [A_e_sum, Ae1, sub_eq_add_neg] using (expended_u_gt_zero (admm:=admm) (admm_kkt:=admm_kkt) n)
  have hsum :
      0 ≤ ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum, Ae2 ⟫
        + ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum - ρₙ (n + 1) • A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫ :=
    add_nonneg hv hu
  set U := -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum with hU
  set Z := A₂ (x₂ n - x₂ (n + 1)) with hZ
  have hrewrite :
      ⟪ ey (n + 1), -A_e_sum ⟫
      - (1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2
      + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫
      =
      ⟪ U, Ae2 ⟫ + ⟪ U - ρₙ (n + 1) • Z, Ae1 ⟫ := by
    have h1 : ⟪ U - ρₙ (n + 1) • Z, Ae1 ⟫ = ⟪ U, Ae1 ⟫ + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ := by
      simpa [sub_eq_add_neg] using (inner_add_left U (-ρₙ (n + 1) • Z) Ae1)
    have h2 : ⟪ U, Ae2 ⟫ + ⟪ U, Ae1 ⟫ = ⟪ U, Ae1 + Ae2 ⟫ := by
      rw [add_comm]
      simpa using (inner_add_right (𝕜 := ℝ) U Ae1 Ae2).symm
    have h3 : Ae1 + Ae2 = A_e_sum := by simp [hAes]
    have h4 : ⟪ U, A_e_sum ⟫ = ⟪ -ey (n + 1), A_e_sum ⟫ + ⟪ -((1 - τ) * ρₙ (n + 1)) • A_e_sum, A_e_sum ⟫ := by
      have : U = (-ey (n + 1)) + ( -((1 - τ) * ρₙ (n + 1)) • A_e_sum) := by
        simp [U, sub_eq_add_neg]
      simp [this, inner_add_left]
    have h5 : ⟪ -ey (n + 1), A_e_sum ⟫ = ⟪ ey (n + 1), -A_e_sum ⟫ := by
      simp [inner_neg_right]
    have h6 : ⟪ -((1 - τ) * ρₙ (n + 1)) • A_e_sum, A_e_sum ⟫ = -(1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2 := by
      simp [real_inner_smul_left, real_inner_self_eq_norm_sq, mul_comm, mul_assoc]; grind
    have h7 : ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ = ρₙ (n + 1) * ⟪ -Z, Ae1 ⟫ := by
      simp [real_inner_smul_left]
    have h8 : -Z = -A₂ (x₂ n - x₂ (n + 1)) := by simp [Z]
    have h6' :
        -(1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2
        = -⟪((1 - τ) * ρₙ (n + 1)) • A_e_sum, A_e_sum⟫ := by
      simpa [inner_neg_left] using h6.symm
    calc
      ⟪ ey (n + 1), -A_e_sum ⟫ - (1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2 + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫
          = (⟪ ey (n + 1), -A_e_sum ⟫ + (-(1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2)) + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫ := by
            ring
      _ = (⟪ -ey (n + 1), A_e_sum ⟫ + ⟪ -((1 - τ) * ρₙ (n + 1)) • A_e_sum, A_e_sum ⟫) + ρₙ (n + 1) * ⟪ -Z, Ae1 ⟫ := by
            rw [h5, h6', h8]; simp
      _ = ⟪ U, A_e_sum ⟫ + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ := by
            have := congrArg (fun t => t + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫) h4
            simpa [real_inner_smul_left] using this.symm
      _ = ⟪ U, Ae1 + Ae2 ⟫ + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ := by
            simp [h3]
      _ = (⟪ U, Ae2 ⟫ + ⟪ U, Ae1 ⟫) + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ := by
            simp [inner_add_right, add_comm]
      _ = ⟪ U, Ae2 ⟫ + ⟪ U - ρₙ (n + 1) • Z, Ae1 ⟫ := by
            simp [sub_eq_add_neg, inner_add_left, real_inner_smul_left, add_comm, add_left_comm, add_assoc]
  have : ⟪ ey (n + 1), -A_e_sum ⟫
          - (1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2
          + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫ ≥ 0 := by
    have h' : 0 ≤ ⟪ U, Ae2 ⟫ + ⟪ U - ρₙ (n + 1) • Z, Ae1 ⟫ := hsum
    simpa [hrewrite.symm] using h'
  simp [A_e_sum, Ae1] at this
  exact le_of_le_of_eq hsum (id (Eq.symm hrewrite))


lemma substitution1 : ∀ n , - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫ = ρₙ (n + 1) * ⟪(A₂ (x₂ n - x₂ (n+1))),(A₂ (e₂ (n+1)))⟫:= by
   intro n
   rw [neg_mul (ρₙ (n + 1)) ⟪(A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫]
   rw [← mul_neg]
   rw [← inner_neg_left (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1)))]
   rw [← map_neg A₂ (x₂ (n+1) - x₂ n)]
   rw [neg_sub (x₂ (n+1)) (x₂ n)]

lemma substitution2 : ∀ n , A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b - A₂ (e₂ (n+1)) = A₁ (e₁ (n+1)) := by
   intro n
   have h := Φ_isdescending_eq3 (admm_kkt := admm_kkt) n
   simp [h]

lemma Φ_isdescending_inequ1 : ∀ n , 1/(τ * ρₙ (n + 1)) * ⟪(ey (n+1)) ,((ey n)-(ey (n+1)))⟫
      - (1-τ)*ρₙ (n + 1)*‖admm.A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)),(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)⟫
         -ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)),(A₂ (e₂ (n+1))) ⟫ ≥ 0 := by
   intro n
   let pm1 := 1 / (τ * ρₙ (n + 1))
   let pm2 := (1 - τ) * ρₙ (n + 1)
   have h1:  pm1 * ⟪ (ey (n+1)),((ey n)-(ey (n+1)))⟫
      = (⟪ ey (n + 1), -((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))) ⟫) := by
      calc  pm1 * ⟪ ey (n+1), ((ey n)-(ey (n+1))) ⟫
         _ = ⟪ ey (n+1), pm1 • ((ey n)-(ey (n+1))) ⟫ := by
            rw [← real_inner_smul_right (ey (n+1)) ((ey n)-(ey (n+1))) pm1]
         _ = ⟪ ey (n+1), pm1 • -((ey (n+1))-(ey n)) ⟫ := by
            rw [← neg_sub (ey (n+1)) (ey n)]
         _ = ⟪ ey (n+1), -(pm1 • ((ey (n+1))-(ey n))) ⟫ := by
            rw [smul_neg]
         _ = ⟪ ey (n+1), -(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ := by
            rw [← Φ_isdescending_eq2, ← Φ_isdescending_eq1]
         _ = ⟪ ey (n+1), -(A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))) ⟫ := by
            rw [Φ_isdescending_eq3]
   have h2:  pm2*‖admm.A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 = pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 := by
      rw [Φ_isdescending_eq3]
   have h3: ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ -ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₂ (e₂ (n+1))) ⟫
   =  ρₙ (n + 1) * ⟪ -A₂ (x₂ (n) - x₂ (n+1)), (A₁ (e₁ (n+1))) ⟫ := by
      calc ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
         -ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₂ (e₂ (n+1))) ⟫
         _ = ρₙ (n + 1) * ⟪ -A₂ (x₂ (n) - x₂ (n+1)), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
         - ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₂ (e₂ (n+1))) ⟫ := by
            rw [← neg_sub (x₂ n) (x₂ (n+1))]
            rw [map_neg A₂ (x₂ (n) - x₂ (n+1))]
         _ = - ρₙ (n + 1) * ⟪ A₂ (x₂ (n) - x₂ (n+1)), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
         - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1))) ⟫ := by
            rw [inner_neg_left (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)]
            simp
         _ = - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
         + ρₙ (n + 1) * ⟪ (A₂ (x₂ n - x₂ (n+1))), (A₂ (e₂ (n+1))) ⟫ := by
            rw [← substitution1]
            simp only [map_sub, neg_mul];rfl
         _ = ρₙ (n + 1) * ⟪ (A₂ (x₂ n - x₂ (n+1))), (A₂ (e₂ (n+1))) ⟫
         - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ := by
            ring
         _ = ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₂ (e₂ (n+1)) - (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)) ⟫ := by
            rw [← mul_sub]
            rw [← inner_sub_right (A₂ (x₂ (n) - x₂ (n+1))) (A₂ (e₂ (n+1))) ((A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))]
         _ = - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b - A₂ (e₂ (n+1))) ⟫ := by
            rw [← neg_sub (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) (A₂ (e₂ (n+1)))]
            rw [inner_neg_right]
            simp only [map_sub, mul_neg, neg_mul]
         _ = - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₁ (e₁ (n+1))) ⟫ := by
            rw [substitution2]
         _ = ρₙ (n + 1) * ⟪ -A₂ (x₂ (n) - x₂ (n + 1)), (A₁ (e₁ (n+1))) ⟫ := by
            rw [neg_mul (ρₙ (n + 1)) ⟪ (A₂ (x₂ (n) - x₂ (n + 1))), (A₁ (e₁ (n+1))) ⟫]
            rw [← mul_neg]
            rw [← inner_neg_left (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (e₁ (n+1)))]
   rw [h1,h2]
   have h4: ⟪ ey (n + 1), -((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))) ⟫
   - pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 +
   (ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ -ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1))) ⟫) = ⟪ ey (n + 1), -((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))) ⟫
   - pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 +
   ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ -ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1))) ⟫ := by ring
   rw [← h4,h3]
   exact expended_u_v_gt_zero n

include admm_kkt in
lemma A'υ_inthesubgradient : ∀ n : ℕ+ , - (A₂†) (υ n) ∈ SubderivAt f₂ (x₂ n):= by
   intro n
   rw [ AdaptiveADMM_Convergence_Proof.υ]
   have : v n = - A₂† (y n + (( 1 - τ) * ρₙ (n))•(A₁ (e₁ n) + A₂ (e₂ n))):= rfl
   rw[Φ_isdescending_eq3' , ← this]
   apply v_inthesubgradient

include admm_kkt in
lemma Φ_isdescending_inequ2 :∀ n : ℕ+ ,
      ⟪ - ( A₂† ( υ (n+1) - υ n )), (x₂ (n+1)) - (x₂ n) ⟫ ≥ ( 0 : ℝ ) := by
   intro n
   let A₂T := A₂†
   let A₂υn := - (A₂T ((υ) n))
   let A₂υn1 := - (A₂T ((υ) (n+1)))
   have h1 : A₂υn ∈ SubderivAt f₂ (x₂ n) := by apply A'υ_inthesubgradient (admm_kkt := admm_kkt)
   have h2 : A₂υn1 ∈ SubderivAt f₂ (x₂ (n+1)) := by apply A'υ_inthesubgradient (admm_kkt := admm_kkt) (n+1)
   have mono : ⟪ A₂υn1 - A₂υn, (x₂ (n+1) - x₂ n) ⟫ ≥ (0:ℝ):= subgradientAt_mono h2 h1
   have h: -(A₂T ((υ (n+1)) - (υ n))) = A₂υn1 - A₂υn := by
      calc
         -(A₂T ((υ (n+1)) - (υ n))) = - (A₂T (υ (n+1)) - A₂T (υ n)) := by continuity
         _=  (A₂T ((υ) n)) - (A₂T ((υ) (n+1))) := by simp
         _= - (A₂T ((υ) (n+1))) - (-(A₂T ((υ) n))) := by rw [sub_neg_eq_add,add_comm (- (A₂T ((υ) (n+1)))),sub_eq_add_neg]
         _= A₂υn1 - A₂υn := by rfl
   rwa [h]

include admm_kkt in
lemma Φ_isdescending_inequ3 : ∀ n : ℕ+ ,
      ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ ≤ (M admm) (n+1) := by
   intro n
   let A₂_x_diff := A₂ (x₂ (n+1) - x₂ n)
   let r_n := A₁ (x₁ n) + A₂ (x₂ n) - b
   let r_n_1 := A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b
   let υ_diff := υ (n+1) - υ n
   let y_diff := y (n+1) - y n
   let x_diff := x₂ (n+1) - x₂ n
   let A₂T := A₂†
   have h: ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ =
      (M admm) (n+1) + ⟪ υ_diff, A₂_x_diff ⟫ := by
         calc
         ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ =
         (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + (τ * ρₙ (n + 1)) * ⟪ A₂_x_diff, r_n_1 ⟫ := by
            linarith
         _= (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + ⟪ A₂_x_diff, (τ * ρₙ (n + 1)) • r_n_1 ⟫ := by
            rw [inner_smul_right]
         _= (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + ⟪ A₂_x_diff, y_diff ⟫ := by
            have : (τ * ρₙ (n + 1)) • r_n_1 = y_diff := by
               simp [r_n_1, y_diff]
               rw [Φ_isdescending_eq1, ← mul_smul, mul_div, mul_one, div_self, one_smul]
               intro H
               rw [mul_eq_zero] at H
               rcases H with _ | _
               · linarith [admm.htau]
               · linarith [admm.hρₙ_pos (n + 1)]
            rw [this]
         _= (1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫ - (1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫
          + (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + ⟪ A₂_x_diff, y_diff ⟫ := by
            rw [sub_self ((1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫), zero_add]
         _= (M admm) (n+1) - (1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫
          + (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + ⟪ A₂_x_diff, y_diff ⟫ := by
            rw [ AdaptiveADMM_Convergence_Proof.M];rfl
         _= (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ - (1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫ +
            (M admm) (n + 1) + ⟪ A₂_x_diff, y_diff ⟫ := by
            ring_nf
         _= ⟪ A₂_x_diff, ((1 - τ) * ρₙ (n + 1)) • r_n_1 - ((1 - τ) * ρₙ n) • r_n ⟫ + (M admm) (n+1) + ⟪ A₂_x_diff, y_diff ⟫ := by
            rw [← inner_smul_right,← inner_smul_right,← inner_sub_right]
         _= ⟪ A₂_x_diff, ((1 - τ) * ρₙ (n + 1)) • r_n_1 - ((1 - τ) * ρₙ n) • r_n + y_diff ⟫ + (M admm) (n+1) := by
            rw [inner_add_right];ring_nf
         _= ⟪ A₂_x_diff, y (n+1) + ((1 - τ) * ρₙ (n + 1)) • r_n_1 - y n - ((1 - τ) * ρₙ n) • r_n ⟫ + (M admm) (n+1) := by
            simp [y_diff]
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
         _= ⟪ A₂_x_diff, υ (n+1) - υ n ⟫ + (M admm) (n+1):= by
            rw [ AdaptiveADMM_Convergence_Proof.υ, AdaptiveADMM_Convergence_Proof.υ]
            simp[r_n_1,r_n]
            rw [sub_sub] -- Reassociate subtraction.
         _= ⟪ A₂_x_diff, υ_diff ⟫ + (M admm) (n+1):= by
            simp [υ_diff]
         _= (M admm) (n+1) + ⟪ A₂_x_diff, υ_diff ⟫ := by
            rw [inner_sub_right];ring
         _= (M admm) (n+1) + ⟪ υ_diff, A₂_x_diff ⟫ := by
            rw [real_inner_comm]
   have mono: ⟪ υ_diff, A₂_x_diff ⟫ ≤ (0:ℝ) := by
      simp [υ_diff, A₂_x_diff]
      rw [← map_sub A₂]
      have : ⟪ υ_diff, A₂_x_diff ⟫ = ⟪ A₂T υ_diff, x_diff ⟫ := by
         rw [ContinuousLinearMap.adjoint_inner_left]
      rw [this]
      apply neg_nonneg.1
      rw [← inner_neg_left]
      apply Φ_isdescending_inequ2 (admm_kkt := admm_kkt)
   linarith

lemma Φ_isdescending_inequ4 : ∀ n : ℕ+, 1 / (τ * ρₙ (n + 1)) * ⟪ ey (n + 1), (ey n) - (ey (n + 1)) ⟫
      - (1 - τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + (M admm) (n + 1)
      - ρₙ (n + 1) * ⟪ A₂ (x₂ (n + 1) - x₂ n), (A₂ (e₂ (n+1))) ⟫ ≥ 0:= by
   intro n
   let a := 1/(τ*ρₙ (n + 1)) * ⟪ ey (n+1), (ey n)-(ey (n+1)) ⟫
      - (1-τ)*ρₙ (n + 1)*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
   let b0 := (M admm) (n+1)
   let c := ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₂ (e₂ (n+1))) ⟫
   let d := ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
   have dleqb: d ≤ b0 := by apply Φ_isdescending_inequ3 (admm_kkt := admm_kkt)
   have h : a + d - c ≥ 0 := by apply Φ_isdescending_inequ1
   have : a + b0 - c ≥ 0 := by linarith
   exact this

lemma inner_eq_norm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      (a₁ a₂ : X) : ⟪ a₁, a₂ ⟫ = 1/2 * (‖a₁‖^2 + ‖a₂‖^2 - ‖a₁- a₂‖^2) := by
   rw [norm_sub_sq (𝕜 := ℝ) a₁ a₂];ring_nf;
   rfl

lemma Φ_isdescending_eq2' :
      ∀ n , (τ * ρₙ (n + 1)) • (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) = ey (n+1) - ey n:=by
   intro n
   rw [Φ_isdescending_eq1, Φ_isdescending_eq2]
   simp only [one_div, mul_inv_rev]
   rw [smul_smul, mul_assoc]
   nth_rw 2 [← mul_assoc]
   rw [mul_inv_cancel₀, one_mul, mul_inv_cancel₀, one_smul]
   rcases admm.htau with ⟨h₁, _⟩
   apply ne_of_gt h₁
   apply ne_of_gt (admm.hρₙ_pos (n + 1))

lemma Φ_isdescending_inequ5' : ∀ n : ℕ+,
      1 / (τ * ρₙ (n + 1)) * (‖ey n‖^2 - ‖ey (n+1)‖^2) - (2 - τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * ((M admm) (n+1)) - ρₙ (n + 1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 - ρₙ (n + 1) * ‖A₂ (e₂ (n+1))‖^2 + ρₙ (n + 1) * ‖A₂ (e₂ n)‖ ^ 2
      = 2 * (1 / (τ * ρₙ (n + 1)) * ⟪ (ey (n+1)),((ey n)-(ey (n+1)))⟫ -
      (1 - τ) * ρₙ  (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + (M admm) (n+1) - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫) := by
   intro n
   have h₄'' : ‖A₂ (x₂') - A₂ (x₂ n)‖ = ‖- (A₂ (x₂ n) - A₂ (x₂'))‖ := by simp only [neg_sub]
   have h₄' : ‖A₂ (x₂ (n+1) - x₂ n) - A₂ (e₂ (n+1))‖ = ‖A₂ (e₂ n)‖ := by rw [ AdaptiveADMM_Convergence_Proof.e₂]; rw[ AdaptiveADMM_Convergence_Proof.e₂]; simp only [map_sub,sub_sub_sub_cancel_left]; rw [h₄'', norm_neg]
   have h₆ : ‖ey (n+1) - ey n‖ = (τ * ρₙ (n + 1)) * ‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖
      := by rw [←Φ_isdescending_eq2', norm_smul]; simp only [norm_mul, Real.norm_eq_abs,mul_eq_mul_right_iff, norm_eq_zero]
            left
            have h1: τ ≥ 0 := by rcases admm.htau with ⟨h₁, _⟩; apply le_of_lt h₁
            have h2: ρₙ (n + 1) ≥ 0 := by apply le_of_lt (admm.hρₙ_pos (n + 1))
            have h3: |τ| = τ := by apply abs_eq_self.mpr h1
            have h4: |ρₙ (n + 1)| = ρₙ (n + 1) := by apply abs_eq_self.mpr h2
            rw [h3, h4]
   symm
   calc 2 * (1/(τ*ρₙ (n + 1)) * ⟪ (ey (n+1)),((ey n)-(ey (n+1)))⟫ - (1-τ)*ρₙ (n + 1)*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + (M admm) (n+1) - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫)
      _ = 2 / (τ * ρₙ (n + 1)) * ⟪ (ey (n+1)),((ey n)-(ey (n+1)))⟫
      - 2 * (1-τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * (M admm) (n+1)
      - 2 * ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫ := by ring
      _ = 2 / (τ * ρₙ (n + 1)) * (1 / 2 * (‖ey (n+1)‖^2 + ‖ey n‖^2 - ‖ey (n+1) - ey n‖^2)-‖ey (n+1)‖^2)
      - 2 * (1-τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * (M admm) (n+1)
      - 2 * ρₙ (n + 1) * ( 1 / 2 * (‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (x₂ (n+1) - x₂ n) - A₂ (e₂ (n+1))‖^2))
      := by nth_rw 2 [inner_eq_norm]; rw [inner_sub_right]; rw [inner_eq_norm, real_inner_self_eq_norm_sq]
      _ = 2 / (τ * ρₙ (n + 1)) * (1 / 2 * (‖ey n‖^2 - ‖ey (n+1) - ey n‖^2-‖ey (n+1)‖^2))
      - 2 * (1-τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * (M admm) (n+1)
      - 2 * ρₙ (n + 1) * ( 1 / 2 * (‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by rw [h₄']; ring_nf
      _ = 1 / (τ * ρₙ (n + 1)) * ((‖ey n‖^2 - ((τ * ρₙ (n + 1)) * ‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2-‖ey (n+1)‖^2))
      - 2 * (1-τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * (M admm) (n+1)
      - 1 * ρₙ (n + 1) * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by rw [h₆]; ring_nf
      _ = 1 / (τ * ρₙ (n+1)) * ((‖ey n‖^2 -‖ey (n+1)‖^2)) - 1 / (τ * ρₙ (n+1)) * (τ * ρₙ (n+1)) ^ 2 * (‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2
      - 2 * (1-τ) * ρₙ (n+1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * (M admm) (n+1)
      - 1 * ρₙ (n+1) * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by ring
      _ = 1 / (τ * ρₙ (n+1)) * ((‖ey n‖^2 -‖ey (n+1)‖^2)) - (τ * ρₙ (n+1)) * (‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2
      - 2 * (1-τ) * ρₙ (n+1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * (M admm) (n+1)
      - 1 * ρₙ (n+1) * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by nth_rw 2 [div_eq_mul_inv]; rw [one_mul]; nth_rw 3 [pow_two]; simp
            left; rw [mul_assoc]
            nth_rw 2 [← mul_assoc]
            nth_rw 2 [← mul_assoc]
            nth_rw 2 [← mul_assoc]
            rw [inv_mul_cancel₀, one_mul]
            repeat rw [← mul_assoc]
            rw [inv_mul_cancel₀, one_mul]
            apply ne_of_gt (admm.hρₙ_pos (n+1))
            rcases admm.htau with ⟨h₁, _⟩
            apply ne_of_gt h₁
      _ = 1/(τ*ρₙ (n+1)) * (‖ey n‖^2 - ‖ey (n+1)‖^2)
      - (2-τ)*ρₙ (n+1)*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2*((M admm) (n+1))
      -ρₙ (n+1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2
      -ρₙ (n+1) * ‖A₂ (e₂ (n+1))‖^2
      +ρₙ (n+1) * ‖A₂ (e₂ n)‖^2
      := by ring_nf

lemma Φ_isdescending_inequ5 : ∀ n : ℕ+ , 1 / (τ * ρₙ (n + 1)) * (‖ey n‖ ^ 2 - ‖ey (n+1)‖ ^ 2)
      - (2 - τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b‖ ^ 2 + 2 * (M admm) (n+1)
      - ρₙ (n + 1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 - ρₙ (n + 1) * ‖A₂ (e₂ (n+1))‖^2 + ρₙ (n + 1) * ‖A₂ (e₂ n)‖^2 ≥ 0:= by
   intro n
   rw [Φ_isdescending_inequ5']
   apply mul_nonneg
   · norm_num
   apply Φ_isdescending_inequ4 n

lemma basic_inequ₁' (n : ℕ+) : 2 * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫
      ≤ ‖A₂ (x₂ n - x₂ (n+1))‖ ^ 2 + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
   have norm_abs:
      ‖A₂ (x₂ n - x₂ (n+1))‖^2 = ‖A₂ (x₂ (n+1) - x₂ (n))‖^2:= by
      rw[← norm_neg]
      have : -(A₂ (x₂ n - x₂ (n+1))) = A₂ (x₂ (n+1) - x₂ (n)) := by continuity
      rw [this]
   rw [←sub_nonneg];
   have : ‖A₂ (x₂ n - x₂ (n+1))‖^2
      + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 - 2 * ⟪ A₂ (x₂ (n+1) - x₂ (n)), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫
      = ‖A₂ (x₂ n - x₂ (n+1))‖^2 - 2 * ⟪ A₂ (x₂ (n+1) - x₂ (n)), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫ + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      := by ring_nf
   rw [this, norm_abs, ← norm_sub_sq_real]
   apply pow_two_nonneg

lemma M_le (n : ℕ+)(htau : 0 < τ ∧ τ ≤ 1 ): 2 * (M admm) (n + 1) ≤ (1 - τ) * ρₙ (n) * ‖A₂ (x₂ n - x₂ (n + 1))‖^2 + (1 - τ) * ρₙ (n) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
   have : (1 - τ) * ρₙ (n ) * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
         + (1 - τ) * ρₙ (n ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
         = (1 - τ) * ρₙ (n ) * (‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
         + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 ) := by ring
   rw [this]
   have : 2 * (M admm) (n + 1) =  (1 - τ) * ρₙ (n ) * ( 2 * ⟪ A₂ (x₂ (n + 1) - x₂ (n)), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫ ) := by
      dsimp [ AdaptiveADMM_Convergence_Proof.M]
      ring_nf
   rw [this]
   apply mul_le_mul_of_nonneg_left (basic_inequ₁' n)
   have : 0 ≤ 1 - τ := by linarith [htau.1]
   apply mul_nonneg
   · exact this
   linarith [admm.hρₙ_pos (n)]

lemma τ_segment  : (0 < τ ∧ τ ≤ 1) ∨ τ > 1 := by
   rcases admm.htau with ⟨h1, _⟩
   by_cases h: τ ≤ 1
   ·  left;exact ⟨h1, h⟩
   ·  right;linarith

lemma τ_min1_1  (h: 0 < τ ∧ τ ≤ 1) : min τ (1 + τ - τ ^ 2) = τ := by
   rcases h with ⟨h1, h2⟩
   apply min_eq_left
   have h3: τ ^ 2 ≤ 1 := by
      apply pow_le_one₀;linarith;linarith
   linarith

lemma τ_min1_2  (h: τ > 1 ) : min τ (1 + τ - τ ^ 2) = 1 + τ - τ ^ 2 := by
   apply min_eq_right
   have : 1 < τ ^ 2 := by
      apply one_lt_pow₀;exact h;linarith
   linarith

lemma τ_min2_1  (h: 0 < τ ∧ τ ≤ 1) : min 1 (1 + 1 / τ - τ ) = 1 := by
   rcases h with ⟨h1, h2⟩
   apply min_eq_left
   have h3: τ ≤ 1 / τ :=
   calc
      _ ≤ 1 := h2
      _ ≤ 1 / τ := by
         apply one_le_one_div h1 h2
   linarith

lemma τ_min2_2  (h: τ > 1 ) : min 1 (1 + 1 / τ - τ ) = 1 + 1 / τ - τ  := by
   apply min_eq_right
   have : τ > 1 / τ :=
   calc
      _ > 1 := h
      _ > 1 / τ := by
         rw [one_div, ← inv_one];apply inv_strictAnti₀;linarith;exact h
   linarith

lemma τ_min3_1  (h: 0 < τ ∧ τ ≤ 1) : max (1 - τ) (1 - 1 / τ) = 1 - τ := by
   rcases h with ⟨h1, h2⟩
   apply max_eq_left
   have h3: τ ≤ 1 / τ :=
   calc
      _ ≤ 1 := h2
      _ ≤ 1 / τ := by
         apply one_le_one_div h1 h2
   linarith

lemma τ_min3_2  (h: τ > 1) : max (1 - τ) (1 - 1 / τ) = 1 - 1 / τ  := by
   apply max_eq_right
   have : τ > 1 / τ :=
   calc
      _ > 1 := h
      _ > 1 / τ := by
         rw [one_div, ← inv_one];apply inv_strictAnti₀;linarith;exact h
   linarith

lemma basic_inequ₂ (n : ℕ+) : - 2 * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫
      ≤ τ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 + 1 / τ * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
   rw [← sub_nonneg]
   have h : τ ≥ 0 := by
      rcases admm.htau with ⟨h₁, _⟩
      linarith
   have h₁ : √τ ^2 = τ := by
      apply Real.sq_sqrt
      assumption
   have h₂ : (τ)⁻¹ = (√τ)⁻¹ ^2 := by
      nth_rw 1[←h₁]; rw [inv_pow]
   rw [div_eq_inv_mul, mul_one, h₂]
   nth_rw 1[←h₁]
   let S1 := A₂ (x₂ (n+1) - x₂ n)
   let S2 := A₁ (x₁ n) + A₂ (x₂ n) - b
   let s1 := √τ
   have h1 : s1 ^2 * ‖S1‖^2 = ‖s1 • S1‖ ^2 := by rw [norm_smul, mul_pow]; simp only [Real.norm_eq_abs,sq_abs]
   have h2 : s1⁻¹ ^2 * ‖S2‖^2 = ‖s1⁻¹ • S2‖ ^2 := by rw [norm_smul, mul_pow]; simp only [inv_pow, norm_inv, Real.norm_eq_abs, sq_abs]
   have : s1 ≠ 0 := by
      have h₃ : s1 = √τ := by rfl
      rw [h₃]
      apply Real.sqrt_ne_zero'.mpr
      rcases admm.htau with ⟨h₁, _⟩
      assumption
   have h3 : inner (𝕜 := ℝ) S1 S2 = inner (𝕜 := ℝ) (s1 • S1) (s1⁻¹ • S2) := by rw [inner_smul_left, inner_smul_right]; rw [← mul_assoc]; simp; rw [mul_inv_cancel₀, one_mul]; exact this
   rw [h1, h2, h3]
   have : ‖s1 • S1‖ ^ 2 + ‖s1⁻¹ • S2‖ ^ 2 - -2 * ⟪s1 • S1, s1⁻¹ • S2⟫_ℝ = ‖s1 • S1‖ ^ 2 + 2 * ⟪s1 • S1, s1⁻¹ • S2⟫_ℝ + ‖s1⁻¹ • S2‖ ^ 2 := by ring_nf
   rw [this, ←norm_add_sq_real]
   apply pow_two_nonneg


end AdaptiveADMM_Convergence_Proof
