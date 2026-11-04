import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/- 本文件保存 Codex 提供的外部证明帮助。对应论文式(20)的代数恒等式。 -/

namespace PDALCodexHelp

open InnerProductSpace
open scoped InnerProduct

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem energyCombinationIdentity (K : X →L[ℝ] Y)
    (u v w xref : X) (a b yref : Y)
    (β τ θ gu gv gw gref hb href : ℝ) :
    let xb := v + θ • (v - u)
    β * ⟪w - v, xref - w⟫_ℝ
      + ⟪b - a, yref - b⟫_ℝ
      + β * ⟪xb - v, w - xb⟫_ℝ
      + β * (τ * ⟪(K†) (b - a), xb - w⟫_ℝ)
      - β * (τ * ((1 + θ) * (gv - gref + ⟪(K†) yref, v - xref⟫_ℝ)
        - θ * (gu - gref + ⟪(K†) yref, u - xref⟫_ℝ)
        + (hb - href - ⟪K xref, b - yref⟫_ℝ)))
    = (β * (⟪w - v, xref - w⟫_ℝ + τ * ⟪(K†) b, xref - w⟫_ℝ)
        - β * (τ * (gw - gref)))
      + (⟪b - a, yref - b⟫_ℝ - (β * τ) * ⟪K xb, yref - b⟫_ℝ
        - (β * τ) * (hb - href))
      + (β * (θ * ⟪v - u, w - v⟫_ℝ) + β * (τ * ⟪(K†) a, w - v⟫_ℝ)
        - β * (τ * (gv - gw)))
      + (β * ((θ * θ) * ⟪v - u, u - v⟫_ℝ)
        + β * ((θ * τ) * ⟪(K†) a, u - v⟫_ℝ)
        - β * ((θ * τ) * (gv - gu))) := by
  dsimp only
  simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    map_add, map_sub, map_smul,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm]
  ring

#print axioms energyCombinationIdentity

theorem scaledEnergyFromOptimality (K : X →L[ℝ] Y)
    (u v w xref : X) (a b yref : Y)
    (β τ σ θ gu gv gw gref hb href : ℝ)
    (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hstep : θ * σ = τ)
    (h11 : τ * (gw - gref) ≤ ⟪w - v + τ • (K†) b, xref - w⟫_ℝ)
    (h12 : (β * τ) * (hb - href) ≤
      ⟪b - a - (β * τ) • K (v + θ • (v - u)), yref - b⟫_ℝ)
    (h13 : σ * (gv - gw) ≤ ⟪v - u + σ • (K†) a, w - v⟫_ℝ)
    (h14 : σ * (gv - gu) ≤ ⟪v - u + σ • (K†) a, u - v⟫_ℝ) :
    β * (τ * ((1 + θ) * (gv - gref + ⟪(K†) yref, v - xref⟫_ℝ)
      - θ * (gu - gref + ⟪(K†) yref, u - xref⟫_ℝ)
      + (hb - href - ⟪K xref, b - yref⟫_ℝ)))
    ≤ β * ⟪w - v, xref - w⟫_ℝ + ⟪b - a, yref - b⟫_ℝ
      + β * ⟪(v + θ • (v - u)) - v, w - (v + θ • (v - u))⟫_ℝ
      + β * (τ * ⟪(K†) (b - a), (v + θ • (v - u)) - w⟫_ℝ) := by
  subst τ
  have h11s := mul_le_mul_of_nonneg_left h11 hβ
  have h13s := mul_le_mul_of_nonneg_left h13 (mul_nonneg hβ hθ)
  have h14s := mul_le_mul_of_nonneg_left h14 (mul_nonneg (mul_nonneg hβ hθ) hθ)
  simp only [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    map_add, map_sub, map_smul,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm] at h11s h12 h13s h14s ⊢
  linear_combination h11s + h12 + h13s + h14s

#print axioms scaledEnergyFromOptimality

end PDALCodexHelp
