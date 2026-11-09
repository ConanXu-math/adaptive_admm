import PDAL.Definitions

/-!
# 论文式（35）的局部能量证明

单步能量不等式：由强凸次梯度支持、近端最优性与 δ=1 接受条件推出。
-/

open scoped InnerProduct
open InnerProductSpace

namespace APDAL

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

def StrongSupport (g : ProperConvex X) (γ : ℝ) : Prop :=
  ∀ p ∈ g.dom, ∀ q : X,
    (∀ z ∈ g.dom, g.f p + ⟪q, z - p⟫_ℝ ≤ g.f z) →
    ∀ z ∈ g.dom, g.f p + ⟪q, z - p⟫_ℝ + γ / 2 * ‖z - p‖^2 ≤ g.f z

theorem strong_prox_optimality (g : ProperConvex X) {γ τ : ℝ}
    (hs : StrongSupport g γ) (hτ : 0 < τ) {input p z : X}
    (hp : prox_scale g τ input p) (hz : z ∈ g.dom) :
    τ * (g.f p - g.f z + γ / 2 * ‖z - p‖^2) ≤ ⟪p - input, z - p⟫_ℝ := by
  let q : X := τ⁻¹ • (input - p)
  have hi (v : X) : ⟪q, v - p⟫_ℝ = -(⟪p - input, v - p⟫_ℝ / τ) := by
    dsimp only [q]
    rw [real_inner_smul_left, show input - p = -(p - input) from by abel,
      inner_neg_left, div_eq_mul_inv]
    ring
  have hq : ∀ v ∈ g.dom, g.f p + ⟪q, v - p⟫_ℝ ≤ g.f v := by
    intro v hv
    have ho := prox_scale_optimality g hτ input hp v hv
    have hd : g.f p - g.f v ≤ ⟪p - input, v - p⟫_ℝ / τ :=
      (le_div_iff₀ hτ).2 (by simpa only [mul_comm] using ho)
    rw [hi]
    linarith only [hd]
  have hstrong := hs p hp.1 q hq z hz
  rw [hi] at hstrong
  have hd : g.f p - g.f z + γ / 2 * ‖z - p‖^2 ≤ ⟪p - input, z - p⟫_ℝ / τ := by
    linarith only [hstrong]
  simpa only [mul_comm] using (le_div_iff₀ hτ).1 hd

theorem cross_le (K : X →L[ℝ] Y) {β τ : ℝ} (hβ : 0 < β) (hτ : 0 < τ)
    {a b : Y} (ha : accept_cond K β 1 τ a b) (d : X) :
    2 * β * (τ * ⟪(K†) (b - a), d⟫_ℝ) ≤ β * ‖d‖^2 + ‖b - a‖^2 := by
  have hsq := Real.sq_sqrt hβ.le
  have hsqrt := Real.sqrt_nonneg β
  have hc : Real.sqrt β * τ * ‖(K†) (b - a)‖ ≤ ‖b - a‖ := by
    simpa only [accept_cond, one_mul] using ha
  have hinner : ⟪(K†) (b - a), d⟫_ℝ ≤ ‖(K†) (b - a)‖ * ‖d‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm _ _)
  calc
    2 * β * (τ * ⟪(K†) (b - a), d⟫_ℝ) ≤
        2 * β * (τ * (‖(K†) (b - a)‖ * ‖d‖)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinner hτ.le) (by positivity)
    _ = 2 * (Real.sqrt β)^2 * (τ * (‖(K†) (b - a)‖ * ‖d‖)) := by rw [hsq]
    _ = (Real.sqrt β * τ * ‖(K†) (b - a)‖) * (2 * Real.sqrt β * ‖d‖) := by ring
    _ ≤ ‖b - a‖ * (2 * Real.sqrt β * ‖d‖) := by
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ β * ‖d‖^2 + ‖b - a‖^2 := by
      have h := sq_nonneg (Real.sqrt β * ‖d‖ - ‖b - a‖)
      have hid : (Real.sqrt β * ‖d‖ - ‖b - a‖)^2 =
          β * ‖d‖^2 + ‖b - a‖^2 - ‖b - a‖ * (2 * Real.sqrt β * ‖d‖) := by
        calc
          _ = (Real.sqrt β)^2 * ‖d‖^2 + ‖b - a‖^2 -
              ‖b - a‖ * (2 * Real.sqrt β * ‖d‖) := by ring
          _ = _ := by rw [hsq]
      rw [hid] at h
      linarith only [h]

theorem local_energy (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (sp : SaddlePoint K g h) {γ β τ σ θ : ℝ}
    (hs : StrongSupport g γ) (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ)
    (hθ : 0 ≤ θ) (ht : θ * σ = τ)
    {u v w : X} {a b : Y} (hu : u ∈ g.dom)
    (hv : prox_scale g σ (u - σ • (K†) a) v)
    (hw : prox_scale g τ (v - τ • (K†) b) w)
    (hb : prox_scale h (β * τ) (a + (β * τ) • K (v + θ • (v - u))) b)
    (ha : accept_cond K β 1 τ a b) :
    let xb := v + θ • (v - u)
    β * (1 + γ * τ) * ‖w - sp.xhat‖^2 / 2 + ‖b - sp.yhat‖^2 / 2
      + β * τ * ((1 + θ) * primal_gap K g v sp.xhat sp.yhat
        - θ * primal_gap K g u sp.xhat sp.yhat + dual_gap K h b sp.yhat sp.xhat)
      + β * ‖xb - v‖^2 / 2
    ≤ β * ‖v - sp.xhat‖^2 / 2 + ‖a - sp.yhat‖^2 / 2 := by
  let xb := v + θ • (v - u)
  let C := γ / 2 * ‖sp.xhat - w‖^2
  let P := fun x => primal_gap K g x sp.xhat sp.yhat
  let D := dual_gap K h b sp.yhat sp.xhat
  have h11 := strong_prox_optimality g hs hτ hw sp.xhat_dom
  rw [show w - (v - τ • (K†) b) = w - v + τ • (K†) b from by abel] at h11
  have h11' : τ * (g.f w - (g.f sp.xhat - C)) ≤ ⟪w - v + τ • (K†) b, sp.xhat - w⟫_ℝ := by
    rw [show g.f w - (g.f sp.xhat - C) = g.f w - g.f sp.xhat + C from by ring]
    exact h11
  have h12 := prox_scale_optimality h (mul_pos hβ hτ) _ hb sp.yhat sp.yhat_dom
  rw [show b - (a + (β * τ) • K xb) = b - a - (β * τ) • K xb from by abel] at h12
  have h13 := prox_scale_optimality g hσ _ hv w hw.1
  have h14 := prox_scale_optimality g hσ _ hv u hu
  rw [show v - (u - σ • (K†) a) = v - u + σ • (K†) a from by abel] at h13 h14
  have H := PDALCodexHelp.scaledEnergyFromOptimality K u v w sp.xhat a b sp.yhat
    β τ σ θ (g.f u) (g.f v) (g.f w) (g.f sp.xhat - C) (h.f b) (h.f sp.yhat)
    hβ.le hθ ht h11' h12 h13 h14
  have heq :
      (1 + θ) * (g.f v - (g.f sp.xhat - C) + ⟪(K†) sp.yhat, v - sp.xhat⟫_ℝ)
        - θ * (g.f u - (g.f sp.xhat - C) + ⟪(K†) sp.yhat, u - sp.xhat⟫_ℝ) + D
      = (1 + θ) * P v - θ * P u + D + C := by
    dsimp only [P, primal_gap]
    ring
  have hcomb : β * (τ * ((1 + θ) * P v - θ * P u + D + C)) ≤
      β * ⟪w - v, sp.xhat - w⟫_ℝ + ⟪b - a, sp.yhat - b⟫_ℝ
        + β * ⟪xb - v, w - xb⟫_ℝ + β * (τ * ⟪(K†) (b - a), xb - w⟫_ℝ) := by
    rw [← heq]
    exact H
  have hcos1 := cosine_rule w v sp.xhat
  have hcos2 := cosine_rule b a sp.yhat
  have hcos3 := cosine_rule xb v w
  rw [norm_sub_rev v w, norm_sub_rev xb w] at hcos3
  have hcross := cross_le K hβ hτ ha (xb - w)
  have hscaled := mul_le_mul_of_nonneg_left hcomb (show (0 : ℝ) ≤ 2 by norm_num)
  have hscaled' : 2 * (β * (τ * ((1 + θ) * P v - θ * P u + D + C))) ≤
      β * (2 * ⟪w - v, sp.xhat - w⟫_ℝ) + 2 * ⟪b - a, sp.yhat - b⟫_ℝ
        + β * (2 * ⟪xb - v, w - xb⟫_ℝ) + 2 * β * (τ * ⟪(K†) (b - a), xb - w⟫_ℝ) := by
    nlinarith only [hscaled]
  rw [hcos1, hcos2, hcos3] at hscaled'
  dsimp only [C] at hscaled'
  rw [norm_sub_rev sp.xhat w] at hscaled'
  change β * (1 + γ * τ) * ‖w - sp.xhat‖^2 / 2 + ‖b - sp.yhat‖^2 / 2
      + β * τ * ((1 + θ) * P v - θ * P u + D) + β * ‖xb - v‖^2 / 2
    ≤ β * ‖v - sp.xhat‖^2 / 2 + ‖a - sp.yhat‖^2 / 2
  have hxe : ‖w - xb‖^2 = ‖xb - w‖^2 := by rw [norm_sub_rev]
  rw [hxe] at hscaled'
  nlinarith only [hscaled', hcross]

end APDAL
