import PDAL.Definitions
import Optlib.Differential.Lemmas

open scoped InnerProduct
open InnerProductSpace

namespace AdaRES

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure Smooth (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  f : E → ℝ
  gradient : E → E
  hasGradient : ∀ x, HasGradientAt f (gradient x) x
  convex : ConvexOn ℝ Set.univ f
  upper : ∀ x y, f x ≤ f y + ⟪gradient y, x - y⟫_ℝ + ‖x - y‖^2 / 2

def objective (data : Smooth E) (ψ : ProperConvex E) (x : E) : ℝ := data.f x + ψ.f x

def step (data : Smooth E) (ψ : ProperConvex E) (y : E) : E :=
  prox ψ 1 zero_lt_one (y - data.gradient y)

theorem step_dom (data : Smooth E) (ψ : ProperConvex E) (y : E) : step data ψ y ∈ ψ.dom :=
  prox_mem_dom ψ 1 zero_lt_one _

theorem lower_tangent (data : Smooth E) (y v : E) :
    data.f y + ⟪data.gradient y, v - y⟫_ℝ ≤ data.f v :=
  Convex_first_order_condition' (data.hasGradient y) data.convex (Set.mem_univ y) v (Set.mem_univ v)

theorem step_three_point (data : Smooth E) (ψ : ProperConvex E) (y v : E) (hv : v ∈ ψ.dom) :
    objective data ψ (step data ψ y) - objective data ψ v
      ≤ (‖y - v‖^2 - ‖step data ψ y - v‖^2) / 2 := by
  let x := step data ψ y
  have hprox := prox_optimality ψ 1 zero_lt_one (y - data.gradient y) v hv
  change ⟪x - (y - data.gradient y), v - x⟫_ℝ ≥ 1 * (ψ.f x - ψ.f v) at hprox
  rw [show x - (y - data.gradient y) = x - y + data.gradient y from by abel,
    inner_add_left, one_mul] at hprox
  have hf := data.upper x y
  have hg := lower_tangent data y v
  have hsum : ⟪data.gradient y, x - y⟫_ℝ + ⟪data.gradient y, v - x⟫_ℝ =
      ⟪data.gradient y, v - y⟫_ℝ := by
    rw [← inner_add_right, show x - y + (v - x) = v - y from by abel]
  have hcos := cosine_rule x y v
  change data.f x + ψ.f x - (data.f v + ψ.f v) ≤ (‖y - v‖^2 - ‖x - v‖^2) / 2
  linarith only [hprox, hf, hg, hsum, hcos]

theorem step_descent (data : Smooth E) (ψ : ProperConvex E) (y : E) (hy : y ∈ ψ.dom) :
    objective data ψ (step data ψ y) + ‖step data ψ y - y‖^2 / 2 ≤ objective data ψ y := by
  have h := step_three_point data ψ y y hy
  simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub] at h
  linarith only [h]

end
end AdaRES
