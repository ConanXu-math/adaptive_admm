import AdaRES.Prox
import Optlib.Function.Lsmooth

open InnerProductSpace
open scoped InnerProduct

namespace AdaRES

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem gradient_cocoercive (data : Smooth E) (x y : E) :
    ‖data.gradient x - data.gradient y‖^2 ≤
      ⟪data.gradient x - data.gradient y, x - y⟫_ℝ := by
  let f := fun z : E => ‖z‖^2 / 2 - data.f z
  let g := fun z : E => z - data.gradient z
  have hg (z : E) : HasGradientAt f (g z) z := by
    have hh := (gradient_norm_sq_eq_two_self z).const_smul (1 / 2 : ℝ)
    have hh' := hh.sub (data.hasGradient z)
    convert hh' using 1
    · funext w
      simp only [f, smul_eq_mul]
      ring
    · simp [g, smul_smul]
  have hconv : ConvexOn ℝ Set.univ f := by
    apply Convex_first_order_condition_inverse' (fun z _ => hg z) convex_univ
    intro u hu v hv
    have hq : ‖v‖^2 / 2 = ‖u‖^2 / 2 + ⟪u, v - u⟫_ℝ + ‖v - u‖^2 / 2 := by
      rw [norm_sub_sq_real v u, inner_sub_right, real_inner_self_eq_norm_sq,
        real_inner_comm v u]
      ring
    have hupp := data.upper v u
    dsimp only [f, g]
    rw [inner_sub_left]
    linarith only [hq, hupp]
  have hconv' : ConvexOn ℝ Set.univ (fun z : E => (1 : ℝ) / 2 * ‖z‖^2 - data.f z) := by
    convert hconv using 1
    funext z
    dsimp only [f]
    ring
  simpa only [div_one, one_mul] using
    convex_to_lower data.hasGradient hconv' (show (0 : ℝ) < 1 by norm_num) data.convex x y

theorem gradient_lipschitz (data : Smooth E) : LipschitzWith 1 data.gradient :=
  lower_to_lipschitz (fun x y => by
    simpa using gradient_cocoercive data x y) zero_lt_one

theorem gradient_step_nonexpansive (data : Smooth E) (x y : E) :
    ‖(x - data.gradient x) - (y - data.gradient y)‖ ≤ ‖x - y‖ := by
  have he : (x - data.gradient x) - (y - data.gradient y) =
      (x - y) - (data.gradient x - data.gradient y) := by abel
  rw [he, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real]
  rw [real_inner_comm (data.gradient x - data.gradient y) (x - y)]
  nlinarith only [gradient_cocoercive data x y, sq_nonneg ‖data.gradient x - data.gradient y‖]

theorem prox_unit_nonexpansive (ψ : ProperConvex E) (x y : E) :
    ‖prox ψ 1 zero_lt_one x - prox ψ 1 zero_lt_one y‖ ≤ ‖x - y‖ := by
  let u := prox ψ 1 zero_lt_one x
  let v := prox ψ 1 zero_lt_one y
  have hu := prox_optimality ψ 1 zero_lt_one x v (prox_mem_dom ψ 1 zero_lt_one y)
  have hv := prox_optimality ψ 1 zero_lt_one y u (prox_mem_dom ψ 1 zero_lt_one x)
  simp only [one_mul] at hu hv
  change ψ.f u - ψ.f v ≤ ⟪u - x, v - u⟫_ℝ at hu
  change ψ.f v - ψ.f u ≤ ⟪v - y, u - v⟫_ℝ at hv
  have he : ⟪u - x, v - u⟫_ℝ + ⟪v - y, u - v⟫_ℝ =
      ⟪x - y, u - v⟫_ℝ - ‖u - v‖^2 := by
    rw [show v - u = -(u - v) from by abel, inner_neg_right]
    calc
      _ = ⟪v - y, u - v⟫_ℝ - ⟪u - x, u - v⟫_ℝ := by ring
      _ = _ := by
        rw [← inner_sub_left, show v - y - (u - x) = (x - y) - (u - v) from by abel,
          inner_sub_left, real_inner_self_eq_norm_sq]
  have hfirm : ‖u - v‖^2 ≤ ⟪x - y, u - v⟫_ℝ := by linarith only [hu, hv, he]
  have hprod := hfirm.trans (real_inner_le_norm (x - y) (u - v))
  change ‖u - v‖ ≤ ‖x - y‖
  by_cases hz : ‖u - v‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · have hpos := lt_of_le_of_ne (norm_nonneg (u - v)) (Ne.symm hz)
    exact (mul_le_mul_right hpos).mp (by simpa only [pow_two] using hprod)

theorem step_nonexpansive (data : Smooth E) (ψ : ProperConvex E) (x y : E) :
    ‖step data ψ x - step data ψ y‖ ≤ ‖x - y‖ :=
  (prox_unit_nonexpansive ψ (x - data.gradient x) (y - data.gradient y)).trans
    (gradient_step_nonexpansive data x y)

end
end AdaRES
