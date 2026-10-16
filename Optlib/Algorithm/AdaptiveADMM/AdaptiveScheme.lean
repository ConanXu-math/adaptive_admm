import Optlib.Function.Proximal
import Mathlib.Topology.MetricSpace.Sequences

noncomputable section

open Set InnerProductSpace Topology Filter

variable (E₁ E₂ F : Type*)
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

-- Problem formulation.
class OptProblem [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] [FiniteDimensional ℝ F] where
  f₁ : E₁ → ℝ
  f₂ : E₂ → ℝ
  A₁ : E₁ →L[ℝ] F
  A₂ : E₂ →L[ℝ] F
  b  : F
  lscf₁ : LowerSemicontinuous f₁
  lscf₂ : LowerSemicontinuous f₂
  cf₁ : ConvexOn ℝ univ f₁
  cf₂ : ConvexOn ℝ univ f₂

-- Augmented Lagrangian Function
def Augmented_Lagrangian_Function (opt : OptProblem E₁ E₂ F) (ρ : ℝ) :
    E₁ × E₂ × F → ℝ :=
  fun (x₁ , x₂ , y) =>
    (opt.f₁ x₁) + (opt.f₂ x₂) +
    @inner ℝ F _ y ((opt.A₁ x₁) + (opt.A₂ x₂) - opt.b) +
    ρ / 2 * ‖(opt.A₁ x₁) + (opt.A₂ x₂) - opt.b‖ ^ 2
-- Variable-penalty ADMM (ρₖ)
class ADMM extends (OptProblem E₁ E₂ F) where
  x₁ : ℕ → E₁
  x₂ : ℕ → E₂
  y  : ℕ → F
  ρₙ : ℕ → ℝ                      -- Variable penalty sequence.
  τ  : ℝ
  hρₙ_pos : ∀ k, ρₙ k > 0         -- Positive rho at every step.
  rho_lower_bound: ∃ BL > 0, ∀ n, ρₙ n ≥ BL
  rho_upper_bound: ∃ BU > 0, ∀ n, ρₙ n ≤ BU
  htau : 0 < τ ∧ τ < (1 + √5)/2
  htau_range : 1 + τ - τ^2 > 0

  -- x₁-subproblem
  itex₁ :
    ∀ k, IsMinOn
      (fun x₁ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem (ρₙ (k+1)))
        (x₁ , x₂ k , y k))
      univ (x₁ (k+1))

  -- x₂-subproblem
  itex₂ :
    ∀ k, IsMinOn
      (fun x₂ ↦ (Augmented_Lagrangian_Function E₁ E₂ F toOptProblem (ρₙ (k+1)))
        (x₁ (k+1) , x₂ , y k))
      univ (x₂ (k+1))

  -- Dual update (HWY).
  itey :
    ∀ k, y (k+1) = y k + (τ * ρₙ (k+1)) • ((A₁ $ x₁ (k+1)) + (A₂ $ x₂ (k+1)) - b)


-- Convex KKT condition
variable {E₁ E₂ F} in
class Convex_KKT (x₁ : E₁ )(x₂ : E₂)(y : F) (opt : OptProblem E₁ E₂ F) :Prop where
   subgrad₁ : -(ContinuousLinearMap.adjoint opt.A₁) y ∈ SubderivAt opt.f₁ x₁
   subgrad₂ : -(ContinuousLinearMap.adjoint opt.A₂) y ∈ SubderivAt opt.f₂ x₂
   eq       :  (opt.A₁ x₁) + (opt.A₂ x₂) = opt.b

variable {E₁ E₂ F} in
/-- A primal-dual KKT point for the problem underlying an ADMM trajectory. -/
structure KKTPoint (admm : ADMM E₁ E₂ F) where
  x₁ : E₁
  x₂ : E₂
  y : F
  h : Convex_KKT x₁ x₂ y admm.toOptProblem
