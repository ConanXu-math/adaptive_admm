import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Optlib.Algorithm.AdaptiveADMM.AdaptiveScheme
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Optlib.Convex.FiniteDimensionalConvexFunctionsLocallyLipschitz
import Optlib.Convex.Subgradient
import Mathlib.Data.Real.Basic


noncomputable section
open Set InnerProductSpace Topology Filter InnerProduct
open scoped Pointwise

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F ]

namespace AdaptiveADMM_Convergence_Proof

variable (admm : ADMM E₁ E₂ F) (admm_kkt : KKTPoint admm)

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

-- Auxiliary variables.
def T_HWY   := 2 - (1/2) * (1 + τ - τ^2)

def e₁  : ℕ → E₁ := fun n => (x₁ n) - x₁'

def e₂ : ℕ → E₂ := fun n => (x₂ n) - x₂'

def ey : ℕ → F :=  fun n => (y  n) - y'

/-- C1 energy: dual error plus rho-squared-weighted primal and feasibility errors. -/
def g1  : ℕ → ℝ := fun n => (‖(ey admm admm_kkt) n‖^2 + τ * ρₙ n^2  * ‖A₂ ((e₂ admm admm_kkt) n)‖^2 + τ * ((T_HWY admm) - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2)

/-- C2 energy: the C1 energy divided by rho squared. -/
def g2  : ℕ → ℝ := fun n => 1 / ρₙ n^2 * ‖(ey admm admm_kkt) n‖^2 + τ * ‖A₂ ((e₂ admm admm_kkt) n)‖^2 + τ * ((T_HWY admm) - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2

def u : ℕ+ → E₁ :=
  fun n => -A₁† (y n + ((1 - τ) * (ρₙ n)) • (A₁ ((e₁ admm admm_kkt) n) + A₂ ((e₂ admm admm_kkt) n))
               + (ρₙ n) • (A₂ (x₂ (n - 1) - x₂ n)))

def v : ℕ → E₂ :=
  fun n => -A₂† (y n + ((1 - τ) * (ρₙ n)) • (A₁ ((e₁ admm admm_kkt) n) + A₂ ((e₂ admm admm_kkt) n)))

def Ψ : ℕ → ℝ :=
  fun n => 1 / (τ * (ρₙ n)) * ‖(ey admm admm_kkt) n‖^2 + (ρₙ n) * ‖A₂ ((e₂ admm admm_kkt) n)‖^2

def Φ : ℕ → ℝ :=
  fun n => (Ψ admm admm_kkt) n + ((max (1 - τ) (1 - 1/τ)) * (ρₙ n)) * ‖A₁ ((e₁ admm admm_kkt) n) + A₂ ((e₂ admm admm_kkt) n)‖^2

def υ : ℕ → F :=
  fun n => (y n) + ((1 - τ) * (ρₙ n)) • (A₁ (x₁ n) + A₂ (x₂ n) - admm.b)

def M : ℕ+ → ℝ :=
  fun n => ((1 - τ) * (ρₙ (n-1)))* ⟪(A₂ ((x₂ n) - (x₂ (n-1)))),(A₁ (x₁ (n-1)) + A₂ (x₂ (n-1)) - admm.b)⟫


end AdaptiveADMM_Convergence_Proof
