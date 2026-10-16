import Optlib.Algorithm.AdaptiveADMM.AdaptiveScheme

/-! Legacy names used by the existing candidate examples. Core proofs use
`KKTPoint` directly and never infer an energy reference point from `Setting`. -/

variable {E₁ E₂ F : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Legacy spelling; use `KKTPoint` in new proofs. -/
abbrev Existance_of_kkt (admm : ADMM E₁ E₂ F) := KKTPoint admm

namespace AdaptiveADMM_Convergence_Proof

/-- Legacy empty parameter retained for the existing candidate examples. -/
class Setting (E₁ E₂ F : outParam Type*)
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (admm : outParam (ADMM E₁ E₂ F))
    (admm_kkt : outParam (KKTPoint admm)) where

end AdaptiveADMM_Convergence_Proof
