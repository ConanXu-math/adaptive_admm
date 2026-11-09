import AdaRES.Prox
import Mathlib.Analysis.InnerProductSpace.PiL2

open InnerProductSpace
open scoped BigOperators InnerProduct

namespace AdaRES

noncomputable section

variable {ι : Type*} [Fintype ι]

def weightedSq (L : ι → ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, L i * (x i)^2

def diagonalEquiv (L : ι → ℝ) (hL : ∀ i, 0 < L i) :
    EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
  let C := EuclideanSpace.equiv ι ℝ
  let D : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := LinearEquiv.piCongrRight fun i =>
    LinearEquiv.smulOfUnit (M := ℝ)
      (Units.mk0 (Real.sqrt (L i)) (Real.sqrt_pos.mpr (hL i)).ne')
  (C.trans D.toContinuousLinearEquiv).trans C.symm

theorem diagonal_apply (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    diagonalEquiv L hL x i = Real.sqrt (L i) * x i := by
  rfl

theorem diagonal_symm_apply (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (x : EuclideanSpace ℝ ι) (i : ι) :
    (diagonalEquiv L hL).symm x i = (Real.sqrt (L i))⁻¹ * x i := by
  rfl

theorem diagonal_norm_sq (L : ι → ℝ) (hL : ∀ i, 0 < L i) (x : EuclideanSpace ℝ ι) :
    ‖diagonalEquiv L hL x‖^2 = weightedSq L x := by
  rw [EuclideanSpace.norm_sq_eq, weightedSq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [diagonal_apply, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (hL i).le]

theorem diagonal_pairing (L : ι → ℝ) (hL : ∀ i, 0 < L i) (g v : EuclideanSpace ℝ ι) :
    ⟪(diagonalEquiv L hL).symm g, diagonalEquiv L hL v⟫_ℝ = ⟪g, v⟫_ℝ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change (diagonalEquiv L hL v i) * ((diagonalEquiv L hL).symm g i) = v i * g i
  rw [diagonal_apply, diagonal_symm_apply]
  field_simp [(Real.sqrt_pos.mpr (hL i)).ne'] <;> ring

structure WeightedSmooth (L : ι → ℝ) where
  f : EuclideanSpace ℝ ι → ℝ
  gradient : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι
  hasGradient : ∀ x, HasGradientAt f (gradient x) x
  convex : ConvexOn ℝ Set.univ f
  upper : ∀ x y, f x ≤ f y + ⟪gradient y, x - y⟫_ℝ + weightedSq L (x - y) / 2

def normalizeSmooth {L : ι → ℝ} (hL : ∀ i, 0 < L i) (data : WeightedSmooth L) :
    Smooth (EuclideanSpace ℝ ι) := by
  let B := diagonalEquiv L hL
  refine { f := data.f ∘ B.symm
           gradient := fun x => B.symm (data.gradient (B.symm x))
           hasGradient := ?_
           convex := ?_
           upper := ?_ }
  · intro u
    rw [hasGradientAt_iff_hasFDerivAt]
    have H := (data.hasGradient (B.symm u)).hasFDerivAt.comp u B.symm.toContinuousLinearMap.hasFDerivAt
    apply H.congr_fderiv
    ext v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply]
    have hp := (diagonal_pairing L hL (data.gradient (B.symm u)) (B.symm v)).symm
    change ⟪data.gradient (B.symm u), B.symm v⟫_ℝ =
      ⟪B.symm (data.gradient (B.symm u)), B (B.symm v)⟫_ℝ at hp
    rw [B.apply_symm_apply] at hp
    exact hp
  · simpa only [Set.preimage_univ] using data.convex.comp_linearMap B.symm.toLinearEquiv.toLinearMap
  · intro u v
    have H := data.upper (B.symm u) (B.symm v)
    have hp := diagonal_pairing L hL (data.gradient (B.symm v)) (B.symm u - B.symm v)
    change ⟪B.symm (data.gradient (B.symm v)), B (B.symm u - B.symm v)⟫_ℝ = _ at hp
    rw [map_sub, B.apply_symm_apply, B.apply_symm_apply] at hp
    have hn := diagonal_norm_sq L hL (B.symm u - B.symm v)
    change ‖B (B.symm u - B.symm v)‖^2 = _ at hn
    rw [map_sub, B.apply_symm_apply, B.apply_symm_apply] at hn
    change data.f (B.symm u) ≤ data.f (B.symm v) +
      ⟪B.symm (data.gradient (B.symm v)), u - v⟫_ℝ + ‖u - v‖^2 / 2
    rwa [hp, hn]

def normalizeRegularizer (L : ι → ℝ) (hL : ∀ i, 0 < L i)
    (ψ : ProperConvex (EuclideanSpace ℝ ι)) : ProperConvex (EuclideanSpace ℝ ι) := by
  let B := diagonalEquiv L hL
  refine { dom := B.symm ⁻¹' ψ.dom
           f := ψ.f ∘ B.symm
           dom_nonempty := ?_
           dom_convex := ?_
           convex_on := ?_
           lsc := ?_ }
  · obtain ⟨x, hx⟩ := ψ.dom_nonempty
    exact ⟨B x, by simpa only [Set.mem_preimage, B.symm_apply_apply] using hx⟩
  · exact ψ.dom_convex.linear_preimage B.symm.toLinearEquiv.toLinearMap
  · exact ψ.convex_on.comp_linearMap B.symm.toLinearEquiv.toLinearMap
  · intro c
    exact (ψ.lsc c).preimage B.symm.continuous

def weightedStep {L : ι → ℝ} (hL : ∀ i, 0 < L i) (data : WeightedSmooth L)
    (ψ : ProperConvex (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  let B := diagonalEquiv L hL
  B.symm (step (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) (B x))

theorem weightedStep_map {L : ι → ℝ} (hL : ∀ i, 0 < L i) (data : WeightedSmooth L)
    (ψ : ProperConvex (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) :
    diagonalEquiv L hL (weightedStep hL data ψ x) =
      step (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) (diagonalEquiv L hL x) := by
  unfold weightedStep
  exact (diagonalEquiv L hL).apply_symm_apply _

def weightedModel {L : ι → ℝ} (data : WeightedSmooth L)
    (ψ : ProperConvex (EuclideanSpace ℝ ι)) (x v : EuclideanSpace ℝ ι) : ℝ :=
  ψ.f v + ⟪data.gradient x, v - x⟫_ℝ + weightedSq L (v - x) / 2

theorem normalized_prox_model {L : ι → ℝ} (hL : ∀ i, 0 < L i) (data : WeightedSmooth L)
    (ψ : ProperConvex (EuclideanSpace ℝ ι)) (x v : EuclideanSpace ℝ ι) :
    let B := diagonalEquiv L hL
    prox_obj (normalizeRegularizer L hL ψ) 1 (B x - B.symm (data.gradient x)) (B v)
      = weightedModel data ψ x v + ‖B.symm (data.gradient x)‖^2 / 2 := by
  let B := diagonalEquiv L hL
  change 1 * ψ.f (B.symm (B v)) + ‖B v - (B x - B.symm (data.gradient x))‖^2 / 2 = _
  rw [B.symm_apply_apply, one_mul]
  rw [show B v - (B x - B.symm (data.gradient x)) = B (v - x) + B.symm (data.gradient x) from by
    rw [map_sub]
    abel]
  rw [norm_add_sq_real, real_inner_comm (B.symm (data.gradient x)) (B (v - x))]
  unfold weightedModel
  rw [show ‖B (v - x)‖^2 = weightedSq L (v - x) from diagonal_norm_sq L hL (v - x)]
  rw [show ⟪B.symm (data.gradient x), B (v - x)⟫_ℝ = ⟪data.gradient x, v - x⟫_ℝ from
    diagonal_pairing L hL (data.gradient x) (v - x)]
  ring

theorem weightedStep_spec {L : ι → ℝ} (hL : ∀ i, 0 < L i) (data : WeightedSmooth L)
    (ψ : ProperConvex (EuclideanSpace ℝ ι)) (x : EuclideanSpace ℝ ι) :
    let w := weightedStep hL data ψ x
    w ∈ ψ.dom ∧ IsMinOn (weightedModel data ψ x) ψ.dom w ∧
      ∀ v ∈ ψ.dom, IsMinOn (weightedModel data ψ x) ψ.dom v → v = w := by
  let B := diagonalEquiv L hL
  let ψB := normalizeRegularizer L hL ψ
  let a := B x - B.symm (data.gradient x)
  let w := weightedStep hL data ψ x
  have hdom (v : EuclideanSpace ℝ ι) : B v ∈ ψB.dom ↔ v ∈ ψ.dom := by
    change B.symm (B v) ∈ ψ.dom ↔ v ∈ ψ.dom
    rw [B.symm_apply_apply]
  have hw : B w = prox ψB 1 zero_lt_one a := by
    rw [show B w = step (normalizeSmooth hL data) ψB (B x) from weightedStep_map hL data ψ x]
    change prox ψB 1 zero_lt_one (B x - B.symm (data.gradient (B.symm (B x)))) = _
    rw [B.symm_apply_apply]
  have hz : prox_scale ψB 1 a (B w) := by
    rw [hw]
    exact prox_spec ψB 1 zero_lt_one a
  refine ⟨(hdom w).1 hz.1, isMinOn_iff.2 ?_, ?_⟩
  · intro v hv
    have h := (isMinOn_iff.1 hz.2) (B v) ((hdom v).2 hv)
    rw [normalized_prox_model hL data ψ x w, normalized_prox_model hL data ψ x v] at h
    exact le_of_add_le_add_right h
  · intro v hv hvmin
    have hvz : prox_scale ψB 1 a (B v) := by
      refine ⟨(hdom v).2 hv, isMinOn_iff.2 ?_⟩
      intro u hu
      obtain ⟨z, rfl⟩ := B.surjective u
      rw [normalized_prox_model hL data ψ x v, normalized_prox_model hL data ψ x z]
      exact add_le_add_right ((isMinOn_iff.1 hvmin) z ((hdom z).1 hu)) _
    exact B.injective (prox_scale_unique ψB zero_lt_one a hvz hz)

end
end AdaRES
