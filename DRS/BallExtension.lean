import Mathlib

/-!
# Weighted variance identities in a real inner product space

For a finite family of points `a i` with weights `w i` summing to one and barycenter
`m = ∑ i, w i • a i`, we prove the parallel axis identity
`∑ i, w i ‖a i - p‖² = ∑ i, w i ‖a i - m‖² + ‖m - p‖²`.
-/

open scoped InnerProductSpace

namespace DRS

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Barycenter of a finite weighted family with weights summing to one. -/
def barycenter (w : ι → ℝ) (a : ι → E) (s : Finset ι) : E :=
  ∑ i ∈ s, w i • a i

/-- The parallel axis identity: for a barycenter of a finite weighted family, the weighted
second moment around any point `p` splits into the weighted variance plus `‖m - p‖²`. -/
theorem barycenter_variance (s : Finset ι) {w : ι → ℝ} {a : ι → E} (hw : ∑ i ∈ s, w i = 1)
    (m : E) (hm : m = barycenter w a s) (p : E) :
    ∑ i ∈ s, w i * ‖a i - p‖ ^ 2
      = ∑ i ∈ s, w i * ‖a i - m‖ ^ 2 + ‖m - p‖ ^ 2 := by
  have hweighted : (∑ i ∈ s, w i • a i) = m := hm.symm
  have hcenter : (∑ i ∈ s, w i • (a i - m)) = 0 := by
    calc
      _ = (∑ i ∈ s, w i • a i) - (∑ i ∈ s, w i • m) := by
        simp only [smul_sub, Finset.sum_sub_distrib]
      _ = 0 := by rw [hweighted, ← Finset.sum_smul, hw, one_smul, sub_self]
  have hc : (∑ i ∈ s, w i * ⟪a i - m, m - p⟫_ℝ) = 0 := by
    calc
      _ = ∑ i ∈ s, ⟪w i • (a i - m), m - p⟫_ℝ := by
        simp only [real_inner_smul_left]
      _ = ⟪(∑ i ∈ s, w i • (a i - m)), m - p⟫_ℝ := by rw [sum_inner]
      _ = 0 := by rw [hcenter, inner_zero_left]
  calc
    (∑ i ∈ s, w i * ‖a i - p‖ ^ 2) =
        ∑ i ∈ s, (w i * ‖a i - m‖ ^ 2 + 2 * (w i * ⟪a i - m, m - p⟫_ℝ)
          + w i * ‖m - p‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hvec : a i - p = (a i - m) + (m - p) := by module
      rw [hvec, norm_add_sq_real]
      ring
    _ = (∑ i ∈ s, w i * ‖a i - m‖ ^ 2) + ‖m - p‖ ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hc, mul_zero, add_zero, ← Finset.sum_mul, hw, one_mul]

/-- The weighted variance around the barycenter equals half the weighted sum of squared
pairwise distances. -/
theorem barycenter_variance_pairwise (s : Finset ι) {w : ι → ℝ} {a : ι → E}
    (hw : ∑ i ∈ s, w i = 1) (m : E) (hm : m = barycenter w a s) :
    ∑ i ∈ s, w i * ‖a i - m‖ ^ 2
      = (1 / 2) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖a i - a j‖ ^ 2 := by
  have hvar : ∀ q : E, ∑ i ∈ s, w i * ‖a i - q‖ ^ 2
      = ∑ i ∈ s, w i * ‖a i - m‖ ^ 2 + ‖m - q‖ ^ 2 :=
    fun q => barycenter_variance s hw m hm q
  have hflip :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖a i - a j‖ ^ 2) =
        ∑ j ∈ s, w j * (∑ i ∈ s, w i * ‖a i - a j‖ ^ 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    ring
  have hrev : (∑ j ∈ s, w j * ‖m - a j‖ ^ 2) =
      ∑ i ∈ s, w i * ‖a i - m‖ ^ 2 := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [norm_sub_rev]
  have hsum : (∑ j ∈ s, w j * (∑ i ∈ s, w i * ‖a i - a j‖ ^ 2)) =
      2 * (∑ i ∈ s, w i * ‖a i - m‖ ^ 2) := by
    calc
      _ = ∑ j ∈ s, w j * ((∑ i ∈ s, w i * ‖a i - m‖ ^ 2) + ‖m - a j‖ ^ 2) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [barycenter_variance s hw m hm (a j)]
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hw, one_mul, hrev]
        ring
  rw [hflip, hsum]
  ring

theorem variance_le_weighted_radius {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : Finset ι) (w : ι → ℝ) (a : ι → E) (b : ι → F) (p : E)
    (hw : (∑ i ∈ s, w i) = 1) (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (h : ∀ i ∈ s, ∀ j ∈ s, ‖b i - b j‖ ≤ ‖a i - a j‖) :
    (∑ i ∈ s, w i * ‖b i - barycenter w b s‖ ^ 2) ≤
      ∑ i ∈ s, w i * ‖a i - p‖ ^ 2 := by
  have hpair :
      (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖b i - b j‖ ^ 2) ≤
        ∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖a i - a j‖ ^ 2 := by
    refine Finset.sum_le_sum fun i hi => ?_
    refine Finset.sum_le_sum fun j hj => ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (h i hi j hj) 2)
      (mul_nonneg (hw0 i hi) (hw0 j hj))
  calc
    (∑ i ∈ s, w i * ‖b i - barycenter w b s‖ ^ 2) =
        (1 / 2) * (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖b i - b j‖ ^ 2) :=
      barycenter_variance_pairwise s hw (barycenter w b s) rfl
    _ ≤ (1 / 2) * (∑ i ∈ s, ∑ j ∈ s, w i * w j * ‖a i - a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ = ∑ i ∈ s, w i * ‖a i - barycenter w a s‖ ^ 2 :=
      (barycenter_variance_pairwise s hw (barycenter w a s) rfl).symm
    _ ≤ ∑ i ∈ s, w i * ‖a i - p‖ ^ 2 := by
      rw [barycenter_variance s hw (barycenter w a s) rfl p]
      exact le_add_of_nonneg_right (sq_nonneg _)

theorem ball_objective_nonpos {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : Finset ι) (w : ι → ℝ) (a : ι → E) (b : ι → F) (p : E)
    (hw : (∑ i ∈ s, w i) = 1) (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (h : ∀ i ∈ s, ∀ j ∈ s, ‖b i - b j‖ ≤ ‖a i - a j‖) :
    (∑ i ∈ s, w i * (‖b i‖ ^ 2 - ‖a i - p‖ ^ 2)) - ‖barycenter w b s‖ ^ 2 ≤ 0 := by
  have hzero := barycenter_variance s hw (barycenter w b s) rfl (0 : F)
  simp only [sub_zero] at hzero
  have hle := variance_le_weighted_radius s w a b p hw hw0 h
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith

def vertexMix [DecidableEq ι] (w : ι → ℝ) (i : ι) (ε : ℝ) (j : ι) : ℝ :=
  (1 - ε) * w j + (if j = i then ε else 0)

theorem sum_vertexMix_mul [DecidableEq ι] (s : Finset ι) {i : ι} (hi : i ∈ s)
    (w c : ι → ℝ) (ε : ℝ) :
    (∑ j ∈ s, vertexMix w i ε j * c j) =
      (1 - ε) * (∑ j ∈ s, w j * c j) + ε * c i := by
  have hsingle : (∑ j ∈ s, (if j = i then ε else 0) * c j) = ε * c i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · intro hni
      exact (hni hi).elim
  simp only [vertexMix, add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum, hsingle]

theorem barycenter_vertexMix [DecidableEq ι] (s : Finset ι) {i : ι} (hi : i ∈ s)
    (w : ι → ℝ) (b : ι → E) (ε : ℝ) :
    barycenter (vertexMix w i ε) b s =
      barycenter w b s + ε • (b i - barycenter w b s) := by
  have hsingle : (∑ j ∈ s, (if j = i then ε else 0) • b j) = ε • b i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · intro hni
      exact (hni hi).elim
  simp only [barycenter, vertexMix, add_smul, mul_smul, Finset.sum_add_distrib]
  rw [← Finset.smul_sum, hsingle]
  module

theorem vertexMix_mem_stdSimplex [Fintype ι] [DecidableEq ι] {w : ι → ℝ}
    (hw : w ∈ stdSimplex ℝ ι) (i : ι) {ε : ℝ} (he0 : 0 ≤ ε) (he1 : ε ≤ 1) :
    vertexMix w i ε ∈ stdSimplex ℝ ι := by
  have hm : vertexMix w i ε = (1 - ε) • w + ε • (Pi.single i (1:ℝ) : ι → ℝ) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [vertexMix, Pi.add_apply, Pi.smul_apply]
    · have hij : i ≠ j := Ne.symm hji
      simp [vertexMix, Pi.add_apply, Pi.smul_apply, hji]
  rw [hm]
  exact convex_stdSimplex ℝ ι hw (single_mem_stdSimplex ℝ i)
    (sub_nonneg.mpr he1) he0 (by ring)

def ballObjective (s : Finset ι) (w : ι → ℝ) (b : ι → E) (r : ι → ℝ) : ℝ :=
  (∑ j ∈ s, w j * (‖b j‖ ^ 2 - (r j) ^ 2)) - ‖barycenter w b s‖ ^ 2

theorem ballObjective_vertexMix [DecidableEq ι] (s : Finset ι) {i : ι} (hi : i ∈ s)
    (w : ι → ℝ) (b : ι → E) (r : ι → ℝ) (ε : ℝ) :
    ballObjective s (vertexMix w i ε) b r - ballObjective s w b r =
      ε * (‖barycenter w b s - b i‖ ^ 2 - (r i) ^ 2 - ballObjective s w b r)
        - ε ^ 2 * ‖b i - barycenter w b s‖ ^ 2 := by
  unfold ballObjective
  rw [sum_vertexMix_mul s hi, barycenter_vertexMix s hi]
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
  simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  rw [inner_sub_right, real_inner_self_eq_norm_sq,
    norm_sub_sq_real (barycenter w b s) (b i)]
  ring

theorem finite_ball_intersection {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype ι] [Nonempty ι] (a : ι → E) (b : ι → F) (p : E)
    (h : ∀ i j, ‖b i - b j‖ ≤ ‖a i - a j‖) :
    ∃ q : F, ∀ i, ‖q - b i‖ ≤ ‖p - a i‖ := by
  classical
  let s : Finset ι := Finset.univ
  let r : ι → ℝ := fun i => ‖a i - p‖
  let f : (ι → ℝ) → ℝ := fun w => ballObjective s w b r
  have hf : Continuous f := by
    dsimp [f, ballObjective, barycenter]
    fun_prop
  let i₀ : ι := Classical.choice inferInstance
  have hs : (stdSimplex ℝ ι).Nonempty :=
    ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
  obtain ⟨w, hw, hmax⟩ := (isCompact_stdSimplex ι).exists_isMaxOn hs hf.continuousOn
  have hF : f w ≤ 0 := ball_objective_nonpos s w a b p
    (by simpa [s] using hw.2) (fun j _ => hw.1 j) (fun j _ k _ => h j k)
  let q := barycenter w b s
  refine ⟨q, fun i => ?_⟩
  have hv : ‖q - b i‖ ^ 2 - (r i) ^ 2 ≤ f w := by
    by_contra hh
    let d := ‖q - b i‖ ^ 2 - (r i) ^ 2 - f w
    let g := ‖b i - q‖ ^ 2
    let ε := min (1 / 2 : ℝ) (d / (2 * (1 + g)))
    have hd : 0 < d := sub_pos.mpr (lt_of_not_ge hh)
    have hg : 0 ≤ g := sq_nonneg _
    have hD : 0 < 2 * (1 + g) := by linarith
    have he : 0 < ε := lt_min (by norm_num) (div_pos hd hD)
    have he1 : ε ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hεg : ε * g ≤ d / 2 := by
      calc
        ε * g ≤ ε * (1 + g) := mul_le_mul_of_nonneg_left (by linarith) he.le
        _ ≤ (d / (2 * (1 + g))) * (1 + g) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
        _ = d / 2 := by
          field_simp [show 1 + g ≠ 0 by linarith]
    have hpos : 0 < ε * (d - ε * g) := mul_pos he (by linarith)
    have hdiff : f (vertexMix w i ε) - f w = ε * d - ε ^ 2 * g :=
      ballObjective_vertexMix s (by simp [s]) w b r ε
    have hle : f (vertexMix w i ε) ≤ f w :=
      isMaxOn_iff.mp hmax _ (vertexMix_mem_stdSimplex hw i he.le he1)
    rw [show ε * (d - ε * g) = ε * d - ε ^ 2 * g by ring, ← hdiff] at hpos
    exact (not_lt_of_ge hle) (sub_pos.mp hpos)
  have hsquared : ‖q - b i‖ ^ 2 ≤ (r i) ^ 2 := by linarith
  have hnorm : ‖q - b i‖ ≤ r i := le_of_sq_le_sq hsquared (norm_nonneg (a i - p))
  simpa only [r, norm_sub_rev (a i) p] using hnorm

theorem ball_family_intersection {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (a : ι → E) (b : ι → F) (p : E)
    (h : ∀ i j, ‖b i - b j‖ ≤ ‖a i - a j‖) :
    ∃ q : F, ∀ i, ‖q - b i‖ ≤ ‖p - a i‖ := by
  classical
  by_cases hI : Nonempty ι
  · let T := InnerProductSpace.toDual ℝ F
    let B (i : ι) : Set (WeakDual ℝ F) :=
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (T (b i)) ‖p - a i‖
    let i₀ : ι := Classical.choice hI
    have hK : IsCompact (B i₀) := WeakDual.isCompact_closedBall ℝ (T (b i₀)) ‖p - a i₀‖
    have hB : ∀ i, IsClosed (B i) := fun i =>
      WeakDual.isClosed_closedBall (T (b i)) ‖p - a i‖
    have hfin (u : Finset ι) : (B i₀ ∩ ⋂ i ∈ u, B i).Nonempty := by
      let s : Finset ι := insert i₀ u
      letI : Nonempty (s : Type _) := (Finset.insert_nonempty i₀ u).coe_sort
      obtain ⟨q, hq⟩ := finite_ball_intersection (ι := (s : Type _))
        (fun j => a j.1) (fun j => b j.1) p (fun j k => h j.1 k.1)
      have hmem (i : ι) (hi : i ∈ s) : StrongDual.toWeakDual (T q) ∈ B i := by
        change dist (T q) (T (b i)) ≤ ‖p - a i‖
        rw [LinearIsometryEquiv.dist_map, dist_eq_norm]
        exact hq ⟨i, hi⟩
      refine ⟨StrongDual.toWeakDual (T q), hmem i₀ (by simp [s]), ?_⟩
      exact Set.mem_iInter₂.mpr fun i hi => hmem i (by simp [s, hi])
    obtain ⟨ℓ, _, hℓ⟩ := hK.inter_iInter_nonempty B hB hfin
    let q := T.symm (WeakDual.toStrongDual ℓ)
    refine ⟨q, fun i => ?_⟩
    have hi : ℓ ∈ B i := Set.mem_iInter.mp hℓ i
    change dist (WeakDual.toStrongDual ℓ) (T (b i)) ≤ ‖p - a i‖ at hi
    have hq : T q = WeakDual.toStrongDual ℓ := T.apply_symm_apply _
    rw [← hq, LinearIsometryEquiv.dist_map, dist_eq_norm] at hi
    exact hi
  · exact ⟨0, fun i => (hI ⟨i⟩).elim⟩

end DRS
