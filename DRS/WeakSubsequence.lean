import Mathlib

/-!
# Weak subsequences of bounded sequences in a Hilbert space

Every bounded sequence in a real Hilbert space has a weakly convergent subsequence,
expressed as convergence of inner products against every test vector. No separability
is assumed for the final statement; the proof reduces to the separable case via the
closed linear span of the sequence.
-/

open Filter Set
open scoped InnerProductSpace Topology

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def WeaklyTendsTo (u : ℕ → E) (z : E) : Prop :=
  ∀ v : E, Tendsto (fun n => ⟪u n, v⟫_ℝ) atTop (𝓝 ⟪z, v⟫_ℝ)

theorem exists_weak_subseq_separable [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z : E, WeaklyTendsTo (u ∘ φ) z := by
  classical
  let T := InnerProductSpace.toDual ℝ E
  let K : Set (WeakDual ℝ E) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M
  have hK : IsCompact K := WeakDual.isCompact_closedBall ℝ (0 : StrongDual ℝ E) M
  letI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  let d : ℕ → E := TopologicalSpace.denseSeq E
  let Φ : ↥K → (ℕ → ℝ) := fun a j => a.1 (d j)
  have hΦ : Continuous Φ := continuous_pi fun j =>
    (WeakDual.eval_continuous (d j)).comp continuous_subtype_val
  have hI : Function.Injective Φ := by
    intro a b hab
    apply Subtype.ext
    apply DFunLike.ext
    intro v
    have hclosed : IsClosed {x : E | a.1 x = b.1 x} :=
      isClosed_eq (WeakDual.toStrongDual a.1).continuous (WeakDual.toStrongDual b.1).continuous
    have hsub : Set.range d ⊆ {x : E | a.1 x = b.1 x} := by
      rintro _ ⟨j, rfl⟩
      exact congr_fun hab j
    exact closure_minimal hsub hclosed (TopologicalSpace.denseRange_denseSeq E v)
  have hEmb := (hΦ.isClosedEmbedding hI).isEmbedding
  let w (n : ℕ) : ↥K := ⟨StrongDual.toWeakDual (T (u n)), by
    change dist (T (u n)) 0 ≤ M
    rw [dist_zero_right, T.norm_map]
    exact hM n⟩
  obtain ⟨z, hz, φ, hφ, hlim⟩ := (isCompact_range hΦ).tendsto_subseq
    (x := Φ ∘ w) (fun n => ⟨w n, rfl⟩)
  obtain ⟨q, rfl⟩ := hz
  have hq : Tendsto (w ∘ φ) atTop (𝓝 q) := by
    rw [hEmb.tendsto_nhds_iff]
    simpa [Function.comp_def] using hlim
  refine ⟨φ, hφ, T.symm (WeakDual.toStrongDual q.1), ?_⟩
  intro v
  have hev : Continuous (fun a : ↥K => a.1 v) :=
    (WeakDual.eval_continuous v).comp continuous_subtype_val
  have hv := (hev.tendsto q).comp hq
  change Tendsto (fun n => (T (u (φ n))) v) atTop
    (𝓝 ((WeakDual.toStrongDual q.1) v)) at hv
  simpa only [Function.comp_def, T, InnerProductSpace.toDual_apply,
    InnerProductSpace.toDual_symm_apply] using hv

theorem exists_weak_subseq (u : ℕ → E) {M : ℝ} (hM : ∀ n, ‖u n‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z : E, WeaklyTendsTo (u ∘ φ) z := by
  classical
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range u)
  let W : Submodule ℝ E := V.topologicalClosure
  have hclosed : IsClosed (W : Set E) := V.isClosed_topologicalClosure
  have hsep : TopologicalSpace.IsSeparable (W : Set E) := by
    change TopologicalSpace.IsSeparable (closure (V : Set E))
    exact ((Set.countable_range u).isSeparable.span (R := ℝ)).closure
  letI : CompleteSpace W := hclosed.completeSpace_coe
  letI : TopologicalSpace.SeparableSpace W := hsep.separableSpace
  let uW (n : ℕ) : W :=
    ⟨u n, V.le_topologicalClosure (Submodule.subset_span (Set.mem_range_self n))⟩
  obtain ⟨φ, hφ, z, hz⟩ := exists_weak_subseq_separable uW (M := M) (fun n => hM n)
  refine ⟨φ, hφ, (z : E), ?_⟩
  intro v
  simpa only [Function.comp_def, Submodule.inner_orthogonalProjection_eq_of_mem_left, uW]
    using hz (W.orthogonalProjection v)

end DRS
