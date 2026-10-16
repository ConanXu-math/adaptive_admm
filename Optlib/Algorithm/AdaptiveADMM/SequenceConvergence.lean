import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Convergence of nonnegative energies

The C1 and C2 proofs use the same scalar argument after normalizing their
energies. Monotonicity is needed only from index one onward.
-/

open Set Filter Topology

namespace AdaptiveADMM_Convergence_Proof

/-- A nonnegative sequence with an antitone tail and a subsequence tending to
zero tends to zero. The initial term need not satisfy the descent inequality. -/
theorem tendsto_zero_of_antitone_tail_of_subseq
    {u : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ u n)
    (h_antitone : Antitone (fun n => u (n + 1)))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_subseq : Tendsto (fun n => u (φ n)) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) := by
  have h_bdd : BddBelow (range (fun n => u (n + 1))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact h_nonneg (n + 1)
  have h_limit : Tendsto u atTop (𝓝 (⨅ n, u (n + 1))) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    exact tendsto_atTop_ciInf h_antitone h_bdd
  have h_zero : (⨅ n, u (n + 1)) = 0 :=
    tendsto_nhds_unique (h_limit.comp hφ.tendsto_atTop) h_subseq
  simpa only [h_zero] using h_limit

/-- Comparison test for nonnegative real-valued families. -/
theorem summable_of_nonneg_of_le {β : Type*} {f g : β → ℝ}
    (hg : ∀ n, 0 ≤ g n) (hgf : ∀ n, g n ≤ f n) (hf : Summable f) :
    Summable g := by
  rw [← NNReal.summable_mk]
  have hf_nonneg : ∀ n, 0 ≤ f n := fun n => (hg n).trans (hgf n)
  have hle : ∀ n, (⟨g n, hg n⟩ : NNReal) ≤ ⟨f n, hf_nonneg n⟩ := by
    intro n
    exact hgf n
  apply NNReal.summable_of_le hle
  rw [← NNReal.summable_coe]
  exact hf
  exact hg

lemma inSet {X : Type*} ( f : ℕ → X ) : ∀ n : ℕ , f n ∈ range f := by
   intro n;use n


end AdaptiveADMM_Convergence_Proof
