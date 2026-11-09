import DRS.EnergyControl
import DRS.GraphLimit
import DRS.WeakAlgebra

/-!
# Assembling weak limits from strong residuals and fixed-metric energy

Two connectors: from strong residual convergence (positions and values of both graphs)
and boundedness to membership of the weak limit in the solution set; and from the
DRS energy control to convergence of the fixed-coefficient pair energy with
coefficient `Lτ²`.
-/

open Filter
open scoped InnerProductSpace Topology

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A B : E → Set E}

theorem extendedSolution_of_residual_weak_pair
    (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    (v a u b : ℕ → E) (z w : E)
    (hva : ∀ n, a n ∈ A (v n)) (hub : ∀ n, b n ∈ B (u n))
    {M N : ℝ} (hU : ∀ n, ‖u n‖ ≤ M) (hBnd : ∀ n, ‖b n‖ ≤ N)
    (hv0 : Tendsto (fun n => ‖v n - u n‖) atTop (𝓝 0))
    (ha0 : Tendsto (fun n => ‖a n + b n‖) atTop (𝓝 0))
    (hu : WeaklyTendsTo u z) (hb : WeaklyTendsTo b w) :
    ExtendedSolution A B z w := by
  have hv := weaklyTendsTo_of_norm_sub_zero hu hv0
  have hdiff : Tendsto (fun n => ‖a n - (-b n)‖) atTop (𝓝 0) := by
    simpa only [sub_neg_eq_add] using ha0
  have ha := weaklyTendsTo_of_norm_sub_zero hb.neg hdiff
  have hvBound : ∀ᶠ n in atTop, ‖v n‖ ≤ M + 1 := by
    filter_upwards [(tendsto_order.1 hv0).2 1 zero_lt_one] with n hn
    calc
      ‖v n‖ ≤ ‖v n - u n‖ + ‖u n‖ := by
        simpa only [sub_add_cancel] using norm_add_le (v n - u n) (u n)
      _ ≤ M + 1 := by linarith [hU n]
  have h₁ := tendsto_inner_zero_of_eventual_bound (fun n => a n + b n) v ha0 hvBound
  have huv : Tendsto (fun n => ‖u n - v n‖) atTop (𝓝 0) := by
    have heq : (fun n => ‖u n - v n‖) = fun n => ‖v n - u n‖ := by
      funext n
      exact norm_sub_rev (u n) (v n)
    rwa [heq]
  have h₂ := tendsto_inner_zero_of_eventual_bound (fun n => u n - v n) b huv
    (Filter.Eventually.of_forall hBnd)
  have hsum : Tendsto (fun n => ⟪a n + b n, v n⟫_ℝ + ⟪u n - v n, b n⟫_ℝ) atTop (𝓝 0) := by
    simpa only [add_zero] using h₁.add h₂
  have heq : (fun n => ⟪a n + b n, v n⟫_ℝ + ⟪u n - v n, b n⟫_ℝ) =
      fun n => ⟪v n, a n⟫_ℝ + ⟪u n, b n⟫_ℝ := by
    funext n
    simp only [inner_add_left, inner_sub_left]
    rw [real_inner_comm (a n) (v n), real_inner_comm (b n) (v n)]
    ring
  rw [heq] at hsum
  exact extendedSolution_of_weak_graph_limit hA hB v a u b z w hva hub hv ha hu hb hsum

theorem drs_fixed_energy_limit (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 < τ n) (s₀ : DRState B)
    {m U Lτ : ℝ} (hm : 0 < m) (hl : ∀ n, m ≤ τ n) (hu : ∀ n, τ n ≤ U)
    (hδ : Summable fun n => |τ (n + 1) - τ n|)
    (hτlim : Tendsto τ atTop (𝓝 Lτ)) {z w : E} (hsol : ExtendedSolution A B z w) :
    let s := drStates hA hB τ hτ s₀
    ∃ L : ℝ, Tendsto (fun n => pairEnergy (Lτ ^ 2) (s n).u (s n).b z w) atTop (𝓝 L) := by
  let s := drStates hA hB τ hτ s₀
  let a (n : ℕ) := ‖(s n).u - z‖ ^ 2
  let b (n : ℕ) := ‖(s n).b - w‖ ^ 2
  let c (n : ℕ) := (τ (n + 1)) ^ 2
  obtain ⟨⟨C, hC⟩, ⟨L, hL⟩, _⟩ := drs_energy_control hA hB τ hτ s₀ hm hl hu hδ hsol
  have hc (n : ℕ) : m ^ 2 ≤ c n := pow_le_pow_left₀ hm.le (hl (n + 1)) 2
  have hBdd (n : ℕ) : b n ≤ C / m ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hm)).2
    calc
      b n * m ^ 2 ≤ b n * c n := mul_le_mul_of_nonneg_left (hc n) (sq_nonneg _)
      _ = c n * b n := mul_comm _ _
      _ ≤ a n + c n * b n := le_add_of_nonneg_left (sq_nonneg _)
      _ ≤ C := hC n
  have hclim : Tendsto c atTop (𝓝 (Lτ ^ 2)) := (hτlim.comp (tendsto_add_atTop_nat 1)).pow 2
  exact ⟨L, fixed_coefficient_energy_tendsto a b c (fun _ => sq_nonneg _) hBdd hclim hL⟩

end DRS
