import DRS.ConvergenceAux

/-!
# Theorem 3.1: full-sequence weak convergence of the Douglas–Rachford recursion

For maximal monotone relations `A`, `B` with a nonempty extended solution set, any
initial graph point and any step size sequence with a uniform positive lower bound,
a finite upper bound, summable consecutive variation and a limit, every weak cluster
point of `(u n, b n)` lies in the solution set and the whole sequences converge weakly
to one such point.
-/

open Filter
open scoped InnerProductSpace Topology

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A B : E → Set E}

theorem drs_weak_convergence (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 < τ n) (s₀ : DRState B)
    {m U Lτ : ℝ} (hm : 0 < m) (hl : ∀ n, m ≤ τ n) (hu : ∀ n, τ n ≤ U)
    (hδ : Summable fun n => |τ (n + 1) - τ n|) (hτlim : Tendsto τ atTop (𝓝 Lτ))
    (hS : ∃ z w : E, ExtendedSolution A B z w) :
    let s := drStates hA hB τ hτ s₀
    ∃ z w : E, ExtendedSolution A B z w ∧
      WeaklyTendsTo (fun n => (s n).u) z ∧ WeaklyTendsTo (fun n => (s n).b) w := by
  let s := drStates hA hB τ hτ s₀
  let d := drTraceStep hA hB τ hτ s₀
  let u (n : ℕ) := (s n).u
  let b (n : ℕ) := (s n).b
  let v (n : ℕ) := (d n).v
  let a (n : ℕ) := (d n).a
  obtain ⟨z₀, w₀, h₀⟩ := hS
  obtain ⟨⟨C, hC⟩, _, hsum⟩ := drs_energy_control hA hB τ hτ s₀ hm hl hu hδ h₀
  obtain ⟨⟨M, hU⟩, ⟨N, hNB⟩⟩ := state_norm_bounds_of_energy s (fun n => (τ (n + 1)) ^ 2)
    (sq_pos_of_pos hm) (fun n => pow_le_pow_left₀ hm.le (hl (n + 1)) 2) z₀ w₀ hC
  have hres : Tendsto (fun n => ‖u n - v n‖) atTop (𝓝 0) :=
    norm_tendsto_zero_of_summable_sq (fun n => u n - v n) hsum
  have hv0 : Tendsto (fun n => ‖v n - u n‖) atTop (𝓝 0) := by
    have heq : (fun n => ‖v n - u n‖) = fun n => ‖u n - v n‖ := by
      funext n
      exact norm_sub_rev (v n) (u n)
    rw [heq]
    exact hres
  have ha0 : Tendsto (fun n => ‖a n + b n‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun n => (d n).a_add_prev_b_bound hm (hl (n + 1))) ?_
    simpa only [zero_div] using hres.div_const m
  have hmem {φ : ℕ → ℕ} (hφ : StrictMono φ) {z w : E}
      (hUz : WeaklyTendsTo (u ∘ φ) z) (hBw : WeaklyTendsTo (b ∘ φ) w) :
      ExtendedSolution A B z w :=
    extendedSolution_of_residual_weak_pair hA hB (v ∘ φ) (a ∘ φ) (u ∘ φ) (b ∘ φ) z w
      (fun n => (d (φ n)).ha) (fun n => (s (φ n)).hb)
      (fun n => hU (φ n)) (fun n => hNB (φ n))
      (hv0.comp hφ.tendsto_atTop) (ha0.comp hφ.tendsto_atTop) hUz hBw
  obtain ⟨φ, hφ, z, w, hUz, hBw⟩ := exists_weak_pair_subseq u b hU hNB
  have hzw := hmem hφ hUz hBw
  have hE := drs_fixed_energy_limit hA hB τ hτ s₀ hm hl hu hδ hτlim hzw
  have hc : 0 < Lτ ^ 2 := sq_pos_of_pos (hm.trans_le (ge_of_tendsto' hτlim hl))
  have hunique {ψ : ℕ → ℕ} (hψ : StrictMono ψ) {z' w' : E}
      (hUz' : WeaklyTendsTo (u ∘ ψ) z') (hBw' : WeaklyTendsTo (b ∘ ψ) w') :
      z = z' ∧ w = w' :=
    weak_pair_limit_unique u b hc hφ hψ hUz hBw hUz' hBw' hE
      (drs_fixed_energy_limit hA hB τ hτ s₀ hm hl hu hδ hτlim (hmem hψ hUz' hBw'))
  have hsub (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
      ∃ χ : ℕ → ℕ, StrictMono χ ∧
        WeaklyTendsTo (u ∘ ψ ∘ χ) z ∧ WeaklyTendsTo (b ∘ ψ ∘ χ) w := by
    obtain ⟨χ, hχ, z', w', hz', hw'⟩ :=
      exists_weak_pair_subseq (u ∘ ψ) (b ∘ ψ) (fun n => hU (ψ n)) (fun n => hNB (ψ n))
    obtain ⟨hz, hw⟩ := hunique (hψ.comp hχ) hz' hw'
    rw [← hz] at hz'
    rw [← hw] at hw'
    exact ⟨χ, hχ, hz', hw'⟩
  refine ⟨z, w, hzw, ?_, ?_⟩
  · intro q
    apply tendsto_real_of_subseq_subseq (fun n => ⟪u n, q⟫_ℝ) ⟪z, q⟫_ℝ
    intro ψ hψ
    obtain ⟨χ, hχ, hz, _⟩ := hsub ψ hψ
    exact ⟨χ, hχ, hz q⟩
  · intro q
    apply tendsto_real_of_subseq_subseq (fun n => ⟪b n, q⟫_ℝ) ⟪w, q⟫_ℝ
    intro ψ hψ
    obtain ⟨χ, hχ, _, hw⟩ := hsub ψ hψ
    exact ⟨χ, hχ, hw q⟩

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem ExtendedSolution.is_zero {z w : E} (h : ExtendedSolution A B z w) :
    ∃ a ∈ A z, ∃ b ∈ B z, a + b = 0 :=
  ⟨-w, h.1, w, h.2, neg_add_cancel w⟩

end DRS
