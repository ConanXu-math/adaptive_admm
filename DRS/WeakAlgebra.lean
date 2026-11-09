import DRS.WeakSubsequence

/-!
# Weak convergence algebra and simultaneous subsequences

Basic tools for weak convergence: strong-to-weak transfer, closure under negation and
under small strong perturbations, simultaneous weak subsequences of pairs of bounded
sequences, and a real-valued criterion that a sequence converges when every subsequence
has a convergent subsubsequence with the same limit.
-/

open Filter
open scoped InnerProductSpace Topology

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem tendsto_inner_zero_of_eventual_bound (f g : ℕ → E) {M : ℝ}
    (hf : Tendsto (fun n => ‖f n‖) atTop (𝓝 0))
    (hg : ∀ᶠ n in atTop, ‖g n‖ ≤ M) :
    Tendsto (fun n => ⟪f n, g n⟫_ℝ) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun n => ‖f n‖ * M) ?_ ?_
  · filter_upwards [hg] with n hn
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm (f n) (g n)).trans
      (mul_le_mul_of_nonneg_left hn (norm_nonneg _))
  · simpa using hf.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => M) atTop (𝓝 M))

omit [CompleteSpace E] in
theorem WeaklyTendsTo.neg {u : ℕ → E} {z : E} (h : WeaklyTendsTo u z) :
    WeaklyTendsTo (fun n => -u n) (-z) := by
  intro v
  simpa only [inner_neg_left] using (h v).neg

omit [CompleteSpace E] in
theorem weaklyTendsTo_of_norm_sub_zero {u v : ℕ → E} {z : E}
    (hu : WeaklyTendsTo u z)
    (h : Tendsto (fun n => ‖v n - u n‖) atTop (𝓝 0)) :
    WeaklyTendsTo v z := by
  intro w
  have h0 := tendsto_inner_zero_of_eventual_bound (fun n => v n - u n) (fun _ => w)
    (M := ‖w‖) h (Filter.Eventually.of_forall fun _ => le_rfl)
  have hsum : Tendsto (fun n => ⟪u n, w⟫_ℝ + ⟪v n - u n, w⟫_ℝ) atTop (𝓝 ⟪z, w⟫_ℝ) := by
    simpa only [add_zero] using (hu w).add h0
  have heq : (fun n => ⟪u n, w⟫_ℝ + ⟪v n - u n, w⟫_ℝ) =
      fun n => ⟪v n, w⟫_ℝ := by
    funext n
    rw [inner_sub_left]
    ring
  rwa [heq] at hsum

theorem exists_weak_pair_subseq (u b : ℕ → E) {M N : ℝ}
    (hU : ∀ n, ‖u n‖ ≤ M) (hB : ∀ n, ‖b n‖ ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z w : E,
      WeaklyTendsTo (u ∘ φ) z ∧ WeaklyTendsTo (b ∘ φ) w := by
  obtain ⟨φ, hφ, z, hz⟩ := exists_weak_subseq u hU
  obtain ⟨ψ, hψ, w, hw⟩ := exists_weak_subseq (b ∘ φ) (fun n => hB (φ n))
  exact ⟨φ ∘ ψ, hφ.comp hψ, z, w, fun v => (hz v).comp hψ.tendsto_atTop, hw⟩

theorem tendsto_real_of_subseq_subseq (f : ℕ → ℝ) (x : ℝ)
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      Tendsto (f ∘ φ ∘ ψ) atTop (𝓝 x)) :
    Tendsto f atTop (𝓝 x) := by
  by_contra hnot
  rw [Metric.tendsto_atTop] at hnot
  push_neg at hnot
  obtain ⟨ε, hε, hbad⟩ := hnot
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist (f n) x := frequently_atTop.2 hbad
  obtain ⟨φ, hφ, hφbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ψ, _, hlim⟩ := h φ hφ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  exact (not_lt_of_ge (hφbad (ψ N))) (hN N le_rfl)

def pairEnergy (c : ℝ) (u b z w : E) : ℝ :=
  ‖u - z‖ ^ 2 + c * ‖b - w‖ ^ 2

omit [CompleteSpace E] in
theorem weak_pair_limit_unique (u b : ℕ → E) {c : ℝ} (hc : 0 < c)
    {z₁ w₁ z₂ w₂ : E} {φ ψ : ℕ → ℕ}
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hu₁ : WeaklyTendsTo (u ∘ φ) z₁) (hb₁ : WeaklyTendsTo (b ∘ φ) w₁)
    (hu₂ : WeaklyTendsTo (u ∘ ψ) z₂) (hb₂ : WeaklyTendsTo (b ∘ ψ) w₂)
    (hE₁ : ∃ L : ℝ, Tendsto (fun n => pairEnergy c (u n) (b n) z₁ w₁) atTop (𝓝 L))
    (hE₂ : ∃ L : ℝ, Tendsto (fun n => pairEnergy c (u n) (b n) z₂ w₂) atTop (𝓝 L)) :
    z₁ = z₂ ∧ w₁ = w₂ := by
  obtain ⟨L₁, hL₁⟩ := hE₁
  obtain ⟨L₂, hL₂⟩ := hE₂
  let C := ‖z₁‖ ^ 2 - ‖z₂‖ ^ 2 + c * (‖w₁‖ ^ 2 - ‖w₂‖ ^ 2)
  let f (n : ℕ) := 2 * ⟪u n, z₂ - z₁⟫_ℝ + (2 * c) * ⟪b n, w₂ - w₁⟫_ℝ
  have heq : (fun n => (pairEnergy c (u n) (b n) z₁ w₁ -
      pairEnergy c (u n) (b n) z₂ w₂) - C) = f := by
    funext n
    dsimp [pairEnergy, C, f]
    simp only [norm_sub_sq_real, inner_sub_right]
    ring
  have hdiff : Tendsto (fun n => (pairEnergy c (u n) (b n) z₁ w₁ -
      pairEnergy c (u n) (b n) z₂ w₂) - C) atTop (𝓝 (L₁ - L₂ - C)) :=
    (hL₁.sub hL₂).sub tendsto_const_nhds
  rw [heq] at hdiff
  have h₁ : Tendsto (f ∘ φ) atTop
      (𝓝 (2 * ⟪z₁, z₂ - z₁⟫_ℝ + (2 * c) * ⟪w₁, w₂ - w₁⟫_ℝ)) :=
    ((hu₁ (z₂ - z₁)).const_mul 2).add ((hb₁ (w₂ - w₁)).const_mul (2 * c))
  have h₂ : Tendsto (f ∘ ψ) atTop
      (𝓝 (2 * ⟪z₂, z₂ - z₁⟫_ℝ + (2 * c) * ⟪w₂, w₂ - w₁⟫_ℝ)) :=
    ((hu₂ (z₂ - z₁)).const_mul 2).add ((hb₂ (w₂ - w₁)).const_mul (2 * c))
  have hEq := (tendsto_nhds_unique h₁ (hdiff.comp hφ.tendsto_atTop)).trans
    (tendsto_nhds_unique (hdiff.comp hψ.tendsto_atTop) h₂)
  have hd : 2 * ‖z₂ - z₁‖ ^ 2 + (2 * c) * ‖w₂ - w₁‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq (z₂ - z₁), ← real_inner_self_eq_norm_sq (w₂ - w₁),
      inner_sub_left, inner_sub_left]
    linarith only [hEq]
  have hb0 : 0 ≤ c * ‖w₂ - w₁‖ ^ 2 := mul_nonneg hc.le (sq_nonneg _)
  have hz : ‖z₂ - z₁‖ ^ 2 = 0 := by linarith only [hd, hb0, sq_nonneg ‖z₂ - z₁‖]
  have hwb : c * ‖w₂ - w₁‖ ^ 2 = 0 := by linarith only [hd, hz]
  have hw := (mul_eq_zero.mp hwb).resolve_left hc.ne'
  exact ⟨(sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))).symm,
    (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hw))).symm⟩

end DRS
