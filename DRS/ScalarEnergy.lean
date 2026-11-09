import Mathlib

/-!
# Scalar energy comparison lemmas

Two elementary statements about nonnegative scalar sequences with a multiplicative or
additive one-step error: exponential-type growth control and convergence of an energy
sequence with summable error.
-/

open Filter
open scoped Topology

namespace DRS

theorem energy_le_exp_total (e c : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hc : ∀ n, 0 ≤ c n) (hs : Summable c)
    (hstep : ∀ n, e (n + 1) ≤ (1 + c n) * e n) :
    ∀ n, e n ≤ e 0 * Real.exp (∑' i, c i) := by
  have hf : ∀ n, e n ≤ e 0 * Real.exp (∑ i ∈ Finset.range n, c i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        e (n + 1) ≤ (1 + c n) * e n := hstep n
        _ ≤ Real.exp (c n) * e n := by
          apply mul_le_mul_of_nonneg_right _ (he n)
          simpa [add_comm] using Real.add_one_le_exp (c n)
        _ ≤ Real.exp (c n) * (e 0 * Real.exp (∑ i ∈ Finset.range n, c i)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_nonneg _)
        _ = _ := by
          rw [Finset.sum_range_succ, Real.exp_add]
          ring
  intro n
  exact (hf n).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (hs.sum_le_tsum (Finset.range n) (fun i _ => hc i))) (he 0))

theorem energy_tendsto_of_summable_error (e r δ : ℕ → ℝ)
    (he : ∀ n, 0 ≤ e n) (hr : ∀ n, 0 ≤ r n)
    (hδ : ∀ n, 0 ≤ δ n) (hs : Summable δ)
    (hstep : ∀ n, e (n + 1) + r n ≤ e n + δ n) :
    ∃ L : ℝ, Tendsto e atTop (𝓝 L) ∧ Summable r := by
  let g (n : ℕ) := e n + (∑ i ∈ Finset.range n, r i) - (∑ i ∈ Finset.range n, δ i)
  have hanti : Antitone g := antitone_nat_of_succ_le fun n => by
    dsimp [g]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith [hstep n]
  have hδfin (n : ℕ) : (∑ i ∈ Finset.range n, δ i) ≤ ∑' i, δ i :=
    hs.sum_le_tsum (Finset.range n) (fun i _ => hδ i)
  have hrfin (n : ℕ) : 0 ≤ ∑ i ∈ Finset.range n, r i :=
    Finset.sum_nonneg fun i _ => hr i
  have hbelow : BddBelow (Set.range g) := by
    refine ⟨-(∑' i, δ i), ?_⟩
    rintro _ ⟨n, rfl⟩
    dsimp [g]
    linarith [he n, hrfin n, hδfin n]
  have hzero : g 0 = e 0 := by simp [g]
  have hsumr : Summable r := summable_of_sum_range_le hr (c := e 0 + ∑' i, δ i) fun n => by
    have hn : g n ≤ e 0 := (hanti (Nat.zero_le n)).trans_eq hzero
    dsimp [g] at hn
    linarith [he n, hδfin n]
  have hlim := ((tendsto_atTop_ciInf hanti hbelow).sub hsumr.hasSum.tendsto_sum_nat).add
    hs.hasSum.tendsto_sum_nat
  have heq :
      (fun n => g n - (∑ i ∈ Finset.range n, r i) + (∑ i ∈ Finset.range n, δ i)) = e := by
    funext n
    dsimp [g]
    ring
  rw [heq] at hlim
  exact ⟨_, hlim, hsumr⟩

theorem shifted_energy_control (a b c r : ℕ → ℝ) {m : ℝ} (hm : 0 < m)
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) (hr : ∀ n, 0 ≤ r n)
    (hc : ∀ n, m ≤ c n) (hd : Summable fun n => |c (n + 1) - c n|)
    (hstep : ∀ n, a (n + 1) + c n * b (n + 1) + r n ≤ a n + c n * b n) :
    (∃ C : ℝ, ∀ n, a n + c n * b n ≤ C) ∧
      (∃ L : ℝ, Tendsto (fun n => a n + c n * b n) atTop (𝓝 L)) ∧ Summable r := by
  let e (n : ℕ) := a n + c n * b n
  let f (n : ℕ) := a (n + 1) + c n * b (n + 1)
  let δ (n : ℕ) := |c (n + 1) - c n|
  have he (n : ℕ) : 0 ≤ e n :=
    add_nonneg (ha n) (mul_nonneg (hm.le.trans (hc n)) (hb n))
  have hδ (n : ℕ) : 0 ≤ δ n := abs_nonneg _
  have hF (n : ℕ) : f n + r n ≤ e n := hstep n
  have hShift (n : ℕ) : e (n + 1) ≤ f n + δ n * b (n + 1) := by
    have h := mul_le_mul_of_nonneg_right (le_abs_self (c (n + 1) - c n)) (hb (n + 1))
    change (c (n + 1) - c n) * b (n + 1) ≤ δ n * b (n + 1) at h
    dsimp only [e, f]
    linarith only [h]
  have hB (n : ℕ) : b (n + 1) ≤ f n / m := by
    apply (le_div_iff₀ hm).2
    calc
      b (n + 1) * m ≤ b (n + 1) * c n := mul_le_mul_of_nonneg_left (hc n) (hb (n + 1))
      _ ≤ f n := by dsimp [f]; linarith [ha (n + 1)]
  have hRel (n : ℕ) : e (n + 1) ≤ (1 + δ n / m) * e n := by
    calc
      e (n + 1) ≤ f n + δ n * b (n + 1) := hShift n
      _ ≤ f n + δ n * (f n / m) :=
        add_le_add_left (mul_le_mul_of_nonneg_left (hB n) (hδ n)) _
      _ = (1 + δ n / m) * f n := by ring
      _ ≤ (1 + δ n / m) * e n :=
        mul_le_mul_of_nonneg_left (by linarith [hF n, hr n])
          (add_nonneg zero_le_one (div_nonneg (hδ n) hm.le))
  have hδm : Summable (fun n => δ n / m) := by
    simpa only [div_eq_mul_inv] using (show Summable δ from hd).mul_right m⁻¹
  let C := e 0 * Real.exp (∑' n, δ n / m)
  have hC (n : ℕ) : e n ≤ C :=
    energy_le_exp_total e (fun n => δ n / m) he
      (fun n => div_nonneg (hδ n) hm.le) hδm hRel n
  have hC0 : 0 ≤ C := (he 0).trans (hC 0)
  have hBC (n : ℕ) : b n ≤ C / m := by
    apply (le_div_iff₀ hm).2
    calc
      b n * m ≤ b n * c n := mul_le_mul_of_nonneg_left (hc n) (hb n)
      _ ≤ e n := by dsimp [e]; linarith [ha n]
      _ ≤ C := hC n
  let err (n : ℕ) := δ n * (C / m)
  have hErr0 (n : ℕ) : 0 ≤ err n := mul_nonneg (hδ n) (div_nonneg hC0 hm.le)
  have hErr : Summable err := (show Summable δ from hd).mul_right (C / m)
  have hAdd (n : ℕ) : e (n + 1) + r n ≤ e n + err n := by
    have h := mul_le_mul_of_nonneg_left (hBC (n + 1)) (hδ n)
    change δ n * b (n + 1) ≤ err n at h
    linarith only [hShift n, hF n, h]
  obtain ⟨L, hL, hrSum⟩ := energy_tendsto_of_summable_error e r err he hr hErr0 hErr hAdd
  exact ⟨⟨C, hC⟩, ⟨L, hL⟩, hrSum⟩

theorem conservation_steps_control (τ κ ω : ℕ → ℝ) {lo hi : ℝ}
    (hlo : 0 < lo) (hκ : ∀ n, lo ≤ κ n ∧ κ n ≤ hi)
    (hω : ∀ n, 0 < ω n ∧ ω n ≤ 1) (hs : Summable ω)
    (hτ0 : τ 0 = 1) (hτ : ∀ n, 0 < τ n)
    (hrec : ∀ n, τ (n + 1) = (1 - ω n + ω n * κ n) * τ n) :
    ∃ m U L : ℝ, 0 < m ∧ (∀ n, m ≤ τ n) ∧ (∀ n, τ n ≤ U) ∧
      Summable (fun n => |τ (n + 1) - τ n|) ∧ Tendsto τ atTop (𝓝 L) := by
  let μ := min (1 : ℝ) lo
  let D := max |lo - 1| |hi - 1|
  let ν (n : ℕ) := 1 - ω n + ω n * κ n
  have hμ : 0 < μ := lt_min zero_lt_one hlo
  have hD : 0 ≤ D := (abs_nonneg _).trans (le_max_left _ _)
  have hνlow (n : ℕ) : μ ≤ ν n := by
    calc
      μ = (1 - ω n) * μ + ω n * μ := by ring
      _ ≤ (1 - ω n) * 1 + ω n * κ n := add_le_add
        (mul_le_mul_of_nonneg_left (min_le_left _ _) (sub_nonneg.mpr (hω n).2))
        (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (hκ n).1) (hω n).1.le)
      _ = ν n := by dsimp [ν]; ring
  have hνabs (n : ℕ) : |ν n - 1| ≤ D * ω n := by
    have hk : |κ n - 1| ≤ D := by
      apply abs_le.2
      constructor
      · have hh : -(lo - 1) ≤ D := (neg_le_abs _).trans (le_max_left _ _)
        linarith [(hκ n).1]
      · have hh : hi - 1 ≤ D := (le_abs_self _).trans (le_max_right _ _)
        linarith [(hκ n).2]
    rw [show ν n - 1 = ω n * (κ n - 1) by dsimp [ν]; ring, abs_mul,
      abs_of_nonneg (hω n).1.le]
    exact (mul_le_mul_of_nonneg_left hk (hω n).1.le).trans_eq (mul_comm _ _)
  have hup (n : ℕ) : τ (n + 1) ≤ (1 + D * ω n) * τ n := by
    rw [hrec n]
    change ν n * τ n ≤ (1 + D * ω n) * τ n
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (ν n - 1), hνabs n]) (hτ n).le
  have hνinv (n : ℕ) : (ν n)⁻¹ ≤ 1 + (D / μ) * ω n := by
    rw [← one_div]
    apply (div_le_iff₀ (hμ.trans_le (hνlow n))).2
    have h := mul_le_mul_of_nonneg_left (hνlow n)
      (div_nonneg (mul_nonneg hD (hω n).1.le) hμ.le)
    rw [div_mul_cancel₀ _ hμ.ne'] at h
    calc
      1 ≤ ν n + D * ω n := by linarith [neg_le_abs (ν n - 1), hνabs n]
      _ ≤ ν n + (D * ω n / μ) * ν n := add_le_add_left h _
      _ = _ := by ring
  have hinv (n : ℕ) : (τ (n + 1))⁻¹ ≤ (1 + (D / μ) * ω n) * (τ n)⁻¹ := by
    rw [hrec n, mul_inv_rev]
    change (τ n)⁻¹ * (ν n)⁻¹ ≤ (1 + (D / μ) * ω n) * (τ n)⁻¹
    exact (mul_le_mul_of_nonneg_left (hνinv n) (inv_nonneg.mpr (hτ n).le)).trans_eq
      (mul_comm _ _)
  let U := Real.exp (∑' n, D * ω n)
  let V := Real.exp (∑' n, (D / μ) * ω n)
  have hU (n : ℕ) : τ n ≤ U := by
    have hh := energy_le_exp_total τ (fun n => D * ω n) (fun k => (hτ k).le)
      (fun k => mul_nonneg hD (hω k).1.le) (hs.mul_left D) hup n
    simpa only [hτ0, one_mul, U] using hh
  have hV (n : ℕ) : (τ n)⁻¹ ≤ V := by
    have hh := energy_le_exp_total (fun k => (τ k)⁻¹) (fun k => (D / μ) * ω k)
      (fun k => inv_nonneg.mpr (hτ k).le)
      (fun k => mul_nonneg (div_nonneg hD hμ.le) (hω k).1.le)
      (hs.mul_left (D / μ)) hinv n
    simpa only [hτ0, inv_one, one_mul, V] using hh
  have hV0 : 0 < V := Real.exp_pos _
  have hl (n : ℕ) : V⁻¹ ≤ τ n := by
    rw [← one_div]
    apply (div_le_iff₀ hV0).2
    have hh : 1 / τ n ≤ V := by simpa only [one_div] using hV n
    simpa only [mul_comm] using (div_le_iff₀ (hτ n)).1 hh
  have habs (n : ℕ) : |τ (n + 1) - τ n| ≤ D * ω n * U := by
    rw [hrec n]
    change |ν n * τ n - τ n| ≤ D * ω n * U
    rw [show ν n * τ n - τ n = (ν n - 1) * τ n by ring, abs_mul, abs_of_nonneg (hτ n).le]
    exact (mul_le_mul_of_nonneg_right (hνabs n) (hτ n).le).trans
      (mul_le_mul_of_nonneg_left (hU n) (mul_nonneg hD (hω n).1.le))
  have hsum : Summable (fun n => |τ (n + 1) - τ n|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) habs ((hs.mul_left D).mul_right U)
  have hdist : Summable (fun n => dist (τ n) (τ (n + 1))) := by
    simpa only [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hsum
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  exact ⟨V⁻¹, U, L, inv_pos.mpr hV0, hl, hU, hsum, hL⟩

end DRS
