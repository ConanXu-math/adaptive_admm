import DRS.Iteration
import DRS.ScalarEnergy

/-!
# Energy and residual control for the Douglas–Rachford sequence

For the recursion of equation (12) with step sizes bounded below by `m > 0`, bounded above
by `U`, and of summable consecutive variation, the shifted energy
`‖u n - z‖² + τ (n+1)² ‖b n - w‖²` is bounded and convergent, and the squared residuals
`‖u n - v (n+1)‖²` are summable, for every extended solution `(z, w)`.
-/

open Filter
open scoped Topology

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A B : E → Set E}

theorem drs_energy_control (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 < τ n) (s₀ : DRState B)
    {m U : ℝ} (hm : 0 < m) (hl : ∀ n, m ≤ τ n) (hu : ∀ n, τ n ≤ U)
    (hδ : Summable fun n => |τ (n + 1) - τ n|) {z w : E}
    (hsol : ExtendedSolution A B z w) :
    let s := drStates hA hB τ hτ s₀
    let d := drTraceStep hA hB τ hτ s₀
    let e (n : ℕ) := ‖(s n).u - z‖ ^ 2 + (τ (n + 1)) ^ 2 * ‖(s n).b - w‖ ^ 2
    (∃ C : ℝ, ∀ n, e n ≤ C) ∧ (∃ L : ℝ, Tendsto e atTop (𝓝 L)) ∧
      Summable (fun n => ‖(s n).u - (d n).v‖ ^ 2) := by
  let s := drStates hA hB τ hτ s₀
  let d := drTraceStep hA hB τ hτ s₀
  let a (n : ℕ) := ‖(s n).u - z‖ ^ 2
  let b (n : ℕ) := ‖(s n).b - w‖ ^ 2
  let c (n : ℕ) := (τ (n + 1)) ^ 2
  let r (n : ℕ) := ‖(s n).u - (d n).v‖ ^ 2
  have htail : Summable (fun n => |τ (n + 2) - τ (n + 1)|) :=
    hδ.comp_injective Nat.succ_injective
  have hsquare : Summable (fun n => |c (n + 1) - c n|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ (htail.mul_left (2 * U))
    intro n
    change |τ (n + 2) ^ 2 - τ (n + 1) ^ 2| ≤ 2 * U * |τ (n + 2) - τ (n + 1)|
    rw [show τ (n + 2) ^ 2 - τ (n + 1) ^ 2 =
      (τ (n + 2) - τ (n + 1)) * (τ (n + 2) + τ (n + 1)) by ring,
      abs_mul, abs_of_nonneg (add_nonneg (hτ (n + 2)).le (hτ (n + 1)).le)]
    calc
      _ ≤ |τ (n + 2) - τ (n + 1)| * (2 * U) :=
        mul_le_mul_of_nonneg_left (by linarith [hu (n + 2), hu (n + 1)]) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hstep (n : ℕ) : a (n + 1) + c n * b (n + 1) + r n ≤ a n + c n * b n :=
    (d n).energy_descent hA.1 hB.1 (hτ (n + 1)) hsol
  exact shifted_energy_control a b c r (sq_pos_of_pos hm)
    (fun _ => sq_nonneg _) (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    (fun n => pow_le_pow_left₀ hm.le (hl (n + 1)) 2) hsquare hstep

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem state_norm_bounds_of_energy (s : ℕ → DRState B) (c : ℕ → ℝ)
    {m C : ℝ} (hm : 0 < m) (hc : ∀ n, m ≤ c n) (z w : E)
    (hC : ∀ n, ‖(s n).u - z‖ ^ 2 + c n * ‖(s n).b - w‖ ^ 2 ≤ C) :
    (∃ M : ℝ, ∀ n, ‖(s n).u‖ ≤ M) ∧ (∃ M : ℝ, ∀ n, ‖(s n).b‖ ≤ M) := by
  have hc0 (n : ℕ) : 0 ≤ c n := hm.le.trans (hc n)
  constructor
  · refine ⟨C + 1 + ‖z‖, fun n => ?_⟩
    have hU : ‖(s n).u - z‖ ^ 2 ≤ C :=
      (le_add_of_nonneg_right (mul_nonneg (hc0 n) (sq_nonneg _))).trans (hC n)
    have hN : ‖(s n).u - z‖ ≤ C + 1 := by
      nlinarith only [hU, sq_nonneg (‖(s n).u - z‖ - 1), norm_nonneg ((s n).u - z)]
    calc
      ‖(s n).u‖ ≤ ‖(s n).u - z‖ + ‖z‖ := by
        simpa only [sub_add_cancel] using norm_add_le ((s n).u - z) z
      _ ≤ _ := add_le_add_right hN _
  · refine ⟨C / m + 1 + ‖w‖, fun n => ?_⟩
    have hB : ‖(s n).b - w‖ ^ 2 ≤ C / m := by
      apply (le_div_iff₀ hm).2
      calc
        ‖(s n).b - w‖ ^ 2 * m ≤ ‖(s n).b - w‖ ^ 2 * c n :=
          mul_le_mul_of_nonneg_left (hc n) (sq_nonneg _)
        _ = c n * ‖(s n).b - w‖ ^ 2 := mul_comm _ _
        _ ≤ ‖(s n).u - z‖ ^ 2 + c n * ‖(s n).b - w‖ ^ 2 :=
          le_add_of_nonneg_left (sq_nonneg _)
        _ ≤ C := hC n
    have hN : ‖(s n).b - w‖ ≤ C / m + 1 := by
      nlinarith only [hB, sq_nonneg (‖(s n).b - w‖ - 1), norm_nonneg ((s n).b - w)]
    calc
      ‖(s n).b‖ ≤ ‖(s n).b - w‖ + ‖w‖ := by
        simpa only [sub_add_cancel] using norm_add_le ((s n).b - w) w
      _ ≤ _ := add_le_add_right hN _

omit [CompleteSpace E] in
theorem fixed_coefficient_energy_tendsto (a b c : ℕ → ℝ) {M L c₀ : ℝ}
    (hb0 : ∀ n, 0 ≤ b n) (hb : ∀ n, b n ≤ M)
    (hc : Tendsto c atTop (𝓝 c₀))
    (he : Tendsto (fun n => a n + c n * b n) atTop (𝓝 L)) :
    Tendsto (fun n => a n + c₀ * b n) atTop (𝓝 L) := by
  have hz : Tendsto (fun n => c n - c₀) atTop (𝓝 0) := by
    simpa using hc.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => c₀) atTop (𝓝 c₀))
  have ha : Tendsto (fun n => |c n - c₀|) atTop (𝓝 0) := by
    simpa [Real.norm_eq_abs] using hz.norm
  have hzero : Tendsto (fun n => (c n - c₀) * b n) atTop (𝓝 0) := by
    refine squeeze_zero_norm (a := fun n => |c n - c₀| * M) ?_ ?_
    · intro n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb0 n)]
      exact mul_le_mul_of_nonneg_left (hb n) (abs_nonneg _)
    · simpa using ha.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => M) atTop (𝓝 M))
  have hh : Tendsto (fun n => (a n + c n * b n) - (c n - c₀) * b n) atTop (𝓝 L) := by
    simpa only [sub_zero] using he.sub hzero
  have heq : (fun n => (a n + c n * b n) - (c n - c₀) * b n) =
      fun n => a n + c₀ * b n := by
    funext n
    ring
  rwa [heq] at hh

omit [CompleteSpace E] in
omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem norm_tendsto_zero_of_summable_sq (f : ℕ → E)
    (h : Summable fun n => ‖f n‖ ^ 2) : Tendsto (fun n => ‖f n‖) atTop (𝓝 0) := by
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h.tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs

omit [CompleteSpace E] in
theorem DRTransition.a_add_prev_b_bound {t : ℝ} {s : DRState B} (d : DRTransition A B t s)
    {m : ℝ} (hm : 0 < m) (hl : m ≤ t) :
    ‖d.a + s.b‖ ≤ ‖s.u - d.v‖ / m := by
  have h : s.u - d.v = t • (d.a + s.b) := by
    calc
      _ = (s.u - t • s.b - d.v) + t • s.b := by module
      _ = _ := by rw [← d.eqA]; module
  have hn : ‖s.u - d.v‖ = t * ‖d.a + s.b‖ := by
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hm.le.trans hl)]
  apply (le_div_iff₀ hm).2
  rw [hn]
  calc
    _ ≤ ‖d.a + s.b‖ * t := mul_le_mul_of_nonneg_left hl (norm_nonneg _)
    _ = _ := mul_comm _ _

end DRS
