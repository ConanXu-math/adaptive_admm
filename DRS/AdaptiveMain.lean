import DRS.Convergence
import DRS.AdaptiveSpec

/-!
# Full-sequence weak convergence for the adaptive recursion of equation (21)

The adaptive Douglas–Rachford recursion with clipped ratio, conservation factor and
summable `ω` produces step sizes satisfying the hypotheses of `drs_weak_convergence`;
its state sequence therefore converges weakly to an extended solution.
-/

open Filter
open scoped InnerProductSpace Topology

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A B : E → Set E}

theorem adaptive_drs_weak_convergence (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 < ω n ∧ ω n ≤ 1) (hs : Summable ω) (y₀ : E)
    (hS : ∃ z w : E, ExtendedSolution A B z w) :
    let s := adaptiveStates hA hB hlo hle ω hω y₀
    ∃ z w : E, ExtendedSolution A B z w ∧
      WeaklyTendsTo (fun n => (s n).state.u) z ∧
      WeaklyTendsTo (fun n => (s n).state.b) w := by
  let s := adaptiveStates hA hB hlo hle ω hω y₀
  let τ : ℕ → ℝ := fun n => (s n).t
  let hτ : ∀ n, 0 < τ n := fun n => (s n).ht
  obtain ⟨m, U, L, hm, hl, hu, hδ, hτlim⟩ := adaptive_steps_control hA hB hlo hle ω hω hs y₀
  obtain ⟨z, w, hz, hU, hBw⟩ :=
    drs_weak_convergence hA hB τ hτ (s 0).state hm hl hu hδ hτlim hS
  have hEq : ∀ n, (s n).state = drStates hA hB τ hτ (s 0).state n :=
    adaptive_state_eq_drStates hA hB hlo hle ω hω y₀
  refine ⟨z, w, hz, ?_, ?_⟩
  · have huEq : (fun n => (s n).state.u) = fun n => (drStates hA hB τ hτ (s 0).state n).u := by
      funext n
      rw [hEq n]
    rw [huEq]
    exact hU
  · have hbEq : (fun n => (s n).state.b) = fun n => (drStates hA hB τ hτ (s 0).state n).b := by
      funext n
      rw [hEq n]
    rw [hbEq]
    exact hBw

def conservationSchedule (ωTail : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => ωTail n

theorem conservationSchedule_valid (ωTail : ℕ → ℝ)
    (hω : ∀ n, 0 < ωTail n ∧ ωTail n ≤ 1) :
    ∀ n, 0 < conservationSchedule ωTail n ∧ conservationSchedule ωTail n ≤ 1 := by
  intro n
  cases n with
  | zero => simp [conservationSchedule]
  | succ n => exact hω n

theorem conservationSchedule_summable (ωTail : ℕ → ℝ) (hs : Summable ωTail) :
    Summable (conservationSchedule ωTail) := by
  apply (summable_nat_add_iff 1).1
  simpa only [conservationSchedule] using hs

noncomputable def adaptiveStatesFromTail
    (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ωTail : ℕ → ℝ) (hω : ∀ n, 0 < ωTail n ∧ ωTail n ≤ 1) (y₀ : E) : ℕ → AdaptiveState B :=
  adaptiveStates hA hB hlo hle (conservationSchedule ωTail)
    (conservationSchedule_valid ωTail hω) y₀

theorem adaptiveStatesFromTail_succ
    (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ωTail : ℕ → ℝ) (hω : ∀ n, 0 < ωTail n ∧ ωTail n ≤ 1) (y₀ : E) (n : ℕ) :
    adaptiveStatesFromTail hA hB hlo hle ωTail hω y₀ (n + 1) =
      adaptiveStep hA hB hlo hle (ωTail n) (hω n).1 (hω n).2
        (adaptiveStatesFromTail hA hB hlo hle ωTail hω y₀ n) :=
  rfl

theorem adaptive_drs_weak_convergence_from_tail
    (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ωTail : ℕ → ℝ) (hω : ∀ n, 0 < ωTail n ∧ ωTail n ≤ 1)
    (hs : Summable ωTail) (y₀ : E) (hS : ∃ z w : E, ExtendedSolution A B z w) :
    let s := adaptiveStatesFromTail hA hB hlo hle ωTail hω y₀
    ∃ z w : E, ExtendedSolution A B z w ∧
      WeaklyTendsTo (fun n => (s n).state.u) z ∧
      WeaklyTendsTo (fun n => (s n).state.b) w :=
  adaptive_drs_weak_convergence hA hB hlo hle (conservationSchedule ωTail)
    (conservationSchedule_valid ωTail hω) (conservationSchedule_summable ωTail hs) y₀ hS

end DRS
