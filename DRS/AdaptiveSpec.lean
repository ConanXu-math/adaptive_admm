import DRS.Adaptive
import DRS.ScalarEnergy

/-!
# Connecting the adaptive recursion of equation (21) to arbitrary-step DRS data

The step size sequence of `adaptiveStates` satisfies the scalar bounds of
`conservation_steps_control`, its state projection equals `drStates`, and the `y`
coordinates obey the scaled resolvent identity of equation (11) with factor
`ν = conservationFactor`.
-/

open Filter
open scoped Topology

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A B : E → Set E}

theorem adaptive_steps_control (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 < ω n ∧ ω n ≤ 1) (hs : Summable ω) (y₀ : E) :
    let s := adaptiveStates hA hB hlo hle ω hω y₀
    let τ : ℕ → ℝ := fun n => (s n).t
    ∃ m U L : ℝ, 0 < m ∧ (∀ n, m ≤ τ n) ∧ (∀ n, τ n ≤ U) ∧
      Summable (fun n => |τ (n + 1) - τ n|) ∧ Tendsto τ atTop (𝓝 L) := by
  let s := adaptiveStates hA hB hlo hle ω hω y₀
  let τ : ℕ → ℝ := fun n => (s n).t
  let κ : ℕ → ℝ := fun n => clipRatio lo hi (s n).state.u (s n).y
  have hsTail : Summable (fun n => ω (n + 1)) := hs.comp_injective Nat.succ_injective
  exact conservation_steps_control τ κ (fun n => ω (n + 1)) hlo
    (fun n => clipRatio_bounds hle (s n).state.u (s n).y) (fun n => hω (n + 1)) hsTail
    rfl (fun n => (s n).ht) (fun _ => rfl)

theorem adaptive_state_eq_drStates (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 < ω n ∧ ω n ≤ 1) (y₀ : E) :
    let s := adaptiveStates hA hB hlo hle ω hω y₀
    let τ : ℕ → ℝ := fun n => (s n).t
    let hτ : ∀ n, 0 < τ n := fun n => (s n).ht
    ∀ n, (s n).state = drStates hA hB τ hτ (s 0).state n := by
  let s := adaptiveStates hA hB hlo hle ω hω y₀
  let τ : ℕ → ℝ := fun n => (s n).t
  let hτ : ∀ n, 0 < τ n := fun n => (s n).ht
  change ∀ n, (s n).state = drStates hA hB τ hτ (s 0).state n
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (drStep hA hB (τ (n + 1)) (hτ (n + 1)) (s n).state).next =
      (drStep hA hB (τ (n + 1)) (hτ (n + 1))
        (drStates hA hB τ hτ (s 0).state n)).next
    rw [ih]

theorem AdaptiveState.resolvent_y (hB : IsMaximalMonotoneRel B) (s : AdaptiveState B) :
    hB.resolvent s.ht s.y = s.state.u := by
  rw [s.hy]
  exact hB.resolvent_graph s.ht s.state.hb

theorem adaptive_y_step (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ω : ℝ) (hω0 : 0 < ω) (hω1 : ω ≤ 1) (s : AdaptiveState B) :
    let ν := conservationFactor ω (clipRatio lo hi s.state.u s.y)
    let s' := adaptiveStep hA hB hlo hle ω hω0 hω1 s
    s'.y = hA.resolvent s'.ht ((1 + ν) • s.state.u - ν • s.y) +
      ν • (s.y - s.state.u) := by
  let ν := conservationFactor ω (clipRatio lo hi s.state.u s.y)
  let s' := adaptiveStep hA hB hlo hle ω hω0 hω1 s
  change s'.y = hA.resolvent s'.ht ((1 + ν) • s.state.u - ν • s.y) +
    ν • (s.y - s.state.u)
  have hy : s.y - s.state.u = s.t • s.state.b := by
    rw [s.hy]
    module
  have hscale : ν • (s.y - s.state.u) = s'.t • s.state.b := by
    rw [hy, smul_smul]
    rfl
  have hpoint : (1 + ν) • s.state.u - ν • s.y = s.state.u - s'.t • s.state.b := by
    rw [← hscale]
    module
  rw [hpoint, hscale]
  rfl

theorem adaptive_factor_eq_ratio (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ω : ℝ) (hω0 : 0 < ω) (hω1 : ω ≤ 1) (s : AdaptiveState B) :
    conservationFactor ω (clipRatio lo hi s.state.u s.y) =
      (adaptiveStep hA hB hlo hle ω hω0 hω1 s).t / s.t := by
  let ν := conservationFactor ω (clipRatio lo hi s.state.u s.y)
  change ν = (ν * s.t) / s.t
  rw [mul_div_assoc, div_self s.ht.ne', mul_one]

end DRS
