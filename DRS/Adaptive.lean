import DRS.Iteration

/-!
# The adaptive step-size recursion of equation (21)

Starting from any `y₀` with `t₀ = 1` and `u₀ = J_{t₀ B} y₀`, `b₀ = (y₀ - u₀)/t₀`, the
recursion of equation (21) updates the step size by

`κ (n+1) = clip_[κ_min, κ_max] (‖u n‖ / ‖y n - u n‖)` (with `κ_max` when the denominator
vanishes), `ν (n+1) = 1 - ω (n+1) + ω (n+1) κ (n+1)`, `t (n+1) = ν (n+1) * t n`, and then
performs one step of equation (12), setting `y (n+1) = v (n+1) + t (n+1) • b n`.
-/

open scoped InnerProductSpace

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A B : E → Set E}

noncomputable def clipRatio (lo hi : ℝ) (u y : E) : ℝ :=
  if ‖y - u‖ = 0 then hi else max lo (min hi (‖u‖ / ‖y - u‖))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem clipRatio_bounds {lo hi : ℝ} (hle : lo ≤ hi) (u y : E) :
    lo ≤ clipRatio lo hi u y ∧ clipRatio lo hi u y ≤ hi := by
  unfold clipRatio
  split
  · exact ⟨hle, le_rfl⟩
  · exact ⟨le_max_left _ _, max_le hle (min_le_left _ _)⟩

def conservationFactor (ω κ : ℝ) : ℝ := 1 - ω + ω * κ

theorem conservationFactor_pos {ω κ : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ 1)
    (hκ : 0 < κ) : 0 < conservationFactor ω κ :=
  add_pos_of_nonneg_of_pos (sub_nonneg.mpr hω1) (mul_pos hω0 hκ)

structure AdaptiveState (B : E → Set E) where
  t : ℝ
  ht : 0 < t
  state : DRState B
  y : E
  hy : y = state.u + t • state.b

noncomputable def adaptiveInit (hB : IsMaximalMonotoneRel B) (y₀ : E) : AdaptiveState B := by
  have h1 : 0 < (1 : ℝ) := by norm_num
  let u := hB.resolvent h1 y₀
  let b := y₀ - u
  have hb : b ∈ B u := by
    simpa [b, u] using hB.resolvent_mem h1 y₀
  refine ⟨1, h1, ⟨u, b, hb⟩, y₀, ?_⟩
  change y₀ = u + (1 : ℝ) • (y₀ - u)
  module

noncomputable def adaptiveStep (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi) (ω : ℝ)
    (hω0 : 0 < ω) (hω1 : ω ≤ 1) (s : AdaptiveState B) : AdaptiveState B := by
  let κ := clipRatio lo hi s.state.u s.y
  let ν := conservationFactor ω κ
  let t := ν * s.t
  have hκ : 0 < κ := hlo.trans_le (clipRatio_bounds hle s.state.u s.y).1
  have ht : 0 < t := mul_pos (conservationFactor_pos hω0 hω1 hκ) s.ht
  let d := drStep hA hB t ht s.state
  exact ⟨t, ht, d.next, d.v + t • s.state.b, d.eqB.symm⟩

noncomputable def adaptiveStates (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    {lo hi : ℝ} (hlo : 0 < lo) (hle : lo ≤ hi)
    (ω : ℕ → ℝ) (hω : ∀ n, 0 < ω n ∧ ω n ≤ 1) (y₀ : E) : ℕ → AdaptiveState B :=
  Nat.rec (adaptiveInit hB y₀)
    (fun n s => adaptiveStep hA hB hlo hle (ω (n + 1)) (hω (n + 1)).1 (hω (n + 1)).2 s)

end DRS
