import Mathlib.Tactic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Order.Basic

open Filter Topology

namespace PDALCodexHelp

/-- 若非负实数列 `f` 为递减且有下界，且 `c k ≤ f k - f(k+1)`，`c k ≥ 0`，则 `c k → 0`。 -/
theorem tendsto_zero_of_antitone_diff {f c : ℕ → ℝ}
    (hanti : Antitone f) (hbdd : BddBelow (Set.range f))
    (hdiff : ∀ k, c k ≤ f k - f (k + 1)) (hc : ∀ k, 0 ≤ c k) :
    Tendsto c atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ := Real.tendsto_of_bddBelow_antitone hbdd hanti
  have hL2 : Tendsto (fun k => f (k + 1)) atTop (𝓝 L) :=
    hL.comp (tendsto_add_atTop_nat 1)
  have hdiff_tendsto : Tendsto (fun k => f k - f (k + 1)) atTop (𝓝 0) := by
    have h := hL.sub hL2
    simp only [sub_self] at h
    exact h
  have hd_nn : ∀ k, 0 ≤ f k - f (k + 1) := fun k =>
    sub_nonneg.mpr (hanti (by omega))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hdiff_tendsto hc (fun k => hdiff k)

/-- 若 `‖a k‖ ≤ c k` 且 `c k → 0` 且 `c k ≥ 0`，则 `a k → 0`。 -/
theorem tendsto_zero_norm_of_le {X : Type*} [NormedAddCommGroup X]
    {a : ℕ → X} {c : ℕ → ℝ}
    (h : ∀ k, ‖a k‖ ≤ c k) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Metric.tendsto_nhds] at hc
  filter_upwards [hc ε hε] with k hk
  rw [dist_zero_right]
  -- hk : dist (c k) 0 < ε, i.e., |c k| < ε
  -- Since ‖a k‖ ≤ c k and ‖a k‖ ≥ 0, we have c k ≥ 0, so c k = |c k| < ε
  have hk' : c k < ε := by
    have hck_nn : 0 ≤ c k := by linarith [h k, norm_nonneg (a k)]
    have : |c k| < ε := by
      rw [abs_of_nonneg hck_nn]
      rwa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hck_nn] at hk
    rwa [abs_of_nonneg hck_nn] at this
  exact lt_of_le_of_lt (h k) hk'

/-- 若 `‖a k - p‖ ≤ c k` 且 `c k → 0`，则 `a k → p`。 -/
theorem tendsto_of_norm_le {X : Type*} [NormedAddCommGroup X]
    {a : ℕ → X} {p : X} {c : ℕ → ℝ}
    (h : ∀ k, ‖a k - p‖ ≤ c k) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 p) := by
  have hsub : Tendsto (fun k => a k - p) atTop (𝓝 0) :=
    tendsto_zero_norm_of_le h hc
  have : Tendsto (fun k => (a k - p) + p) atTop (𝓝 (0 + p)) :=
    hsub.add tendsto_const_nhds
  have h0 : (0 + p : X) = p := by rw [zero_add]
  rw [h0] at this
  convert this using 1
  ext k
  abel

end PDALCodexHelp
