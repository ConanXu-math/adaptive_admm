import AdaRES.Geometry
import AdaRES.Fista

open Filter Topology InnerProductSpace
open scoped InnerProduct

namespace AdaRES

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure Minimum (data : Smooth E) (ψ : ProperConvex E) where
  xstar : E
  dom : xstar ∈ ψ.dom
  minimal : ∀ x ∈ ψ.dom, objective data ψ xstar ≤ objective data ψ x

def gap {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ) (x : E) : ℝ :=
  objective data ψ x - objective data ψ opt.xstar

def solutions {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ) : Set E :=
  {x | x ∈ ψ.dom ∧ objective data ψ x = objective data ψ opt.xstar}

def residual (data : Smooth E) (ψ : ProperConvex E) (x : E) : ℝ := ‖step data ψ x - x‖^2

def LocalGrowth {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ)
    (x0 : E) (μ : ℝ) : Prop :=
  ∀ x ∈ ψ.dom, objective data ψ x ≤ objective data ψ x0 →
    μ / 2 * (Metric.infDist x (solutions opt))^2 ≤ gap opt x

theorem gap_nonneg {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ)
    (x : E) (hx : x ∈ ψ.dom) : 0 ≤ gap opt x := sub_nonneg.mpr (opt.minimal x hx)

theorem objective_sublevel_closed (data : Smooth E) (ψ : ProperConvex E) (c : ℝ) :
    IsClosed {x | x ∈ ψ.dom ∧ objective data ψ x ≤ c} := by
  let S : Set E := {x | x ∈ ψ.dom ∧ objective data ψ x ≤ c}
  have hcont : Continuous data.f := continuous_iff_continuousAt.2 fun x => (data.hasGradient x).continuousAt
  apply closure_subset_iff_isClosed.mp
  change closure S ⊆ S
  intro z hz
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hz
  have hlimf : Tendsto (fun n => data.f (u n)) atTop (𝓝 (data.f z)) :=
    (hcont.tendsto z).comp hlim
  have he (ε : ℝ) (hε : 0 < ε) : z ∈ ψ.dom ∧ ψ.f z ≤ c - data.f z + ε := by
    apply (ψ.lsc (c - data.f z + ε)).mem_of_tendsto hlim
    apply (hlimf.eventually (eventually_gt_nhds (show data.f z - ε < data.f z by linarith))).mono
    intro n hn
    have hmem : u n ∈ ψ.dom ∧ objective data ψ (u n) ≤ c := hu n
    refine ⟨hmem.1, ?_⟩
    have hf := hmem.2
    unfold objective at hf
    linarith only [hf, hn]
  refine ⟨(he 1 zero_lt_one).1, ?_⟩
  by_contra! hf
  let ε := (objective data ψ z - c) / 2
  have hε : 0 < ε := div_pos (sub_pos.mpr hf) (by norm_num)
  have h := (he ε hε).2
  dsimp only [ε, objective] at h hf
  linarith only [h, hf]

theorem solutions_closed {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ) :
    IsClosed (solutions opt) := by
  have he : solutions opt = {x | x ∈ ψ.dom ∧ objective data ψ x ≤ objective data ψ opt.xstar} := by
    ext x
    constructor
    · intro h
      exact ⟨h.1, h.2.le⟩
    · intro h
      exact ⟨h.1, le_antisymm h.2 (opt.minimal x h.1)⟩
  rw [he]
  exact objective_sublevel_closed data ψ _

theorem nearest_solution {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ) (x : E) :
    ∃ u ∈ solutions opt, Metric.infDist x (solutions opt) = ‖x - u‖ := by
  have hne : (solutions opt).Nonempty := ⟨opt.xstar, opt.dom, rfl⟩
  simpa only [dist_eq_norm] using (solutions_closed opt).exists_infDist_eq_dist hne x

theorem residual_le_gap {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ)
    (x : E) (hx : x ∈ ψ.dom) : residual data ψ x ≤ 2 * gap opt x := by
  have hd := step_descent data ψ x hx
  have hm := opt.minimal (step data ψ x) (step_dom data ψ x)
  unfold residual gap
  linarith only [hd, hm]

theorem gap_step_le_residual {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ)
    (x0 : E) {μ : ℝ} (hμ : 0 < μ) (hq : LocalGrowth opt x0 μ)
    (x : E) (hx : x ∈ ψ.dom) (hlevel : objective data ψ x ≤ objective data ψ x0) :
    gap opt (step data ψ x) ≤ 8 * residual data ψ x / μ := by
  let z := step data ψ x
  let r := ‖z - x‖
  let A := gap opt z
  have hz := step_dom data ψ x
  have hA := gap_nonneg opt z hz
  have hdesc := step_descent data ψ x hx
  have hzl : objective data ψ z ≤ objective data ψ x0 := by
    have hh : 0 ≤ ‖z - x‖^2 / 2 := by positivity
    linarith only [hlevel, hdesc, hh]
  obtain ⟨u, hu, hdist⟩ := nearest_solution opt z
  let d := ‖z - u‖
  have hqd := hq z hz hzl
  rw [hdist] at hqd
  have hqd' : μ * d^2 ≤ 2 * A := by
    change μ / 2 * d^2 ≤ A at hqd
    nlinarith only [hqd]
  have hprox := prox_optimality ψ 1 zero_lt_one (x - data.gradient x) u hu.1
  simp only [one_mul] at hprox
  change ψ.f z - ψ.f u ≤ ⟪z - (x - data.gradient x), u - z⟫_ℝ at hprox
  rw [show z - (x - data.gradient x) = z - x + data.gradient x from by abel] at hprox
  have hf := lower_tangent data z u
  let v := (z - x) + (data.gradient x - data.gradient z)
  have hminor : A ≤ ⟪v, u - z⟫_ℝ := by
    change objective data ψ z - objective data ψ opt.xstar ≤ _
    rw [← hu.2]
    simp only [objective, v, inner_add_left, inner_sub_left] at *
    linarith only [hprox, hf]
  have hl := (lipschitzWith_iff_norm_sub_le.mp (gradient_lipschitz data)) x z
  have hg : ‖data.gradient x - data.gradient z‖ ≤ r := by
    rw [norm_sub_rev x z] at hl
    simpa only [NNReal.coe_one, one_mul] using hl
  have hv : ‖v‖ ≤ 2 * r := by
    calc
      _ ≤ ‖z - x‖ + ‖data.gradient x - data.gradient z‖ := norm_add_le _ _
      _ ≤ _ := by change r + ‖data.gradient x - data.gradient z‖ ≤ 2 * r; linarith only [hg]
  have hAd : A ≤ 2 * r * d := by
    calc
      _ ≤ ‖v‖ * ‖u - z‖ := hminor.trans (real_inner_le_norm _ _)
      _ ≤ _ := by rw [norm_sub_rev u z]; exact mul_le_mul_of_nonneg_right hv (norm_nonneg _)
  have hAsq := (sq_le_sq₀ hA (show 0 ≤ 2 * r * d by dsimp [r, d]; positivity)).2 hAd
  have h1 := mul_le_mul_of_nonneg_left hAsq hμ.le
  have h2 := mul_le_mul_of_nonneg_left hqd' (show 0 ≤ 4 * r^2 by positivity)
  have h3 : (μ * A) * A ≤ (8 * r^2) * A := by nlinarith only [h1, h2]
  change A ≤ 8 * r^2 / μ
  by_cases hzero : A = 0
  · rw [hzero]
    positivity
  · have hp : 0 < A := lt_of_le_of_ne hA (Ne.symm hzero)
    rw [le_div_iff₀ hμ, mul_comm A μ]
    exact (mul_le_mul_right hp).mp h3

theorem fista_descent (data : Smooth E) (ψ : ProperConvex E) (x : E)
    (hx : x ∈ ψ.dom) (K : ℕ) : objective data ψ (fista data ψ x K) ≤ objective data ψ x := by
  cases K with
  | zero => rfl
  | succ n =>
    have h := fista_bound data ψ x x hx hx n
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_div, sub_nonpos] using h

theorem fista_gap_bound {data : Smooth E} {ψ : ProperConvex E} (opt : Minimum data ψ)
    (x0 : E) {μ : ℝ} (hμ : 0 < μ) (hq : LocalGrowth opt x0 μ)
    (x : E) (hx : x ∈ ψ.dom) (hl : objective data ψ x ≤ objective data ψ x0) (n : ℕ) :
    gap opt (fista data ψ x (n + 1)) ≤ ((theta n)^2 / μ) * gap opt x := by
  obtain ⟨u, hu, hdist⟩ := nearest_solution opt x
  have h := fista_bound data ψ x u hx hu.1 n
  rw [hu.2] at h
  have hg := hq x hx hl
  rw [hdist] at hg
  calc
    _ ≤ (theta n)^2 * ‖x - u‖^2 / 2 := h
    _ = ((theta n)^2 / μ) * (μ / 2 * ‖x - u‖^2) := by field_simp [hμ.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hg (div_nonneg (sq_nonneg _) hμ.le)

end
end AdaRES
