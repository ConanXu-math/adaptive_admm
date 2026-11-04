import Optlib.Function.Proximal
import Optlib.Convex.ConvexFunction
import Optlib.Convex.StronglyConvex
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Sequences
import PDAL.CodexEnergyHelp
import PDAL.CodexBoundHelp
import PDAL.CodexClusterHelp
import PDAL.AffineSeparationHelp
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence

open Filter Topology

/-- 如果 `β > 0`、`τmin > 0`、每个 `τ n ≥ τmin` 且 `‖dy n‖ → 0`，
则 `(1 / (β * τ n)) • dy n → 0`。 -/
theorem scaled_smul_tendsto_zero {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (β τmin : ℝ) (hβ : 0 < β) (hτmin : 0 < τmin)
    (τ : ℕ → ℝ) (hτpos : ∀ n, 0 < τ n) (hτle : ∀ n, τmin ≤ τ n)
    (dy : ℕ → X) (hdy : Tendsto (fun n => ‖dy n‖) atTop (𝓝 0)) :
    Tendsto (fun n => (1 / (β * τ n)) • dy n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : ∀ n : ℕ, ‖(1 / (β * τ n)) • dy n‖
      = (1 / (β * τ n)) * ‖dy n‖ := by
    intro n
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos one_pos (mul_pos hβ (hτpos n)))]
  -- 统一上界：‖(1/(β*τ n))•dy n‖ ≤ (1/(β*τmin)) * ‖dy n‖
  have hupper : ∀ n : ℕ, ‖(1 / (β * τ n)) • dy n‖
      ≤ (1 / (β * τmin)) * ‖dy n‖ := by
    intro n
    rw [hsq n]
    have hratio : (1 : ℝ) / (β * τ n) ≤ (1 : ℝ) / (β * τmin) := by
      -- div_le_div₀ (hc : 0 ≤ c) (hac : a ≤ c) (hd : 0 < d) (hdb : d ≤ b) : a / b ≤ c / d
      refine div_le_div₀ zero_le_one (le_refl 1) (mul_pos hβ hτmin) ?_
      exact mul_le_mul_of_nonneg_left (hτle n) hβ.le
    exact mul_le_mul_of_nonneg_right hratio (norm_nonneg (dy n))
  -- 上界函数趋零：右端 (1/(β*τmin)) * ‖dy n‖ → 0
  have hlim : Tendsto (fun n => (1 / (β * τmin)) * ‖dy n‖) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n => (1 / (β * τmin)) * ‖dy n‖) atTop
        (𝓝 ((1 / (β * τmin)) * 0)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hdy.const_mul (1 / (β * τmin)))
        (fun n => by
          simp only [mul_zero]
          exact mul_nonneg (le_of_lt (div_pos one_pos (mul_pos hβ hτmin)))
            (norm_nonneg (dy n)))
        (fun n => le_of_eq (rfl : (1 / (β * τmin)) * ‖dy n‖
          = (1 / (β * τmin)) * ‖dy n‖))
    have h0 : (1 / (β * τmin)) * 0 = 0 := mul_zero _
    rwa [h0] at hbase
  -- 目标范数逐点 ≤ 上界函数，上界函数趋零，且目标范数非负，用夹逼得到目标趋零
  have hle : (fun n : ℕ => ‖(1 / (β * τ n)) • dy n‖)
      ≤ (fun n : ℕ => (1 / (β * τmin)) * ‖dy n‖) := hupper
  have hzero : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 ((0:ℝ))) := tendsto_const_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hzero hlim
    (fun _ => by exact norm_nonneg _) hle

/-!
# Primal-Dual Algorithm with Linesearch (PDAL)

Formalization of Algorithm 1, Lemma 1, Theorem 1–2 from
Malitsky & Pock, arXiv:1608.08883v2, Sections 1–2.
-/

noncomputable section PDAL_section

open Set InnerProductSpace Topology Filter Bornology

open scoped InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [ProperSpace E]

/-! ## Proper l.s.c. convex functions via a domain.

The model uses a real-valued function `f` on a convex domain set `dom`.
Lower semicontinuity is encoded as: for every `c ∈ ℝ`, the sublevel set
`{z ∈ dom | f z ≤ c}` is closed in `E`. This is equivalent to the
extended-real function `f̃(z) = f(z)` on `dom`, `+∞` outside, being l.s.c.,
and does **not** require `dom` to be closed. The affine minorant is a
standard consequence of proper l.s.c. convexity in finite dimensions
(Hahn–Banach separation of the closed convex epigraph); it is **derived**
from these assumptions by `ProperConvex.affine_minorant_exists` (via
`PDAL.AffineSeparationHelp.affine_minorant_of_lsc_convex`), not an input
field, and is used in the proximal-existence proof.
-/

structure ProperConvex (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] where
  dom : Set E
  f : E → ℝ
  dom_nonempty : dom.Nonempty
  dom_convex : Convex ℝ dom
  convex_on : ConvexOn ℝ dom f
  -- Lower semicontinuity in the extended sense: sublevel sets are closed in E.
  lsc : ∀ (c : ℝ), IsClosed {z : E | z ∈ dom ∧ f z ≤ c}

/-- 仿射下界由原始 proper l.s.c. 凸条件推导（finite-dim 严格分离，见
`PDAL.AffineSeparationHelp` 的 `affine_minorant_of_lsc_convex`）。 -/
theorem ProperConvex.affine_minorant_exists (G : ProperConvex E) [FiniteDimensional ℝ E] :
    ∃ (a : E) (b : ℝ), ∀ z ∈ G.dom, G.f z ≥ ⟪a, z⟫_ℝ + b :=
  affine_minorant_of_lsc_convex G.dom G.f G.dom_nonempty G.dom_convex G.convex_on G.lsc

variable {G : ProperConvex E}

/-- Key lemma: if `f` is l.s.c. (in the extended sense) and `g` is continuous,
then the sublevel set `{z ∈ dom | τ·f(z) + g(z) ≤ C}` is closed in `E`.

This replaces the previous `dom_closed + continuous_on` argument and works
for non-closed domains. -/
private lemma sublevel_closed_of_lsc_add_continuous
    (G : ProperConvex E) {τ : ℝ} (hτ : 0 < τ) (g : E → ℝ) (hg : Continuous g) (C : ℝ) :
    IsClosed {z : E | z ∈ G.dom ∧ τ * G.f z + g z ≤ C} := by
  set S := {z : E | z ∈ G.dom ∧ τ * G.f z + g z ≤ C}
  have hclosure : closure S ⊆ S := by
    intro z hz
    rcases mem_closure_iff_seq_limit.mp hz with ⟨u, huS, hu_lim⟩
    have hg_lim : Tendsto (fun n => g (u n)) atTop (𝓝 (g z)) := (hg.tendsto z).comp hu_lim
    have hu_dom : ∀ n, u n ∈ G.dom := fun n => (huS n).1
    have hu_ineq : ∀ n, τ * G.f (u n) + g (u n) ≤ C := fun n => (huS n).2
    -- For any ε > 0, eventually g(u n) > g(z) - ε, so f(u n) ≤ (C - g(z) + ε) / τ.
    -- The sublevel set {w ∈ dom | f(w) ≤ (C - g(z) + ε) / τ} is closed (lsc).
    have hkey : ∀ (ε : ℝ), 0 < ε → G.f z ≤ (C - g z + ε) / τ ∧ z ∈ G.dom := by
      intro ε hε
      set cε := (C - g z + ε) / τ
      have hTε_closed : IsClosed {w : E | w ∈ G.dom ∧ G.f w ≤ cε} := G.lsc cε
      have hTε_eventually : ∀ᶠ n in atTop, u n ∈ {w : E | w ∈ G.dom ∧ G.f w ≤ cε} := by
        apply (hg_lim.eventually (eventually_gt_nhds (by linarith : g z - ε < g z))).mono
        intro n hn_g
        refine ⟨hu_dom n, ?_⟩
        have hineq := hu_ineq n
        have h1 : τ * G.f (u n) ≤ C - g (u n) := by linarith
        have h2 : C - g (u n) < C - (g z - ε) := by linarith
        have h3 : C - (g z - ε) = C - g z + ε := by ring
        rw [h3] at h2
        have h4 : τ * G.f (u n) < C - g z + ε := lt_of_le_of_lt h1 h2
        rw [le_div_iff₀ hτ]
        linarith
      have hz_in_Tε : z ∈ {w : E | w ∈ G.dom ∧ G.f w ≤ cε} :=
        hTε_closed.mem_of_tendsto hu_lim hTε_eventually
      exact ⟨hz_in_Tε.2, hz_in_Tε.1⟩
    have hz_dom : z ∈ G.dom := (hkey 1 (by norm_num)).2
    have hf_z_le : ∀ (ε : ℝ), 0 < ε → G.f z ≤ (C - g z + ε) / τ := fun ε hε =>
      (hkey ε hε).1
    have hfinal : τ * G.f z + g z ≤ C := by
      by_contra h_neg
      push_neg at h_neg
      have hε_pos : 0 < (τ * G.f z + g z - C) / 2 := div_pos (by linarith) (by norm_num)
      have hkey_ε := hf_z_le _ hε_pos
      have h1 : (C - g z + (τ * G.f z + g z - C) / 2) / τ
          < (C - g z + (τ * G.f z + g z - C)) / τ := by
        apply div_lt_div_of_pos_right _ hτ
        linarith
      have h2 : (C - g z + (τ * G.f z + g z - C)) / τ = G.f z := by
        field_simp; ring
      linarith [hkey_ε, h1, h2]
    exact ⟨hz_dom, hfinal⟩
  exact closure_subset_iff_isClosed.mp hclosure

/-- A lower semicontinuous function on a compact set attains its minimum.

Uses sequential compactness: choose z_n with φ(z_n) near the infimum,
extract a convergent subsequence, and use lsc to show the limit is a minimizer.
-/
private lemma exists_minOn_of_lsc_compact
    (S : Set E) (hS_compact : IsCompact S) (hS_ne : S.Nonempty)
    (φ : E → ℝ)
    (hφ_lsc : ∀ (c : ℝ), IsClosed {z : E | z ∈ S ∧ φ z ≤ c})
    (hφ_bdd : BddBelow (φ '' S)) :
    ∃ z ∈ S, IsMinOn φ S z := by
  set m := sInf (φ '' S)
  have himg_ne : (φ '' S).Nonempty := hS_ne.image φ
  have hm_lb : ∀ y ∈ φ '' S, m ≤ y := fun y hy => csInf_le hφ_bdd hy
  -- For each n, S_n = {z ∈ S | φ(z) ≤ m + 1/(n+1)} is nonempty (by infimum)
  have hSn_nonempty : ∀ (n : ℕ), {z : E | z ∈ S ∧ φ z ≤ m + 1 / (n + 1 : ℝ)}.Nonempty := by
    intro n
    have h_eps : 0 < 1 / (n + 1 : ℝ) :=
      div_pos (by norm_num) (by exact_mod_cast Nat.succ_pos n)
    have h_exists : ∃ y ∈ φ '' S, y < m + 1 / (n + 1 : ℝ) := by
      by_contra h_neg
      push_neg at h_neg
      have h_bound : m + 1 / (n + 1 : ℝ) ≤ m := le_csInf himg_ne h_neg
      linarith
    rcases h_exists with ⟨y, ⟨z, hzS, rfl⟩, hy_lt⟩
    exact ⟨z, hzS, le_of_lt hy_lt⟩
  -- Choose z_n ∈ S with φ(z_n) ≤ m + 1/(n+1)
  choose z_n hz_n using hSn_nonempty
  have hz_n_S : ∀ n, z_n n ∈ S := fun n => (hz_n n).1
  have hz_n_φ : ∀ n, φ (z_n n) ≤ m + 1 / (n + 1 : ℝ) := fun n => (hz_n n).2
  -- S is compact → sequentially compact (in uniform/metric spaces)
  have hS_seq : IsSeqCompact S := hS_compact.isSeqCompact
  -- Extract a convergent subsequence z_{n_k} → z*
  rcases hS_seq.subseq_of_frequently_in (Frequently.of_forall hz_n_S) with
    ⟨zstar, hzstar_S, φ_sub, hφ_mono, hzstar_lim⟩
  -- For any ε > 0, for large k, 1/(φ_sub k + 1) < ε, so φ(z_{φ_sub k}) ≤ m + ε
  -- Since {z ∈ S | φ(z) ≤ m + ε} is closed and z_{φ_sub k} → z*, we get z* ∈ this set
  have hzstar_φ_le : ∀ (ε : ℝ), 0 < ε → φ zstar ≤ m + ε := by
    intro ε hε
    have hT_closed : IsClosed {z : E | z ∈ S ∧ φ z ≤ m + ε} := hφ_lsc (m + ε)
    have hφ_sub_le : ∀ k, k ≤ φ_sub k := StrictMono.id_le hφ_mono
    rcases exists_nat_one_div_lt hε with ⟨n₀, hn₀⟩
    have hT_eventually : ∀ᶠ k in atTop, z_n (φ_sub k) ∈ {z : E | z ∈ S ∧ φ z ≤ m + ε} := by
      filter_upwards [Filter.eventually_ge_atTop n₀] with k hk
      have hk_le_φk : k ≤ φ_sub k := hφ_sub_le k
      have hφk : (n₀ : ℕ) + 1 ≤ (φ_sub k : ℕ) + 1 := by omega
      have h1_div : 1 / ((φ_sub k : ℕ) + 1 : ℝ) ≤ 1 / ((n₀ : ℕ) + 1 : ℝ) := by
        rw [div_le_div_iff₀ (by exact_mod_cast Nat.succ_pos (φ_sub k : ℕ))
            (by exact_mod_cast Nat.succ_pos (n₀ : ℕ))]
        simp only [one_mul]
        exact_mod_cast hφk
      have hφ_le : φ (z_n (φ_sub k)) ≤ m + 1 / ((φ_sub k : ℕ) + 1 : ℝ) := hz_n_φ (φ_sub k)
      refine ⟨hz_n_S (φ_sub k), ?_⟩
      linarith
    have hzstar_in_T : zstar ∈ {z : E | z ∈ S ∧ φ z ≤ m + ε} :=
      hT_closed.mem_of_tendsto hzstar_lim hT_eventually
    exact hzstar_in_T.2
  -- Taking ε → 0: φ(z*) ≤ m
  have hzstar_le_m : φ zstar ≤ m := by
    -- φ(z*) ≤ m + ε for all ε > 0, so φ(z*) ≤ m
    by_contra h_neg
    push_neg at h_neg
    have h_eps_pos : 0 < (φ zstar - m) / 2 := by linarith
    have := hzstar_φ_le _ h_eps_pos
    linarith
  -- m ≤ φ(z*) (since m = sInf and z* ∈ S)
  have hm_le : m ≤ φ zstar :=
    hm_lb _ ⟨zstar, hzstar_S, rfl⟩
  -- φ(z*) = m, so z* is a minimizer
  have hzstar_min : IsMinOn φ S zstar := by
    rw [isMinOn_iff]
    intro y hy
    exact le_trans hzstar_le_m (hm_lb _ ⟨y, hy, rfl⟩)
  exact ⟨zstar, hzstar_S, hzstar_min⟩

def prox_obj (G : ProperConvex E) (τ : ℝ) (x : E) (z : E) : ℝ :=
  τ * G.f z + ‖z - x‖ ^ 2 / 2

def prox_scale (G : ProperConvex E) (τ : ℝ) (x : E) (z : E) : Prop :=
  z ∈ G.dom ∧ IsMinOn (prox_obj G τ x) G.dom z

/-- The proximal sublevel set is closed (using lsc, not dom_closed + continuous_on). -/
private lemma prox_sublevel_closed (G : ProperConvex E) {τ : ℝ} (hτ : 0 < τ) (x : E) (C : ℝ) :
    IsClosed {z : E | z ∈ G.dom ∧ τ * G.f z + ‖z - x‖ ^ 2 / 2 ≤ C} := by
  have hquad_cont : Continuous (fun z : E => ‖z - x‖ ^ 2 / 2) := by
    have h1 : Continuous (fun z : E => ‖z - x‖) := (continuous_id.sub continuous_const).norm
    exact (h1.pow 2).div_const 2
  exact sublevel_closed_of_lsc_add_continuous G hτ (fun z => ‖z - x‖ ^ 2 / 2) hquad_cont C

/-- The scaled proximal point exists (for `τ > 0`). -/
theorem prox_scale_exists (G : ProperConvex E) {τ : ℝ} (hτ : 0 < τ) (x : E) :
    ∃ z, prox_scale G τ x z := by
  rcases G.affine_minorant_exists with ⟨a, b, ham⟩
  rcases G.dom_nonempty with ⟨z0, hz0⟩
  set φ := prox_obj G τ x
  set S := {z ∈ G.dom | φ z ≤ φ z0}
  have hS_eq : S = {z : E | z ∈ G.dom ∧ τ * G.f z + ‖z - x‖ ^ 2 / 2 ≤ φ z0} := by
    ext z; simp [S, φ, prox_obj]
  have hS_ne : S.Nonempty := ⟨z0, hz0, le_rfl⟩
  have hS_closed : IsClosed S := by
    rw [hS_eq]
    exact prox_sublevel_closed G hτ x (φ z0)
  have hS_bounded : IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall x]
    set C := φ z0 - τ * b
    have hD : ∀ z ∈ S, ‖z - x‖ ^ 2 / 2 ≤ (C + τ * ‖a‖ * ‖x‖) + τ * ‖a‖ * ‖z - x‖ := by
      rintro z ⟨hzd, hzφ⟩
      have hamz := ham z hzd
      have hφz : φ z = τ * G.f z + ‖z - x‖ ^ 2 / 2 := rfl
      have h1 : ‖z - x‖ ^ 2 / 2 ≤ φ z0 - τ * G.f z := by
        rw [hφz] at hzφ; linarith
      have hcs : ⟪a, z⟫_ℝ ≥ -‖a‖ * ‖z‖ := by
        have hh := abs_real_inner_le_norm a z
        rcases abs_le.mp hh with ⟨h1, h2⟩
        linarith
      have hnorm_z : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
        have hle := norm_add_le (z - x) x
        rw [show (z - x) + x = z from by abel] at hle
        exact hle
      calc ‖z - x‖ ^ 2 / 2
          ≤ φ z0 - τ * G.f z := h1
        _ ≤ φ z0 - τ * (⟪a, z⟫_ℝ + b) := by
          rw [sub_le_sub_iff_left]; exact mul_le_mul_of_nonneg_left hamz (le_of_lt hτ)
        _ = C - τ * ⟪a, z⟫_ℝ := by simp [C, φ]; ring
        _ ≤ C + τ * ‖a‖ * ‖z‖ := by
          have h1 : -⟪a, z⟫_ℝ ≤ ‖a‖ * ‖z‖ := by linarith
          have h2 : τ * (-⟪a, z⟫_ℝ) ≤ τ * (‖a‖ * ‖z‖) :=
            mul_le_mul_of_nonneg_left h1 (le_of_lt hτ)
          linarith
        _ ≤ C + τ * ‖a‖ * (‖z - x‖ + ‖x‖) := by
          have hmul : τ * ‖a‖ * ‖z‖ ≤ τ * ‖a‖ * (‖z - x‖ + ‖x‖) :=
            mul_le_mul_of_nonneg_left hnorm_z (mul_nonneg (le_of_lt hτ) (norm_nonneg _))
          linarith
        _ = C + τ * ‖a‖ * ‖x‖ + τ * ‖a‖ * ‖z - x‖ := by ring
    set D := C + τ * ‖a‖ * ‖x‖
    set R := τ * ‖a‖ + Real.sqrt (2 * max D 0 + τ ^ 2 * ‖a‖ ^ 2)
    use R
    rintro z hzs
    have hp := hD z hzs
    set p := ‖z - x‖
    have p_nn : 0 ≤ p := norm_nonneg _
    have hp2 : p ^ 2 ≤ 2 * D + 2 * τ * ‖a‖ * p := by linarith
    have hsq : (p - τ * ‖a‖) ^ 2 ≤ 2 * max D 0 + τ ^ 2 * ‖a‖ ^ 2 := by
      have hexpand : (p - τ * ‖a‖) ^ 2 = p ^ 2 - 2 * τ * ‖a‖ * p + τ ^ 2 * ‖a‖ ^ 2 := by ring
      rw [hexpand]
      have : p ^ 2 - 2 * τ * ‖a‖ * p ≤ 2 * D := by linarith
      have : p ^ 2 - 2 * τ * ‖a‖ * p + τ ^ 2 * ‖a‖ ^ 2 ≤ 2 * D + τ ^ 2 * ‖a‖ ^ 2 := by linarith
      have : 2 * D + τ ^ 2 * ‖a‖ ^ 2 ≤ 2 * max D 0 + τ ^ 2 * ‖a‖ ^ 2 := by
        have : D ≤ max D 0 := le_max_left D 0
        linarith
      linarith
    have hsqrt : p - τ * ‖a‖ ≤ Real.sqrt (2 * max D 0 + τ ^ 2 * ‖a‖ ^ 2) :=
      Real.le_sqrt_of_sq_le hsq
    have hpR : p ≤ R := by simp [R]; linarith
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hpR
  have hS_compact : IsCompact S :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hS_closed, hS_bounded⟩
  -- φ is lsc on S (sublevel sets closed). We prove the minimum is attained
  -- using the lsc + compact argument (Cantor's intersection theorem).
  have hφ_lsc_on_S : ∀ (c : ℝ), IsClosed {z : E | z ∈ S ∧ φ z ≤ c} := by
    intro c
    have hS_closed' : IsClosed S := hS_closed
    have hφ_sublevel : IsClosed {z : E | z ∈ G.dom ∧ τ * G.f z + ‖z - x‖ ^ 2 / 2 ≤ c} :=
      prox_sublevel_closed G hτ x c
    have heq : {z : E | z ∈ S ∧ φ z ≤ c} =
      S ∩ {z : E | z ∈ G.dom ∧ τ * G.f z + ‖z - x‖ ^ 2 / 2 ≤ c} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro ⟨hzS, hφc⟩
        exact ⟨hzS, hzS.1, hφc⟩
      · rintro ⟨hzS, _, hφc⟩
        exact ⟨hzS, hφc⟩
    rw [heq]
    exact IsClosed.inter hS_closed' hφ_sublevel
  -- φ is bounded below on S (by the affine minorant + boundedness of S)
  have hφ_bdd : BddBelow (φ '' S) := by
    rcases G.affine_minorant_exists with ⟨a, b, ham⟩
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hS_bounded
    use τ * b - τ * ‖a‖ * (‖x‖ + R)
    rw [mem_lowerBounds]
    rintro y ⟨z, hzS, rfl⟩
    have hz_dom : z ∈ G.dom := hzS.1
    have hamz := ham z hz_dom
    have hφz : φ z = τ * G.f z + ‖z - x‖ ^ 2 / 2 := rfl
    have hnorm_nn : 0 ≤ ‖z - x‖ := norm_nonneg _
    have hsq_nn : 0 ≤ ‖z - x‖ ^ 2 / 2 := by
      have : 0 ≤ ‖z - x‖ ^ 2 := sq_nonneg _
      linarith
    have hcs : ⟪a, z⟫_ℝ ≥ -‖a‖ * ‖z‖ := by
      have hh := abs_real_inner_le_norm a z
      rcases abs_le.mp hh with ⟨h1, h2⟩
      linarith
    have hnorm_z : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
      have hle := norm_add_le (z - x) x
      rw [show (z - x) + x = z from by abel] at hle
      exact hle
    have hzR : ‖z‖ ≤ R := by
      have := hR hzS
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hanonn : 0 ≤ ‖a‖ := norm_nonneg _
    have hxnonn : 0 ≤ ‖x‖ := norm_nonneg _
    have hτnn : 0 ≤ τ := le_of_lt hτ
    have hgf_lower : G.f z ≥ b - ‖a‖ * R := by nlinarith
    have hφ_lower : φ z ≥ τ * (b - ‖a‖ * R) := by nlinarith
    have htarget : τ * b - τ * ‖a‖ * (‖x‖ + R) ≤ τ * (b - ‖a‖ * R) := by
      have : τ * ‖a‖ * ‖x‖ ≥ 0 := mul_nonneg (mul_nonneg hτnn hanonn) hxnonn
      linarith
    nlinarith
  -- Minimum exists by lsc + compact
  rcases exists_minOn_of_lsc_compact S hS_compact hS_ne φ hφ_lsc_on_S hφ_bdd with
    ⟨zmin, hzmin, hmin⟩
  have hmin' := isMinOn_iff.mp hmin
  have hzmin_dom : zmin ∈ G.dom := hzmin.1
  have hzmin_min : ∀ y ∈ G.dom, φ zmin ≤ φ y := by
    intro y hy
    by_cases hys : y ∈ S
    · exact hmin' y hys
    · have hyS : ¬ (y ∈ G.dom ∧ φ y ≤ φ z0) := by simpa [S] using hys
      have hφ_y : φ z0 < φ y := by
        have hne : ¬ (φ y ≤ φ z0) := fun h => hyS ⟨hy, h⟩
        linarith
      have hφ_zmin : φ zmin ≤ φ z0 := hzmin.2
      linarith
  refine ⟨zmin, hzmin_dom, ?_⟩
  intro y hy
  exact hzmin_min y hy

/-- The proximal minimizer is unique (strong convexity of the objective). -/
theorem prox_scale_unique (G : ProperConvex E) {τ : ℝ} (hτ : 0 < τ) (x : E)
    {z₁ z₂ : E} (h₁ : prox_scale G τ x z₁) (h₂ : prox_scale G τ x z₂) :
    z₁ = z₂ := by
  have hz₁ : z₁ ∈ G.dom := h₁.1
  have hz₂ : z₂ ∈ G.dom := h₂.1
  have hmin₁ := isMinOn_iff.mp h₁.2
  have hmin₂ := isMinOn_iff.mp h₂.2
  have heq : prox_obj G τ x z₁ = prox_obj G τ x z₂ := by
    have e1 := hmin₁ z₂ hz₂
    have e2 := hmin₂ z₁ hz₁
    linarith
  set zm := (1/2 : ℝ) • (z₁ + z₂)
  have hzm_dom : zm ∈ G.dom := by
    have hconv := G.dom_convex
    rw [convex_iff_add_mem] at hconv
    have h1 : (0 : ℝ) ≤ 1/2 := by norm_num
    have h2 : (0 : ℝ) ≤ 1/2 := by norm_num
    have h3 : (1/2 : ℝ) + 1/2 = 1 := by norm_num
    have hzmin_mem := hconv hz₁ hz₂ h1 h2 h3
    have heq_zm : (1/2 : ℝ) • z₁ + (1/2 : ℝ) • z₂ = zm := by simp [zm]
    rw [heq_zm] at hzmin_mem; exact hzmin_mem
  have hfm : G.f zm ≤ (G.f z₁ + G.f z₂) / 2 := by
    have hconv := G.convex_on.2
    have := @hconv z₁ hz₁ z₂ hz₂ (1/2 : ℝ) (1/2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have heq_smul : (1/2 : ℝ) • z₁ + (1/2 : ℝ) • z₂ = zm := by simp [zm]
    rw [heq_smul] at this
    simp only [smul_eq_mul] at this
    linarith
  have hzm_x : zm - x = (1/2 : ℝ) • (z₁ - x) + (1/2 : ℝ) • (z₂ - x) := by
    simp [zm]; module
  have hap : ‖zm - x‖ ^ 2 = (‖z₁ - x‖ ^ 2 + ‖z₂ - x‖ ^ 2) / 2 - ‖z₁ - z₂‖ ^ 2 / 4 := by
    rw [hzm_x]
    have hns1 : ‖(1/2 : ℝ) • (z₁ - x)‖ = ‖z₁ - x‖ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; ring
    have hns2 : ‖(1/2 : ℝ) • (z₂ - x)‖ = ‖z₂ - x‖ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; ring
    have his : ⟪(1/2:ℝ)•(z₁-x), (1/2:ℝ)•(z₂-x)⟫_ℝ = ⟪z₁-x, z₂-x⟫_ℝ / 4 := by
      rw [inner_smul_left, inner_smul_right, RCLike.conj_to_real]; ring
    have hexp : ‖(1/2:ℝ)•(z₁-x) + (1/2:ℝ)•(z₂-x)‖^2 =
        ‖(1/2:ℝ)•(z₁-x)‖^2 + 2*⟪(1/2:ℝ)•(z₁-x), (1/2:ℝ)•(z₂-x)⟫_ℝ
        + ‖(1/2:ℝ)•(z₂-x)‖^2 := by rw [norm_add_sq_real]
    rw [hexp, hns1, hns2, his]
    have hpar : ‖z₁-x‖^2 + ‖z₂-x‖^2 = 2*⟪z₁-x, z₂-x⟫_ℝ + ‖z₁-z₂‖^2 := by
      have hdiff : (z₁ - x) - (z₂ - x) = z₁ - z₂ := by module
      have hns : ‖(z₁-x) - (z₂-x)‖^2 = ‖z₁-x‖^2 - 2*⟪z₁-x, z₂-x⟫_ℝ + ‖z₂-x‖^2 := by
        rw [norm_sub_sq_real]
      rw [hdiff] at hns
      linarith
    field_simp
    nlinarith [hpar, sq_nonneg ‖z₁ - z₂‖, norm_nonneg (z₁ - x), norm_nonneg (z₂ - x)]
  have hφzm_le : prox_obj G τ x zm ≤ prox_obj G τ x z₁ - ‖z₁ - z₂‖ ^ 2 / 8 := by
    have hφz1 : prox_obj G τ x z₁ = τ * G.f z₁ + ‖z₁ - x‖ ^ 2 / 2 := rfl
    have hφz2 : prox_obj G τ x z₂ = τ * G.f z₂ + ‖z₂ - x‖ ^ 2 / 2 := rfl
    have hφzm : prox_obj G τ x zm = τ * G.f zm + ‖zm - x‖ ^ 2 / 2 := rfl
    have hτf : τ * G.f zm ≤ τ * ((G.f z₁ + G.f z₂) / 2) :=
      mul_le_mul_of_nonneg_left hfm (le_of_lt hτ)
    rw [hφz1, hφz2] at heq
    rw [hφzm, hap]
    nlinarith
  have hφzm_ge : prox_obj G τ x z₁ ≤ prox_obj G τ x zm := hmin₁ zm hzm_dom
  have hgap : ‖z₁ - z₂‖ ^ 2 / 8 ≤ 0 := by linarith
  have hsq_nn : 0 ≤ ‖z₁ - z₂‖ ^ 2 := sq_nonneg _
  have hsq_zero : ‖z₁ - z₂‖ ^ 2 = 0 := by nlinarith
  have hsub_zero : z₁ - z₂ = 0 :=
    norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq_zero)
  exact sub_eq_zero.mp hsub_zero

/-! ### Optimality condition (eq. (4) scaled by `τ`) -/

theorem prox_scale_optimality (G : ProperConvex E) {τ : ℝ} (hτ : 0 < τ) (x : E)
    {zbar : E} (hzbar : prox_scale G τ x zbar) (y : E) (hy : y ∈ G.dom) :
    ⟪zbar - x, y - zbar⟫_ℝ ≥ τ * (G.f zbar - G.f y) := by
  have hmin := isMinOn_iff.mp hzbar.2
  have hkey : ∀ t, 0 < t → t ≤ 1 →
      τ * (G.f zbar - G.f y) ≤ ⟪zbar - x, y - zbar⟫_ℝ + t * ‖y - zbar‖ ^ 2 / 2 := by
    intro t ht_pos ht_le
    set zt := (1 - t) • zbar + t • y
    have hzt_dom : zt ∈ G.dom := by
      have hconv := G.dom_convex
      rw [convex_iff_add_mem] at hconv
      have := @hconv zbar hzbar.1 y hy (1 - t) t (sub_nonneg.mpr ht_le) ht_pos.le (by linarith)
      simpa [zt] using this
    have hzt_min : prox_obj G τ x zbar ≤ prox_obj G τ x zt := hmin zt hzt_dom
    have hgzt : G.f zt ≤ (1 - t) * G.f zbar + t * G.f y := by
      have hconv := G.convex_on.2
      have := @hconv zbar hzbar.1 y hy (1 - t) t (sub_nonneg.mpr ht_le) ht_pos.le (by linarith)
      simpa [zt] using this
    have hzt_x : zt - x = (zbar - x) + t • (y - zbar) := by simp [zt]; module
    have hnorm_exp : ‖zt - x‖ ^ 2 = ‖zbar - x‖ ^ 2 + 2 * t * ⟪zbar - x, y - zbar⟫_ℝ
        + t ^ 2 * ‖y - zbar‖ ^ 2 := by
      rw [hzt_x, norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_pos.le,
        inner_smul_right]
      ring
    have hφzbar : prox_obj G τ x zbar = τ * G.f zbar + ‖zbar - x‖ ^ 2 / 2 := rfl
    have hφzt : prox_obj G τ x zt = τ * G.f zt + ‖zt - x‖ ^ 2 / 2 := rfl
    rw [hφzbar, hφzt] at hzt_min
    rw [hnorm_exp] at hzt_min
    have hτt : τ * t * (G.f zbar - G.f y) ≤ t * ⟪zbar - x, y - zbar⟫_ℝ
        + t ^ 2 * ‖y - zbar‖ ^ 2 / 2 := by nlinarith
    have : τ * (G.f zbar - G.f y) ≤ ⟪zbar - x, y - zbar⟫_ℝ + t * ‖y - zbar‖ ^ 2 / 2 := by
      have : τ * t * (G.f zbar - G.f y) = t * (τ * (G.f zbar - G.f y)) := by ring
      rw [this] at hτt
      have ht : t > 0 := ht_pos
      nlinarith
    exact this
  by_contra h_neg
  push_neg at h_neg
  have c_nn : 0 ≤ ‖y - zbar‖ ^ 2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
  have diff_pos : 0 < τ * (G.f zbar - G.f y) - ⟪zbar - x, y - zbar⟫_ℝ := by linarith
  set t := min 1 ((τ * (G.f zbar - G.f y) - ⟪zbar - x, y - zbar⟫_ℝ) / (‖y - zbar‖ ^ 2 / 2 + 1))
  have ht_pos : 0 < t := lt_min (by norm_num)
    (div_pos diff_pos (by linarith : 0 < ‖y - zbar‖ ^ 2 / 2 + 1))
  have ht_le : t ≤ 1 := min_le_left 1 _
  have hkey_t := hkey t ht_pos ht_le
  have ht_bound : t * (‖y - zbar‖ ^ 2 / 2 + 1) ≤ τ * (G.f zbar - G.f y) - ⟪zbar - x, y - zbar⟫_ℝ := by
    have h1 : t ≤ (τ * (G.f zbar - G.f y) - ⟪zbar - x, y - zbar⟫_ℝ) / (‖y - zbar‖ ^ 2 / 2 + 1) :=
      min_le_right 1 _
    rw [le_div_iff₀ (by linarith : 0 < ‖y - zbar‖ ^ 2 / 2 + 1)] at h1
    exact h1
  have htc_lt : t * (‖y - zbar‖ ^ 2 / 2) < τ * (G.f zbar - G.f y) - ⟪zbar - x, y - zbar⟫_ℝ := by
    have : t * (‖y - zbar‖ ^ 2 / 2) ≤ (τ * (G.f zbar - G.f y) - ⟪zbar - x, y - zbar⟫_ℝ) - t := by linarith
    linarith
  linarith

/-! ## Proximal operator as a function -/

/-- The proximal point as a function (unique by `prox_scale_unique`). -/
noncomputable def prox (G : ProperConvex E) (τ : ℝ) (hτ : 0 < τ) (x : E) : E :=
  Classical.choose (prox_scale_exists G hτ x)

lemma prox_spec (G : ProperConvex E) (τ : ℝ) (hτ : 0 < τ) (x : E) :
    prox_scale G τ x (prox G τ hτ x) :=
  Classical.choose_spec (prox_scale_exists G hτ x)

lemma prox_mem_dom (G : ProperConvex E) (τ : ℝ) (hτ : 0 < τ) (x : E) :
    prox G τ hτ x ∈ G.dom :=
  (prox_spec G τ hτ x).1

lemma prox_isMinOn (G : ProperConvex E) (τ : ℝ) (hτ : 0 < τ) (x : E) :
    IsMinOn (prox_obj G τ x) G.dom (prox G τ hτ x) :=
  (prox_spec G τ hτ x).2

lemma prox_optimality (G : ProperConvex E) (τ : ℝ) (hτ : 0 < τ) (x : E) (y : E) (hy : y ∈ G.dom) :
    ⟪prox G τ hτ x - x, y - prox G τ hτ x⟫_ℝ ≥ τ * (G.f (prox G τ hτ x) - G.f y) :=
  prox_scale_optimality G hτ x (prox_spec G τ hτ x) y hy

/-! ## PDAL Algorithm structure -/

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X] [ProperSpace X]

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [CompleteSpace Y] [FiniteDimensional ℝ Y] [ProperSpace Y]

/-! ### Primal-dual gap and saddle point (eqs. (6)–(7))

Following the paper, with `(x̂, ŷ)` a saddle point:
- `P(x) = g(x) - g(x̂) + ⟨K*ŷ, x - x̂⟩ ≥ 0` for all `x ∈ dom g`
- `D(y) = f*(y) - f*(ŷ) - ⟨Kx̂, y - ŷ⟩ ≥ 0` for all `y ∈ dom f*`
- `G = P + D`
-/

/-- Primal gap `P(x) = g(x) - g(x̂) + ⟨K*ŷ, x - x̂⟩` (eq. (6)). -/
def primal_gap (K : X →L[ℝ] Y) (g : ProperConvex X) (x xhat : X) (yhat : Y) : ℝ :=
  g.f x - g.f xhat + ⟪(K†) yhat, x - xhat⟫_ℝ

/-- Dual gap `D(y) = f*(y) - f*(ŷ) - ⟨Kx̂, y - ŷ⟩` (eq. (7)). -/
def dual_gap (K : X →L[ℝ] Y) (h : ProperConvex Y) (y yhat : Y) (xhat : X) : ℝ :=
  h.f y - h.f yhat - ⟪K xhat, y - yhat⟫_ℝ

/-- The full primal-dual gap `G = P + D`. -/
def pd_gap (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x : X) (y : Y) (xhat : X) (yhat : Y) : ℝ :=
  primal_gap K g x xhat yhat + dual_gap K h y yhat xhat

/-- A saddle point: `(x̂, ŷ)` satisfies the saddle point inequalities.

From eq. (6): `g(x̂) ≤ g(x) + ⟨K*ŷ, x - x̂⟩` for all `x ∈ dom g`, i.e.
`P(x) = g(x) - g(x̂) + ⟨K*ŷ, x - x̂⟩ ≥ 0`.

From eq. (7): `f*(ŷ) ≤ f*(y) - ⟨Kx̂, y - ŷ⟩` for all `y ∈ dom f*`, i.e.
`D(y) = f*(y) - f*(ŷ) - ⟨Kx̂, y - ŷ⟩ ≥ 0`.
-/
structure SaddlePoint (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y) where
  xhat : X
  yhat : Y
  xhat_dom : xhat ∈ g.dom
  yhat_dom : yhat ∈ h.dom
  saddle_primal : ∀ x ∈ g.dom, g.f xhat ≤ g.f x + ⟪(K†) yhat, x - xhat⟫_ℝ
  saddle_dual : ∀ y ∈ h.dom, h.f yhat ≤ h.f y - ⟪K xhat, y - yhat⟫_ℝ

/-- Propositional version of `SaddlePoint`: `(xhat, yhat)` is a saddle point. -/
def IsSaddlePoint (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (xhat : X) (yhat : Y) : Prop :=
  xhat ∈ g.dom ∧ yhat ∈ h.dom ∧
  (∀ x ∈ g.dom, g.f xhat ≤ g.f x + ⟪(K†) yhat, x - xhat⟫_ℝ) ∧
  (∀ y ∈ h.dom, h.f yhat ≤ h.f y - ⟪K xhat, y - yhat⟫_ℝ)

/-- Convert a `SaddlePoint` structure to the `IsSaddlePoint` proposition. -/
lemma SaddlePoint.is_saddle (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (sp : SaddlePoint K g h) : IsSaddlePoint K g h sp.xhat sp.yhat :=
  ⟨sp.xhat_dom, sp.yhat_dom, sp.saddle_primal, sp.saddle_dual⟩

/-- At a saddle point, `P(x) ≥ 0` for all `x ∈ dom g`. -/
lemma primal_gap_nonneg (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (sp : SaddlePoint K g h) (x : X) (hx : x ∈ g.dom) :
    0 ≤ primal_gap K g x sp.xhat sp.yhat := by
  have := sp.saddle_primal x hx
  simp [primal_gap]; linarith

/-- At a saddle point, `D(y) ≥ 0` for all `y ∈ dom f*`. -/
lemma dual_gap_nonneg (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (sp : SaddlePoint K g h) (y : Y) (hy : y ∈ h.dom) :
    0 ≤ dual_gap K h y sp.yhat sp.xhat := by
  have := sp.saddle_dual y hy
  simp [dual_gap]; linarith

/-- At a saddle point, `G(x, y) = P(x) + D(y) ≥ 0` for valid `(x, y)`. -/
lemma pd_gap_nonneg (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (sp : SaddlePoint K g h) (x : X) (hx : x ∈ g.dom) (y : Y) (hy : y ∈ h.dom) :
    0 ≤ pd_gap K g h x y sp.xhat sp.yhat := by
  simp only [pd_gap]
  exact add_nonneg (primal_gap_nonneg K g h sp x hx) (dual_gap_nonneg K g h sp y hy)

/-! ## Linesearch -/

/-- The acceptance condition (8): `√β τ ‖K*y' - K*y‖ ≤ δ ‖y' - y‖`. -/
def accept_cond (K : X →L[ℝ] Y) (beta delta tau : ℝ) (y yp : Y) : Prop :=
  Real.sqrt beta * tau * ‖(K†) (yp - y)‖ ≤ delta * ‖yp - y‖

/-- The acceptance condition holds for any candidate whenever
`√β τ ‖K‖ ≤ δ`, by the operator norm bound `‖K† v‖ ≤ ‖K‖ ‖v‖`. -/
lemma accept_cond_of_small_tau (K : X →L[ℝ] Y) {beta delta tau : ℝ}
    (hbeta : 0 < beta) (hdelta : 0 < delta) (htau : 0 < tau)
    (y yp : Y) (hsmall : Real.sqrt beta * tau * ‖K‖ ≤ delta) :
    accept_cond K beta delta tau y yp := by
  simp only [accept_cond]
  have hadj_norm : ‖(K† : Y →L[ℝ] X)‖ = ‖K‖ :=
    LinearIsometryEquiv.norm_map _ _
  have hK_op : ‖(K†) (yp - y)‖ ≤ ‖K‖ * ‖yp - y‖ := by
    rw [← hadj_norm]
    exact ContinuousLinearMap.le_opNorm _ _
  have hnn : 0 ≤ Real.sqrt beta * tau := by positivity
  calc Real.sqrt beta * tau * ‖(K†) (yp - y)‖
      ≤ Real.sqrt beta * tau * (‖K‖ * ‖yp - y‖) :=
        mul_le_mul_of_nonneg_left hK_op hnn
    _ = Real.sqrt beta * tau * ‖K‖ * ‖yp - y‖ := by ring
    _ ≤ delta * ‖yp - y‖ :=
        mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)

/-- Lemma 1(i): The linesearch always terminates.

Given the current state and a positive trial step size, there exists a
finite acceptance index `i` such that the candidate step `τ_trial · μ^i`
satisfies the acceptance condition. This is proved from the operator norm
bound, **not** from a pre-existing `accept` field.

When `‖K‖ = 0`, any step is accepted (index `i = 0`).
When `‖K‖ > 0`, since `μ^i → 0`, we can find `i` with
`τ_trial · μ^i ≤ δ / (√β · ‖K‖)`, which implies acceptance.
-/
theorem linesearch_terminates
    (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x_k x_km1 : X) (y_k : Y)
    (tau_km1 tau_trial : ℝ) (beta delta mu : ℝ)
    (h_tau_km1 : 0 < tau_km1) (h_tau_trial : 0 < tau_trial)
    (h_beta : 0 < beta) (h_delta : 0 < delta) (h_mu : 0 < mu ∧ mu < 1) :
    ∃ i : ℕ, 0 < tau_trial * mu ^ i ∧
      accept_cond K beta delta (tau_trial * mu ^ i) y_k
        (prox h (beta * (tau_trial * mu ^ i))
          (mul_pos h_beta (mul_pos h_tau_trial (pow_pos h_mu.1 i)))
          (y_k + (beta * (tau_trial * mu ^ i)) • K
            (x_k + (tau_trial * mu ^ i / tau_km1) • (x_k - x_km1)))) := by
  set L := ‖K‖ with hL_def
  by_cases hL : L = 0
  · refine ⟨0, ?_, ?_⟩
    · simp [pow_zero, *]
    · have htau0 : 0 < tau_trial * mu ^ 0 := by simp [pow_zero, *]
      have hbeta_tau : 0 < beta * (tau_trial * mu ^ 0) := by
        simp [pow_zero, *]
      have hK0 : ‖K‖ = 0 := hL_def ▸ hL
      have hsmall : Real.sqrt beta * (tau_trial * mu ^ 0) * ‖K‖ ≤ delta := by
        have : ‖K‖ = 0 := hL_def ▸ hL
        simp [pow_zero, this, le_of_lt h_delta]
      exact accept_cond_of_small_tau K h_beta h_delta htau0 y_k
        (prox h (beta * (tau_trial * mu ^ 0)) hbeta_tau
          (y_k + (beta * (tau_trial * mu ^ 0)) • K
            (x_k + (tau_trial * mu ^ 0 / tau_km1) • (x_k - x_km1)))) hsmall
  have hL_pos : 0 < L := by
    rcases lt_or_eq_of_le (norm_nonneg K) with h | h
    · exact h
    · exfalso; apply hL; rw [hL_def]; exact h.symm
  have h_sqrt_beta_pos : 0 < Real.sqrt beta := Real.sqrt_pos.mpr h_beta
  have h_mu_tendsto : Tendsto (fun n => mu ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h_mu.1.le h_mu.2
  have hmul_pos : 0 < Real.sqrt beta * L * tau_trial :=
    mul_pos (mul_pos h_sqrt_beta_pos hL_pos) h_tau_trial
  have h_threshold_pos : 0 < delta / (Real.sqrt beta * L * tau_trial) :=
    div_pos h_delta hmul_pos
  rcases (h_mu_tendsto.eventually (gt_mem_nhds h_threshold_pos)).exists with ⟨i, hi⟩
  have h_mu_i_pos : 0 < mu ^ i := pow_pos h_mu.1 i
  have h_tau_i : 0 < tau_trial * mu ^ i := mul_pos h_tau_trial h_mu_i_pos
  have h_beta_tau_i : 0 < beta * (tau_trial * mu ^ i) :=
    mul_pos h_beta (mul_pos h_tau_trial h_mu_i_pos)
  have h_tau_i_le : tau_trial * mu ^ i < delta / (Real.sqrt beta * L) := by
    rw [lt_div_iff₀ (mul_pos h_sqrt_beta_pos hL_pos)]
    have hkey : mu ^ i * (Real.sqrt beta * L * tau_trial) < delta := by
      rw [← lt_div_iff₀ hmul_pos]; exact hi
    have : tau_trial * mu ^ i * (Real.sqrt beta * L) =
           mu ^ i * (Real.sqrt beta * L * tau_trial) := by ring
    linarith
  have hsmall : Real.sqrt beta * (tau_trial * mu ^ i) * L ≤ delta := by
    have : Real.sqrt beta * (tau_trial * mu ^ i) * L =
           (tau_trial * mu ^ i) * (Real.sqrt beta * L) := by ring
    rw [this, ← le_div_iff₀ (mul_pos h_sqrt_beta_pos hL_pos)]
    linarith
  refine ⟨i, h_tau_i, ?_⟩
  exact accept_cond_of_small_tau K h_beta h_delta h_tau_i y_k
    (prox h (beta * (tau_trial * mu ^ i)) h_beta_tau_i
      (y_k + (beta * (tau_trial * mu ^ i)) • K
        (x_k + (tau_trial * mu ^ i / tau_km1) • (x_k - x_km1)))) hsmall

/-! ## Minimal acceptance index and recursive construction -/

/-- The set of acceptance indices for a given state.

An index `i` is in `accept_set` if the candidate step `τ_trial · μ^i` yields
a dual proximal point that satisfies the acceptance condition (8).
-/
def accept_set (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x_k x_km1 : X) (y_k : Y)
    (tau_km1 tau_trial beta delta mu : ℝ)
    (h_tau_km1 : 0 < tau_km1) (h_tau_trial : 0 < tau_trial)
    (h_beta : 0 < beta) (h_delta : 0 < delta) (h_mu : 0 < mu ∧ mu < 1) : Set ℕ :=
  { i | 0 < tau_trial * mu ^ i ∧
    accept_cond K beta delta (tau_trial * mu ^ i) y_k
      (prox h (beta * (tau_trial * mu ^ i))
        (mul_pos h_beta (mul_pos h_tau_trial (pow_pos h_mu.1 i)))
        (y_k + (beta * (tau_trial * mu ^ i)) • K
          (x_k + (tau_trial * mu ^ i / tau_km1) • (x_k - x_km1)))) }

/-- `accept_set` is nonempty by `linesearch_terminates`. -/
theorem accept_set_nonempty (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x_k x_km1 : X) (y_k : Y)
    (tau_km1 tau_trial beta delta mu : ℝ)
    (h_tau_km1 : 0 < tau_km1) (h_tau_trial : 0 < tau_trial)
    (h_beta : 0 < beta) (h_delta : 0 < delta) (h_mu : 0 < mu ∧ mu < 1) :
    (accept_set K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
      h_tau_km1 h_tau_trial h_beta h_delta h_mu).Nonempty := by
  have h := linesearch_terminates K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
    h_tau_km1 h_tau_trial h_beta h_delta h_mu
  obtain ⟨i, hi1, hi2⟩ := h
  refine ⟨i, ?_⟩
  simp only [accept_set, Set.mem_setOf]
  refine ⟨hi1, ?_⟩
  exact hi2

/-- The minimal acceptance index, defined via `Nat.find`.

This is the smallest non-negative integer `i` such that the candidate step
`τ_trial · μ^i` satisfies the acceptance condition (8).
-/
def min_accept_index (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x_k x_km1 : X) (y_k : Y)
    (tau_km1 tau_trial beta delta mu : ℝ)
    (h_tau_km1 : 0 < tau_km1) (h_tau_trial : 0 < tau_trial)
    (h_beta : 0 < beta) (h_delta : 0 < delta) (h_mu : 0 < mu ∧ mu < 1) : ℕ :=
  @Nat.find (fun i => i ∈ accept_set K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
    h_tau_km1 h_tau_trial h_beta h_delta h_mu)
    (fun _ => Classical.dec _)
    (accept_set_nonempty K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
      h_tau_km1 h_tau_trial h_beta h_delta h_mu)

/-- The minimal acceptance index satisfies the acceptance condition. -/
theorem min_accept_index_accept (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x_k x_km1 : X) (y_k : Y)
    (tau_km1 tau_trial beta delta mu : ℝ)
    (h_tau_km1 : 0 < tau_km1) (h_tau_trial : 0 < tau_trial)
    (h_beta : 0 < beta) (h_delta : 0 < delta) (h_mu : 0 < mu ∧ mu < 1) :
    let i := min_accept_index K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
      h_tau_km1 h_tau_trial h_beta h_delta h_mu
    0 < tau_trial * mu ^ i ∧
    accept_cond K beta delta (tau_trial * mu ^ i) y_k
      (prox h (beta * (tau_trial * mu ^ i))
        (mul_pos h_beta (mul_pos h_tau_trial (pow_pos h_mu.1 i)))
        (y_k + (beta * (tau_trial * mu ^ i)) • K
          (x_k + (tau_trial * mu ^ i / tau_km1) • (x_k - x_km1)))) := by
  have h := @Nat.find_spec _ (fun _ => Classical.dec _)
    (accept_set_nonempty K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
      h_tau_km1 h_tau_trial h_beta h_delta h_mu)
  simp only [accept_set, Set.mem_setOf] at h
  exact h

/-- The minimal acceptance index is minimal: no smaller index is accepted. -/
theorem min_accept_index_minimal (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x_k x_km1 : X) (y_k : Y)
    (tau_km1 tau_trial beta delta mu : ℝ)
    (h_tau_km1 : 0 < tau_km1) (h_tau_trial : 0 < tau_trial)
    (h_beta : 0 < beta) (h_delta : 0 < delta) (h_mu : 0 < mu ∧ mu < 1) :
    ∀ j, j < min_accept_index K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
      h_tau_km1 h_tau_trial h_beta h_delta h_mu →
      j ∉ accept_set K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
        h_tau_km1 h_tau_trial h_beta h_delta h_mu := by
  intro j hj
  exact @Nat.find_min _ (fun _ => Classical.dec _)
    (accept_set_nonempty K g h x_k x_km1 y_k tau_km1 tau_trial beta delta mu
      h_tau_km1 h_tau_trial h_beta h_delta h_mu) j hj

/-! ## Step size lower bound (Lemma 1(ii))

Proven after the PDAL structure definition, since it requires `ls_index_minimal`.
-/

/-! ## PDAL structure with trial and accepted step sizes -/

/-- PDAL: the primal-dual algorithm with linesearch (Algorithm 1).

The structure distinguishes:
- **Trial step size** `tau_trial`: chosen in `[τ_{k-1}, τ_{k-1}√(1+θ_{k-1})]`
- **Accepted step size** `tau`: `tau_trial · μ^{ls_index}`, which can be
  smaller than the previous step `tau (k-1)`.
- **Linesearch index** `ls_index`: the number of reductions by `μ`.

The acceptance condition is justified by the construction (via
`linesearch_terminates`), not assumed a priori.
-/
structure PDAL (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y) where
  x : ℕ → X
  y : ℕ → Y
  tau : ℕ → ℝ          -- accepted step sizes
  tau_trial : ℕ → ℝ    -- trial step sizes
  theta : ℕ → ℝ        -- extrapolation parameters
  ls_index : ℕ → ℕ     -- linesearch acceptance indices
  -- Parameters
  mu : ℝ
  mu_pos : 0 < mu ∧ mu < 1
  delta : ℝ
  delta_pos : 0 < delta ∧ delta < 1
  beta : ℝ
  beta_pos : 0 < beta
  -- Initial values
  tau0_pos : tau 0 > 0
  theta0_eq : theta 0 = 1
  -- All accepted step sizes are positive (derivable from other fields)
  tau_pos_all : ∀ k, 0 < tau k
  -- Trial step range: τ_k^trial ∈ [τ_{k-1}, τ_{k-1}√(1+θ_{k-1})]  (Algorithm 1, Step 2)
  tau_trial_range : ∀ k ≥ 1,
    tau_trial k ≥ tau (k - 1) ∧ tau_trial k ≤ tau (k - 1) * Real.sqrt (1 + theta (k - 1))
  -- Accepted step: τ_k = τ_k^trial · μ^{i_k}
  tau_def : ∀ k ≥ 1, tau k = tau_trial k * mu ^ (ls_index k)
  -- θ_k = τ_k / τ_{k-1}
  theta_def : ∀ k ≥ 1, theta k = tau k / tau (k - 1)
  -- Primal update: x_k = prox_{τ_{k-1} g}(x_{k-1} - τ_{k-1} K* y_k)
  primal_update : ∀ k ≥ 1, prox_scale g (tau (k - 1))
      (x (k - 1) - (tau (k - 1)) • (K†) (y k)) (x k)
  -- Dual update: y_{k+1} = prox_{β τ_k h}(y_k + β τ_k K x̄_k)
  -- where x̄_k = x_k + θ_k(x_k - x_{k-1})
  dual_update : ∀ k ≥ 1, prox_scale h (beta * tau k)
      (y k + (beta * tau k) • K (x k + theta k • (x k - x (k - 1)))) (y (k + 1))
  -- Acceptance condition (8) at the accepted index
  accept : ∀ k ≥ 1,
      accept_cond K beta delta (tau k) (y k) (y (k + 1))
  -- Minimality of the linesearch index: for j < ls_index k, the candidate
  -- at index j does NOT satisfy the acceptance condition.
  -- The proximal point at the rejected candidate is computed with the same
  -- formula as in the linesearch.
  ls_index_minimal : ∀ k, (hk : k ≥ 1) → ∀ j, (hj : j < ls_index k) →
      ¬ accept_cond K beta delta (tau_trial k * mu ^ j) (y k)
        (prox h (beta * (tau_trial k * mu ^ j))
          (mul_pos beta_pos
            (mul_pos (lt_of_lt_of_le (tau_pos_all (k - 1)) (tau_trial_range k hk).1)
              (pow_pos mu_pos.1 j)))
          (y k + (beta * (tau_trial k * mu ^ j)) • K
            (x k + (tau_trial k * mu ^ j / tau (k - 1)) • (x k - x (k - 1)))))

variable {K : X →L[ℝ] Y} {g : ProperConvex X} {h : ProperConvex Y}
variable {alg : PDAL K g h}

/-! ## Recursive construction of PDAL from raw data -/

/-- State of the PDAL recursion after completing step `k`:
`xk = x^k`, `yk = y^{k+1}`, `tauk = τ_k`, `thetak = θ_k`, and `lsidx` is the
linesearch index used at step `k` (0 for the initial state).  The proof fields
make the positivity of the accepted step sizes and of the extrapolation
parameters available inside the recursion itself. -/
structure PDState where
  xk : X
  yk : Y
  tauk : ℝ
  thetak : ℝ
  lsidx : ℕ
  htau : 0 < tauk
  htheta : 0 ≤ thetak

/-- One PDAL step: from the state after step `k` compute the state after step
`k+1`.  The trial step size is `sel (k+1) τ_k θ_k` (legal selector), the
accepted step size is `τ_trial · μ^i` with `i` the minimal acceptance index
(from `min_accept_index`), and the primal/dual proximal updates use `prox`.
No operator norm is used; the linesearch termination is guaranteed by the
minimal acceptance index via `linesearch_terminates`. -/
noncomputable def pdNext (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ))
    (k : ℕ) (s : PDState (X := X) (Y := Y)) : PDState (X := X) (Y := Y) :=
  let xnext := prox g s.tauk s.htau (s.xk - s.tauk • (K†) s.yk)
  let τt := sel (k + 1) s.tauk s.thetak
  let hτt : 0 < τt := lt_of_lt_of_le s.htau (hsel (k + 1) s.tauk s.htau s.thetak s.htheta).1
  let i := min_accept_index K g h xnext s.xk s.yk s.tauk τt beta delta mu
    s.htau hτt hb hd.1 hm
  let τn := τt * mu ^ i
  let hβτn : 0 < beta * τn := mul_pos hb (mul_pos hτt (pow_pos hm.1 i))
  let θn := τn / s.tauk
  let ynext := prox h (beta * τn) hβτn
    (s.yk + (beta * τn) • K (xnext + θn • (xnext - s.xk)))
  { xk := xnext
    yk := ynext
    tauk := τn
    thetak := θn
    lsidx := i
    htau := mul_pos hτt (pow_pos hm.1 i)
    htheta := div_nonneg (le_of_lt (mul_pos hτt (pow_pos hm.1 i))) (le_of_lt s.htau) }

/-- The PDAL state sequence generated from raw data by recursion on `ℕ`:
state 0 is `(x₀, y₁, τ₀, θ₀ = 1)`, and each successor state is one PDAL step
(`pdNext`). -/
noncomputable def pdSeq (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x0 : X) (y1 : Y) (tau0 : ℝ) (htau0 : 0 < tau0)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ)) :
    ℕ → PDState (X := X) (Y := Y) :=
  fun k => Nat.rec (motive := fun _ => PDState (X := X) (Y := Y))
    { xk := x0, yk := y1, tauk := tau0, thetak := 1, lsidx := 0,
      htau := htau0, htheta := le_of_lt (by norm_num : (0:ℝ) < 1) }
    (fun j acc => pdNext K g h mu delta beta hm hd hb sel hsel j acc) k

/-- **Recursive construction (Algorithm 1)**: given the raw data `x₀ ∈ X`,
`y₁ ∈ Y`, `τ₀ > 0`, parameters `μ ∈ (0,1)`, `δ ∈ (0,1)`, `β > 0`, and any
legal trial-step selector `sel` (with `sel k τ θ ∈ [τ, τ·√(1+θ)]` whenever
`τ > 0` and `θ ≥ 0`), construct a full PDAL instance: initialization, step
size positivity, legal trial range, minimal acceptance indices, acceptance
conditions and both proximal updates all hold **by construction**.
Note `x 0` is arbitrary (no `dom g` requirement); the operator norm is not
an input. -/
noncomputable def mkPDAL (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x0 : X) (y1 : Y) (tau0 : ℝ) (htau0 : 0 < tau0)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ)) :
    PDAL K g h :=
  { x := fun k => (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel k).xk
    y := fun k => Nat.rec (motive := fun _ => Y) y1
      (fun j _ => (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).yk) k
    tau := fun k => (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel k).tauk
    tau_trial := fun k => Nat.rec (motive := fun _ => ℝ) tau0
      (fun j _ => sel (j + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).thetak) k
    theta := fun k => (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel k).thetak
    ls_index := fun k => (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel k).lsidx
    mu := mu
    mu_pos := hm
    delta := delta
    delta_pos := hd
    beta := beta
    beta_pos := hb
    tau0_pos := htau0
    theta0_eq := rfl
    tau_pos_all := fun k => (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel k).htau
    tau_trial_range := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      show sel (j + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
          (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).thetak
        ≥ (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk ∧
        sel (j + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
          (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).thetak
        ≤ (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
          * Real.sqrt (1 + (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).thetak)
      exact hsel (j + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htau
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).thetak
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htheta
    tau_def := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rfl
    theta_def := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rfl
    primal_update := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact prox_spec g (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htau
        ((pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).xk
          - (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
            • (K†) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).yk)
    dual_update := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact prox_spec h (beta * (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel (j + 1)).tauk)
        (mul_pos hb
          (mul_pos
            (lt_of_lt_of_le (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htau
              (hsel (j + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
                (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htau
                (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).thetak
                (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htheta).1)
            (pow_pos hm.1 (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel (j + 1)).lsidx)))
        ((pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).yk
          + (beta * (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel (j + 1)).tauk)
            • K ((pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel (j + 1)).xk
              + (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel (j + 1)).thetak
                • ((pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel (j + 1)).xk
                  - (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).xk)))
    accept := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact (min_accept_index_accept K g h
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel (j + 1)).xk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).xk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).yk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
        (sel (j + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
          (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).thetak)
        beta delta mu
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htau
        (lt_of_lt_of_le (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htau
          (hsel (j + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).tauk
            (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htau
            (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).thetak
            (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel j).htheta).1)
        hb hd.1 hm).2
    ls_index_minimal := by
      intro k hk j hj
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      refine fun hacc => min_accept_index_minimal K g h
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel (m + 1)).xk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).xk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).yk
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).tauk
        (sel (m + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).tauk
          (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).thetak)
        beta delta mu
        (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).htau
        (lt_of_lt_of_le (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).htau
          (hsel (m + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).tauk
            (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).htau
            (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).thetak
            (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).htheta).1)
        hb hd.1 hm j hj
        ⟨mul_pos
          (lt_of_lt_of_le (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).htau
            (hsel (m + 1) (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).tauk
              (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).htau
              (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).thetak
              (pdSeq K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel m).htheta).1)
          (pow_pos hm.1 j), hacc⟩ }

/-- Sanity check: `mkPDAL` really produces a PDAL instance (its fields hold
by construction). -/
theorem mkPDAL_spec (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x0 : X) (y1 : Y) (tau0 : ℝ) (htau0 : 0 < tau0)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ)) :
    let alg := mkPDAL K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel
    (∀ k ≥ 1, prox_scale g (alg.tau (k - 1))
        (alg.x (k - 1) - (alg.tau (k - 1)) • (K†) (alg.y k)) (alg.x k)) ∧
    (∀ k ≥ 1, accept_cond K alg.beta alg.delta (alg.tau k) (alg.y k) (alg.y (k + 1))) := by
  intro alg
  exact ⟨fun k hk => alg.primal_update k hk, alg.accept⟩

/-- The extrapolated point x̄_k = x_k + θ_k(x_k - x_{k-1}). -/
def xbar (alg : PDAL K g h) (k : ℕ) : X :=
  alg.x k + alg.theta k • (alg.x k - alg.x (k - 1))

/-- All accepted step sizes are positive. -/
lemma tau_pos (alg : PDAL K g h) : ∀ k, 0 < alg.tau k := alg.tau_pos_all

/-- All trial step sizes are positive. -/
lemma tau_trial_pos (alg : PDAL K g h) : ∀ k ≥ 1, 0 < alg.tau_trial k := by
  intro k hk
  have hr := alg.tau_trial_range k hk
  exact lt_of_lt_of_le (tau_pos alg (k - 1)) hr.1

/-! ### Lemma 1(iii): θ_k upper bound -/

/-- The golden ratio bound `(√5 + 1)/2`. -/
def theta_bound : ℝ := (Real.sqrt 5 + 1) / 2

/-- Helper: if `θ ≤ (√5+1)/2` then `√(1+θ) ≤ (√5+1)/2`. -/
lemma sqrt_one_plus_le_bound (θ : ℝ) (hθ : 0 ≤ θ) (hθb : θ ≤ theta_bound) :
    Real.sqrt (1 + θ) ≤ theta_bound := by
  have hb_pos : 0 < theta_bound := by
    have : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 5)
    exact div_pos (by linarith) (by norm_num)
  have hb_sq : theta_bound ^ 2 = theta_bound + 1 := by
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
    have h1 : theta_bound = (Real.sqrt 5 + 1) / 2 := rfl
    have h2 : theta_bound ^ 2 = ((Real.sqrt 5 + 1) / 2) ^ 2 := by rw [h1]
    have h3 : ((Real.sqrt 5 + 1) / 2) ^ 2 = (6 + 2 * Real.sqrt 5) / 4 := by
      field_simp; nlinarith [h5]
    rw [h2, h3]
    have h4 : (6 + 2 * Real.sqrt 5) / 4 = (Real.sqrt 5 + 1) / 2 + 1 := by ring
    rw [h4, ← h1]
  have hsq : 1 + θ ≤ theta_bound ^ 2 := by
    have : theta_bound ^ 2 = theta_bound + 1 := hb_sq
    rw [this]; linarith
  have htb_nn : 0 ≤ theta_bound := le_of_lt hb_pos
  calc Real.sqrt (1 + θ)
      ≤ Real.sqrt (theta_bound ^ 2) := Real.sqrt_le_sqrt hsq
    _ = theta_bound := Real.sqrt_sq htb_nn

/-- Lemma 1(iii): θ_k ≤ (√5 + 1)/2 for all k.

Note: the proof uses `tau_trial_range` (trial step upper bound) combined with
`tau_def` (accepted step = trial · μ^i ≤ trial), giving
`tau k ≤ tau_trial k ≤ tau (k-1) √(1+θ_{k-1})`, hence
`θ_k = tau k / tau (k-1) ≤ √(1+θ_{k-1})`.
-/
theorem theta_upper_bound (alg : PDAL K g h) :
    ∀ k, alg.theta k ≤ theta_bound := by
  have htp : ∀ k, 0 < alg.tau k := tau_pos alg
  -- θ_k ≤ √(1+θ_{k-1}) for k ≥ 1
  have hrel : ∀ k ≥ 1, alg.theta k ≤ Real.sqrt (1 + alg.theta (k - 1)) := by
    intro k hk
    have hr := alg.tau_trial_range k hk
    have ht := alg.theta_def k hk
    have htd := alg.tau_def k hk
    have htau_pos : 0 < alg.tau (k - 1) := htp (k - 1)
    have hmu_nn : 0 ≤ alg.mu := le_of_lt alg.mu_pos.1
    -- tau k = tau_trial k * mu^i ≤ tau_trial k (since 0 < mu^i ≤ 1)
    have htau_le_trial : alg.tau k ≤ alg.tau_trial k := by
      rw [htd]
      have hmi_le1 : alg.mu ^ (alg.ls_index k) ≤ 1 :=
        pow_le_one₀ hmu_nn (le_of_lt alg.mu_pos.2)
      have htt_nn : 0 ≤ alg.tau_trial k := le_of_lt (tau_trial_pos alg k hk)
      calc alg.tau_trial k * alg.mu ^ (alg.ls_index k)
          ≤ alg.tau_trial k * 1 := mul_le_mul_of_nonneg_left hmi_le1 htt_nn
        _ = alg.tau_trial k := by rw [mul_one]
    rw [ht, div_le_iff₀ htau_pos]
    calc alg.tau k ≤ alg.tau_trial k := htau_le_trial
      _ ≤ alg.tau (k - 1) * Real.sqrt (1 + alg.theta (k - 1)) := hr.2
      _ = Real.sqrt (1 + alg.theta (k - 1)) * alg.tau (k - 1) := by rw [mul_comm]
  -- Induction
  intro k
  induction k with
  | zero =>
    rw [alg.theta0_eq, theta_bound]
    have h5 : 1 ≤ Real.sqrt 5 := Real.le_sqrt_of_sq_le (by norm_num : (1:ℝ) ^ 2 ≤ 5)
    linarith
  | succ k ih =>
    have htheta_k_nn : 0 ≤ alg.theta k := by
      by_cases hk : k = 0
      · rw [hk, alg.theta0_eq]; norm_num
      · have hk1 : k ≥ 1 := by omega
        have ht := alg.theta_def k hk1
        rw [ht]
        apply div_nonneg
        · exact le_of_lt (htp k)
        · exact le_of_lt (htp (k - 1))
    have hrel' := hrel (k + 1) (by omega)
    have : alg.theta ((k + 1) - 1) = alg.theta k := by rw [Nat.add_one_sub_one]
    rw [this] at hrel'
    exact le_trans hrel' (sqrt_one_plus_le_bound (alg.theta k) htheta_k_nn ih)

/-! ### Energy inequality (eq. 24) -/

/-- All iterates x_k for k ≥ 1 are in dom g (from the primal proximal update).

Note that `x 0 ∈ X` is arbitrary; the additional assumption `x 0 ∈ dom g` is
needed only for the finite ergodic rate (Theorem 2). -/
lemma x_mem_dom (alg : PDAL K g h) : ∀ k ≥ 1, alg.x k ∈ g.dom := by
  intro k hk
  exact (alg.primal_update k hk).1

/-- Cosine rule: `2⟨a-b, c-a⟩ = ‖b-c‖² - ‖a-b‖² - ‖a-c‖²` (eq. 5). -/
lemma cosine_rule (a b c : X) :
    2 * ⟪a - b, c - a⟫_ℝ = ‖b - c‖^2 - ‖a - b‖^2 - ‖a - c‖^2 := by
  have h := norm_add_sq_real (a - b) (c - a)
  have h1 : (a - b) + (c - a) = c - b := by abel
  have h2 : ‖c - b‖ = ‖b - c‖ := by rw [← neg_sub, norm_neg]
  have h3 : ‖c - a‖ = ‖a - c‖ := by rw [← neg_sub, norm_neg]
  rw [h1, h2, h3] at h
  linarith

/-- `θ_k · τ_k ≤ (1 + θ_{k-1}) · τ_{k-1}` (from `tau ≤ tau_trial ≤ tau_{k-1}√(1+θ_{k-1})`). -/
lemma theta_tau_bound (alg : PDAL K g h) :
    ∀ k ≥ 1, alg.theta k * alg.tau k ≤ (1 + alg.theta (k - 1)) * alg.tau (k - 1) := by
  intro k hk
  have hτk_pos : 0 < alg.tau k := tau_pos alg k
  have hτkm1_pos : 0 < alg.tau (k - 1) := tau_pos alg (k - 1)
  have hθk : alg.theta k = alg.tau k / alg.tau (k - 1) := alg.theta_def k hk
  have hr := alg.tau_trial_range k hk
  have hmi_le1 : alg.mu ^ alg.ls_index k ≤ 1 :=
    pow_le_one₀ (le_of_lt alg.mu_pos.1) (le_of_lt alg.mu_pos.2)
  have htt_nn : 0 ≤ alg.tau_trial k := le_of_lt (tau_trial_pos alg k hk)
  have htau_le_trial : alg.tau k ≤ alg.tau_trial k := by
    rw [alg.tau_def k hk]
    calc alg.tau_trial k * alg.mu ^ alg.ls_index k
        ≤ alg.tau_trial k * 1 := mul_le_mul_of_nonneg_left hmi_le1 htt_nn
      _ = alg.tau_trial k := mul_one _
  have htau_le : alg.tau k ≤ alg.tau (k - 1) * Real.sqrt (1 + alg.theta (k - 1)) :=
    le_trans htau_le_trial hr.2
  -- Key: θk = τk/τkm1 ≤ √(1+θkm1), so θk * τk ≤ √(1+θkm1) * τk ≤ √(1+θkm1) * τkm1 * √(1+θkm1) = τkm1 * (1+θkm1)
  have hθk_le_sqrt : alg.theta k ≤ Real.sqrt (1 + alg.theta (k - 1)) := by
    rw [hθk, div_le_iff₀ hτkm1_pos]
    linarith [htau_le, mul_comm (Real.sqrt (1 + alg.theta (k - 1))) (alg.tau (k - 1))]
  have hθkm1_nn : 0 ≤ 1 + alg.theta (k - 1) := by
    have : 0 ≤ alg.theta (k - 1) := by
      by_cases hk1 : k - 1 = 0
      · rw [hk1, alg.theta0_eq]; norm_num
      · have hk2 : k - 1 ≥ 1 := by omega
        rw [alg.theta_def (k - 1) hk2]
        apply div_nonneg
        · exact le_of_lt (tau_pos alg (k - 1))
        · exact le_of_lt (tau_pos alg (k - 2))
    linarith
  have hsqrt_sq : Real.sqrt (1 + alg.theta (k - 1)) * Real.sqrt (1 + alg.theta (k - 1))
      = 1 + alg.theta (k - 1) := Real.mul_self_sqrt hθkm1_nn
  calc alg.theta k * alg.tau k
      ≤ Real.sqrt (1 + alg.theta (k - 1)) * alg.tau k :=
        mul_le_mul_of_nonneg_right hθk_le_sqrt (le_of_lt hτk_pos)
    _ ≤ Real.sqrt (1 + alg.theta (k - 1)) * (alg.tau (k - 1) * Real.sqrt (1 + alg.theta (k - 1))) :=
        mul_le_mul_of_nonneg_left htau_le (Real.sqrt_nonneg _)
    _ = (1 + alg.theta (k - 1)) * alg.tau (k - 1) := by
        rw [show Real.sqrt (1 + alg.theta (k - 1)) * (alg.tau (k - 1) * Real.sqrt (1 + alg.theta (k - 1)))
            = (Real.sqrt (1 + alg.theta (k - 1)) * Real.sqrt (1 + alg.theta (k - 1))) * alg.tau (k - 1)
            from by ring, hsqrt_sq]

set_option maxHeartbeats 2000000 in
/-- The energy inequality (eq. 24).

For any saddle point `(x̂, ŷ)`, the sequence
`a_k = ½‖x_k - x̂‖² + (1/(2β))‖y_k - ŷ‖² + τ_{k-1}(1+θ_{k-1})P(x_{k-1})`
is non-increasing, with the decrease bounded below by
`½‖x̄_k - x_k‖² + (1-δ²)/(2β)‖y_{k+1} - y_k‖²`.

The proof combines four proximal optimality conditions (eqs. 11–14),
the cosine rule (eq. 5), the acceptance condition (eq. 8), and the
adjoint identity, following the paper's derivation of eqs. (15)–(24).
-/
theorem energy_inequality_with_gap (alg : PDAL K g h) (sp : SaddlePoint K g h) (k : ℕ) (hk : k ≥ 1)
    (hxkm1 : alg.x (k - 1) ∈ g.dom) :
    ‖alg.x (k + 1) - sp.xhat‖^2 / 2
    + ‖alg.y (k + 1) - sp.yhat‖^2 / (2 * alg.beta)
    + alg.tau k * (1 + alg.theta k) * primal_gap K g (alg.x k) sp.xhat sp.yhat
  ≤ ‖alg.x k - sp.xhat‖^2 / 2
    + ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta)
    + alg.tau (k - 1) * (1 + alg.theta (k - 1)) * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat
    - ‖xbar alg k - alg.x k‖^2 / 2
    - (1 - alg.delta^2) * ‖alg.y (k + 1) - alg.y k‖^2 / (2 * alg.beta)
    ∧ alg.tau k * ((1 + alg.theta k)
        * primal_gap K g (alg.x k) sp.xhat sp.yhat
      - alg.theta k * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat
      + dual_gap K h (alg.y (k + 1)) sp.yhat sp.xhat)
    ≤ (‖alg.x k - sp.xhat‖^2 / 2
        + ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta))
      - (‖alg.x (k + 1) - sp.xhat‖^2 / 2
        + ‖alg.y (k + 1) - sp.yhat‖^2 / (2 * alg.beta)) := by
  -- Key positivity facts
  have hτk_pos : 0 < alg.tau k := tau_pos alg k
  have hτkm1_pos : 0 < alg.tau (k - 1) := tau_pos alg (k - 1)
  have hβ_pos : 0 < alg.beta := alg.beta_pos
  have hβτk_pos : 0 < alg.beta * alg.tau k := mul_pos hβ_pos hτk_pos
  have hδ_nn : 0 ≤ alg.delta := le_of_lt alg.delta_pos.1
  have hδ_lt1 : alg.delta < 1 := alg.delta_pos.2
  have hxkp1_dom : alg.x (k + 1) ∈ g.dom := x_mem_dom alg (k + 1) (by omega)
  have hxkm1_dom : alg.x (k - 1) ∈ g.dom := hxkm1
  have hθk_def : alg.theta k = alg.tau k / alg.tau (k - 1) := alg.theta_def k hk
  have hθτ : alg.theta k * alg.tau (k - 1) = alg.tau k := by
    rw [hθk_def]; exact div_mul_cancel₀ _ (ne_of_gt hτkm1_pos)
  have hsqrtβ_pos : 0 < Real.sqrt alg.beta := Real.sqrt_pos.mpr hβ_pos
  -- Proximal optimality conditions (eqs. 11–14)
  have hpu_kp1 := alg.primal_update (k + 1) (by omega)
  have hpu_k := alg.primal_update k hk
  have hdu_k := alg.dual_update k hk
  have h11 := prox_scale_optimality g hτk_pos _ hpu_kp1 sp.xhat sp.xhat_dom
  have h12 := prox_scale_optimality h hβτk_pos _ hdu_k sp.yhat sp.yhat_dom
  have h13 := prox_scale_optimality g hτkm1_pos _ hpu_k (alg.x (k+1)) hxkp1_dom
  have h14 := prox_scale_optimality g hτkm1_pos _ hpu_k (alg.x (k-1)) hxkm1_dom
  -- Acceptance condition
  have haccept := alg.accept k hk
  simp only [accept_cond] at haccept
  -- P, D, and non-negativity
  have hP_nn : 0 ≤ primal_gap K g (alg.x k) sp.xhat sp.yhat :=
    primal_gap_nonneg K g h sp (alg.x k) (x_mem_dom alg k hk)
  have hPkm1_nn : 0 ≤ primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat :=
    primal_gap_nonneg K g h sp (alg.x (k-1)) hxkm1_dom
  have hD_nn : 0 ≤ dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat :=
    dual_gap_nonneg K g h sp (alg.y (k+1)) ((alg.dual_update k hk).1)
  have hθτb := theta_tau_bound alg k hk
  -- Cosine rule (for all three key inner products)
  have hcos1 : 2 * ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
      = ‖alg.x k - sp.xhat‖^2 - ‖alg.x (k+1) - alg.x k‖^2 - ‖alg.x (k+1) - sp.xhat‖^2 :=
    cosine_rule (alg.x (k+1)) (alg.x k) sp.xhat
  -- K* norm bound from acceptance condition
  have hK_dnorm : ‖(K†) (alg.y (k+1) - alg.y k)‖ ≤ (alg.delta / Real.sqrt alg.beta) *
      ‖alg.y (k+1) - alg.y k‖ / alg.tau k := by
    have hτβ_pos : 0 < Real.sqrt alg.beta * alg.tau k := mul_pos hsqrtβ_pos hτk_pos
    have hrw : (alg.delta / Real.sqrt alg.beta) * ‖alg.y (k+1) - alg.y k‖ / alg.tau k
        = alg.delta * ‖alg.y (k+1) - alg.y k‖ / (Real.sqrt alg.beta * alg.tau k) := by
      field_simp
    rw [hrw, le_div_iff₀ hτβ_pos]
    nlinarith [haccept, hτβ_pos]
  -- Additional cosine rules for Y and x̄_k
  have hcos2 : 2 * ⟪alg.y (k+1) - alg.y k, sp.yhat - alg.y (k+1)⟫_ℝ
      = ‖alg.y k - sp.yhat‖^2 - ‖alg.y (k+1) - alg.y k‖^2 - ‖alg.y (k+1) - sp.yhat‖^2 := by
    have h := norm_add_sq_real (alg.y (k+1) - alg.y k) (sp.yhat - alg.y (k+1))
    have h1 : (alg.y (k+1) - alg.y k) + (sp.yhat - alg.y (k+1)) = sp.yhat - alg.y k := by abel
    have h2 : ‖sp.yhat - alg.y k‖ = ‖alg.y k - sp.yhat‖ := by rw [← neg_sub, norm_neg]
    have h3 : ‖sp.yhat - alg.y (k+1)‖ = ‖alg.y (k+1) - sp.yhat‖ := by rw [← neg_sub, norm_neg]
    rw [h1, h2, h3] at h
    linarith
  have hcos3 : 2 * ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
      = ‖alg.x k - alg.x (k+1)‖^2 - ‖xbar alg k - alg.x k‖^2 - ‖xbar alg k - alg.x (k+1)‖^2 :=
    cosine_rule (xbar alg k) (alg.x k) (alg.x (k+1))
  have hnorm_sym : ‖alg.x k - alg.x (k+1)‖^2 = ‖alg.x (k+1) - alg.x k‖^2 := by
    rw [← norm_sub_rev]
  have hnorm_sym2 : ‖xbar alg k - alg.x (k+1)‖^2 = ‖alg.x (k+1) - xbar alg k‖^2 := by
    rw [← norm_sub_rev]
  have hsβ : Real.sqrt alg.beta * Real.sqrt alg.beta = alg.beta := Real.mul_self_sqrt hβ_pos.le
  -- K† term bound: τ_k⟨K†Δy, x̄-x_{k+1}⟩ ≤ ‖x̄-x_{k+1}‖²/2 + δ²‖Δy‖²/(2β)
  -- via Cauchy-Schwarz + acceptance + Young's inequality
  have hK_bound : alg.tau k * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ
      ≤ ‖xbar alg k - alg.x (k+1)‖^2 / 2
        + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 / (2 * alg.beta) := by
    have hcs : ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ
        ≤ ‖(K†) (alg.y (k+1) - alg.y k)‖ * ‖xbar alg k - alg.x (k+1)‖ :=
      (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    have hτK : alg.tau k * ‖(K†) (alg.y (k+1) - alg.y k)‖
        ≤ (alg.delta / Real.sqrt alg.beta) * ‖alg.y (k+1) - alg.y k‖ := by
      have h := hK_dnorm
      rw [le_div_iff₀ hτk_pos] at h
      rw [show alg.tau k * ‖(K†) (alg.y (k+1) - alg.y k)‖
          = ‖(K†) (alg.y (k+1) - alg.y k)‖ * alg.tau k from mul_comm _ _]
      exact h
    -- Young's: (δ/√β) * a * b ≤ a²/2 + δ²b²/(2β), equivalent to (√β*a - δ*b)² ≥ 0
    have hyoung : (alg.delta / Real.sqrt alg.beta) * (‖xbar alg k - alg.x (k+1)‖
        * ‖alg.y (k+1) - alg.y k‖) ≤ ‖xbar alg k - alg.x (k+1)‖^2 / 2
        + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 / (2 * alg.beta) := by
      have hsq : 0 ≤ (Real.sqrt alg.beta * ‖xbar alg k - alg.x (k+1)‖
        - alg.delta * ‖alg.y (k+1) - alg.y k‖)^2 := sq_nonneg _
      have hkey : 2 * Real.sqrt alg.beta * alg.delta * (‖xbar alg k - alg.x (k+1)‖ * ‖alg.y (k+1) - alg.y k‖)
          ≤ alg.beta * ‖xbar alg k - alg.x (k+1)‖^2 + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 := by
        have hexp : (Real.sqrt alg.beta * ‖xbar alg k - alg.x (k+1)‖ - alg.delta * ‖alg.y (k+1) - alg.y k‖)^2
            = Real.sqrt alg.beta * Real.sqrt alg.beta * ‖xbar alg k - alg.x (k+1)‖^2
              - 2 * Real.sqrt alg.beta * alg.delta * (‖xbar alg k - alg.x (k+1)‖ * ‖alg.y (k+1) - alg.y k‖)
              + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 := by ring
        rw [hexp, hsβ] at hsq
        linarith
      have h2β : 0 < 2 * alg.beta := by positivity
      have hLHS_eq : (alg.delta / Real.sqrt alg.beta) * (‖xbar alg k - alg.x (k+1)‖ * ‖alg.y (k+1) - alg.y k‖)
          = 2 * Real.sqrt alg.beta * alg.delta * (‖xbar alg k - alg.x (k+1)‖ * ‖alg.y (k+1) - alg.y k‖)
            / (2 * alg.beta) := by
        field_simp [ne_of_gt hβ_pos, ne_of_gt hsqrtβ_pos]
        rw [Real.sq_sqrt hβ_pos.le]
        ring
      have hRHS_eq : ‖xbar alg k - alg.x (k+1)‖^2 / 2 + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 / (2 * alg.beta)
          = (alg.beta * ‖xbar alg k - alg.x (k+1)‖^2 + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2)
            / (2 * alg.beta) := by
        field_simp [ne_of_gt hβ_pos]
      rw [hLHS_eq, hRHS_eq, div_le_div_iff₀ h2β h2β]
      nlinarith [hkey, h2β, hsβ]
    -- Combine via calc chain: hcs → hτK → hyoung
    have hK_bound : alg.tau k * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ
        ≤ ‖xbar alg k - alg.x (k+1)‖^2 / 2
          + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 / (2 * alg.beta) := by
      have hnorm_xbar : 0 ≤ ‖xbar alg k - alg.x (k+1)‖ := norm_nonneg (xbar alg k - alg.x (k+1))
      have h1 : alg.tau k * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ
          ≤ alg.tau k * (‖(K†) (alg.y (k+1) - alg.y k)‖ * ‖xbar alg k - alg.x (k+1)‖) :=
        mul_le_mul_of_nonneg_left hcs (le_of_lt hτk_pos)
      have h2 : alg.tau k * (‖(K†) (alg.y (k+1) - alg.y k)‖ * ‖xbar alg k - alg.x (k+1)‖)
          ≤ (alg.delta / Real.sqrt alg.beta) * ‖alg.y (k+1) - alg.y k‖ * ‖xbar alg k - alg.x (k+1)‖ := by
        have := mul_le_mul_of_nonneg_right hτK hnorm_xbar
        nlinarith [this, hnorm_xbar]
      have h3 : (alg.delta / Real.sqrt alg.beta) * ‖alg.y (k+1) - alg.y k‖ * ‖xbar alg k - alg.x (k+1)‖
          ≤ ‖xbar alg k - alg.x (k+1)‖^2 / 2
            + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 / (2 * alg.beta) := by
        rw [mul_assoc (alg.delta / Real.sqrt alg.beta) ‖alg.y (k+1) - alg.y k‖ ‖xbar alg k - alg.x (k+1)‖,
          mul_comm ‖alg.y (k+1) - alg.y k‖ ‖xbar alg k - alg.x (k+1)‖]
        exact hyoung
      linarith [h1, h2, h3]
    exact hK_bound
  -- Combined inequality (20) from the paper:
  -- ⟨Δx, x̂-x_{k+1}⟩ + (1/β)⟨Δy, ŷ-y_{k+1}⟩ + ⟨x̄-x_k, x_{k+1}-x̄⟩
  -- + τ_k⟨K†Δy, x̄-x_{k+1}⟩ ≥ τ_k((1+θ_k)P(x_k) - θ_k P(x_{k-1}) + D(y_{k+1}))
  have h20 : ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
      + ⟪alg.y (k+1) - alg.y k, sp.yhat - alg.y (k+1)⟫_ℝ / alg.beta
      + ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
      + alg.tau k * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ
      ≥ alg.tau k * ((1 + alg.theta k) * primal_gap K g (alg.x k) sp.xhat sp.yhat
          - alg.theta k * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
          + dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat) := by
    have hk11 : alg.x (k + 1 - 1) = alg.x k := congr_arg alg.x (by omega)
    have hk12 : alg.tau (k + 1 - 1) = alg.tau k := congr_arg alg.tau (by omega)
    have hadj (y : Y) (x : X) : ⟪(K†) y, x⟫_ℝ = ⟪y, K x⟫_ℝ :=
      ContinuousLinearMap.adjoint_inner_left K x y
    -- Expand h11
    have h11a : ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
        + alg.tau k * ⟪(K†) (alg.y (k+1)), sp.xhat - alg.x (k+1)⟫_ℝ
        ≥ alg.tau k * (g.f (alg.x (k+1)) - g.f sp.xhat) := by
      have h := h11
      rw [hk11, hk12,
        show alg.x (k+1) - (alg.x k - alg.tau k • (K†) (alg.y (k+1)))
            = (alg.x (k+1) - alg.x k) + alg.tau k • (K†) (alg.y (k+1)) from by abel,
        inner_add_left, real_inner_smul_left] at h
      exact h
    -- Expand h12
    have h12a : ⟪alg.y (k+1) - alg.y k, sp.yhat - alg.y (k+1)⟫_ℝ
        - (alg.beta * alg.tau k) * ⟪K (xbar alg k), sp.yhat - alg.y (k+1)⟫_ℝ
        ≥ (alg.beta * alg.tau k) * (h.f (alg.y (k+1)) - h.f sp.yhat) := by
      have h := h12
      rw [show alg.x k + alg.theta k • (alg.x k - alg.x (k-1)) = xbar alg k from rfl,
        show alg.y (k+1) - (alg.y k + (alg.beta * alg.tau k) • K (xbar alg k))
            = (alg.y (k+1) - alg.y k) - (alg.beta * alg.tau k) • K (xbar alg k) from by abel,
        inner_sub_left, real_inner_smul_left] at h
      exact h
    -- Expand h13
    have h13a : ⟪alg.x k - alg.x (k-1), alg.x (k+1) - alg.x k⟫_ℝ
        + alg.tau (k-1) * ⟪(K†) (alg.y k), alg.x (k+1) - alg.x k⟫_ℝ
        ≥ alg.tau (k-1) * (g.f (alg.x k) - g.f (alg.x (k+1))) := by
      have h := h13
      rw [show alg.x k - (alg.x (k-1) - alg.tau (k-1) • (K†) (alg.y k))
          = (alg.x k - alg.x (k-1)) + alg.tau (k-1) • (K†) (alg.y k) from by abel,
        inner_add_left, real_inner_smul_left] at h
      exact h
    -- Expand h14
    have h14a : ⟪alg.x k - alg.x (k-1), alg.x (k-1) - alg.x k⟫_ℝ
        + alg.tau (k-1) * ⟪(K†) (alg.y k), alg.x (k-1) - alg.x k⟫_ℝ
        ≥ alg.tau (k-1) * (g.f (alg.x k) - g.f (alg.x (k-1))) := by
      have h := h14
      rw [show alg.x k - (alg.x (k-1) - alg.tau (k-1) • (K†) (alg.y k))
          = (alg.x k - alg.x (k-1)) + alg.tau (k-1) • (K†) (alg.y k) from by abel,
        inner_add_left, real_inner_smul_left] at h
      exact h
    have hβ_nn : 0 ≤ alg.beta := le_of_lt hβ_pos
    have hθk_nn : 0 ≤ alg.theta k := by
      rw [hθk_def]; exact div_nonneg (le_of_lt hτk_pos) (le_of_lt hτkm1_pos)
    -- Scale h11a by β
    have h11β := mul_le_mul_of_nonneg_left h11a hβ_nn
    -- Scale h13a by βθ_k (using hθτ)
    have h13βθ := mul_le_mul_of_nonneg_left h13a (mul_nonneg hβ_nn hθk_nn)
    -- Scale h14a by βθ_k²
    have h14βθ2 := mul_le_mul_of_nonneg_left h14a
      (mul_nonneg hβ_nn (mul_nonneg hθk_nn hθk_nn))
    -- Adjoint identities
    have hKadj : ⟪K (xbar alg k), sp.yhat - alg.y (k+1)⟫_ℝ
        = ⟪(K†) (sp.yhat - alg.y (k+1)), xbar alg k⟫_ℝ := by
      rw [real_inner_comm, ← hadj]
    have hDadj : ⟪K sp.xhat, alg.y (k+1) - sp.yhat⟫_ℝ
        = ⟪(K†) (alg.y (k+1) - sp.yhat), sp.xhat⟫_ℝ := by
      rw [real_inner_comm, ← hadj]
    -- x̄ definitions
    have hxb_diff : xbar alg k - alg.x k = alg.theta k • (alg.x k - alg.x (k-1)) := by
      simp [xbar, add_sub_cancel]
    have hxb_diff2 : alg.x (k+1) - xbar alg k
        = (alg.x (k+1) - alg.x k) - alg.theta k • (alg.x k - alg.x (k-1)) := by
      simp [xbar]; abel
    -- P, D definitions
    have hPk : primal_gap K g (alg.x k) sp.xhat sp.yhat
        = g.f (alg.x k) - g.f sp.xhat
          + ⟪(K†) sp.yhat, alg.x k - sp.xhat⟫_ℝ := rfl
    have hPkm1 : primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
        = g.f (alg.x (k-1)) - g.f sp.xhat
          + ⟪(K†) sp.yhat, alg.x (k-1) - sp.xhat⟫_ℝ := rfl
    have hDk : dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat
        = h.f (alg.y (k+1)) - h.f sp.yhat
          - ⟪K sp.xhat, alg.y (k+1) - sp.yhat⟫_ℝ := rfl
    -- θ_k² * τ_{k-1} = θ_k * τ_k
    have hθ2τ : alg.theta k * (alg.theta k * alg.tau (k-1)) = alg.theta k * alg.tau k := by
      rw [hθτ]
    -- Combine all scaled hypotheses with nlinarith
    -- The key mathematical identity: h11β + h12a + h13βθ + h14βθ2 ≥ combined_RHS
    -- and combined_LHS = β*h20_LHS + correction, combined_RHS = β*h20_RHS + correction
    -- so h20 follows.
    -- Key equality: non-K inner product combination
    have hE1 : alg.beta * alg.theta k
          * ⟪alg.x k - alg.x (k-1), alg.x (k+1) - alg.x k⟫_ℝ
        + alg.beta * (alg.theta k * alg.theta k)
          * ⟪alg.x k - alg.x (k-1), alg.x (k-1) - alg.x k⟫_ℝ
        = alg.beta * ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ := by
      have hexp : ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
          = alg.theta k * ⟪alg.x k - alg.x (k-1), alg.x (k+1) - alg.x k⟫_ℝ
            - (alg.theta k * alg.theta k)
              * ⟪alg.x k - alg.x (k-1), alg.x k - alg.x (k-1)⟫_ℝ := by
        rw [hxb_diff, hxb_diff2, real_inner_smul_left,
          show (alg.x (k+1) - alg.x k) - alg.theta k • (alg.x k - alg.x (k-1))
            = (alg.x (k+1) - alg.x k) + -(alg.theta k • (alg.x k - alg.x (k-1))) from by abel,
          inner_add_right, inner_neg_right, real_inner_smul_right]
        ring
      have hneg : ⟪alg.x k - alg.x (k-1), alg.x (k-1) - alg.x k⟫_ℝ
          = -⟪alg.x k - alg.x (k-1), alg.x k - alg.x (k-1)⟫_ℝ := by
        rw [show alg.x (k-1) - alg.x k = -(alg.x k - alg.x (k-1)) from by abel,
          inner_neg_right]
      rw [hexp, hneg]
      ring
    -- Prove β-scaled h20 using Codex-proven scaledEnergyFromOptimality, then divide by β
    have h20β : alg.beta * ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
        + ⟪alg.y (k+1) - alg.y k, sp.yhat - alg.y (k+1)⟫_ℝ
        + alg.beta * ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
        + alg.beta * (alg.tau k * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ)
        ≥ alg.beta * (alg.tau k * ((1 + alg.theta k)
            * primal_gap K g (alg.x k) sp.xhat sp.yhat
          - alg.theta k * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
          + dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat)) := by
      have H := PDALCodexHelp.scaledEnergyFromOptimality K
        (alg.x (k-1)) (alg.x k) (alg.x (k+1)) sp.xhat
        (alg.y k) (alg.y (k+1)) sp.yhat
        alg.beta (alg.tau k) (alg.tau (k-1)) (alg.theta k)
        (g.f (alg.x (k-1))) (g.f (alg.x k)) (g.f (alg.x (k+1))) (g.f sp.xhat)
        (h.f (alg.y (k+1))) (h.f sp.yhat)
        hβ_nn hθk_nn hθτ
        (by simpa only [inner_add_left, real_inner_smul_left] using h11a)
        (by simpa only [xbar, inner_sub_left, real_inner_smul_left] using h12a)
        (by simpa only [inner_add_left, real_inner_smul_left] using h13a)
        (by simpa only [inner_add_left, real_inner_smul_left] using h14a)
      simpa only [xbar, primal_gap, dual_gap] using H
    -- Derive h20 from h20β by dividing by β
    have hLHS_eq : (⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
        + ⟪alg.y (k+1) - alg.y k, sp.yhat - alg.y (k+1)⟫_ℝ / alg.beta
        + ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
        + alg.tau k * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ)
      = (alg.beta * ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
        + ⟪alg.y (k+1) - alg.y k, sp.yhat - alg.y (k+1)⟫_ℝ
        + alg.beta * ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
        + alg.beta * (alg.tau k * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ))
        / alg.beta := by field_simp [ne_of_gt hβ_pos]
    have hRHS_eq : alg.tau k * ((1 + alg.theta k)
            * primal_gap K g (alg.x k) sp.xhat sp.yhat
          - alg.theta k * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
          + dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat)
      = (alg.beta * (alg.tau k * ((1 + alg.theta k)
            * primal_gap K g (alg.x k) sp.xhat sp.yhat
          - alg.theta k * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
          + dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat))) / alg.beta := by
        field_simp [ne_of_gt hβ_pos]
    rw [hLHS_eq, hRHS_eq]
    exact div_le_div_of_nonneg_right h20β (le_of_lt hβ_pos)
  have h2β_pos : 0 < 2 * alg.beta := by positivity
  have h2β_nn : 0 ≤ 2 * alg.beta := le_of_lt h2β_pos
  have hβ_nn : 0 ≤ alg.beta := le_of_lt hβ_pos
  have hθτb_P : alg.tau k * alg.theta k * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
      ≤ (1 + alg.theta (k-1)) * alg.tau (k-1) * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat := by
    have hw := mul_le_mul_of_nonneg_right hθτb hPkm1_nn
    nlinarith [hw]
  have hτD_nn : 0 ≤ alg.tau k * dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat :=
    mul_nonneg (le_of_lt hτk_pos) hD_nn
  have hK_bound_s : 2 * alg.beta * (alg.tau k
      * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ)
      ≤ alg.beta * ‖xbar alg k - alg.x (k+1)‖^2
        + alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 := by
    have hw := mul_le_mul_of_nonneg_left hK_bound h2β_nn
    field_simp [ne_of_gt hβ_pos, ne_of_gt h2β_pos] at hw
    linarith [hw]
  have h20_s : 2 * alg.beta * ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
      + 2 * ⟪alg.y (k+1) - alg.y k, sp.yhat - alg.y (k+1)⟫_ℝ
      + 2 * alg.beta * ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
      + 2 * alg.beta * (alg.tau k
          * ⟪(K†) (alg.y (k+1) - alg.y k), xbar alg k - alg.x (k+1)⟫_ℝ)
      ≥ 2 * alg.beta * (alg.tau k * (1 + alg.theta k)
          * primal_gap K g (alg.x k) sp.xhat sp.yhat)
        - 2 * alg.beta * (alg.tau k * alg.theta k
          * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat)
        + 2 * alg.beta * (alg.tau k
          * dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat) := by
    have hw := mul_le_mul_of_nonneg_left h20 h2β_nn
    field_simp [ne_of_gt hβ_pos] at hw
    have hRHS_eq : 2 * alg.beta * (alg.tau k
        * ((1 + alg.theta k) * primal_gap K g (alg.x k) sp.xhat sp.yhat
          - alg.theta k * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
          + dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat))
        = 2 * alg.beta * (alg.tau k * (1 + alg.theta k)
          * primal_gap K g (alg.x k) sp.xhat sp.yhat)
        - 2 * alg.beta * (alg.tau k * alg.theta k
          * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat)
        + 2 * alg.beta * (alg.tau k
          * dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat) := by ring
    linarith [hw, hRHS_eq]
  have h2βτD_nn : 0 ≤ 2 * alg.beta * (alg.tau k
      * dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat) :=
    mul_nonneg h2β_nn hτD_nn
  have h2βθτb_P : 2 * alg.beta * (alg.tau k * alg.theta k
      * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat)
      ≤ 2 * alg.beta * (alg.tau (k-1) * (1 + alg.theta (k-1))
      * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat) := by
    have hw := mul_le_mul_of_nonneg_left hθτb_P h2β_nn
    have hring : (1 + alg.theta (k-1)) * alg.tau (k-1)
        = alg.tau (k-1) * (1 + alg.theta (k-1)) := by ring
    rw [hring] at hw
    exact hw
  have hexpand : (1 - alg.delta^2) * ‖alg.y (k+1) - alg.y k‖^2
      = ‖alg.y (k+1) - alg.y k‖^2
        - alg.delta^2 * ‖alg.y (k+1) - alg.y k‖^2 := by ring
  have hgoal_s : alg.beta * ‖alg.x (k+1) - sp.xhat‖^2
      + ‖alg.y (k+1) - sp.yhat‖^2
      + 2 * alg.beta * alg.tau k * (1 + alg.theta k)
        * primal_gap K g (alg.x k) sp.xhat sp.yhat
    ≤ alg.beta * ‖alg.x k - sp.xhat‖^2 + ‖alg.y k - sp.yhat‖^2
      + 2 * alg.beta * alg.tau (k-1) * (1 + alg.theta (k-1))
        * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
      - alg.beta * ‖xbar alg k - alg.x k‖^2
      - (1 - alg.delta^2) * ‖alg.y (k+1) - alg.y k‖^2 := by
    nlinarith [h20_s, hcos1, hcos2, hcos3, hK_bound_s, hnorm_sym, hnorm_sym2,
      h2βτD_nn, h2βθτb_P, hP_nn, hPkm1_nn, hD_nn, hβ_nn, h2β_nn, hδ_nn,
      hτk_pos, hτkm1_pos, h2β_pos, hsβ, hθτ, hβ_pos, hexpand]
  have hLHS_eq : (‖alg.x (k + 1) - sp.xhat‖^2 / 2
      + ‖alg.y (k + 1) - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau k * (1 + alg.theta k) * primal_gap K g (alg.x k) sp.xhat sp.yhat)
    = (alg.beta * ‖alg.x (k + 1) - sp.xhat‖^2 + ‖alg.y (k + 1) - sp.yhat‖^2
      + 2 * alg.beta * alg.tau k * (1 + alg.theta k)
        * primal_gap K g (alg.x k) sp.xhat sp.yhat) / (2 * alg.beta) := by
    field_simp [ne_of_gt hβ_pos, ne_of_gt h2β_pos]
  have hRHS_eq : (‖alg.x k - sp.xhat‖^2 / 2
      + ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau (k - 1) * (1 + alg.theta (k - 1))
        * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat
      - ‖xbar alg k - alg.x k‖^2 / 2
      - (1 - alg.delta^2) * ‖alg.y (k + 1) - alg.y k‖^2 / (2 * alg.beta))
    = (alg.beta * ‖alg.x k - sp.xhat‖^2 + ‖alg.y k - sp.yhat‖^2
      + 2 * alg.beta * alg.tau (k - 1) * (1 + alg.theta (k - 1))
        * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat
      - alg.beta * ‖xbar alg k - alg.x k‖^2
      - (1 - alg.delta^2) * ‖alg.y (k + 1) - alg.y k‖^2) / (2 * alg.beta) := by
    field_simp [ne_of_gt hβ_pos, ne_of_gt h2β_pos]
  constructor
  · rw [hLHS_eq, hRHS_eq]
    exact div_le_div_of_nonneg_right hgoal_s (le_of_lt h2β_pos)
  · -- Gap inequality: keep the D term; from h20_s and the cosine rules
    have h1mδ_nn : 0 ≤ 1 - alg.delta^2 := by
      have hδsq : alg.delta^2 < 1 := by
        have : alg.delta < 1 := alg.delta_pos.2
        nlinarith [le_of_lt alg.delta_pos.1]
      linarith
    have hxb2nn : 0 ≤ alg.beta * ‖xbar alg k - alg.x k‖^2 :=
      mul_nonneg hβ_nn (sq_nonneg _)
    have hynnn : 0 ≤ (1 - alg.delta^2) * ‖alg.y (k+1) - alg.y k‖^2 :=
      mul_nonneg h1mδ_nn (sq_nonneg _)
    -- β-scaled exact cosine equalities
    have hc1β := congrArg (fun r : ℝ => alg.beta * r) hcos1
    have hc3β := congrArg (fun r : ℝ => alg.beta * r) hcos3
    have hsymβ := congrArg (fun r : ℝ => alg.beta * r) hnorm_sym
    dsimp only at hc1β hc3β hsymβ
    -- x inner product sum keeps all negative residual terms
    have hA : 2 * alg.beta * ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
        + 2 * alg.beta * ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
        = alg.beta * ‖alg.x k - sp.xhat‖^2 - alg.beta * ‖alg.x (k+1) - sp.xhat‖^2
          - alg.beta * ‖xbar alg k - alg.x k‖^2
          - alg.beta * ‖xbar alg k - alg.x (k+1)‖^2 := by
      rw [show 2 * alg.beta * ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ
          = alg.beta * (2 * ⟪alg.x (k+1) - alg.x k, sp.xhat - alg.x (k+1)⟫_ℝ) from by ring,
        show 2 * alg.beta * ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ
          = alg.beta * (2 * ⟪xbar alg k - alg.x k, alg.x (k+1) - xbar alg k⟫_ℝ) from by ring]
      rw [hc1β, hc3β]
      have hs := hsymβ
      linarith
    -- expand the gap expression to match h20_s's RHS form
    have hrw : 2 * alg.beta * (alg.tau k * ((1 + alg.theta k)
          * primal_gap K g (alg.x k) sp.xhat sp.yhat
        - alg.theta k * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
        + dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat))
      = 2 * alg.beta * (alg.tau k * (1 + alg.theta k)
          * primal_gap K g (alg.x k) sp.xhat sp.yhat)
        - 2 * alg.beta * (alg.tau k * alg.theta k
          * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat)
        + 2 * alg.beta * (alg.tau k * dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat) := by
      ring
    have hmain : 2 * alg.beta * (alg.tau k * ((1 + alg.theta k)
        * primal_gap K g (alg.x k) sp.xhat sp.yhat
        - alg.theta k * primal_gap K g (alg.x (k-1)) sp.xhat sp.yhat
        + dual_gap K h (alg.y (k+1)) sp.yhat sp.xhat))
        ≤ (alg.beta * ‖alg.x k - sp.xhat‖^2 + ‖alg.y k - sp.yhat‖^2)
          - (alg.beta * ‖alg.x (k+1) - sp.xhat‖^2
            + ‖alg.y (k+1) - sp.yhat‖^2) := by
      have h1 := h20_s
      have hkb := hK_bound_s
      have h2 := hcos2
      have h4 := hexpand
      have hnn : 0 ≤ (1 - alg.delta^2) * ‖alg.y (k+1) - alg.y k‖^2 := hynnn
      have hnn2 : 0 ≤ alg.beta * ‖xbar alg k - alg.x k‖^2 := hxb2nn
      have hysq : 0 ≤ ‖alg.y (k+1) - alg.y k‖^2 := sq_nonneg _
      rw [hrw]
      linarith [hA, h1, hkb, h2, h4, hnn, hnn2, hysq]
    have hnorm : (alg.beta * ‖alg.x k - sp.xhat‖^2 + ‖alg.y k - sp.yhat‖^2)
        - (alg.beta * ‖alg.x (k+1) - sp.xhat‖^2 + ‖alg.y (k+1) - sp.yhat‖^2)
        = 2 * alg.beta * ((‖alg.x k - sp.xhat‖^2 / 2
            + ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta))
          - (‖alg.x (k+1) - sp.xhat‖^2 / 2
            + ‖alg.y (k+1) - sp.yhat‖^2 / (2 * alg.beta))) := by
      field_simp [ne_of_gt hβ_pos, ne_of_gt h2β_pos]
    rw [hnorm] at hmain
    exact le_of_mul_le_mul_left hmain h2β_pos

/-- Original energy inequality (eq. 24), recovered from the gap version. -/
theorem energy_inequality (alg : PDAL K g h) (sp : SaddlePoint K g h) (k : ℕ) (hk : k ≥ 1)
    (hxkm1 : alg.x (k - 1) ∈ g.dom) :
    ‖alg.x (k + 1) - sp.xhat‖^2 / 2
    + ‖alg.y (k + 1) - sp.yhat‖^2 / (2 * alg.beta)
    + alg.tau k * (1 + alg.theta k) * primal_gap K g (alg.x k) sp.xhat sp.yhat
  ≤ ‖alg.x k - sp.xhat‖^2 / 2
    + ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta)
    + alg.tau (k - 1) * (1 + alg.theta (k - 1)) * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat
    - ‖xbar alg k - alg.x k‖^2 / 2
    - (1 - alg.delta^2) * ‖alg.y (k + 1) - alg.y k‖^2 / (2 * alg.beta) :=
  (energy_inequality_with_gap alg sp k hk hxkm1).1

/-- Single-step gap inequality preserving the `D(y_{k+1})` term (used for
the ergodic rate). -/
theorem pdal_gap_step (alg : PDAL K g h) (sp : SaddlePoint K g h)
    (k : ℕ) (hk : 1 ≤ k) (hxkm1 : alg.x (k - 1) ∈ g.dom) :
    alg.tau k * ((1 + alg.theta k)
        * primal_gap K g (alg.x k) sp.xhat sp.yhat
      - alg.theta k * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat
      + dual_gap K h (alg.y (k + 1)) sp.yhat sp.xhat)
    ≤ (‖alg.x k - sp.xhat‖^2 / 2
        + ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta))
      - (‖alg.x (k + 1) - sp.xhat‖^2 / 2
        + ‖alg.y (k + 1) - sp.yhat‖^2 / (2 * alg.beta)) :=
  (energy_inequality_with_gap alg sp k hk hxkm1).2

/-- **Theorem 1 (Boundedness)**: The sequence (x^k, y^k) is bounded.

This follows from the energy inequality (24): for `k ≥ 2` the Lyapunov function
`a_k = ½‖x_k - x̂‖² + (1/(2β))‖y_k - ŷ‖² + τ_{k-1}(1+θ_{k-1})P(x_{k-1})`
is non-increasing (no assumption on `x 0` is needed, since `x 1, x 2 ∈ dom g`
holds automatically by `x_mem_dom`). The finitely many initial iterates are
bounded trivially. -/
theorem pdal_bounded (alg : PDAL K g h) (sp : SaddlePoint K g h) :
    IsBounded (Set.range fun k => (alg.x k, alg.y k)) := by
  -- Key positivity facts (needed early)
  have hβ_pos : 0 < alg.beta := alg.beta_pos
  have hτ_pos : ∀ k, 0 < alg.tau k := tau_pos alg
  -- Monotonicity a(k+1) ≤ a(k) for k ≥ 2, where
  -- a(k) = ‖x_k - x̂‖²/2 + ‖y_k - ŷ‖²/(2β) + τ_{k-1}(1+θ_{k-1})P(x_{k-1})
  have ha_mono : ∀ k ≥ 2,
      ‖alg.x (k + 1) - sp.xhat‖^2 / 2
      + ‖alg.y (k + 1) - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau k * (1 + alg.theta k)
        * primal_gap K g (alg.x k) sp.xhat sp.yhat
    ≤ ‖alg.x k - sp.xhat‖^2 / 2
      + ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau (k - 1) * (1 + alg.theta (k - 1))
        * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat := by
    intro k hk
    have h := energy_inequality alg sp k (by omega) (x_mem_dom alg (k - 1) (by omega))
    -- h: a(k+1) ≤ a(k) - ‖x̄^k - x^k‖²/2 - (1-δ²)‖y^{k+1}-y^k‖²/(2β)
    -- Since the subtracted terms are ≥ 0, a(k+1) ≤ a(k)
    have hδ_nn : 0 ≤ alg.delta := le_of_lt alg.delta_pos.1
    have h1mδsq_nn : 0 ≤ 1 - alg.delta ^ 2 := by
      have hδsq_lt1 : alg.delta ^ 2 < 1 := by
        have : alg.delta < 1 := alg.delta_pos.2
        nlinarith
      linarith
    have h1 : 0 ≤ ‖xbar alg k - alg.x k‖^2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
    have h2 : 0 ≤ (1 - alg.delta ^ 2) * ‖alg.y (k + 1) - alg.y k‖^2 / (2 * alg.beta) := by
      apply div_nonneg
      · exact mul_nonneg h1mδsq_nn (sq_nonneg _)
      · linarith
    linarith
  have hθ_nn : ∀ k, 0 ≤ alg.theta k := by
    intro k
    by_cases hk : k = 0
    · subst k; rw [alg.theta0_eq]; norm_num
    · have hk1 : k ≥ 1 := by omega
      rw [alg.theta_def k hk1]
      apply div_nonneg
      · exact le_of_lt (hτ_pos k)
      · exact le_of_lt (hτ_pos (k - 1))
  have hP_nn : ∀ k ≥ 2, 0 ≤ primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat := by
    intro k hk
    exact primal_gap_nonneg K g h sp (alg.x (k - 1)) (x_mem_dom alg (k - 1) (by omega))
  have hLyap_nn : ∀ k ≥ 2, 0 ≤ alg.tau (k - 1) * (1 + alg.theta (k - 1))
      * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat := by
    intro k hk
    exact mul_nonneg (mul_nonneg (le_of_lt (hτ_pos (k - 1)))
      (by linarith [hθ_nn (k - 1)])) (hP_nn k (by omega))
  -- Define a(2) as the reference Lyapunov value (finite: x 1, x 2 ∈ dom g)
  set a2 : ℝ := ‖alg.x 2 - sp.xhat‖^2 / 2
    + ‖alg.y 2 - sp.yhat‖^2 / (2 * alg.beta)
    + alg.tau 1 * (1 + alg.theta 1)
      * primal_gap K g (alg.x 1) sp.xhat sp.yhat with ha2_def
  -- Prove a(j) ≤ a(2) for all j ≥ 2 by induction
  have ha_bound : ∀ j ≥ 2,
      ‖alg.x j - sp.xhat‖^2 / 2
      + ‖alg.y j - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau (j - 1) * (1 + alg.theta (j - 1))
        * primal_gap K g (alg.x (j - 1)) sp.xhat sp.yhat
    ≤ a2 := by
    intro j
    induction j using Nat.strongRecOn with
    | ind j ih =>
      intro hj
      by_cases hj2 : j = 2
      · subst j; exact le_rfl
      -- j ≥ 3, so j - 1 ≥ 2
      have hjm1_ge2 : j - 1 ≥ 2 := by omega
      have hjm1_add : j - 1 + 1 = j := by omega
      have hstep := ha_mono (j - 1) hjm1_ge2
      rw [hjm1_add] at hstep
      have ihjm1 := ih (j - 1) (by omega) hjm1_ge2
      exact le_trans hstep ihjm1
  -- Common bound for all k ≥ 1 (k = 1 handled explicitly)
  set A : ℝ := max (max a2 (‖alg.x 1 - sp.xhat‖^2 / 2))
      (‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)) with hA_def
  have hx_sq : ∀ k ≥ 1, ‖alg.x k - sp.xhat‖^2 / 2 ≤ A := by
    intro k hk
    by_cases hk1 : k = 1
    · subst k
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    · have hk2 : k ≥ 2 := by omega
      have h1 : 0 ≤ ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta) :=
        div_nonneg (sq_nonneg _) (by linarith)
      have hR : 0 ≤ alg.tau (k - 1) * (1 + alg.theta (k - 1))
          * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat := hLyap_nn k hk2
      have hsum := ha_bound k hk2
      have hxk : ‖alg.x k - sp.xhat‖^2 / 2 ≤ a2 := by linarith
      exact le_trans hxk (le_trans (le_max_left _ _) (le_max_left _ _))
  have hy_sq : ∀ k ≥ 1, ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta) ≤ A := by
    intro k hk
    by_cases hk1 : k = 1
    · subst k; exact le_max_right _ _
    · have hk2 : k ≥ 2 := by omega
      have h1 : 0 ≤ ‖alg.x k - sp.xhat‖^2 / 2 :=
        div_nonneg (sq_nonneg _) (by norm_num)
      have hR : 0 ≤ alg.tau (k - 1) * (1 + alg.theta (k - 1))
          * primal_gap K g (alg.x (k - 1)) sp.xhat sp.yhat := hLyap_nn k hk2
      have hsum := ha_bound k hk2
      have hyk : ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta) ≤ a2 := by linarith
      exact le_trans hyk (le_trans (le_max_left _ _) (le_max_left _ _))
  exact PDALCodexHelp.boundedPairsOfSquareBounds
    alg.x alg.y sp.xhat sp.yhat alg.beta A hβ_pos hx_sq hy_sq

/-! ## Step size lower bound (Lemma 1(ii)) -/

/-- Lemma 1(ii): There exists `τ_min > 0` such that `τ_k ≥ τ_min` for all `k`.

The lower bound is `min{τ_0, δμ / (√β · ‖K‖)}`.
When `‖K‖ = 0`, all candidates are accepted (index 0), so `τ_k ≥ τ_0`.
When `‖K‖ > 0`, the rejected candidate `τ' = τ_trial · μ^{i-1}` must satisfy
`τ' > δ / (√β · ‖K‖)`, so `τ_k = τ' · μ > δμ / (√β · ‖K‖)`.
-/
theorem tau_lower_bound (alg : PDAL K g h) :
    ∃ τ_min : ℝ, 0 < τ_min ∧ ∀ k, τ_min ≤ alg.tau k := by
  set L := ‖K‖ with hL_def
  have hadj_norm : ‖(K† : Y →L[ℝ] X)‖ = ‖K‖ := LinearIsometryEquiv.norm_map _ _
  by_cases hL : L = 0
  · -- ‖K‖ = 0: accept_cond always holds, so ls_index k = 0 for all k ≥ 1
    have hK_adj_zero : ‖(K† : Y →L[ℝ] X)‖ = 0 := by
      rw [hadj_norm, ← hL_def, hL]
    have hKd_any : ∀ (v : Y), ‖(K†) v‖ = 0 := by
      intro v
      have hle : ‖(K†) v‖ ≤ ‖(K† : Y →L[ℝ] X)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      rw [hK_adj_zero] at hle
      simp at hle
      rw [hle]
      exact norm_zero
    have hls_zero : ∀ k ≥ 1, alg.ls_index k = 0 := by
      intro k hk
      by_contra h_ne
      have hls_pos : 1 ≤ alg.ls_index k := by omega
      have hrej := alg.ls_index_minimal k hk 0 (by omega)
      set τ' := alg.tau_trial k * alg.mu ^ (0 : ℕ)
      set yp := prox h (alg.beta * τ')
        (mul_pos alg.beta_pos
          (mul_pos (lt_of_lt_of_le (alg.tau_pos_all (k - 1)) (alg.tau_trial_range k hk).1)
            (pow_pos alg.mu_pos.1 0)))
        (alg.y k + (alg.beta * τ') • K
          (alg.x k + (τ' / alg.tau (k - 1)) • (alg.x k - alg.x (k - 1))))
      have haccept : accept_cond K alg.beta alg.delta τ' (alg.y k) yp := by
        simp only [accept_cond]
        rw [hKd_any (yp - alg.y k), mul_zero]
        exact mul_nonneg (le_of_lt alg.delta_pos.1) (norm_nonneg _)
      exact hrej haccept
    refine ⟨alg.tau 0, alg.tau0_pos, ?_⟩
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have hk1 : k + 1 ≥ 1 := by omega
      have hls := hls_zero (k + 1) hk1
      have htd := alg.tau_def (k + 1) hk1
      rw [htd, hls, pow_zero, mul_one]
      exact le_trans ih (alg.tau_trial_range (k + 1) hk1).1
  -- ‖K‖ > 0
  have hL_pos : 0 < L := by
    rcases lt_or_eq_of_le (norm_nonneg K) with h | h
    · exact h
    · exfalso; apply hL; rw [hL_def]; exact h.symm
  have h_sqrt_beta_pos : 0 < Real.sqrt alg.beta := Real.sqrt_pos.mpr alg.beta_pos
  have h_threshold : 0 < alg.delta * alg.mu / (Real.sqrt alg.beta * L) := by
    apply div_pos
    · exact mul_pos alg.delta_pos.1 alg.mu_pos.1
    · exact mul_pos h_sqrt_beta_pos hL_pos
  set τ_min := min (alg.tau 0) (alg.delta * alg.mu / (Real.sqrt alg.beta * L))
  refine ⟨τ_min, lt_min alg.tau0_pos h_threshold, ?_⟩
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    by_cases hk : k = 0
    · -- τ_min = min τ_0 threshold ≤ τ_0
      rw [hk]
      exact min_le_left (alg.tau 0) (alg.delta * alg.mu / (Real.sqrt alg.beta * L))
    have hk1 : k ≥ 1 := by omega
    have htd := alg.tau_def k hk1
    rw [htd]
    by_cases hls : alg.ls_index k = 0
    · -- ls_index k = 0: τ_k = tau_trial k ≥ tau(k-1) ≥ τ_min (IH)
      rw [hls, pow_zero, mul_one]
      have hr := alg.tau_trial_range k hk1
      exact le_trans (ih (k - 1) (by omega)) hr.1
    -- ls_index k ≥ 1: contradiction with accept_cond_of_small_tau
    have hls_pos : 1 ≤ alg.ls_index k := by omega
    by_contra h_not_gt
    push_neg at h_not_gt
    -- h_not_gt : τ_k < τ_min ≤ threshold, so τ_k < threshold
    have h_threshold' : alg.tau_trial k * alg.mu ^ (alg.ls_index k)
        ≤ alg.delta * alg.mu / (Real.sqrt alg.beta * L) :=
      le_of_lt (lt_of_lt_of_le h_not_gt
        (min_le_right (alg.tau 0) (alg.delta * alg.mu / (Real.sqrt alg.beta * L))))
    have htt_pos : 0 < alg.tau_trial k :=
      lt_of_lt_of_le (alg.tau_pos_all (k - 1)) (alg.tau_trial_range k hk1).1
    have hτ'_pos : 0 < alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1) :=
      mul_pos htt_pos (pow_pos alg.mu_pos.1 _)
    -- τ_k = τ' * μ where τ' = tau_trial k * mu^(ls_index k - 1)
    have hτk_decomp : alg.tau_trial k * alg.mu ^ (alg.ls_index k)
        = (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1)) * alg.mu := by
      have h1 : alg.ls_index k - 1 + 1 = alg.ls_index k := Nat.sub_add_cancel hls_pos
      nth_rw 1 [← h1]
      rw [pow_add, pow_one, ← mul_assoc]
    rw [hτk_decomp] at h_threshold'
    -- h_threshold' : τ' * μ ≤ δ * μ / (√β * L)
    have hmu_pos : 0 < alg.mu := alg.mu_pos.1
    have hsbL_pos : 0 < Real.sqrt alg.beta * L := mul_pos h_sqrt_beta_pos hL_pos
    -- √β * τ' * ‖K‖ ≤ δ
    have hsmall : Real.sqrt alg.beta * (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1)) * ‖K‖ ≤ alg.delta := by
      rw [← hL_def]
      -- From h_threshold': τ' * μ ≤ δ * μ / (√β * L)
      -- => τ' * μ * (√β * L) ≤ δ * μ  =>  τ' * (√β * L) ≤ δ  =>  √β * τ' * L ≤ δ
      have h1 : (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1)) * alg.mu * (Real.sqrt alg.beta * L)
          ≤ alg.delta * alg.mu :=
        (le_div_iff₀ hsbL_pos).mp h_threshold'
      have h2 : (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1)) * (Real.sqrt alg.beta * L) ≤ alg.delta := by
        nlinarith [h1, hmu_pos, hsbL_pos, h_sqrt_beta_pos, hL_pos, hτ'_pos, alg.delta_pos.1]
      rw [show Real.sqrt alg.beta * (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1)) * L
          = (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1)) * (Real.sqrt alg.beta * L) from by ring]
      exact h2
    -- Contradiction with ls_index_minimal
    have hbt'_pos : 0 < alg.beta * (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1)) :=
      mul_pos alg.beta_pos
        (mul_pos (lt_of_lt_of_le (alg.tau_pos_all (k - 1)) (alg.tau_trial_range k hk1).1)
          (pow_pos alg.mu_pos.1 (alg.ls_index k - 1)))
    have hrej := alg.ls_index_minimal k hk1 (alg.ls_index k - 1) (by omega)
    have haccept := accept_cond_of_small_tau K alg.beta_pos alg.delta_pos.1 hτ'_pos (alg.y k)
      (prox h (alg.beta * (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1))) hbt'_pos
        (alg.y k + (alg.beta * (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1))) • K
          (alg.x k + (alg.tau_trial k * alg.mu ^ (alg.ls_index k - 1) / alg.tau (k - 1)) •
            (alg.x k - alg.x (k - 1)))))
      hsmall
    exact hrej haccept

/-- Key residual estimates: ‖x̄_k - x_k‖ → 0 and ‖y_{k+1} - y_k‖ → 0.

These follow from the energy inequality: the Lyapunov function is
non-increasing and bounded below, so the telescoping negative terms must
converge to zero.
-/
lemma pdal_residuals_to_zero (alg : PDAL K g h) (sp : SaddlePoint K g h) :
    Tendsto (fun k => ‖xbar alg k - alg.x k‖) atTop (𝓝 0) ∧
    Tendsto (fun k => ‖alg.y (k + 1) - alg.y k‖) atTop (𝓝 0) := by
  have hβ_pos : 0 < alg.beta := alg.beta_pos
  have hτ_pos : ∀ k, 0 < alg.tau k := tau_pos alg
  have h1mδsq_nn : 0 ≤ 1 - alg.delta ^ 2 := by
    have : alg.delta ^ 2 < 1 := by nlinarith [alg.delta_pos.2, le_of_lt alg.delta_pos.1]
    linarith
  have h1mδsq_pos : 0 < 1 - alg.delta ^ 2 := by
    have : alg.delta ^ 2 < 1 := by nlinarith [alg.delta_pos.2, le_of_lt alg.delta_pos.1]
    linarith
  -- Lyapunov function: f(k) = E_{k+1} (shifted by one so that the energy
  -- inequality is available at every step, without assumptions on x 0)
  set f : ℕ → ℝ := fun k =>
    ‖alg.x (k + 2) - sp.xhat‖^2 / 2
    + ‖alg.y (k + 2) - sp.yhat‖^2 / (2 * alg.beta)
    + alg.tau (k + 1) * (1 + alg.theta (k + 1))
      * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat
  -- f is antitone: f(j+1) ≤ f(j) from energy_inequality at step (j+2) ≥ 2
  have hf_anti : Antitone f := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j _ ih =>
      have hj2 : j + 2 ≥ 2 := by omega
      have hstep := energy_inequality alg sp (j + 2) (by omega)
        (x_mem_dom alg (j + 1) (by omega))
      have hxb_nn : 0 ≤ ‖xbar alg (j + 2) - alg.x (j + 2)‖^2 / 2 :=
        div_nonneg (sq_nonneg _) (by norm_num)
      have hyn_nn : 0 ≤ (1 - alg.delta ^ 2) * ‖alg.y (j + 3) - alg.y (j + 2)‖^2 / (2 * alg.beta) := by
        apply div_nonneg
        · exact mul_nonneg h1mδsq_nn (sq_nonneg _)
        · linarith
      have hjm1 : j + 2 - 1 = j + 1 := by omega
      have hjp1 : j + 2 + 1 = j + 3 := by omega
      rw [hjm1, hjp1] at hstep
      have hfj : f (j + 1) ≤ f j := by
        show ‖alg.x (j + 1 + 2) - sp.xhat‖^2 / 2
            + ‖alg.y (j + 1 + 2) - sp.yhat‖^2 / (2 * alg.beta)
            + alg.tau (j + 1 + 1) * (1 + alg.theta (j + 1 + 1))
              * primal_gap K g (alg.x (j + 1 + 1)) sp.xhat sp.yhat
          ≤ ‖alg.x (j + 2) - sp.xhat‖^2 / 2
            + ‖alg.y (j + 2) - sp.yhat‖^2 / (2 * alg.beta)
            + alg.tau (j + 1) * (1 + alg.theta (j + 1))
              * primal_gap K g (alg.x (j + 1)) sp.xhat sp.yhat
        rw [show j + 1 + 2 = j + 3 from rfl, show j + 1 + 1 = j + 2 from rfl]
        linarith [hstep, hxb_nn, hyn_nn]
      exact le_trans hfj ih
  -- f is bounded below by 0
  have hf_bdd : BddBelow (Set.range f) := by
    rw [BddBelow]
    refine ⟨0, ?_⟩
    intro b hb
    rw [Set.mem_range] at hb
    obtain ⟨k, hk⟩ := hb
    subst hk
    show 0 ≤ f k
    have h1 : 0 ≤ ‖alg.x (k + 2) - sp.xhat‖^2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
    have h2 : 0 ≤ ‖alg.y (k + 2) - sp.yhat‖^2 / (2 * alg.beta) :=
      div_nonneg (sq_nonneg _) (by linarith)
    have hP_nn : 0 ≤ primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat :=
      primal_gap_nonneg K g h sp (alg.x (k + 1)) (x_mem_dom alg (k + 1) (by omega))
    have hθ_nn : 0 ≤ 1 + alg.theta (k + 1) := by
      have : 0 ≤ alg.theta (k + 1) := by
        have hk1 : k + 1 ≥ 1 := by omega
        rw [alg.theta_def (k + 1) hk1]
        apply div_nonneg
        · exact le_of_lt (hτ_pos (k + 1))
        · exact le_of_lt (hτ_pos (k + 1 - 1))
      linarith
    have h3 : 0 ≤ alg.tau (k + 1) * (1 + alg.theta (k + 1))
        * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat :=
      mul_nonneg (mul_nonneg (le_of_lt (hτ_pos (k + 1))) hθ_nn) hP_nn
    show 0 ≤ f k
    rw [show f k = ‖alg.x (k + 2) - sp.xhat‖^2 / 2
        + ‖alg.y (k + 2) - sp.yhat‖^2 / (2 * alg.beta)
        + alg.tau (k + 1) * (1 + alg.theta (k + 1))
          * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat from rfl]
    linarith
  -- Residual: c(k) = ‖x̄_{k+2} - x_{k+2}‖²/2 + (1-δ²)‖y_{k+3} - y_{k+2}‖²/(2β)
  set c : ℕ → ℝ := fun k =>
    ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2
    + (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta)
  have hc_diff : ∀ k, c k ≤ f k - f (k + 1) := by
    intro k
    have hk2 : k + 2 ≥ 2 := by omega
    have hstep := energy_inequality alg sp (k + 2) (by omega)
      (x_mem_dom alg (k + 1) (by omega))
    have hkm1 : k + 2 - 1 = k + 1 := by omega
    have hkp1 : k + 2 + 1 = k + 3 := by omega
    rw [hkm1, hkp1] at hstep
    show c k ≤ f k - f (k + 1)
    rw [show f k = ‖alg.x (k + 2) - sp.xhat‖^2 / 2
            + ‖alg.y (k + 2) - sp.yhat‖^2 / (2 * alg.beta)
            + alg.tau (k + 1) * (1 + alg.theta (k + 1))
              * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat from rfl,
        show f (k + 1) = ‖alg.x (k + 1 + 2) - sp.xhat‖^2 / 2
            + ‖alg.y (k + 1 + 2) - sp.yhat‖^2 / (2 * alg.beta)
            + alg.tau (k + 1 + 1) * (1 + alg.theta (k + 1 + 1))
              * primal_gap K g (alg.x (k + 1 + 1)) sp.xhat sp.yhat from rfl,
        show c k = ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2
            + (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta) from rfl]
    rw [show k + 1 + 2 = k + 3 from rfl, show k + 1 + 1 = k + 2 from rfl]
    linarith [hstep]
  have hc_nn : ∀ k, 0 ≤ c k := by
    intro k
    show 0 ≤ ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2
        + (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta)
    have h1 : 0 ≤ ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
    have h2 : 0 ≤ (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta) := by
      apply div_nonneg
      · exact mul_nonneg h1mδsq_nn (sq_nonneg _)
      · linarith
    linarith
  have hc_zero := PDALCodexHelp.tendsto_zero_of_antitone_diff hf_anti hf_bdd hc_diff hc_nn
  -- From c(k) → 0: ‖x̄_{k+2} - x_{k+2}‖²/2 ≤ c(k) → 0
  have hxb_le_c : ∀ k, ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2 ≤ c k := by
    intro k
    show ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2
        ≤ ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2
          + (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta)
    have h2_nn : 0 ≤ (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta) := by
      apply div_nonneg
      · exact mul_nonneg h1mδsq_nn (sq_nonneg _)
      · linarith
    linarith
  have hxb_sq_zero : Tendsto (fun k => ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hc_zero (fun k => div_nonneg (sq_nonneg _) (by norm_num)) hxb_le_c
  have hxb_sq2_zero : Tendsto (fun k => ‖xbar alg (k + 2) - alg.x (k + 2)‖^2) atTop (𝓝 0) := by
    have heq : (fun k => ‖xbar alg (k + 2) - alg.x (k + 2)‖^2)
        = fun k => 2 * (‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2) := by ext k; ring
    rw [heq]
    have h2 := hxb_sq_zero.const_mul 2
    simpa [mul_zero] using h2
  have hxb_norm_zero : Tendsto (fun k => ‖xbar alg (k + 2) - alg.x (k + 2)‖) atTop (𝓝 0) := by
    have heq : (fun k => ‖xbar alg (k + 2) - alg.x (k + 2)‖)
        = fun k => Real.sqrt (‖xbar alg (k + 2) - alg.x (k + 2)‖^2) := by
      ext k; exact (Real.sqrt_sq (norm_nonneg _)).symm
    rw [heq]
    have h2 := hxb_sq2_zero.sqrt
    simpa [Real.sqrt_zero] using h2
  have hxb_zero : Tendsto (fun k => ‖xbar alg k - alg.x k‖) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 2]
    exact hxb_norm_zero
  -- (1-δ²)‖y_{k+3} - y_{k+2}‖²/(2β) ≤ c(k) → 0
  have hyn_le_c : ∀ k,
      (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta) ≤ c k := by
    intro k
    show (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta)
        ≤ ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2
          + (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta)
    have h1_nn : 0 ≤ ‖xbar alg (k + 2) - alg.x (k + 2)‖^2 / 2 :=
      div_nonneg (sq_nonneg _) (by norm_num)
    linarith
  have hyn_sq_zero : Tendsto (fun k =>
      (1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hc_zero
      (fun k => by
        apply div_nonneg
        · exact mul_nonneg h1mδsq_nn (sq_nonneg _)
        · linarith)
      hyn_le_c
  have hyn_sq2_zero : Tendsto (fun k => ‖alg.y (k + 3) - alg.y (k + 2)‖^2) atTop (𝓝 0) := by
    have hfac : (2 * alg.beta) / (1 - alg.delta ^ 2) = 2 * alg.beta / (1 - alg.delta ^ 2) := rfl
    have heq : (fun k => ‖alg.y (k + 3) - alg.y (k + 2)‖^2)
        = fun k => (2 * alg.beta / (1 - alg.delta ^ 2))
          * ((1 - alg.delta ^ 2) * ‖alg.y (k + 3) - alg.y (k + 2)‖^2 / (2 * alg.beta)) := by
      ext k
      field_simp
    rw [heq]
    have h2 := hyn_sq_zero.const_mul (2 * alg.beta / (1 - alg.delta ^ 2))
    simpa [mul_zero] using h2
  have hyn_norm_zero : Tendsto (fun k => ‖alg.y (k + 3) - alg.y (k + 2)‖) atTop (𝓝 0) := by
    have heq : (fun k => ‖alg.y (k + 3) - alg.y (k + 2)‖)
        = fun k => Real.sqrt (‖alg.y (k + 3) - alg.y (k + 2)‖^2) := by
      ext k; exact (Real.sqrt_sq (norm_nonneg _)).symm
    rw [heq]
    have h2 := hyn_sq2_zero.sqrt
    simpa [Real.sqrt_zero] using h2
  have hyn_zero : Tendsto (fun k => ‖alg.y (k + 1) - alg.y k‖) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 2]
    exact hyn_norm_zero
  exact ⟨hxb_zero, hyn_zero⟩

/-- LSC limit lemma: if z_n → z* in dom, f(z_n) ≤ c_n, c_n → c, then z* ∈ dom and f(z*) ≤ c.

This uses the sublevel-set characterization of lower semicontinuity
from `ProperConvex.lsc`.
-/
lemma ProperConvex.lsc_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [ProperSpace E] (G : ProperConvex E)
    {z : ℕ → E} {zstar : E} {c : ℕ → ℝ} {clim : ℝ}
    (hz : Tendsto z atTop (𝓝 zstar))
    (hz_dom : ∀ n, z n ∈ G.dom)
    (hf : ∀ n, G.f (z n) ≤ c n)
    (hc : Tendsto c atTop (𝓝 clim)) :
    zstar ∈ G.dom ∧ G.f zstar ≤ clim := by
  -- For any ε > 0, eventually c_n < clim + ε, so f(z_n) ≤ clim + ε.
  -- {z ∈ dom | f z ≤ clim + ε} is closed, so z* is in it.
  -- Since this holds for all ε > 0, f(z*) ≤ clim.
  -- For dom membership: dom = {z | f z ≤ M} for some M (from affine minorant),
  -- but more directly, we use the closed set {z ∈ dom | f z ≤ clim + 1}.
  -- z_n is eventually in this set, so z* is in it, hence z* ∈ dom.
  have hε : ∀ ε > (0 : ℝ), zstar ∈ G.dom ∧ G.f zstar ≤ clim + ε := by
    intro ε hε_pos
    have hset_closed : IsClosed {w : E | w ∈ G.dom ∧ G.f w ≤ clim + ε} := G.lsc (clim + ε)
    -- Eventually |c_n - clim| < ε, so c_n < clim + ε, so f(z_n) ≤ c_n ≤ clim + ε
    have hc_event : ∀ᶠ n in atTop, c n ≤ clim + ε := by
      rw [Metric.tendsto_nhds] at hc
      have hev := hc ε hε_pos
      apply hev.mono
      intro n hn
      have hdist : dist (c n) clim < ε := hn
      have habs : |c n - clim| < ε := by rw [Real.dist_eq] at hdist; exact hdist
      have : c n - clim < ε := by
        rcases lt_or_ge (c n) clim with h | h
        · linarith
        · have hnn : 0 ≤ c n - clim := sub_nonneg.mpr h
          have := abs_of_nonneg hnn
          rw [this] at habs
          exact habs
      linarith
    have h_event : ∀ᶠ n in atTop, z n ∈ {w : E | w ∈ G.dom ∧ G.f w ≤ clim + ε} := by
      apply hc_event.mono
      intro n hn
      simp only [Set.mem_setOf]
      refine ⟨hz_dom n, ?_⟩
      exact le_trans (hf n) hn
    exact hset_closed.mem_of_tendsto hz h_event
  -- Get dom membership from ε = 1
  have hdom := (hε 1 (by norm_num)).1
  -- Get f(z*) ≤ clim: for all ε > 0, f(z*) ≤ clim + ε, so f(z*) ≤ clim
  have hfle : G.f zstar ≤ clim := by
    by_contra hneg
    push_neg at hneg
    have heps : 0 < (G.f zstar - clim) / 2 := by linarith
    have h1 := (hε _ heps).2
    linarith
  exact ⟨hdom, hfle⟩

/-- A point `p` is a cluster point of a sequence `u : ℕ → X` if there exists
a strictly monotone subsequence converging to `p`. -/
def IsClusterPoint {Z : Type*} [TopologicalSpace Z] (u : ℕ → Z) (p : Z) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 p)

/-- **Theorem 1 (Cluster points are saddle points)**: Every cluster point
of the PDAL sequence is a saddle point of (1).

This follows from the energy inequality: ‖x̄_k - x_k‖ → 0 and
‖y_{k+1} - y_k‖ → 0, so any cluster point satisfies the variational
inequality characterizing saddle points.
-/
theorem pdal_cluster_point_saddle (alg : PDAL K g h) (sp : SaddlePoint K g h) :
    ∀ (xstar : X) (ystar : Y),
      IsClusterPoint (fun k => (alg.x k, alg.y k)) (xstar, ystar) →
      IsSaddlePoint K g h xstar ystar := by
  intro xstar ystar hcl
  obtain ⟨φ, hφmono, hφtend⟩ := hcl
  obtain ⟨hxb, hyd⟩ := pdal_residuals_to_zero alg sp
  obtain ⟨τmin, hτmin_pos, hτmin_le⟩ := tau_lower_bound alg
  have hτpos : ∀ k, 0 < alg.tau k := tau_pos alg
  have hβpos : 0 < alg.beta := alg.beta_pos
  -- pair convergence along φ, and along the shifted subsequence n ↦ φ (n+1)
  have hpair : Tendsto (fun n => (alg.x (φ n), alg.y (φ n))) atTop (𝓝 (xstar, ystar)) := hφtend
  have hψpair : Tendsto (fun n => (alg.x (φ (n + 1)), alg.y (φ (n + 1)))) atTop
      (𝓝 (xstar, ystar)) := (tendsto_add_atTop_iff_nat 1).mpr hpair
  have hxψ : Tendsto (fun n => alg.x (φ (n + 1))) atTop (𝓝 xstar) :=
    (continuous_fst.tendsto' (xstar, ystar) xstar rfl).comp hψpair
  have hyψ : Tendsto (fun n => alg.y (φ (n + 1))) atTop (𝓝 ystar) :=
    (continuous_snd.tendsto' (xstar, ystar) ystar rfl).comp hψpair
  -- residuals along the shifted subsequence
  have hxbψ0 : Tendsto (fun n => ‖xbar alg (φ (n + 1)) - alg.x (φ (n + 1))‖) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hxb.comp hφmono.tendsto_atTop)
  have hΔyψ0 : Tendsto (fun n => ‖alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))‖) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hyd.comp hφmono.tendsto_atTop)
  have hy1ψ : Tendsto (fun n => alg.y (φ (n + 1) + 1)) atTop (𝓝 ystar) := by
    have h := hyψ.add ((tendsto_zero_iff_norm_tendsto_zero).mpr hΔyψ0)
    simpa using h
  have hxbψ : Tendsto (fun n => xbar alg (φ (n + 1))) atTop (𝓝 xstar) := by
    have h := hxψ.add ((tendsto_zero_iff_norm_tendsto_zero).mpr hxbψ0)
    simpa using h
  -- every index φ (n+1) is ≥ 1
  have hψ1 : ∀ n, 1 ≤ φ (n + 1) := by
    intro n
    have h1 : n + 1 ≤ φ (n + 1) := StrictMono.id_le hφmono (n + 1)
    omega
  -- key identity: (x_k - x_{k-1})/τ_{k-1} = (x̄_k - x_k)/τ_k for k ≥ 1
  have hw_eq : ∀ k ≥ 1, (1 / alg.tau (k - 1)) • (alg.x k - alg.x (k - 1))
      = (1 / alg.tau k) • (xbar alg k - alg.x k) := by
    intro k hk1
    have hθ : alg.theta k = alg.tau k / alg.tau (k - 1) := alg.theta_def k hk1
    show (1 / alg.tau (k - 1)) • (alg.x k - alg.x (k - 1))
        = (1 / alg.tau k) • ((alg.x k + alg.theta k • (alg.x k - alg.x (k - 1))) - alg.x k)
    rw [add_sub_cancel_left, hθ, smul_smul, div_eq_inv_mul]
    have hk0 : alg.tau k ≠ 0 := ne_of_gt (hτpos k)
    have hk0' : alg.tau (k - 1) ≠ 0 := ne_of_gt (hτpos (k - 1))
    congr 1
    field_simp
  -- the normalized primal increment tends to 0 along the shifted subsequence
  have hwψ : Tendsto (fun n => (1 / alg.tau (φ (n + 1) - 1)) •
      (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hupper : ∀ n, (1 / alg.tau (φ (n + 1) - 1)) *
        ‖alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)‖
        ≤ (1 / τmin) * ‖xbar alg (φ (n + 1)) - alg.x (φ (n + 1))‖ := by
      intro n
      have hk1 := hψ1 n
      have hsm : (1 / alg.tau (φ (n + 1) - 1)) •
          (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1))
          = (1 / alg.tau (φ (n + 1))) • (xbar alg (φ (n + 1)) - alg.x (φ (n + 1))) :=
        hw_eq (φ (n + 1)) hk1
      calc (1 / alg.tau (φ (n + 1) - 1)) * ‖alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)‖
          = ‖(1 / alg.tau (φ (n + 1) - 1)) •
              (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1))‖ := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (div_pos one_pos (hτpos (φ (n + 1) - 1)))]
        _ = ‖(1 / alg.tau (φ (n + 1))) • (xbar alg (φ (n + 1)) - alg.x (φ (n + 1)))‖ := by
            rw [hsm]
        _ = (1 / alg.tau (φ (n + 1))) * ‖xbar alg (φ (n + 1)) - alg.x (φ (n + 1))‖ := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (div_pos one_pos (hτpos (φ (n + 1))))]
        _ ≤ (1 / τmin) * ‖xbar alg (φ (n + 1)) - alg.x (φ (n + 1))‖ := by
            exact mul_le_mul_of_nonneg_right
              (div_le_div₀ zero_le_one (le_refl 1) hτmin_pos (hτmin_le (φ (n + 1))))
              (norm_nonneg _)
    have hnonneg : (fun n : ℕ => (1 / τmin) * 0) ≤ fun n =>
        (1 / alg.tau (φ (n + 1) - 1)) *
        ‖alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)‖ := by
      intro n
      simp only [mul_zero]
      exact mul_nonneg (le_of_lt (div_pos one_pos (hτpos (φ (n + 1) - 1))))
        (norm_nonneg (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)))
    have hlim : Tendsto (fun n => (1 / τmin) *
        ‖xbar alg (φ (n + 1)) - alg.x (φ (n + 1))‖) atTop (𝓝 ((1 / τmin) * 0)) :=
      hxbψ0.const_mul (1 / τmin)
    have hsq0 : ∀ n, ‖(1 / alg.tau (φ (n + 1) - 1)) •
        (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1))‖
        = (1 / alg.tau (φ (n + 1) - 1)) *
          ‖alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)‖ := fun n => by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos one_pos (hτpos (φ (n + 1) - 1)))]
    have hsqueeze : Tendsto (fun n => (1 / alg.tau (φ (n + 1) - 1)) *
        ‖alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)‖) atTop
        (𝓝 ((1 / τmin) * 0)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        hnonneg hupper
    have hfinal : Tendsto (fun n => ‖(1 / alg.tau (φ (n + 1) - 1)) •
        (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1))‖) atTop (𝓝 0) := by
      have hconv : Tendsto (fun n => (1 / alg.tau (φ (n + 1) - 1)) *
          ‖alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)‖) atTop (𝓝 0) := by
        have : (1 / τmin) * 0 = 0 := mul_zero _
        rw [this] at hsqueeze
        exact hsqueeze
      exact Tendsto.congr (fun n => (hsq0 n).symm) hconv
    exact hfinal
  -- the scaled dual increment tends to 0 along the shifted subsequence
  have hΔyψ : Tendsto (fun n => (1 / (alg.beta * alg.tau (φ (n + 1)))) •
      (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1)))) atTop (𝓝 0) :=
    scaled_smul_tendsto_zero alg.beta τmin hβpos hτmin_pos
      (fun n => alg.tau (φ (n + 1))) (fun n => hτpos (φ (n + 1)))
      (fun n => hτmin_le (φ (n + 1)))
      (fun n => alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))) hΔyψ0
  -- primal variational inequality at (xstar, ystar)
  have primal_vi : ∀ x ∈ g.dom, xstar ∈ g.dom ∧
      g.f xstar ≤ g.f x + ⟪(K†) ystar, x - xstar⟫_ℝ := by
    intro x hxd
    have hKy : Tendsto (fun n => (K†) (alg.y (φ (n + 1)))) atTop (𝓝 ((K†) ystar)) :=
      ((K†).continuous.tendsto' ystar ((K†) ystar) rfl).comp hyψ
    have hu : Tendsto (fun n => (1 / alg.tau (φ (n + 1) - 1)) •
        (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1))))
        atTop (𝓝 ((K†) ystar)) := by
      have h := hwψ.add hKy
      simpa using h
    have hinner : Tendsto (fun n => ⟪(1 / alg.tau (φ (n + 1) - 1)) •
        (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1))),
          x - alg.x (φ (n + 1))⟫_ℝ) atTop (𝓝 (⟪(K†) ystar, x - xstar⟫_ℝ)) :=
      Filter.Tendsto.inner hu (tendsto_const_nhds.sub hxψ)
    have hopt : ∀ n, g.f (alg.x (φ (n + 1))) ≤ g.f x + ⟪(1 / alg.tau (φ (n + 1) - 1)) •
        (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1))),
          x - alg.x (φ (n + 1))⟫_ℝ := by
      intro n
      have hk1 := hψ1 n
      have hpu := alg.primal_update (φ (n + 1)) hk1
      have hopt' := prox_scale_optimality g (hτpos (φ (n + 1) - 1)) _ hpu x hxd
      have hvec : alg.x (φ (n + 1)) - (alg.x (φ (n + 1) - 1)
            - (alg.tau (φ (n + 1) - 1)) • (K†) (alg.y (φ (n + 1))))
          = (alg.tau (φ (n + 1) - 1)) • ((1 / alg.tau (φ (n + 1) - 1)) •
              (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1)))) := by
        rw [smul_add]
        have h1 : (alg.tau (φ (n + 1) - 1)) • ((1 / alg.tau (φ (n + 1) - 1)) •
            (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)))
            = alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1) := by
          rw [smul_smul, div_eq_inv_mul, mul_one,
            mul_inv_cancel₀ (ne_of_gt (hτpos (φ (n + 1) - 1))), one_smul]
        rw [h1]
        congr 1
        module
      rw [hvec, real_inner_smul_left] at hopt'
      have h2 : alg.tau (φ (n + 1) - 1) * (g.f (alg.x (φ (n + 1))) - g.f x)
          ≤ alg.tau (φ (n + 1) - 1) * ⟪(1 / alg.tau (φ (n + 1) - 1)) •
              (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1))),
            x - alg.x (φ (n + 1))⟫_ℝ := by linarith
      have h3 : g.f (alg.x (φ (n + 1))) ≤ g.f x + ⟪(1 / alg.tau (φ (n + 1) - 1)) •
          (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1))),
          x - alg.x (φ (n + 1))⟫_ℝ := by
        have h3' := le_of_mul_le_mul_left h2 (hτpos (φ (n + 1) - 1))
        have heq : ⟪(1 / alg.tau (φ (n + 1) - 1)) •
            (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1))),
            x - alg.x (φ (n + 1))⟫_ℝ + g.f x
            = g.f x + ⟪(1 / alg.tau (φ (n + 1) - 1)) •
            (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1))),
            x - alg.x (φ (n + 1))⟫_ℝ := add_comm _ _
        linarith
      exact h3
    -- lsc_limit 需要上界序列 c_n = g.f x + ⟪w_n, x - x_n⟫ 趋于 g.f x + ⟪(K†) ystar, x - xstar⟫
    have hc'' : Tendsto (fun n => g.f x + ⟪(1 / alg.tau (φ (n + 1) - 1)) •
        (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) + (K†) (alg.y (φ (n + 1))),
          x - alg.x (φ (n + 1))⟫_ℝ) atTop
        (𝓝 (g.f x + ⟪(K†) ystar, x - xstar⟫_ℝ)) :=
      (tendsto_const_nhds : Tendsto (fun _ => g.f x) atTop (𝓝 (g.f x))).add hinner
    exact ProperConvex.lsc_limit g hxψ
      (fun n => (alg.primal_update (φ (n + 1)) (hψ1 n)).1) hopt hc''
  -- dual variational inequality at (xstar, ystar)
  have dual_vi : ∀ y ∈ h.dom, ystar ∈ h.dom ∧
      h.f ystar ≤ h.f y - ⟪K xstar, y - ystar⟫_ℝ := by
    intro y hyd
    have hKx : Tendsto (fun n => K (xbar alg (φ (n + 1)))) atTop (𝓝 (K xstar)) :=
      (K.continuous.tendsto' xstar (K xstar) rfl).comp hxbψ
    have hv : Tendsto (fun n => (1 / (alg.beta * alg.tau (φ (n + 1)))) •
        (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))) - K (xbar alg (φ (n + 1))))
        atTop (𝓝 (-(K xstar))) := by
      have h := Filter.Tendsto.sub hΔyψ hKx
      simpa using h
    have hinner : Tendsto (fun n => ⟪(1 / (alg.beta * alg.tau (φ (n + 1)))) •
        (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))) - K (xbar alg (φ (n + 1))),
          y - alg.y (φ (n + 1) + 1)⟫_ℝ) atTop (𝓝 (⟪-(K xstar), y - ystar⟫_ℝ)) :=
      Filter.Tendsto.inner hv (tendsto_const_nhds.sub hy1ψ)
    have hopt : ∀ n, h.f (alg.y (φ (n + 1) + 1)) ≤ ⟪(1 / (alg.beta * alg.tau (φ (n + 1)))) •
        (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))) - K (xbar alg (φ (n + 1))),
          y - alg.y (φ (n + 1) + 1)⟫_ℝ + h.f y := by
      intro n
      have hk1 := hψ1 n
      have hdu := alg.dual_update (φ (n + 1)) hk1
      have hopt' := prox_scale_optimality h (mul_pos hβpos (hτpos (φ (n + 1)))) _ hdu y hyd
      have hxbar : xbar alg (φ (n + 1)) = alg.x (φ (n + 1)) + alg.theta (φ (n + 1)) •
          (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1)) := rfl
      have hvec : alg.y (φ (n + 1) + 1) - (alg.y (φ (n + 1)) + (alg.beta * alg.tau (φ (n + 1))) •
            K (xbar alg (φ (n + 1))))
          = (alg.beta * alg.tau (φ (n + 1))) • ((1 / (alg.beta * alg.tau (φ (n + 1)))) •
              (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))) - K (xbar alg (φ (n + 1)))) := by
        have hsmul : (alg.beta * alg.tau (φ (n + 1))) •
            ((1 / (alg.beta * alg.tau (φ (n + 1)))) •
              (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))))
            = alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1)) := by
          rw [smul_smul, div_eq_inv_mul, mul_one,
            mul_inv_cancel₀ (ne_of_gt (mul_pos hβpos (hτpos (φ (n + 1))))), one_smul]
        rw [sub_add_eq_sub_sub, smul_sub, hsmul]
        -- hvec 证明完成后不再改写 hopt' 的 xbar；h2 直接由 hopt' 取得
      -- hopt' 内层 K 已展开为 hxbar 的形式，无需再改写 xbar
      have h2 : alg.beta * alg.tau (φ (n + 1)) * (h.f (alg.y (φ (n + 1) + 1)) - h.f y)
          ≤ alg.beta * alg.tau (φ (n + 1)) * ⟪(1 / (alg.beta * alg.tau (φ (n + 1)))) •
              (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))) - K (xbar alg (φ (n + 1))),
            y - alg.y (φ (n + 1) + 1)⟫_ℝ := by
        -- 先用 hxbar 反向把 hopt' 的 K(...) 改写为 K(x̄)，再用 hvec 折叠
        rw [show K (alg.x (φ (n + 1)) + alg.theta (φ (n + 1)) •
          (alg.x (φ (n + 1)) - alg.x (φ (n + 1) - 1))) = K (xbar alg (φ (n + 1))) from by rw [hxbar]] at hopt'
        rw [hvec, real_inner_smul_left] at hopt'
        linarith [hopt']
      have h3 : h.f (alg.y (φ (n + 1) + 1)) ≤ ⟪(1 / (alg.beta * alg.tau (φ (n + 1)))) •
          (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))) - K (xbar alg (φ (n + 1))),
          y - alg.y (φ (n + 1) + 1)⟫_ℝ + h.f y := by
        have := le_of_mul_le_mul_left h2 (mul_pos hβpos (hτpos (φ (n + 1))))
        linarith
      exact h3
    have hclim : Tendsto (fun n => ⟪(1 / (alg.beta * alg.tau (φ (n + 1)))) •
        (alg.y (φ (n + 1) + 1) - alg.y (φ (n + 1))) - K (xbar alg (φ (n + 1))),
          y - alg.y (φ (n + 1) + 1)⟫_ℝ + h.f y) atTop
        (𝓝 (⟪-(K xstar), y - ystar⟫_ℝ + h.f y)) :=
      hinner.add (tendsto_const_nhds : Tendsto (fun _ => h.f y) atTop (𝓝 (h.f y)))
    obtain ⟨hymem, hyineq⟩ := ProperConvex.lsc_limit h hy1ψ
      (fun n => (alg.dual_update (φ (n + 1)) (hψ1 n)).1) hopt hclim
    refine ⟨hymem, ?_⟩
    have hneg : ⟪-(K xstar), y - ystar⟫_ℝ = -⟪K xstar, y - ystar⟫_ℝ := by
      rw [inner_neg_left]
    rw [hneg] at hyineq
    linarith
  obtain ⟨x0, hx0⟩ := g.dom_nonempty
  obtain ⟨y0, hy0⟩ := h.dom_nonempty
  exact ⟨(primal_vi x0 hx0).1, (dual_vi y0 hy0).1,
    fun x hx => (primal_vi x hx).2, fun y hy => (dual_vi y hy).2⟩

/-- 有界序列存在一个鞍点聚点（Theorem 1 收敛性的第一步：紧性提取 + 聚点鞍点）。 -/
theorem pdal_has_saddle_cluster_point (alg : PDAL K g h) (sp : SaddlePoint K g h) :
    ∃ xstar ystar,
      IsClusterPoint (fun k => (alg.x k, alg.y k)) (xstar, ystar) ∧
      IsSaddlePoint K g h xstar ystar := by
  have hc : IsCompact (closure (Set.range (fun k => (alg.x k, alg.y k)))) := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨isClosed_closure, (pdal_bounded alg sp).closure⟩
  have hf : ∃ᶠ n in atTop,
      (alg.x n, alg.y n) ∈ closure (Set.range (fun k => (alg.x k, alg.y k))) :=
    Frequently.of_forall (fun n => subset_closure (Set.mem_range_self n))
  obtain ⟨z, hz, φ, hφ, ht⟩ := hc.isSeqCompact.subseq_of_frequently_in hf
  have hcluster : IsClusterPoint (fun k => (alg.x k, alg.y k)) (z.1, z.2) :=
    ⟨φ, hφ, ht⟩
  exact ⟨z.1, z.2, hcluster, pdal_cluster_point_saddle alg sp z.1 z.2 hcluster⟩

/-- Lyapunov 能量函数：`E_n = ½‖x_{n+2}-x̂‖² + ‖y_{n+2}-ŷ‖²/(2β)
+ τ_{n+1}(1+θ_{n+1})P(x_{n+1})`。

平移 2 使得能量不等式在每一步都可用（x_1, x_2 ∈ dom g 由 x_mem_dom 自动给出，
不需要 x₀ ∈ dom g）。 -/
def pdal_lyapunov (alg : PDAL K g h) (sp : SaddlePoint K g h) (n : ℕ) : ℝ :=
  ‖alg.x (n + 2) - sp.xhat‖^2 / 2
  + ‖alg.y (n + 2) - sp.yhat‖^2 / (2 * alg.beta)
  + alg.tau (n + 1) * (1 + alg.theta (n + 1))
    * primal_gap K g (alg.x (n + 1)) sp.xhat sp.yhat

/-- Lyapunov 能量非负。 -/
lemma pdal_lyapunov_nonneg (alg : PDAL K g h) (sp : SaddlePoint K g h) :
    ∀ n, 0 ≤ pdal_lyapunov alg sp n := by
  intro n
  have hτ_pos : ∀ k, 0 < alg.tau k := tau_pos alg
  have h1 : 0 ≤ ‖alg.x (n + 2) - sp.xhat‖^2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
  have h2 : 0 ≤ ‖alg.y (n + 2) - sp.yhat‖^2 / (2 * alg.beta) := by
    have hβ : 0 < 2 * alg.beta := by exact mul_pos two_pos alg.beta_pos
    exact div_nonneg (sq_nonneg _) hβ.le
  have hP_nn : 0 ≤ primal_gap K g (alg.x (n + 1)) sp.xhat sp.yhat :=
    primal_gap_nonneg K g h sp (alg.x (n + 1)) (x_mem_dom alg (n + 1) (by omega))
  have hθ_nn : 0 ≤ alg.theta (n + 1) := by
    have hk1 : n + 1 ≥ 1 := by omega
    rw [alg.theta_def (n + 1) hk1]
    apply div_nonneg
    · exact le_of_lt (hτ_pos (n + 1))
    · exact le_of_lt (hτ_pos n)
  have h3 : 0 ≤ alg.tau (n + 1) * (1 + alg.theta (n + 1))
      * primal_gap K g (alg.x (n + 1)) sp.xhat sp.yhat :=
    mul_nonneg (mul_nonneg (le_of_lt (hτ_pos (n + 1))) (by linarith)) hP_nn
  have hE : pdal_lyapunov alg sp n = ‖alg.x (n + 2) - sp.xhat‖^2 / 2
      + ‖alg.y (n + 2) - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau (n + 1) * (1 + alg.theta (n + 1))
        * primal_gap K g (alg.x (n + 1)) sp.xhat sp.yhat := rfl
  rw [hE]
  linarith

/-- Lyapunov 能量单调递减（Antitone），由 energy_inequality 在 k = n+2 处给出。 -/
lemma pdal_lyapunov_antitone (alg : PDAL K g h) (sp : SaddlePoint K g h) :
    Antitone (pdal_lyapunov alg sp) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j _ ih =>
    have hj2 : j + 2 ≥ 2 := by omega
    have hstep := energy_inequality alg sp (j + 2) (by omega)
      (x_mem_dom alg (j + 1) (by omega))
    have hδ_nn : 0 ≤ alg.delta := le_of_lt alg.delta_pos.1
    have h1mδsq_nn : 0 ≤ 1 - alg.delta ^ 2 := by
      have hδsq : alg.delta ^ 2 < 1 := by
        have : alg.delta < 1 := alg.delta_pos.2
        nlinarith
      linarith
    have hxb_nn : 0 ≤ ‖xbar alg (j + 2) - alg.x (j + 2)‖^2 / 2 :=
      div_nonneg (sq_nonneg _) (by norm_num)
    have hyn_nn : 0 ≤ (1 - alg.delta ^ 2) * ‖alg.y (j + 3) - alg.y (j + 2)‖^2 / (2 * alg.beta) := by
      apply div_nonneg
      · exact mul_nonneg h1mδsq_nn (sq_nonneg _)
      · have hβ : 0 < 2 * alg.beta := by exact mul_pos two_pos alg.beta_pos
        exact le_of_lt hβ
    have hjm1 : j + 2 - 1 = j + 1 := by omega
    have hjp1 : j + 2 + 1 = j + 3 := by omega
    rw [hjm1, hjp1] at hstep
    have hfj : pdal_lyapunov alg sp (j + 1) ≤ pdal_lyapunov alg sp j := by
      have hE1 : pdal_lyapunov alg sp j = ‖alg.x (j + 2) - sp.xhat‖^2 / 2
          + ‖alg.y (j + 2) - sp.yhat‖^2 / (2 * alg.beta)
          + alg.tau (j + 1) * (1 + alg.theta (j + 1))
            * primal_gap K g (alg.x (j + 1)) sp.xhat sp.yhat := rfl
      have hE2 : pdal_lyapunov alg sp (j + 1) = ‖alg.x (j + 1 + 2) - sp.xhat‖^2 / 2
          + ‖alg.y (j + 1 + 2) - sp.yhat‖^2 / (2 * alg.beta)
          + alg.tau (j + 1 + 1) * (1 + alg.theta (j + 1 + 1))
            * primal_gap K g (alg.x (j + 1 + 1)) sp.xhat sp.yhat := rfl
      rw [hE1, hE2, show j + 1 + 2 = j + 3 from rfl, show j + 1 + 1 = j + 2 from rfl]
      linarith [hstep, hxb_nn, hyn_nn]
    exact le_trans hfj ih

/-- 原变量相邻增量范数趋于零：由 x̄_k - x_k 与步长上下界得到。

关键恒等式（θ_{k+1} = τ_{k+1}/τ_k）：
‖x_{k+1} - x_k‖ = (τ_k / τ_{k+1}) · ‖x̄_{k+1} - x_{k+1}‖ ≤ (M/τ_min) · ‖x̄_{k+1} - x_{k+1}‖。 -/
lemma pdal_primal_diff_norm_tendsto_zero
    (alg : PDAL K g h) (sp : SaddlePoint K g h)
    (tau_bdd : ∃ M, ∀ k, alg.tau k ≤ M) :
    Tendsto (fun k => ‖alg.x (k + 1) - alg.x k‖) atTop (𝓝 0) := by
  obtain ⟨τmin, hτmin_pos, hτmin_le⟩ := tau_lower_bound alg
  obtain ⟨M, hM⟩ := tau_bdd
  have hM_pos : 0 < M := lt_of_lt_of_le (tau_pos alg 0) (hM 0)
  obtain ⟨hxb, _⟩ := pdal_residuals_to_zero alg sp
  -- 范数恒等式：‖x_{k+1} - x_k‖ = (τ_k / τ_{k+1}) · ‖x̄_{k+1} - x_{k+1}‖
  have hbound' : ∀ k, ‖alg.x (k + 1) - alg.x k‖
      = (alg.tau k / alg.tau (k + 1)) * ‖xbar alg (k + 1) - alg.x (k + 1)‖ := by
    intro k
    have hk1 : k + 1 ≥ 1 := by omega
    have hθ : alg.theta (k + 1) = alg.tau (k + 1) / alg.tau k := alg.theta_def (k + 1) hk1
    have hxb_eq : xbar alg (k + 1) - alg.x (k + 1)
        = alg.theta (k + 1) • (alg.x (k + 1) - alg.x k) := by
      simp only [xbar]
      abel
    have hθpos : 0 ≤ alg.tau (k + 1) / alg.tau k :=
      div_nonneg (le_of_lt (tau_pos alg (k + 1))) (le_of_lt (tau_pos alg k))
    rw [hxb_eq, hθ, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθpos]
    have e1 : alg.tau (k + 1) ≠ 0 := ne_of_gt (tau_pos alg (k + 1))
    have e2 : alg.tau k ≠ 0 := ne_of_gt (tau_pos alg k)
    field_simp
  have hbound2 : ∀ k, ‖alg.x (k + 1) - alg.x k‖
      ≤ (M / τmin) * ‖xbar alg (k + 1) - alg.x (k + 1)‖ := by
    intro k
    rw [hbound' k]
    have hτle : alg.tau k / alg.tau (k + 1) ≤ M / τmin := by
      exact div_le_div₀ hM_pos.le (hM k) hτmin_pos (hτmin_le (k + 1))
    exact mul_le_mul_of_nonneg_right hτle (norm_nonneg _)
  -- 索引平移后的残差趋零
  have hshift : Tendsto (fun k => ‖xbar alg (k + 1) - alg.x (k + 1)‖) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hxb
  have hfac : Tendsto (fun k => (M / τmin) * ‖xbar alg (k + 1) - alg.x (k + 1)‖) atTop
      (𝓝 ((M / τmin) * 0)) := hshift.const_mul (M / τmin)
  have hfac0 : (M / τmin) * 0 = 0 := mul_zero _
  rw [hfac0] at hfac
  have hnn : (fun k : ℕ => (0 : ℝ)) ≤ fun k => ‖alg.x (k + 1) - alg.x k‖ :=
    fun k => norm_nonneg _
  have hle : (fun k : ℕ => ‖alg.x (k + 1) - alg.x k‖)
      ≤ fun k => (M / τmin) * ‖xbar alg (k + 1) - alg.x (k + 1)‖ := hbound2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfac hnn hle

/-- 辅助：单调递减非负数列趋于其下确界；若沿子列某点后有项 ≤ 0，则整列趋于零。
这里直接给出收敛性证明所需的组合引理：若 `a` 单调递减、非负，且存在子列趋于 0，
则整列趋于 0。 -/
lemma antitone_nonneg_tendsto_of_subseq
    {a : ℕ → ℝ} (hanti : Antitone a) (hnn : ∀ n, 0 ≤ a n)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) (hsub : Tendsto (a ∘ ψ) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range a) := ⟨0, fun _ ⟨n, hn⟩ => hn ▸ hnn n⟩
  obtain ⟨L, hL⟩ := Real.tendsto_of_bddBelow_antitone hbdd hanti
  have hsub' : Tendsto (fun n => a (ψ n)) atTop (𝓝 L) := hL.comp hψ.tendsto_atTop
  have hL0 : L = 0 := by
    have h1 : Tendsto (a ∘ ψ) atTop (𝓝 (0:ℝ)) := hsub
    have h2 : Tendsto (a ∘ ψ) atTop (𝓝 L) := hL.comp hψ.tendsto_atTop
    exact tendsto_nhds_unique (f := a ∘ ψ) (l := atTop) h2 h1
  rw [hL0] at hL
  exact hL
/-- 相邻增量趋零 + 子列收敛 ⇒ 前移一位子列收敛：若 ‖u(k+1)-u(k)‖ → 0
且 u(φ n) → p（φ 严格递增），则 u(φ n - 1) → p（当 φ n ≥ 1）。 -/
lemma subseq_shift_one_tendsto {X : Type*} [NormedAddCommGroup X]
    {u : ℕ → X} {p : X} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hφ1 : ∀ n, 1 ≤ φ n)
    (hu : Tendsto (fun n => u (φ n)) atTop (𝓝 p))
    (hd : Tendsto (fun k => ‖u (k + 1) - u k‖) atTop (𝓝 0)) :
    Tendsto (fun n => u (φ n - 1)) atTop (𝓝 p) := by
  have hidx : ∀ n, φ n - 1 + 1 = φ n :=
    fun n => Nat.sub_add_cancel (hφ1 n)
  have hmono : StrictMono (fun n => φ n - 1) := by
    intro i j hij
    change φ i - 1 < φ j - 1
    have hi := hφ1 i
    have hij' := hφ hij
    omega
  have hu1 : Tendsto (fun n => u (φ n - 1 + 1)) atTop (𝓝 p) := by
    simpa only [hidx] using hu
  have hdn : Tendsto (fun n => ‖u (φ n - 1 + 1) - u (φ n - 1)‖)
      atTop (𝓝 0) := hd.comp hmono.tendsto_atTop
  have hdv : Tendsto (fun n => u (φ n - 1 + 1) - u (φ n - 1))
      atTop (𝓝 0) := (tendsto_zero_iff_norm_tendsto_zero).mpr hdn
  have hh := hu1.sub hdv
  simpa only [sub_sub_cancel, sub_zero] using hh

/-- **Theorem 1 (Convergence)**: If g|_{dom g} is continuous and (τ_k) is
bounded from above, then the whole sequence (x^k, y^k) converges to a
solution of (1).
-/
theorem pdal_convergence (alg : PDAL K g h) (sp : SaddlePoint K g h)
    (g_cont : ContinuousOn g.f g.dom) (tau_bdd : ∃ M, ∀ k, alg.tau k ≤ M) :
    ∃ (xstar : X) (ystar : Y),
      IsSaddlePoint K g h xstar ystar ∧
      Tendsto (fun k => alg.x k) atTop (𝓝 xstar) ∧
      Tendsto (fun k => alg.y k) atTop (𝓝 ystar) := by
  -- 第一步：提取鞍点聚点与对应子列
  obtain ⟨xstar, ystar, hcl, hsaddle⟩ := pdal_has_saddle_cluster_point alg sp
  obtain ⟨φ, hφmono, hφtend⟩ := hcl
  have hxφ : Tendsto (fun n => alg.x (φ n)) atTop (𝓝 xstar) :=
    (continuous_fst.tendsto' (xstar, ystar) xstar rfl).comp hφtend
  have hyφ : Tendsto (fun n => alg.y (φ n)) atTop (𝓝 ystar) :=
    (continuous_snd.tendsto' (xstar, ystar) ystar rfl).comp hφtend
  -- 第二步：残差与步长界
  obtain ⟨hxb, hyd⟩ := pdal_residuals_to_zero alg sp
  obtain ⟨M, hM⟩ := tau_bdd
  have hM_pos : 0 < M := lt_of_lt_of_le (tau_pos alg 0) (hM 0)
  have hprimal_diff : Tendsto (fun k => ‖alg.x (k + 1) - alg.x k‖) atTop (𝓝 0) :=
    pdal_primal_diff_norm_tendsto_zero alg sp ⟨M, hM⟩
  -- 以新聚点为中心的鞍点结构（let 使投影可由 rfl 化简）
  let spstar : SaddlePoint K g h := ⟨xstar, ystar, hsaddle.1, hsaddle.2.1,
    hsaddle.2.2.1, hsaddle.2.2.2⟩
  have hsp_hat : spstar.xhat = xstar ∧ spstar.yhat = ystar := ⟨rfl, rfl⟩
  -- 全局 θ 非负性
  have hθnn_all : ∀ k, 0 ≤ alg.theta k := by
    intro k
    by_cases hk : k = 0
    · rw [hk, alg.theta0_eq]; norm_num
    · have hk1 : k ≥ 1 := by omega
      rw [alg.theta_def k hk1]
      exact div_nonneg (le_of_lt (tau_pos alg k)) (le_of_lt (tau_pos alg (k - 1)))
  -- 子列平移：ψ n = φ(n+2)，则 ψ n ≥ 2
  have hψmono : StrictMono (fun n => φ (n + 2)) := fun i j hij =>
    hφmono (by omega)
  have hψtend : Tendsto (fun n => (alg.x (φ (n + 2)), alg.y (φ (n + 2)))) atTop
      (𝓝 (xstar, ystar)) := (tendsto_add_atTop_iff_nat 2).mpr hφtend
  have hxψ : Tendsto (fun n => alg.x (φ (n + 2))) atTop (𝓝 xstar) :=
    (continuous_fst.tendsto' (xstar, ystar) xstar rfl).comp hψtend
  have hyψ : Tendsto (fun n => alg.y (φ (n + 2))) atTop (𝓝 ystar) :=
    (continuous_snd.tendsto' (xstar, ystar) ystar rfl).comp hψtend
  have hψ2 : ∀ n, 2 ≤ φ (n + 2) := by
    intro n
    have h1 : n + 2 ≤ φ (n + 2) := StrictMono.id_le hφmono (n + 2)
    omega
  -- γ n = ψ n - 2 严格递增
  have hγmono : StrictMono (fun n => φ (n + 2) - 2) := by
    intro i j hij
    change φ (i + 2) - 2 < φ (j + 2) - 2
    have h1 : i + 2 ≤ φ (i + 2) := StrictMono.id_le hφmono (i + 2)
    have h2 : i + 2 < j + 2 := by omega
    have h3 := hφmono h2
    omega
  -- x_{ψ n - 1} → xstar：直接用全局相邻增量极限调用 subseq_shift_one_tendsto
  have hxψm1 : Tendsto (fun n => alg.x (φ (n + 2) - 1)) atTop (𝓝 xstar) :=
    subseq_shift_one_tendsto hψmono (fun n => le_of_lt (hψ2 n)) hxψ hprimal_diff
  -- xstar ∈ dom g（由鞍点结论）
  have hxstar_dom : xstar ∈ g.dom := hsaddle.1
  -- hxmem：x(ψ n - 1) ∈ dom g（ψ n ≥ 2 ⇒ ψ n - 1 ≥ 1）
  have hxmem : ∀ n, alg.x (φ (n + 2) - 1) ∈ g.dom := by
    intro n
    have h1 : φ (n + 2) - 1 ≥ 1 := by have := hψ2 n; omega
    exact x_mem_dom alg (φ (n + 2) - 1) h1
  -- 第四步：P(x_{ψ n - 1}) → 0（常量向量是 (K†) ystar : X）
  have hPψ : Tendsto (fun n => primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar)
      atTop (𝓝 0) := by
    have hca : ContinuousWithinAt g.f g.dom xstar := g_cont xstar hxstar_dom
    have hwithin : Tendsto (fun n => alg.x (φ (n + 2) - 1)) atTop (𝓝[g.dom] xstar) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        (fun n => alg.x (φ (n + 2) - 1)) hxψm1
        (Filter.Eventually.of_forall (fun n => hxmem n))
    have hgf : Tendsto (fun n => g.f (alg.x (φ (n + 2) - 1))) atTop (𝓝 (g.f xstar)) :=
      hca.tendsto.comp hwithin
    have hdiff : Tendsto (fun n => alg.x (φ (n + 2) - 1) - xstar) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => alg.x (φ (n + 2) - 1)) atTop (𝓝 xstar) := hxψm1
      have h2 : Tendsto (fun _ : ℕ => (xstar : X)) atTop (𝓝 (xstar : X)) := tendsto_const_nhds
      have h3 : Tendsto (fun n => alg.x (φ (n + 2) - 1) - xstar) atTop
          (𝓝 ((xstar - xstar : X))) := h1.sub h2
      rw [show (xstar - xstar : X) = 0 from sub_self xstar] at h3
      exact h3
    have hinner : Tendsto (fun n => ⟪(K†) ystar, alg.x (φ (n + 2) - 1) - xstar⟫_ℝ)
        atTop (𝓝 (⟪(K†) ystar, (0:X)⟫_ℝ)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (K†) ystar) atTop (𝓝 ((K†) ystar))).inner
        hdiff
    have hinner0 : ⟪(K†) ystar, (0:X)⟫_ℝ = 0 := by simp
    rw [hinner0] at hinner
    have hPconv : Tendsto (fun n => g.f (alg.x (φ (n + 2) - 1)) - g.f xstar
        + ⟪(K†) ystar, alg.x (φ (n + 2) - 1) - xstar⟫_ℝ) atTop
        (𝓝 (g.f xstar - g.f xstar + (0:ℝ))) := hgf.sub tendsto_const_nhds |>.add hinner
    simp only [sub_self, add_zero] at hPconv
    have hPdef : ∀ n, primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar
        = g.f (alg.x (φ (n + 2) - 1)) - g.f xstar
          + ⟪(K†) ystar, alg.x (φ (n + 2) - 1) - xstar⟫_ℝ := fun n => rfl
    have hfinal : Tendsto (fun n => primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar)
        atTop (𝓝 0) := by
      apply hPconv.congr
      intro n
      exact (hPdef n).symm
    exact hfinal
  -- 第五步：能量沿子列 γ n = ψ n - 2 趋零
  have hEγ : Tendsto (fun n => pdal_lyapunov alg spstar (φ (n + 2) - 2)) atTop (𝓝 0) := by
    -- 展开（n+2、n+1 定义匹配 ψ n、ψ n - 1）
    have hEopen : ∀ n, pdal_lyapunov alg spstar (φ (n + 2) - 2)
        = ‖alg.x (φ (n + 2)) - xstar‖^2 / 2
          + ‖alg.y (φ (n + 2)) - ystar‖^2 / (2 * alg.beta)
          + alg.tau (φ (n + 2) - 1) * (1 + alg.theta (φ (n + 2) - 1))
            * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar := by
      intro n
      show ‖alg.x (φ (n + 2) - 2 + 2) - spstar.xhat‖^2 / 2
          + ‖alg.y (φ (n + 2) - 2 + 2) - spstar.yhat‖^2 / (2 * alg.beta)
          + alg.tau (φ (n + 2) - 2 + 1) * (1 + alg.theta (φ (n + 2) - 2 + 1))
            * primal_gap K g (alg.x (φ (n + 2) - 2 + 1)) spstar.xhat spstar.yhat
          = ‖alg.x (φ (n + 2)) - xstar‖^2 / 2
            + ‖alg.y (φ (n + 2)) - ystar‖^2 / (2 * alg.beta)
            + alg.tau (φ (n + 2) - 1) * (1 + alg.theta (φ (n + 2) - 1))
              * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar
      rw [show φ (n + 2) - 2 + 2 = φ (n + 2) from by have := hψ2 n; omega,
        show φ (n + 2) - 2 + 1 = φ (n + 2) - 1 from by have := hψ2 n; omega,
        hsp_hat.1, hsp_hat.2]
    -- 第一项趋零
    have hterm1 : Tendsto (fun n => ‖alg.x (φ (n + 2)) - xstar‖^2 / 2) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => alg.x (φ (n + 2)) - xstar) atTop (𝓝 0) := by
        have h3 := hxψ.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => xstar) atTop
          (𝓝 xstar))
        simpa using h3
      have h1 : Tendsto (fun n => ‖alg.x (φ (n + 2)) - xstar‖) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mp h2
      have hpow : Tendsto (fun n => ‖alg.x (φ (n + 2)) - xstar‖ ^ 2) atTop
          (𝓝 ((0:ℝ) ^ 2)) := h1.pow 2
      have hpow0 : (0:ℝ) ^ 2 = 0 := by norm_num
      rw [hpow0] at hpow
      have hdiv : Tendsto (fun n => ‖alg.x (φ (n + 2)) - xstar‖ ^ 2 / 2) atTop
          (𝓝 ((0:ℝ) / 2)) := hpow.div_const 2
      simpa using hdiv
    -- 第二项趋零
    have hterm2 : Tendsto (fun n => ‖alg.y (φ (n + 2)) - ystar‖^2 / (2 * alg.beta))
        atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => alg.y (φ (n + 2)) - ystar) atTop (𝓝 0) := by
        have h3 := hyψ.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => ystar) atTop
          (𝓝 ystar))
        simpa using h3
      have h1 : Tendsto (fun n => ‖alg.y (φ (n + 2)) - ystar‖) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mp h2
      have hpow : Tendsto (fun n => ‖alg.y (φ (n + 2)) - ystar‖ ^ 2) atTop
          (𝓝 ((0:ℝ) ^ 2)) := h1.pow 2
      have hpow0 : (0:ℝ) ^ 2 = 0 := by norm_num
      rw [hpow0] at hpow
      have hdiv : Tendsto (fun n => ‖alg.y (φ (n + 2)) - ystar‖ ^ 2 / (2 * alg.beta)) atTop
          (𝓝 ((0:ℝ) / (2 * alg.beta))) := hpow.div_const (2 * alg.beta)
      simpa using hdiv
    -- 第三项趋零：τ ≤ M，θ ≤ θ_bound，P → 0
    have hterm3 : Tendsto (fun n => alg.tau (φ (n + 2) - 1) * (1 + alg.theta (φ (n + 2) - 1))
        * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar) atTop (𝓝 0) := by
      have hτle : ∀ n, alg.tau (φ (n + 2) - 1) ≤ M := fun n => hM (φ (n + 2) - 1)
      have hθle : ∀ n, 1 + alg.theta (φ (n + 2) - 1) ≤ 1 + theta_bound := fun n =>
        add_le_add_left (theta_upper_bound alg (φ (n + 2) - 1)) 1
      have hPnn : ∀ n, 0 ≤ primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar := fun n =>
        primal_gap_nonneg K g h spstar (alg.x (φ (n + 2) - 1)) (hxmem n)
      have hup : Tendsto (fun n => M * (1 + theta_bound)
          * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar) atTop
          (𝓝 (M * (1 + theta_bound) * 0)) := hPψ.const_mul _
      have hup0 : M * (1 + theta_bound) * 0 = 0 := mul_zero _
      rw [hup0] at hup
      have hnn : (fun n : ℕ => (0:ℝ)) ≤ fun n => alg.tau (φ (n + 2) - 1)
          * (1 + alg.theta (φ (n + 2) - 1))
          * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar := by
        intro n
        have hτnn : 0 ≤ alg.tau (φ (n + 2) - 1) := le_of_lt (tau_pos alg (φ (n + 2) - 1))
        have hθnn : 0 ≤ 1 + alg.theta (φ (n + 2) - 1) := by
          have h0 := hθnn_all (φ (n + 2) - 1)
          linarith
        exact mul_nonneg (mul_nonneg hτnn hθnn) (hPnn n)
      have hle : (fun n => alg.tau (φ (n + 2) - 1) * (1 + alg.theta (φ (n + 2) - 1))
          * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar)
          ≤ fun n => M * (1 + theta_bound)
            * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar := by
        intro n
        have h1 : alg.tau (φ (n + 2) - 1) * (1 + alg.theta (φ (n + 2) - 1))
            ≤ M * (1 + theta_bound) :=
          mul_le_mul (hτle n) (hθle n)
            (by have h0 := hθnn_all (φ (n + 2) - 1); linarith) hM_pos.le
        exact mul_le_mul_of_nonneg_right h1 (hPnn n)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hnn hle
    -- 合并三项并匹配能量展开
    have hsum : Tendsto (fun n => ‖alg.x (φ (n + 2)) - xstar‖^2 / 2
        + ‖alg.y (φ (n + 2)) - ystar‖^2 / (2 * alg.beta)
        + alg.tau (φ (n + 2) - 1) * (1 + alg.theta (φ (n + 2) - 1))
          * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar) atTop (𝓝 0) := by
      have h12 : Tendsto (fun n => ‖alg.x (φ (n + 2)) - xstar‖^2 / 2
          + ‖alg.y (φ (n + 2)) - ystar‖^2 / (2 * alg.beta)) atTop
          (𝓝 ((0:ℝ) + 0)) := hterm1.add hterm2
      have h120 : ((0:ℝ) + 0) = 0 := add_zero _
      rw [h120] at h12
      have h123 : Tendsto (fun n => ‖alg.x (φ (n + 2)) - xstar‖^2 / 2
          + ‖alg.y (φ (n + 2)) - ystar‖^2 / (2 * alg.beta)
          + alg.tau (φ (n + 2) - 1) * (1 + alg.theta (φ (n + 2) - 1))
            * primal_gap K g (alg.x (φ (n + 2) - 1)) xstar ystar) atTop
          (𝓝 ((0:ℝ) + 0)) := h12.add hterm3
      rw [h120] at h123
      exact h123
    apply hsum.congr
    intro n
    exact (hEopen n).symm
  -- 第六步：能量整列趋零（单调非负 + 子列趋零，γ 严格递增）
  have hEzero : Tendsto (pdal_lyapunov alg spstar) atTop (𝓝 0) :=
    antitone_nonneg_tendsto_of_subseq (pdal_lyapunov_antitone alg spstar)
      (pdal_lyapunov_nonneg alg spstar) hγmono hEγ
  -- 第七步：由能量趋零推出 x、y 整列收敛
  refine ⟨xstar, ystar, hsaddle, ?_, ?_⟩
  · -- x_k → xstar：½‖x_{k+2} - x*‖² ≤ E_k → 0
    have hsq_le : ∀ k, ‖alg.x (k + 2) - xstar‖^2 / 2 ≤ pdal_lyapunov alg spstar k := by
      intro k
      have hE : pdal_lyapunov alg spstar k = ‖alg.x (k + 2) - xstar‖^2 / 2
          + ‖alg.y (k + 2) - ystar‖^2 / (2 * alg.beta)
          + alg.tau (k + 1) * (1 + alg.theta (k + 1))
            * primal_gap K g (alg.x (k + 1)) xstar ystar := rfl
      have h1 : 0 ≤ ‖alg.y (k + 2) - ystar‖^2 / (2 * alg.beta) := by
        refine div_nonneg (sq_nonneg _) ?_
        exact le_of_lt (mul_pos two_pos alg.beta_pos)
      have h2 : 0 ≤ alg.tau (k + 1) * (1 + alg.theta (k + 1))
          * primal_gap K g (alg.x (k + 1)) xstar ystar := by
        have hτnn : 0 ≤ alg.tau (k + 1) := le_of_lt (tau_pos alg (k + 1))
        have hθnn : 0 ≤ 1 + alg.theta (k + 1) := by
          have h0 : 0 ≤ alg.theta (k + 1) := by
            have hk1 : k + 1 ≥ 1 := by omega
            rw [alg.theta_def (k + 1) hk1]
            exact div_nonneg (le_of_lt (tau_pos alg (k + 1))) (le_of_lt (tau_pos alg k))
          linarith
        have hPnn : 0 ≤ primal_gap K g (alg.x (k + 1)) xstar ystar :=
          primal_gap_nonneg K g h spstar (alg.x (k + 1)) (x_mem_dom alg (k + 1) (by omega))
        exact mul_nonneg (mul_nonneg hτnn hθnn) hPnn
      rw [hE]
      linarith
    -- ‖x_{k+2} - x*‖² / 2 → 0 ⇒ x_{k+2} → x*
    have hx2 : Tendsto (fun k => alg.x (k + 2)) atTop (𝓝 xstar) := by
      have h1 : Tendsto (fun k => ‖alg.x (k + 2) - xstar‖^2 / 2) atTop (𝓝 0) := by
        have h2 : (fun k => ‖alg.x (k + 2) - xstar‖^2 / 2)
            ≤ pdal_lyapunov alg spstar := hsq_le
        have h3 : Tendsto (pdal_lyapunov alg spstar) atTop (𝓝 0) := hEzero
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
          (fun k => div_nonneg (sq_nonneg _) (by norm_num)) h2
      have h4 : Tendsto (fun k => ‖alg.x (k + 2) - xstar‖) atTop (𝓝 0) := by
        have h5 : Tendsto (fun k => 2 * (‖alg.x (k + 2) - xstar‖^2 / 2)) atTop
            (𝓝 (2 * 0)) := h1.const_mul 2
        simp only [mul_zero] at h5
        have h6 : Tendsto (fun k => ‖alg.x (k + 2) - xstar‖^2) atTop (𝓝 0) := by
          have hcongr : (fun k => ‖alg.x (k + 2) - xstar‖^2)
              = fun k => 2 * (‖alg.x (k + 2) - xstar‖^2 / 2) := by
            funext k; ring
          rw [hcongr]; exact h5
        have h7 : Tendsto (fun k => Real.sqrt (‖alg.x (k + 2) - xstar‖ ^ 2)) atTop
            (𝓝 (Real.sqrt (0:ℝ))) := h6.sqrt
        have h7' : Real.sqrt (0:ℝ) = 0 := Real.sqrt_zero
        rw [h7'] at h7
        have h8' : ∀ k, (Real.sqrt (‖alg.x (k + 2) - xstar‖ ^ 2) : ℝ)
            = ‖alg.x (k + 2) - xstar‖ := fun k => Real.sqrt_sq (norm_nonneg _)
        have h8c : (fun k => Real.sqrt (‖alg.x (k + 2) - xstar‖ ^ 2))
            = fun k => ‖alg.x (k + 2) - xstar‖ := by
          funext k; exact h8' k
        rw [h8c] at h7
        exact h7
      have h8 : Tendsto (fun k => alg.x (k + 2) - xstar) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr h4
      have h9 : Tendsto (fun k => (alg.x (k + 2) - xstar) + xstar) atTop
          (𝓝 ((0:X) + xstar)) := h8.add tendsto_const_nhds
      have h10 : (fun k => (alg.x (k + 2) - xstar) + xstar) = fun k => alg.x (k + 2) := by
        funext k; abel
      rw [h10, zero_add] at h9
      exact h9
    exact (tendsto_add_atTop_iff_nat 2).mp hx2
  · -- y_k → ystar：‖y_{k+2} - y*‖²/(2β) ≤ E_k → 0
    have hsq_le : ∀ k, ‖alg.y (k + 2) - ystar‖^2 / (2 * alg.beta)
        ≤ pdal_lyapunov alg spstar k := by
      intro k
      have hE : pdal_lyapunov alg spstar k = ‖alg.x (k + 2) - xstar‖^2 / 2
          + ‖alg.y (k + 2) - ystar‖^2 / (2 * alg.beta)
          + alg.tau (k + 1) * (1 + alg.theta (k + 1))
            * primal_gap K g (alg.x (k + 1)) xstar ystar := rfl
      have h1 : 0 ≤ ‖alg.x (k + 2) - xstar‖^2 / 2 :=
        div_nonneg (sq_nonneg _) (by norm_num)
      have h2 : 0 ≤ alg.tau (k + 1) * (1 + alg.theta (k + 1))
          * primal_gap K g (alg.x (k + 1)) xstar ystar := by
        have hτnn : 0 ≤ alg.tau (k + 1) := le_of_lt (tau_pos alg (k + 1))
        have hθnn : 0 ≤ 1 + alg.theta (k + 1) := by
          have h0 : 0 ≤ alg.theta (k + 1) := by
            have hk1 : k + 1 ≥ 1 := by omega
            rw [alg.theta_def (k + 1) hk1]
            exact div_nonneg (le_of_lt (tau_pos alg (k + 1))) (le_of_lt (tau_pos alg k))
          linarith
        have hPnn : 0 ≤ primal_gap K g (alg.x (k + 1)) xstar ystar :=
          primal_gap_nonneg K g h spstar (alg.x (k + 1)) (x_mem_dom alg (k + 1) (by omega))
        exact mul_nonneg (mul_nonneg hτnn hθnn) hPnn
      rw [hE]
      linarith
    have hy2 : Tendsto (fun k => alg.y (k + 2)) atTop (𝓝 ystar) := by
      have h1 : Tendsto (fun k => ‖alg.y (k + 2) - ystar‖^2 / (2 * alg.beta)) atTop (𝓝 0) := by
        have h2 : (fun k => ‖alg.y (k + 2) - ystar‖^2 / (2 * alg.beta))
            ≤ pdal_lyapunov alg spstar := hsq_le
        have h3 : Tendsto (pdal_lyapunov alg spstar) atTop (𝓝 0) := hEzero
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
          (fun k => div_nonneg (sq_nonneg _)
            (by linarith [le_of_lt (mul_pos two_pos alg.beta_pos)]))
          h2
      have h4 : Tendsto (fun k => ‖alg.y (k + 2) - ystar‖^2) atTop (𝓝 0) := by
        have hβne : (2 * alg.beta) ≠ 0 := ne_of_gt (mul_pos two_pos alg.beta_pos)
        have h5 : Tendsto (fun k => (2 * alg.beta) * (‖alg.y (k + 2) - ystar‖^2 / (2 * alg.beta)))
            atTop (𝓝 ((2 * alg.beta) * 0)) := h1.const_mul _
        have h5' : (2 * alg.beta) * 0 = 0 := mul_zero _
        rw [h5'] at h5
        have hcongr : (fun k => ‖alg.y (k + 2) - ystar‖^2)
            = fun k => (2 * alg.beta) * (‖alg.y (k + 2) - ystar‖^2 / (2 * alg.beta)) := by
          funext k
          have hβ : (2 * alg.beta) ≠ 0 := ne_of_gt (mul_pos two_pos alg.beta_pos)
          rw [mul_div_cancel₀ _ hβ]
        rw [hcongr]
        exact h5
      have h6 : Tendsto (fun k => ‖alg.y (k + 2) - ystar‖) atTop (𝓝 0) := by
        have h7 : Tendsto (fun k => Real.sqrt (‖alg.y (k + 2) - ystar‖ ^ 2)) atTop
            (𝓝 (Real.sqrt (0:ℝ))) := h4.sqrt
        have h7' : Real.sqrt (0:ℝ) = 0 := Real.sqrt_zero
        rw [h7'] at h7
        have h8' : ∀ k, (Real.sqrt (‖alg.y (k + 2) - ystar‖ ^ 2) : ℝ)
            = ‖alg.y (k + 2) - ystar‖ := fun k => Real.sqrt_sq (norm_nonneg _)
        have h8c : (fun k => Real.sqrt (‖alg.y (k + 2) - ystar‖ ^ 2))
            = fun k => ‖alg.y (k + 2) - ystar‖ := by
          funext k; exact h8' k
        rw [h8c] at h7
        exact h7
      have h8 : Tendsto (fun k => alg.y (k + 2) - ystar) atTop (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr h6
      have h9 : Tendsto (fun k => (alg.y (k + 2) - ystar) + ystar) atTop
          (𝓝 ((0:Y) + ystar)) := h8.add tendsto_const_nhds
      have h10 : (fun k => (alg.y (k + 2) - ystar) + ystar) = fun k => alg.y (k + 2) := by
        funext k; abel
      rw [h10, zero_add] at h9
      exact h9
    exact (tendsto_add_atTop_iff_nat 2).mp hy2

/-- 通用引理：`List.range` 上的 `foldl` 求和等于 `Finset.range` 上的有限和
（适用于任意 `AddCommMonoid`）。 -/
theorem pdal_foldl_range_eq_sum {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (N : ℕ) :
    (List.range N).foldl (fun acc k => acc + f k) 0
      = ∑ k ∈ Finset.range N, f k := by
  have h1 : (List.range N).foldl (fun acc k => acc + f k) 0
      = ((List.range N).map f).sum := by
    rw [List.sum_eq_foldl, List.foldl_map]
  have h2 : ((List.range N).map f).sum = (List.range N).toFinset.sum f := by
    exact (List.sum_toFinset f (List.nodup_range)).symm
  have h3 : (List.range N).toFinset = Finset.range N := List.toFinset_range N
  rw [h1, h2, h3]

/-- `⟪v, ·⟫ - c` 在凸集上是凸的（仿射函数）：由双线性与凸组合定义直接展开。 -/
lemma inner_sub_const_convexOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (c : ℝ) {s : Set E} (hs : Convex ℝ s) :
    ConvexOn ℝ s (fun x => ⟪v, x⟫_ℝ - c) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  change ⟪v, a • x + b • y⟫_ℝ - c
    ≤ a * (⟪v, x⟫_ℝ - c) + b * (⟪v, y⟫_ℝ - c)
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hc : a * c + b * c = c := by
    calc a * c + b * c = (a + b) * c := by ring
      _ = c := by rw [hab, one_mul]
  linarith only [hc]

/-- Convexity of the primal gap `P(x) = g(x) - g(x̂) + ⟨K*ŷ, x - x̂⟩` on `dom g`. -/
lemma primal_gap_convex (K : X →L[ℝ] Y) (g : ProperConvex X)
    (xhat : X) (yhat : Y) :
    ConvexOn ℝ g.dom (fun x => primal_gap K g x xhat yhat) := by
  set v : X := (K†) yhat with hv
  have h2 : ConvexOn ℝ g.dom (fun x => ⟪v, x⟫_ℝ - (g.f xhat + ⟪v, xhat⟫_ℝ)) :=
    inner_sub_const_convexOn v (g.f xhat + ⟪v, xhat⟫_ℝ) g.dom_convex
  have h3 : ConvexOn ℝ g.dom (fun x => g.f x + (⟪v, x⟫_ℝ - (g.f xhat + ⟪v, xhat⟫_ℝ))) :=
    g.convex_on.add h2
  convert h3 using 1
  funext x
  show g.f x - g.f xhat + ⟪v, x - xhat⟫_ℝ
      = g.f x + (⟪v, x⟫_ℝ - (g.f xhat + ⟪v, xhat⟫_ℝ))
  rw [inner_sub_right]
  ring

/-- Convexity of the dual gap `D(y) = h(y) - h(ŷ) - ⟨Kx̂, y - ŷ⟩` on `dom h`. -/
lemma dual_gap_convex (K : X →L[ℝ] Y) (h : ProperConvex Y)
    (yhat : Y) (xhat : X) :
    ConvexOn ℝ h.dom (fun y => dual_gap K h y yhat xhat) := by
  set w : Y := K xhat with hw
  have h2 : ConvexOn ℝ h.dom
      (fun y => ⟪-w, y⟫_ℝ - (h.f yhat - ⟪w, yhat⟫_ℝ)) :=
    inner_sub_const_convexOn (-w) (h.f yhat - ⟪w, yhat⟫_ℝ) h.dom_convex
  have h3 : ConvexOn ℝ h.dom
      (fun y => h.f y + (⟪-w, y⟫_ℝ - (h.f yhat - ⟪w, yhat⟫_ℝ))) :=
    h.convex_on.add h2
  convert h3 using 1
  funext y
  show h.f y - h.f yhat - ⟪w, y - yhat⟫_ℝ
      = h.f y + (⟪-w, y⟫_ℝ - (h.f yhat - ⟪w, yhat⟫_ℝ))
  rw [inner_sub_right, inner_neg_left]
  ring

/-- 逐项求和的单步间隙界：由 `pdal_gap_step` 相加并望远消去距离差。 -/
theorem pdal_gap_sum (alg : PDAL K g h) (sp : SaddlePoint K g h)
    (hx0 : alg.x 0 ∈ g.dom) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      alg.tau (j + 1) * ((1 + alg.theta (j + 1))
          * primal_gap K g (alg.x (j + 1)) sp.xhat sp.yhat
        - alg.theta (j + 1) * primal_gap K g (alg.x j) sp.xhat sp.yhat
        + dual_gap K h (alg.y (j + 2)) sp.yhat sp.xhat))
    ≤ (‖alg.x 1 - sp.xhat‖^2 / 2
        + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta))
      - (‖alg.x (N + 1) - sp.xhat‖^2 / 2
        + ‖alg.y (N + 1) - sp.yhat‖^2 / (2 * alg.beta)) := by
  let C : ℕ → ℝ := fun k => ‖alg.x k - sp.xhat‖^2 / 2
    + ‖alg.y k - sp.yhat‖^2 / (2 * alg.beta)
  calc
    _ ≤ ∑ j ∈ Finset.range N, (C (j + 1) - C (j + 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hdom : alg.x j ∈ g.dom := by
        cases j with
        | zero => exact hx0
        | succ j => exact x_mem_dom alg (j + 1) (by omega)
      have hprev : alg.x (j + 1 - 1) ∈ g.dom := by
        simpa only [Nat.add_sub_cancel] using hdom
      simpa [C, Nat.add_assoc] using pdal_gap_step alg sp (j + 1) (by omega) hprev
    _ = C 1 - C (N + 1) := by
      simpa only [Nat.zero_add, Nat.add_assoc] using
        (Finset.sum_range_sub' (fun j => C (j + 1)) N)

/-! ### 遍历率：权重与Jensen辅助 -/

/-- θ 的全局非负性。 -/
lemma theta_nonneg (alg : PDAL K g h) : ∀ k, 0 ≤ alg.theta k := by
  intro k
  by_cases hk : k = 0
  · subst k; rw [alg.theta0_eq]; norm_num
  · have hk1 : k ≥ 1 := by omega
    rw [alg.theta_def k hk1]
    exact div_nonneg (le_of_lt (tau_pos alg k)) (le_of_lt (tau_pos alg (k - 1)))

/-- 遍历权 `w_k = τ_{k+1}(1+θ_{k+1}) − τ_{k+2}θ_{k+2}` 非负（k ≤ N−2）。 -/
lemma pdal_weight_nonneg (alg : PDAL K g h) :
    ∀ N k, k + 2 ≤ N →
      0 ≤ alg.tau (k + 1) * (1 + alg.theta (k + 1))
        - alg.tau (k + 2) * alg.theta (k + 2) := by
  intro N k hk
  have h1 : alg.theta (k + 2) * alg.tau (k + 2)
      ≤ (1 + alg.theta (k + 1)) * alg.tau (k + 1) := by
    have hb := theta_tau_bound alg (k + 2) (by omega)
    have hshift : k + 2 - 1 = k + 1 := by omega
    rw [hshift] at hb
    exact hb
  have hτ1 : 0 ≤ alg.tau (k + 1) := le_of_lt (tau_pos alg (k + 1))
  have hθ1 : 0 ≤ 1 + alg.theta (k + 1) := by linarith [theta_nonneg alg (k + 1)]
  linarith [mul_comm (alg.tau (k + 2)) (alg.theta (k + 2)), h1]

/-- 遍历率主权的非负性：末权 `τN(1+θN) > 0`，前权非负。 -/
lemma pdal_weight_last_pos (alg : PDAL K g h) (N : ℕ) (hN : 1 ≤ N) :
    0 < alg.tau N * (1 + alg.theta N) := by
  have hτ : 0 < alg.tau N := tau_pos alg N
  have hθ : 0 < 1 + alg.theta N := by linarith [theta_nonneg alg N]
  exact mul_pos hτ hθ

/-- 望远和：`∑_{k∈range m} (f(k+1) − f(k+2)) = f 1 − f (m+1)`。 -/
lemma pdal_telescope_shift (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ Finset.range m, (f (k + 1) - f (k + 2)))
      = f 1 - f (m + 1) := by
  have h := Finset.sum_range_sub' (fun j => f (j + 1)) m
  simpa only [Nat.add_assoc] using h

/-- 权重和恒等式（对 k ∈ range N 使用指标平移后的 wfun）。 -/
lemma pdal_weight_sum (alg : PDAL K g h) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range N, (alg.tau (k + 1) * (1 + alg.theta (k + 1))
        - (if h : k + 1 < N then alg.tau (k + 2) * alg.theta (k + 2) else 0)))
      = alg.tau 1 * alg.theta 1
        + ∑ k ∈ Finset.range N, alg.tau (k + 1) := by
  cases N with
  | zero => omega
  | succ m =>
    -- 望远和：∑_{k∈range m} (τ(k+1)θ(k+1) − τ(k+2)θ(k+2)) = τ1θ1 − τ(m+1)θ(m+1)
    have htel : (∑ k ∈ Finset.range m,
        (alg.tau (k + 1) * alg.theta (k + 1)
          - alg.tau (k + 2) * alg.theta (k + 2)))
        = alg.tau 1 * alg.theta 1
          - alg.tau (m + 1) * alg.theta (m + 1) :=
      pdal_telescope_shift (fun j => alg.tau j * alg.theta j) m
    -- range m 内减项全部激活（k + 1 < m + 1）
    have hinner :
        (∑ k ∈ Finset.range m,
          (alg.tau (k + 1) * (1 + alg.theta (k + 1))
            - (if h : k + 1 < m + 1 then
                alg.tau (k + 2) * alg.theta (k + 2) else 0)))
          = (∑ k ∈ Finset.range m, alg.tau (k + 1))
            + (alg.tau 1 * alg.theta 1
              - alg.tau (m + 1) * alg.theta (m + 1)) := by
      calc
        _ = ∑ k ∈ Finset.range m,
            (alg.tau (k + 1)
              + (alg.tau (k + 1) * alg.theta (k + 1)
                - alg.tau (k + 2) * alg.theta (k + 2))) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk1 : k + 1 < m + 1 := by
            have hk' := Finset.mem_range.mp hk
            omega
          rw [dif_pos hk1]
          ring
        _ = (∑ k ∈ Finset.range m, alg.tau (k + 1))
            + (∑ k ∈ Finset.range m,
                (alg.tau (k + 1) * alg.theta (k + 1)
                  - alg.tau (k + 2) * alg.theta (k + 2))) :=
          Finset.sum_add_distrib
        _ = _ := by rw [htel]
    -- 拆出末项（range (m+1) = range m + {m}）
    rw [Finset.sum_range_succ]
    simp only [dif_neg (Nat.lt_irrefl (m + 1)), sub_zero]
    rw [hinner]
    -- 剩余为线性恒等式
    rw [Finset.sum_range_succ (fun k => alg.tau (k + 1)) m]
    ring

/-- 权重的 ℝ 值函数（k ∈ range N 时使用；k = N−1 处减项为 0）。 -/
def pdalWeight (alg : PDAL K g h) (N k : ℕ) : ℝ :=
  alg.tau (k + 1) * (1 + alg.theta (k + 1))
    - (if k + 1 < N then alg.tau (k + 2) * alg.theta (k + 2) else 0)

/-- 权重的非负性（k ∈ range N）。 -/
lemma pdalWeight_nonneg (alg : PDAL K g h) (N : ℕ) {k : ℕ} (hk : k ∈ Finset.range N) :
    0 ≤ pdalWeight alg N k := by
  unfold pdalWeight
  by_cases hlast : k + 1 = N
  · rw [if_neg (by omega : ¬ (k + 1 < N))]
    have : 0 ≤ alg.tau (k + 1) * (1 + alg.theta (k + 1)) := by
      apply mul_nonneg (le_of_lt (tau_pos alg (k + 1)))
      linarith [theta_nonneg alg (k + 1)]
    linarith
  · have hlt : k + 1 < N := by
      have hk' := Finset.mem_range.mp hk
      omega
    rw [if_pos hlt]
    exact pdal_weight_nonneg alg N k hlt

/-- 权重和：∑_{k∈range N} w_k = τ1θ1 + sN。 -/
lemma pdalWeight_sum (alg : PDAL K g h) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range N, pdalWeight alg N k)
      = alg.tau 1 * alg.theta 1 + ∑ k ∈ Finset.range N, alg.tau (k + 1) := by
  unfold pdalWeight
  exact pdal_weight_sum alg N hN

/-- 单点提取：∑_{k∈range m} (若 k = j 取 c 否则 0) • z = c • z（j < m）。 -/
lemma pdal_sum_single {M : Type*} [AddCommGroup M] [Module ℝ M]
    (z : M) (m j : ℕ) (c : ℝ) (hj : j < m) :
    (∑ k ∈ Finset.range m, (if k = j then c else (0:ℝ)) • z) = c • z := by
  rw [← Finset.sum_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range.mpr hj, if_true]

/-- 权重向量恒等式：w 权组合等于 τ1θ1•x0 + ∑ τ(k+1)•xbar(k+1)（N ≥ 1）。 -/
lemma pdal_weight_vec (alg : PDAL K g h) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.range N, pdalWeight alg N k • alg.x (k + 1))
      = (alg.tau 1 * alg.theta 1) • alg.x 0
        + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1) := by
  cases N with
  | zero => omega
  | succ m =>
    set z : ℕ → X := fun j =>
      (alg.tau (j + 1) * alg.theta (j + 1)) • alg.x j with hz
    have hstep : ∀ k ∈ Finset.range m,
        pdalWeight alg (m + 1) k • alg.x (k + 1)
          = alg.tau (k + 1) • xbar alg (k + 1)
            + (z k - z (k + 1)) := by
      intro k hk
      have hk1 : k + 1 < m + 1 := by
        have hk' := Finset.mem_range.mp hk
        omega
      simp only [pdalWeight, if_pos hk1, xbar, z,
        Nat.add_sub_cancel, Nat.add_assoc, sub_smul, mul_smul,
        add_smul, one_smul, smul_add, smul_sub]
      abel
    have hlast :
        pdalWeight alg (m + 1) m • alg.x (m + 1)
          = alg.tau (m + 1) • xbar alg (m + 1) + z m := by
      simp only [pdalWeight, if_neg (Nat.lt_irrefl (m + 1)),
        sub_zero, xbar, z, Nat.add_sub_cancel, mul_smul,
        add_smul, one_smul, smul_add, smul_sub]
      abel
    have htel : (∑ k ∈ Finset.range m, (z k - z (k + 1)))
        = z 0 - z m := Finset.sum_range_sub' z m
    have hinner :
        (∑ k ∈ Finset.range m,
          pdalWeight alg (m + 1) k • alg.x (k + 1))
          = (∑ k ∈ Finset.range m,
              alg.tau (k + 1) • xbar alg (k + 1)) + (z 0 - z m) := by
      calc
        _ = ∑ k ∈ Finset.range m,
            (alg.tau (k + 1) • xbar alg (k + 1)
              + (z k - z (k + 1))) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hstep k hk
        _ = _ := by rw [Finset.sum_add_distrib, htel]
    rw [Finset.sum_range_succ, hlast, hinner]
    rw [Finset.sum_range_succ
      (fun k => alg.tau (k + 1) • xbar alg (k + 1)) m]
    dsimp [z]
    abel

/-- 标量权重恒等式：∑ w_k·f(k+1) = a·f0 + ∑ τ(k+1)·((1+θ(k+1))f(k+1) − θ(k+1)f k)。 -/
lemma pdal_weight_values (alg : PDAL K g h) (N : ℕ) (hN : 1 ≤ N)
    (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range N, pdalWeight alg N k * f (k + 1))
      = (alg.tau 1 * alg.theta 1) * f 0
        + ∑ k ∈ Finset.range N,
          alg.tau (k + 1) * ((1 + alg.theta (k + 1)) * f (k + 1)
            - alg.theta (k + 1) * f k) := by
  cases N with
  | zero => omega
  | succ m =>
    set z : ℕ → ℝ := fun j =>
      alg.tau (j + 1) * alg.theta (j + 1) * f j with hz
    have hstep : ∀ k ∈ Finset.range m,
        pdalWeight alg (m + 1) k * f (k + 1)
          = alg.tau (k + 1) *
              ((1 + alg.theta (k + 1)) * f (k + 1)
                - alg.theta (k + 1) * f k)
            + (z k - z (k + 1)) := by
      intro k hk
      have hk1 : k + 1 < m + 1 := by
        have hk' := Finset.mem_range.mp hk
        omega
      simp only [pdalWeight, if_pos hk1, z, Nat.add_assoc]
      ring
    have hlast :
        pdalWeight alg (m + 1) m * f (m + 1)
          = alg.tau (m + 1) *
              ((1 + alg.theta (m + 1)) * f (m + 1)
                - alg.theta (m + 1) * f m) + z m := by
      simp only [pdalWeight, if_neg (Nat.lt_irrefl (m + 1)), sub_zero, z]
      ring
    have htel : (∑ k ∈ Finset.range m, (z k - z (k + 1)))
        = z 0 - z m := Finset.sum_range_sub' z m
    have hinner :
        (∑ k ∈ Finset.range m, pdalWeight alg (m + 1) k * f (k + 1))
          = (∑ k ∈ Finset.range m,
              alg.tau (k + 1) * ((1 + alg.theta (k + 1)) * f (k + 1)
                - alg.theta (k + 1) * f k)) + (z 0 - z m) := by
      calc
        _ = ∑ k ∈ Finset.range m,
            (alg.tau (k + 1) * ((1 + alg.theta (k + 1)) * f (k + 1)
              - alg.theta (k + 1) * f k) + (z k - z (k + 1))) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hstep k hk
        _ = _ := by rw [Finset.sum_add_distrib, htel]
    rw [Finset.sum_range_succ, hlast, hinner]
    rw [Finset.sum_range_succ (fun k => alg.tau (k + 1) *
      ((1 + alg.theta (k + 1)) * f (k + 1) - alg.theta (k + 1) * f k)) m]
    dsimp [z]
    ring

/-- Jensen 组合辅助：非负权、正总权下，加权平均点属于凸集且凸函数值受加权和控制。 -/
lemma pdal_jensen_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (s : Set E) (f : E → ℝ) (hf : ConvexOn ℝ s f)
    (w : ℕ → ℝ) (p : ℕ → E) (N : ℕ)
    (hw : ∀ k ∈ Finset.range N, 0 ≤ w k)
    (hW : 0 < ∑ k ∈ Finset.range N, w k)
    (hp : ∀ k ∈ Finset.range N, p k ∈ s) :
    ((1 / (∑ k ∈ Finset.range N, w k)) •
        ∑ k ∈ Finset.range N, w k • p k) ∈ s ∧
      f ((1 / (∑ k ∈ Finset.range N, w k)) •
          ∑ k ∈ Finset.range N, w k • p k)
        ≤ (1 / (∑ k ∈ Finset.range N, w k)) *
          ∑ k ∈ Finset.range N, w k * f (p k) := by
  constructor
  · simpa only [Finset.centerMass, one_div] using
      hf.1.centerMass_mem hw hW hp
  · simpa only [Finset.centerMass, Function.comp_apply, smul_eq_mul, one_div] using
      hf.map_centerMass_le hw hW hp

theorem pdal_ergodic_rate (alg : PDAL K g h) (sp : SaddlePoint K g h)
    (hx0 : alg.x 0 ∈ g.dom) :
    ∀ N ≥ 1,
      let s_N := (List.range N).foldl (fun acc k => acc + alg.tau (k + 1)) 0
      let X_N := (1 / (alg.tau 1 * alg.theta 1 + s_N)) •
        ((alg.tau 1 * alg.theta 1) • alg.x 0 +
          (List.range N).foldl (fun acc k => acc + alg.tau (k + 1) • xbar alg (k + 1)) 0)
      let Y_N := (1 / s_N) •
        (List.range N).foldl (fun acc k => acc + alg.tau (k + 1) • alg.y (k + 2)) 0
      pd_gap K g h X_N Y_N sp.xhat sp.yhat
      ≤ (1 / s_N) * (‖alg.x 1 - sp.xhat‖^2 / 2
        + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
        + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat) := by
  intro N hN
  -- 权重记号：W = τ1θ1 + sN
  set W : ℝ := alg.tau 1 * alg.theta 1
    + (List.range N).foldl (fun acc k => acc + alg.tau (k + 1)) 0 with hW
  have hW_pos : 0 < W := by
    have h1 : 0 < alg.tau 1 * alg.theta 1 := by
      have hτ : 0 < alg.tau 1 := tau_pos alg 1
      have hθ : 0 < alg.theta 1 := by
        rw [alg.theta_def 1 (by omega)]
        exact div_pos (tau_pos alg 1) (tau_pos alg 0)
      exact mul_pos hτ hθ
    have h2 : 0 ≤ (List.range N).foldl (fun acc k => acc + alg.tau (k + 1)) 0 := by
      have hsum : (List.range N).foldl (fun acc k => acc + alg.tau (k + 1)) 0
          = ∑ k ∈ Finset.range N, alg.tau (k + 1) :=
        pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1)) N
      rw [hsum]
      exact Finset.sum_nonneg (fun i _ => le_of_lt (tau_pos alg (i + 1)))
    rw [hW]
    linarith
  -- 率主体
  -- foldl restated as Finset sums via the general lemma
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1)) N]
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1) • xbar alg (k + 1)) N]
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1) • alg.y (k + 2)) N]
  -- 记号：s = Στ(k+1)，a = τ1θ1，W = s + a
  set s : ℝ := ∑ k ∈ Finset.range N, alg.tau (k + 1) with hs_def
  set a : ℝ := alg.tau 1 * alg.theta 1 with ha_def
  have hs_pos : 0 < s := by
    rw [hs_def]
    apply Finset.sum_pos'
    · intro k hk
      exact le_of_lt (tau_pos alg (k + 1))
    · exact ⟨0, Finset.mem_range.mpr (by omega), by simpa using tau_pos alg 1⟩
  have ha_nn : 0 ≤ a := by
    rw [ha_def]
    exact mul_nonneg (le_of_lt (tau_pos alg 1)) (theta_nonneg alg 1)
  have hW_eq : W = s + a := by
    have h1 : W = a + ∑ k ∈ Finset.range N, alg.tau (k + 1) := by
      simpa only [ha_def] using
        (pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1)) N ▸ hW)
    rw [h1, hs_def]
    ring
  -- C1：初始距离常数
  set C1 : ℝ := ‖alg.x 1 - sp.xhat‖^2 / 2
    + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta) with hC1
  have hC1_nn : 0 ≤ C1 := by
    rw [hC1]
    apply add_nonneg
    · exact div_nonneg (sq_nonneg _) (by norm_num)
    · exact div_nonneg (sq_nonneg _) (by linarith [alg.beta_pos])
  -- P0 = P(x0)，a·P0 ≥ 0
  have hP0_nn : 0 ≤ primal_gap K g (alg.x 0) sp.xhat sp.yhat :=
    primal_gap_nonneg K g h sp (alg.x 0) hx0
  have hap0_nn : 0 ≤ a * primal_gap K g (alg.x 0) sp.xhat sp.yhat := by
    rw [ha_def]
    exact mul_nonneg (le_of_lt (mul_pos (tau_pos alg 1)
      (by rw [alg.theta_def 1 (by omega)]; exact div_pos (tau_pos alg 1) (tau_pos alg 0))))
      hP0_nn
  -- 权重：pdalWeight 非负，总权 W
  have hw_nn : ∀ k ∈ Finset.range N, 0 ≤ pdalWeight alg N k :=
    fun k hk => pdalWeight_nonneg alg N hk
  have hWsum : ∑ k ∈ Finset.range N, pdalWeight alg N k = W := by
    rw [pdalWeight_sum alg N hN, hW_eq, hs_def, ha_def]
    ring
  have hWsum_pos : 0 < ∑ k ∈ Finset.range N, pdalWeight alg N k := by
    rw [hWsum]; exact hW_pos
  -- Primal Jensen：点为 x(k+1) ∈ dom g
  have hxmem : ∀ k ∈ Finset.range N, alg.x (k + 1) ∈ g.dom :=
    fun k _ => x_mem_dom alg (k + 1) (by omega)
  obtain ⟨hXN_dom, hP_XN⟩ := pdal_jensen_sum g.dom
    (fun x => primal_gap K g x sp.xhat sp.yhat) (primal_gap_convex K g sp.xhat sp.yhat)
    (pdalWeight alg N) (fun k => alg.x (k + 1)) N hw_nn hWsum_pos hxmem
  -- XN = (1/W)·(a•x0 + Στ(k+1)•xbar(k+1))：权重向量恒等式
  have hXN_eq : (1 / W) • ((a) • alg.x 0
      + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1))
      = (1 / W) • ∑ k ∈ Finset.range N, pdalWeight alg N k • alg.x (k + 1) :=
    congrArg (fun v : X => (1 / W) • v) (pdal_weight_vec alg N hN).symm
  -- Jensen 值的右端改写为 A/W
  have hA : ∑ k ∈ Finset.range N, pdalWeight alg N k
      * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat
      = a * primal_gap K g (alg.x 0) sp.xhat sp.yhat
        + ∑ k ∈ Finset.range N,
          alg.tau (k + 1) * ((1 + alg.theta (k + 1))
            * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat
          - alg.theta (k + 1) * primal_gap K g (alg.x k) sp.xhat sp.yhat) := by
    rw [pdal_weight_values alg N hN
      (fun j => primal_gap K g (alg.x j) sp.xhat sp.yhat)]
  -- Dual Jensen：权 τ(k+1)/s
  have hyτ_nn : ∀ k ∈ Finset.range N, 0 ≤ alg.tau (k + 1) :=
    fun k _ => le_of_lt (tau_pos alg (k + 1))
  have hs_sum_pos : 0 < ∑ k ∈ Finset.range N, alg.tau (k + 1) := hs_pos
  have hymem : ∀ k ∈ Finset.range N, alg.y (k + 2) ∈ h.dom := by
    intro k hk
    exact (alg.dual_update (k + 1) (by omega)).1
  obtain ⟨hYN_dom, hD_YN⟩ := pdal_jensen_sum h.dom
    (fun y => dual_gap K h y sp.yhat sp.xhat) (dual_gap_convex K h sp.yhat sp.xhat)
    (fun k => alg.tau (k + 1)) (fun k => alg.y (k + 2)) N hyτ_nn hs_sum_pos hymem
  -- B = Σ τ(k+1) D(y(k+2))
  set B : ℝ := ∑ k ∈ Finset.range N,
    alg.tau (k + 1) * dual_gap K h (alg.y (k + 2)) sp.yhat sp.xhat with hB_def
  have hB_nn : 0 ≤ B := by
    rw [hB_def]
    exact Finset.sum_nonneg (fun k _ =>
      mul_nonneg (le_of_lt (tau_pos alg (k + 1)))
        (dual_gap_nonneg K g h sp (alg.y (k + 2)) ((alg.dual_update (k + 1) (by omega)).1)))
  -- pdal_gap_sum：A' + B ≤ C1 + a·P0 − Cend，其中
  -- A' = Σ τ(k+1)((1+θ)P(x(k+1)) − θP(x k))
  set A' : ℝ := ∑ k ∈ Finset.range N,
    alg.tau (k + 1) * ((1 + alg.theta (k + 1))
      * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat
    - alg.theta (k + 1) * primal_gap K g (alg.x k) sp.xhat sp.yhat) with hA'_def
  have hgap : A' + B ≤ C1
      - (‖alg.x (N + 1) - sp.xhat‖^2 / 2
        + ‖alg.y (N + 1) - sp.yhat‖^2 / (2 * alg.beta)) := by
    have hsum := pdal_gap_sum alg sp hx0 N
    simp_rw [mul_add] at hsum
    rw [Finset.sum_add_distrib] at hsum
    exact hsum
  -- A = a·P0 + A'，且 a·P0 ≥ 0
  have hA_eq : ∑ k ∈ Finset.range N, pdalWeight alg N k
      * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat
      = a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A' := hA
  -- P(XN) ≤ A/W = (a·P0 + A')/W，D(YN) ≤ B/s
  have hPbound : primal_gap K g
      ((1 / W) • ((a) • alg.x 0
        + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1))) sp.xhat sp.yhat
      ≤ (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / W := by
    have h1 := hP_XN
    rw [hWsum] at h1
    rw [← hXN_eq, hA_eq] at h1
    have h2 : (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / W
        = (1 / W) * (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') := by ring
    exact h2 ▸ h1
  have hDbound : dual_gap K h
      ((1 / s) • ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2))
      sp.yhat sp.xhat ≤ B / s := by
    have h1 : dual_gap K h
        ((1 / s) • ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2))
        sp.yhat sp.xhat ≤ (1 / s) * B := hD_YN
    have h2 : B / s = (1 / s) * B := by ring
    rw [h2]
    exact h1
  -- A ≥ 0（权非负、P ≥ 0）
  have hA_nn : 0 ≤ a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A' := by
    have h1 : 0 ≤ ∑ k ∈ Finset.range N, pdalWeight alg N k
        * primal_gap K g (alg.x (k + 1)) sp.xhat sp.yhat := by
      apply Finset.sum_nonneg
      intro k hk
      apply mul_nonneg (hw_nn k hk)
      exact primal_gap_nonneg K g h sp (alg.x (k + 1)) (hxmem k hk)
    rw [hA_eq] at h1
    exact h1
  -- 组合：G = P + D ≤ (aP0 + A')/W + B/s ≤ (aP0 + A' + B)/s ≤ (C1 + aP0)/s
  -- 目标（let 展开后）：
  show pd_gap K g h
      ((1 / (a + s)) • (a • alg.x 0
        + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1)))
      ((1 / s) • ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2))
      sp.xhat sp.yhat
    ≤ (1 / s) * (C1 + a * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
  have hW_as : W = a + s := by rw [hW_eq]; ring
  rw [← hW_as]
  have hgap2 : A' + B ≤ C1 := by
    have hCend : 0 ≤ ‖alg.x (N + 1) - sp.xhat‖^2 / 2
        + ‖alg.y (N + 1) - sp.yhat‖^2 / (2 * alg.beta) := by
      apply add_nonneg
      · exact div_nonneg (sq_nonneg _) (by norm_num)
      · exact div_nonneg (sq_nonneg _) (by linarith [alg.beta_pos])
    linarith [hgap, hCend]
  -- (aP0 + A')/W ≤ (aP0 + A')/s（分子非负，s ≤ W）
  have hdiv : (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / W
      ≤ (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / s :=
    div_le_div_of_nonneg_left hA_nn hs_pos (by
      rw [hW_eq]
      linarith [ha_nn])
  -- G = P(XN) + D(YN)（pd_gap 定义）
  have hG : pd_gap K g h
      ((1 / W) • (a • alg.x 0
        + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1)))
      ((1 / s) • ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2))
      sp.xhat sp.yhat
      ≤ (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / W + B / s := by
    simp only [pd_gap]
    linarith [hPbound, hDbound]
  -- P0 ≥ 0 使 aP0 + A' + B ≤ C1 + aP0
  have hfinal : (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / W + B / s
      ≤ (1 / s) * (C1 + a * primal_gap K g (alg.x 0) sp.xhat sp.yhat) := by
    have hdenom : 0 < s := hs_pos
    have hstep1 : (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / W + B / s
        ≤ (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A' + B) / s := by
      calc (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / W + B / s
          ≤ (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A') / s + B / s :=
            add_le_add_right hdiv _
        _ = _ := by ring
    have hstep2 : (a * primal_gap K g (alg.x 0) sp.xhat sp.yhat + A' + B) / s
        ≤ (C1 + a * primal_gap K g (alg.x 0) sp.xhat sp.yhat) / s :=
      (div_le_div_iff_of_pos_right hs_pos).mpr (by linarith [hgap2])
    have hstep3 : (C1 + a * primal_gap K g (alg.x 0) sp.xhat sp.yhat) / s
        = (1 / s) * (C1 + a * primal_gap K g (alg.x 0) sp.xhat sp.yhat) := by ring
    linarith [hstep1, hstep2, hstep3]
  linarith [hG, hfinal]

/-- **遍历平均点的定义域**：`X_N ∈ dom g`、`Y_N ∈ dom h`（N ≥ 1）。

X_N 是 x1..xN 的非负权凸组合（权重和 W = τ1θ1 + sN > 0），由权重向量恒等式
与 `Convex.centerMass_mem` 取得；Y_N 是 y2..y_{N+1} 的非负权平均。 -/
theorem pdal_ergodic_dom (alg : PDAL K g h) (N : ℕ) (hN : 1 ≤ N) :
    ((1 / (alg.tau 1 * alg.theta 1
        + ∑ k ∈ Finset.range N, alg.tau (k + 1))) •
      ((alg.tau 1 * alg.theta 1) • alg.x 0
        + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1))) ∈ g.dom
    ∧ ((1 / ∑ k ∈ Finset.range N, alg.tau (k + 1)) •
      ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2)) ∈ h.dom := by
  constructor
  · -- X_N = (1/W)·Σ w_k x(k+1)，权非负、总权 W > 0
    set W : ℝ := alg.tau 1 * alg.theta 1
      + ∑ k ∈ Finset.range N, alg.tau (k + 1) with hWdef
    have hW_pos : 0 < W := by
      rw [hWdef]
      have h1 : 0 < alg.tau 1 * alg.theta 1 := by
        have hτ : 0 < alg.tau 1 := tau_pos alg 1
        have hθ : 0 < alg.theta 1 := by
          rw [alg.theta_def 1 (by omega)]
          exact div_pos (tau_pos alg 1) (tau_pos alg 0)
        exact mul_pos hτ hθ
      have h2 : 0 ≤ ∑ k ∈ Finset.range N, alg.tau (k + 1) :=
        Finset.sum_nonneg (fun i _ => le_of_lt (tau_pos alg (i + 1)))
      linarith
    have hWsum_pos : 0 < ∑ k ∈ Finset.range N, pdalWeight alg N k := by
      rw [pdalWeight_sum alg N hN]
      linarith
    have hWsum' : ∑ k ∈ Finset.range N, pdalWeight alg N k = W :=
      pdalWeight_sum alg N hN
    have hxmem : ∀ k ∈ Finset.range N, alg.x (k + 1) ∈ g.dom :=
      fun k _ => x_mem_dom alg (k + 1) (by omega)
    have hXN' := (pdal_jensen_sum g.dom (fun _ : X => (0:ℝ))
      (convexOn_const (0:ℝ) g.dom_convex)
      (pdalWeight alg N) (fun k => alg.x (k + 1)) N
      (fun k hk => pdalWeight_nonneg alg N hk) hWsum_pos hxmem).1
    -- 改写为原 XN 形式
    have hveq : ∑ k ∈ Finset.range N, pdalWeight alg N k • alg.x (k + 1)
        = (alg.tau 1 * alg.theta 1) • alg.x 0
          + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1) :=
      pdal_weight_vec alg N hN
    rw [hveq] at hXN'
    have hWinv : (1 / ∑ k ∈ Finset.range N, pdalWeight alg N k)
        = 1 / W := by
      rw [hWsum']
    rw [hWinv] at hXN'
    exact hXN'
  · -- Y_N = (1/s)·Σ τ(k+1) y(k+2)
    have hs_pos : 0 < ∑ k ∈ Finset.range N, alg.tau (k + 1) := by
      apply Finset.sum_pos'
      · intro k hk; exact le_of_lt (tau_pos alg (k + 1))
      · exact ⟨0, Finset.mem_range.mpr (by omega), by simpa using tau_pos alg 1⟩
    have hymem : ∀ k ∈ Finset.range N, alg.y (k + 2) ∈ h.dom := by
      intro k hk
      exact (alg.dual_update (k + 1) (by omega)).1
    have hYN := (pdal_jensen_sum h.dom (fun _ : Y => (0:ℝ))
      (convexOn_const (0:ℝ) h.dom_convex)
      (fun k => alg.tau (k + 1)) (fun k => alg.y (k + 2)) N
      (fun k _ => le_of_lt (tau_pos alg (k + 1))) hs_pos hymem).1
    exact hYN

/-- **O(1/N) 遍历率**：存在与 N 无关的常数 C ≥ 0 使
`G(X_N, Y_N) ≤ C / N`（N ≥ 1，需要 x0 ∈ dom g）。 -/
theorem pdal_ergodic_rate_O1 (alg : PDAL K g h) (sp : SaddlePoint K g h)
    (hx0 : alg.x 0 ∈ g.dom) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ≥ 1,
      let s_N := ∑ k ∈ Finset.range N, alg.tau (k + 1)
      let X_N := (1 / (alg.tau 1 * alg.theta 1 + s_N)) •
        ((alg.tau 1 * alg.theta 1) • alg.x 0
          + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1))
      let Y_N := (1 / s_N) •
        ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2)
      pd_gap K g h X_N Y_N sp.xhat sp.yhat ≤ C / N := by
  obtain ⟨τmin, hτmin_pos, hτmin_le⟩ := tau_lower_bound alg
  -- 常数：C = (C1 + τ1θ1P(x0)) / τmin
  refine ⟨(‖alg.x 1 - sp.xhat‖^2 / 2 + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
    + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat) / τmin,
    div_nonneg (add_nonneg (add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      (div_nonneg (sq_nonneg _) (by linarith [alg.beta_pos])))
      (mul_nonneg (mul_nonneg (le_of_lt (tau_pos alg 1)) (theta_nonneg alg 1))
        (primal_gap_nonneg K g h sp (alg.x 0) hx0))) (le_of_lt hτmin_pos),
    ?_⟩
  intro N hN
  -- s_N ≥ N·τmin（对常数函数求和直接计算）
  have h2 : ∑ k ∈ Finset.range N, (τmin : ℝ) = N * τmin := by
    rw [Finset.sum_const, Finset.card_range]
    simp [Nat.cast_mul]
  have hs_ge : ∑ k ∈ Finset.range N, alg.tau (k + 1) ≥ N * τmin := by
    calc ∑ k ∈ Finset.range N, alg.tau (k + 1)
        ≥ ∑ k ∈ Finset.range N, τmin :=
        Finset.sum_le_sum (fun k _ => hτmin_le (k + 1))
      _ = N * τmin := h2
  -- 直接使用率定理（其 let 形式与这里一致：foldl 形式先转为 Finset 和）
  have hrate := pdal_ergodic_rate alg sp hx0 N hN
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1)) N] at hrate
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1) • xbar alg (k + 1)) N] at hrate
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1) • alg.y (k + 2)) N] at hrate
  -- s_N = Σ τ(k+1) > 0
  have hs_pos : 0 < ∑ k ∈ Finset.range N, alg.tau (k + 1) := by
    apply Finset.sum_pos'
    · intro k hk; exact le_of_lt (tau_pos alg (k + 1))
    · exact ⟨0, Finset.mem_range.mpr hN, by simpa using tau_pos alg 1⟩
  have hNmin_pos : 0 < (N : ℝ) * τmin := by
    exact mul_pos (by exact_mod_cast hN) hτmin_pos
  have hC_nn : 0 ≤ ‖alg.x 1 - sp.xhat‖^2 / 2
      + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat := by
    apply add_nonneg
    · apply add_nonneg
      · exact div_nonneg (sq_nonneg _) (by norm_num)
      · exact div_nonneg (sq_nonneg _) (by linarith [alg.beta_pos])
    · exact mul_nonneg (mul_nonneg (le_of_lt (tau_pos alg 1)) (theta_nonneg alg 1))
        (primal_gap_nonneg K g h sp (alg.x 0) hx0)
  have hbound : (1 / (∑ k ∈ Finset.range N, alg.tau (k + 1)))
      * (‖alg.x 1 - sp.xhat‖^2 / 2
      + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
      ≤ (1 / ((N : ℝ) * τmin)) * (‖alg.x 1 - sp.xhat‖^2 / 2
      + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat) := by
    have h1 : 1 / (∑ k ∈ Finset.range N, alg.tau (k + 1))
        ≤ 1 / ((N : ℝ) * τmin) :=
      one_div_le_one_div_of_le hNmin_pos (by linarith)
    exact mul_le_mul_of_nonneg_right h1 hC_nn
  have hlast : (1 / ((N : ℝ) * τmin)) * (‖alg.x 1 - sp.xhat‖^2 / 2
      + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
      + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
      = ((‖alg.x 1 - sp.xhat‖^2 / 2 + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
        + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
        / τmin) / N := by
    field_simp
  have hrate'' : pd_gap K g h
      ((1 / (alg.tau 1 * alg.theta 1
          + ∑ k ∈ Finset.range N, alg.tau (k + 1))) •
        ((alg.tau 1 * alg.theta 1) • alg.x 0
          + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1)))
      ((1 / ∑ k ∈ Finset.range N, alg.tau (k + 1)) •
        ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2))
      sp.xhat sp.yhat
      ≤ ((‖alg.x 1 - sp.xhat‖^2 / 2 + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
        + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
        / τmin) / N := by
    have h2 : (1 / (∑ k ∈ Finset.range N, alg.tau (k + 1))) * (‖alg.x 1 - sp.xhat‖^2 / 2
        + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
        + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
        ≤ ((‖alg.x 1 - sp.xhat‖^2 / 2 + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
          + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
          / τmin) / N :=
      le_trans hbound (le_of_eq hlast)
    linarith [hrate, h2]
  exact hrate''

/-! ## 主定理：从原始数据直接得到全部结论

以下主定理以 `mkPDAL` 从原始数据 `x₀ ∈ X`、`y₁ ∈ Y`、`τ₀ > 0`、
`μ ∈ (0,1)`、`δ ∈ (0,1)`、`β > 0` 及任意合法选择器 `sel` 构造的序列为对象，
把有界性、聚点鞍点、整列收敛（条件）与遍历 O(1/N) 率直接连接，
不需要调用者再提供 PDAL 对象或任何算法正确性结论。

关于扩展实值模型：`ProperConvex` 把函数表示为 `f : E → ℝ` 定义在显式域
`dom` 上（域外视为 +∞）；indicators（域外 +∞）即取 `f ≡ 0`、`dom` 为约束集，
`lsc` 字段要求次水平集在 `E` 中闭，与一般 proper l.s.c. 凸函数模型一致。 -/

/-- 初始化等式：`mkPDAL` 的第 0 项就是原始数据。 -/
lemma mkPDAL_x0 (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x0 : X) (y1 : Y) (tau0 : ℝ) (htau0 : 0 < tau0)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ)) :
    (mkPDAL K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel).x 0 = x0 := rfl

/-- 初始化等式：`mkPDAL` 的对偶第 0 项就是 y₁。 -/
lemma mkPDAL_y0 (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x0 : X) (y1 : Y) (tau0 : ℝ) (htau0 : 0 < tau0)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ)) :
    (mkPDAL K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel).y 0 = y1 := rfl

/-- **主定理（原始数据 → 有界性 + 全部聚点鞍点 + 条件整列收敛）**。

给定原始数据 `x₀ ∈ X`（任意，无定义域要求）、`y₁ ∈ Y`、`τ₀ > 0`、
`μ ∈ (0,1)`、`δ ∈ (0,1)`、`β > 0` 与任意合法选择器 `sel`，令
`alg := mkPDAL …`。若存在鞍点，则：

1. 迭代序列 `(alg.x k, alg.y k)` 有界；
2. 每个聚点都是鞍点；
3. 存在鞍点聚点 `(x★, y★)`；
4. 若进一步 `g` 在 `dom g` 上连续且 `(τ_k)` 有上界，则整列收敛到鞍点。

第四部分的条件是论文 Theorem 1 的分析假设，不是算法输入；
前三部分不需要 `x₀ ∈ dom g`。 -/
theorem pdal_main
    (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x0 : X) (y1 : Y) (tau0 : ℝ) (htau0 : 0 < tau0)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ))
    (sp : SaddlePoint K g h) :
    let alg := mkPDAL K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel
    -- (1) 有界性
    IsBounded (Set.range fun k => (alg.x k, alg.y k))
    -- (2) 全部聚点都是鞍点
    ∧ (∀ (xstar : X) (ystar : Y),
        IsClusterPoint (fun k => (alg.x k, alg.y k)) (xstar, ystar) →
        IsSaddlePoint K g h xstar ystar)
    -- (3) 鞍点聚点存在
    ∧ (∃ xstar ystar,
        IsClusterPoint (fun k => (alg.x k, alg.y k)) (xstar, ystar) ∧
        IsSaddlePoint K g h xstar ystar)
    -- (4) 条件整列收敛
    ∧ ((ContinuousOn g.f g.dom ∧ (∃ M, ∀ k, alg.tau k ≤ M)) →
        ∃ xstar ystar,
          IsSaddlePoint K g h xstar ystar ∧
          Tendsto (fun k => alg.x k) atTop (𝓝 xstar) ∧
          Tendsto (fun k => alg.y k) atTop (𝓝 ystar)) := by
  intro alg
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact pdal_bounded alg sp
  · exact pdal_cluster_point_saddle alg sp
  · exact pdal_has_saddle_cluster_point alg sp
  · rintro ⟨g_cont, hTauUpper⟩
    exact pdal_convergence alg sp g_cont hTauUpper

/-- **主定理（原始数据 → 遍历 O(1/N) 率）**。

同一 `mkPDAL` 构造下，若 `x₀ ∈ dom g`，则存在常数 `C ≥ 0`（依赖
`‖x₁ - x̂‖²/2 + ‖y₁ - ŷ‖²/(2β) + τ₁θ₁P(x₀)` 与 `τ_min`，与 `N` 无关）使
遍历平均点的原始对偶间隙满足 `G(X_N, Y_N) ≤ C / N`（N ≥ 1）。
这里 `X_N = (τ₁θ₁x₀ + Στ_k x̄_k)/(τ₁θ₁+s_N)`、
`Y_N = (Στ_k y_{k+1})/s_N`（对偶平均采用 `y_{k+1}`，与式 (20) 及式 (25)
后的 `D(y_{k+1})` 求和一致）。 -/
theorem pdal_main_rate
    (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x0 : X) (y1 : Y) (tau0 : ℝ) (htau0 : 0 < tau0)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ))
    (sp : SaddlePoint K g h) (hx0 : x0 ∈ g.dom) :
    let alg := mkPDAL K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ≥ 1,
      let s_N := ∑ k ∈ Finset.range N, alg.tau (k + 1)
      let X_N := (1 / (alg.tau 1 * alg.theta 1 + s_N)) •
        ((alg.tau 1 * alg.theta 1) • alg.x 0
          + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1))
      let Y_N := (1 / s_N) •
        ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2)
      pd_gap K g h X_N Y_N sp.xhat sp.yhat ≤ C / N := by
  intro alg
  exact pdal_ergodic_rate_O1 alg sp hx0

/-- **主定理（原始数据 → 遍历界与平均点定义域、间隙非负的完整包装）**。

同一 `mkPDAL` 构造下，对任意 `N ≥ 1`：
- 平均点 `X_N ∈ dom g`、`Y_N ∈ dom h`（不需要 `x₀ ∈ dom g`）；
- 若 `x₀ ∈ dom g`，则 `0 ≤ G(X_N, Y_N) ≤ C₁ / s_N`，其中
  `C₁ = ‖x₁ - x̂‖²/2 + ‖y₁ - ŷ‖²/(2β) + τ₁θ₁P(x₀)` 是原有限常数，
  `s_N = Σ_{k=1}^N τ_k`；结合 `s_N ≥ N·τ_min` 得 O(1/N) 率。

`x₀ ∈ dom g` 只进入有限常数据率部分；平均点定义域与间隙非负对任意
初始点成立。 -/
theorem pdal_main_ergodic
    (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (x0 : X) (y1 : Y) (tau0 : ℝ) (htau0 : 0 < tau0)
    (mu delta beta : ℝ) (hm : 0 < mu ∧ mu < 1) (hd : 0 < delta ∧ delta < 1) (hb : 0 < beta)
    (sel : ℕ → ℝ → ℝ → ℝ)
    (hsel : ∀ (j : ℕ) (τ : ℝ), 0 < τ → ∀ θ : ℝ, 0 ≤ θ →
      sel j τ θ ≥ τ ∧ sel j τ θ ≤ τ * Real.sqrt (1 + θ))
    (sp : SaddlePoint K g h) :
    let alg := mkPDAL K g h x0 y1 tau0 htau0 mu delta beta hm hd hb sel hsel
    ∀ N ≥ 1,
      let s_N := ∑ k ∈ Finset.range N, alg.tau (k + 1)
      let X_N := (1 / (alg.tau 1 * alg.theta 1 + s_N)) •
        ((alg.tau 1 * alg.theta 1) • alg.x 0
          + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1))
      let Y_N := (1 / s_N) •
        ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2)
      -- 平均点落在定义域内、间隙非负（均不需要 x₀ ∈ dom g）
      X_N ∈ g.dom ∧ Y_N ∈ h.dom
      ∧ 0 ≤ pd_gap K g h X_N Y_N sp.xhat sp.yhat
      -- 若 x₀ ∈ dom g：G(X_N, Y_N) ≤ C₁ / s_N
      ∧ ((x0 ∈ g.dom) →
          pd_gap K g h X_N Y_N sp.xhat sp.yhat
            ≤ (‖alg.x 1 - sp.xhat‖^2 / 2 + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
              + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
              / s_N) := by
  intro alg N hN
  -- 定义域（不需要 x₀ ∈ dom g）
  have hdom := pdal_ergodic_dom alg N hN
  refine ⟨hdom.1, hdom.2, ?_, ?_⟩
  -- 间隙非负（只使用定义域，不需要 x₀ ∈ dom g）
  · exact pd_gap_nonneg K g h sp
      ((1 / (alg.tau 1 * alg.theta 1
          + ∑ k ∈ Finset.range N, alg.tau (k + 1))) •
        ((alg.tau 1 * alg.theta 1) • alg.x 0
          + ∑ k ∈ Finset.range N, alg.tau (k + 1) • xbar alg (k + 1)))
      hdom.1
      ((1 / ∑ k ∈ Finset.range N, alg.tau (k + 1)) •
        ∑ k ∈ Finset.range N, alg.tau (k + 1) • alg.y (k + 2))
      hdom.2
  -- 有限常数 / s_N 上界（x₀ ∈ dom g 只用在这里）
  intro hx0
  -- 原率定理
  have hrate := pdal_ergodic_rate alg sp hx0 N hN
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1)) N] at hrate
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1) • xbar alg (k + 1)) N] at hrate
  rw [pdal_foldl_range_eq_sum (fun k => alg.tau (k + 1) • alg.y (k + 2)) N] at hrate
  -- s_N > 0
  have hs_pos : 0 < ∑ k ∈ Finset.range N, alg.tau (k + 1) := by
    apply Finset.sum_pos'
    · intro k hk; exact le_of_lt (tau_pos alg (k + 1))
    · exact ⟨0, Finset.mem_range.mpr hN, by simpa using tau_pos alg 1⟩
  -- 重排 1/s_N * C₁ 为 C₁ / s_N
  have hmul : (1 / (∑ k ∈ Finset.range N, alg.tau (k + 1)))
      * (‖alg.x 1 - sp.xhat‖^2 / 2 + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
        + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
      = (‖alg.x 1 - sp.xhat‖^2 / 2 + ‖alg.y 1 - sp.yhat‖^2 / (2 * alg.beta)
        + alg.tau 1 * alg.theta 1 * primal_gap K g (alg.x 0) sp.xhat sp.yhat)
        / (∑ k ∈ Finset.range N, alg.tau (k + 1)) := by
    field_simp
  rw [← hmul]; exact hrate
