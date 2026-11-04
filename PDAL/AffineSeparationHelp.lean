import Mathlib

/-!
# Affine minorant from proper l.s.c. convex data

Given a convex function `f : E → ℝ` on a convex domain `dom`, finite on `dom`,
with closed sublevel sets in `E` (l.s.c. in the extended sense), this file
constructs an affine minorant of `f` on `dom` via strict separation of the
point `(z₀, f z₀ - 1)` from the closed convex epigraph, following the
diagnosis provided by Codex:

* strict separation gives `ℓ p < u < ℓ q` for all `q` in the epigraph;
* writing `ℓ (z, t) = A z + b t` (Fréchet–Riesz on the finite-dimensional
  Hilbert space `WithLp 2 (E × ℝ)`), plugging `q = (z₀, f z₀)` and comparing
  with `p = (z₀, f z₀ - 1)` gives `b > 0`;
* then `c < A z + b f z` for all `z ∈ dom`, and dividing by `b` yields the
  affine minorant.
-/

open scoped InnerProductSpace

/-- Inner product on `ℝ` is multiplication. -/
theorem real_inner_mul (r s : ℝ) : ⟪r, s⟫_ℝ = r * s := by
  simp [RCLike.inner_apply, mul_comm]

/-- Any functional on `WithLp 2 (E × ℝ)` is of the form
`p ↦ ⟪a, p.1⟫ + b * p.2`. -/
theorem strongDual_repr_prod {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (ℓ : StrongDual ℝ (WithLp 2 (E × ℝ))) :
    ∃ (a : E) (b : ℝ), ∀ (p : WithLp 2 (E × ℝ)),
      ℓ p = ⟪a, (WithLp.ofLp p).1⟫_ℝ + b * (WithLp.ofLp p).2 := by
  obtain ⟨w, rfl⟩ := (InnerProductSpace.toDual ℝ (WithLp 2 (E × ℝ))).surjective ℓ
  refine ⟨WithLp.ofLp w |>.1, WithLp.ofLp w |>.2, fun p => ?_⟩
  show ((InnerProductSpace.toDual ℝ (WithLp 2 (E × ℝ))) w) p = _
  rw [InnerProductSpace.toDual_apply, WithLp.prod_inner_apply, real_inner_mul]

lemma affineVerticalCoeff_pos {a b c r : ℝ}
    (hp : a + b * (r - 1) < c)
    (hq : c < a + b * r) : 0 < b := by
  nlinarith

lemma affineLowerBound_of_strictSeparation {a b c r : ℝ}
    (hb : 0 < b) (hq : c < a + b * r) :
    (c - a) / b ≤ r := by
  apply (div_le_iff₀ hb).2
  nlinarith

/-- The linear functional representation composed with `prodContinuousLinearEquiv`:
any `ℓ` on `WithLp 2 (E × ℝ)` is `p ↦ ⟪a, z⟫ + b * t` where `(z, t) = ofLp p`. -/
lemma strongDual_repr_prod' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (ℓ : StrongDual ℝ (WithLp 2 (E × ℝ))) :
    ∃ (a : E) (b : ℝ), ∀ (z : E) (t : ℝ),
      ℓ (WithLp.toLp 2 (z, t)) = ⟪a, z⟫_ℝ + b * t := by
  obtain ⟨a, b, h⟩ := strongDual_repr_prod ℓ
  refine ⟨a, b, fun z t => ?_⟩
  have h2 := h (WithLp.toLp 2 (z, t))
  rw [show (WithLp.toLp 2 (z, t)).ofLp = (z, t) from rfl] at h2
  simpa using h2

/-- 从原始 l.s.c. 假设证明上镜图闭性。 -/
theorem isClosed_epigraph_of_lsc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (dom : Set E) (f : E → ℝ)
    (hlsc : ∀ c : ℝ, IsClosed {z : E | z ∈ dom ∧ f z ≤ c}) :
    IsClosed { p : WithLp 2 (E × ℝ) |
      (WithLp.ofLp p).1 ∈ dom ∧ f (WithLp.ofLp p).1 ≤ (WithLp.ofLp p).2 } := by
  have hcont : Continuous (fun p : WithLp 2 (E × ℝ) => ((WithLp.ofLp p).1, (WithLp.ofLp p).2)) := by
    exact WithLp.prod_continuous_ofLp (p := 2) (α := E) (β := ℝ)
  -- {q | q.1 ∈ dom ∧ f q.1 ≤ q.2} 的闭性直接由 lsc 子水平集通过序列论证：
  -- 对闭包中任一点 q，取收敛序列 u n，先用闭子水平集 {f ≤ q.2 + 1} 得 q.1 ∈ dom，
  -- 再反证：若 f q.1 > q.2，取 ε = (f q.1 - q.2)/2，闭子水平集 {f ≤ q.2 + ε}
  -- 与 (u n).2 < q.2 + ε 的最终成员性矛盾。
  have hclosed : IsClosed { q : E × ℝ | q.1 ∈ dom ∧ f q.1 ≤ q.2 } := by
    have hcl : closure { q : E × ℝ | q.1 ∈ dom ∧ f q.1 ≤ q.2 }
        ⊆ { q : E × ℝ | q.1 ∈ dom ∧ f q.1 ≤ q.2 } := by
      intro q hq
      -- via sequences: metric space
      rcases mem_closure_iff_seq_limit.mp hq with ⟨u, hu, hu_lim⟩
      open Filter Topology in
      have hsnd_lim : Tendsto (fun n => (u n).2) atTop (𝓝 q.2) :=
        (continuous_snd.tendsto q).comp hu_lim
      have hfst_lim : Tendsto (fun n => (u n).1) atTop (𝓝 q.1) :=
        (continuous_fst.tendsto q).comp hu_lim
      have hq_dom : ∀ n, (u n).1 ∈ dom := fun n => (hu n).1
      -- f (u n).1 ≤ (u n).2 and (u n).2 → q.2; use the closed sublevel set at q.2 + ε
      have hmem1 : q.1 ∈ dom ∧ f q.1 ≤ q.2 + 1 := by
        have hT : IsClosed {z : E | z ∈ dom ∧ f z ≤ q.2 + 1} := hlsc (q.2 + 1)
        have hT_ev : ∀ᶠ n in atTop, (u n).1 ∈ {z : E | z ∈ dom ∧ f z ≤ q.2 + 1} := by
          apply (hsnd_lim.eventually (eventually_lt_nhds (by linarith : q.2 < q.2 + 1))).mono
          intro n hn
          exact ⟨hq_dom n, le_trans (hu n).2 (le_of_lt hn)⟩
        exact hT.mem_of_tendsto hfst_lim hT_ev
      have hdom : q.1 ∈ dom := hmem1.1
      have hfle : f q.1 ≤ q.2 := by
        by_contra hfg
        -- f q.1 > q.2: take ε = (f q.1 - q.2)/2, contradiction
        set ε := (f q.1 - q.2) / 2 with hε_def
        have hε_pos : 0 < ε := by linarith
        have hT3 : IsClosed {z : E | z ∈ dom ∧ f z ≤ q.2 + ε} := hlsc (q.2 + ε)
        have hq2 : q.2 + ε < f q.1 := by linarith
        have hq2lt : q.2 < q.2 + ε := by linarith
        have hT3_ev : ∀ᶠ n in atTop, (u n).1 ∈ {z : E | z ∈ dom ∧ f z ≤ q.2 + ε} := by
          apply (hsnd_lim.eventually (eventually_lt_nhds hq2lt)).mono
          intro n hn
          exact ⟨hq_dom n, le_trans (hu n).2 (le_of_lt hn)⟩
        have hmem := hT3.mem_of_tendsto hfst_lim hT3_ev
        linarith [hmem.2]
      exact ⟨hdom, hfle⟩
    exact closure_subset_iff_isClosed.mp hcl
  -- transfer closedness to WithLp 2 (E × ℝ) via the continuous map
  have hseteq : { p : WithLp 2 (E × ℝ) | (WithLp.ofLp p).1 ∈ dom ∧ f (WithLp.ofLp p).1 ≤ (WithLp.ofLp p).2 }
      = (fun p : WithLp 2 (E × ℝ) => ((WithLp.ofLp p).1, (WithLp.ofLp p).2)) ⁻¹'
          { q : E × ℝ | q.1 ∈ dom ∧ f q.1 ≤ q.2 } := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_setOf_eq]
  rw [hseteq]
  exact hclosed.preimage hcont

/-- 从 proper l.s.c. 凸数据构造仿射下界（最终主引理）。

设 `dom ⊆ E` 凸且非空，`f : E → ℝ` 在 `dom` 上凸、有限，且所有子水平集
`{z ∈ dom | f z ≤ c}` 在 `E` 中闭（扩展意义下半连续）。则存在 `a : E` 与 `b : ℝ`
使得对一切 `z ∈ dom` 有 `f z ≥ ⟪a, z⟫_ℝ + b`。

证明思路（Codex 诊断）：取 `z₀ ∈ dom`，考虑点 `p = (z₀, f z₀ - 1)` 与闭凸上镜图
`epi = {(z,t) | z ∈ dom, f z ≤ t}`。严格分离给出 `ℓ p < u < ℓ q`（对所有 `q ∈ epi`）。
用乘积泛函表示 `ℓ (z,t) = ⟪a,z⟫ + b t`，比较 `q₁ = (z₀, f z₀)`（属 `epi`）与
`p = (z₀, f z₀ - 1)` 得 `b > 0`（`affineVerticalCoeff_pos`）。注意 `(z₀, f z₀)` ∈ epi
给出 `c < ⟪a,z₀⟫ + b f z₀`；而由 `b > 0` 与平移不变性（把 `a` 换成 `a/b·b` 后调整）
可从 `epi` 的竖直平移封闭性推出 `⟪a,z⟫ + b f z ≥ c + b t'` 对任意平移，
特别地 `b t' ≤ ⟪a,z₀⟫ + b f z₀ - c` 对一切 `t' > 0`，故 `b ≤ ...`；结合 `b > 0` 取
下界 `(c - ⟪a,·⟫)/b`。具体地：对 `q = (z, f z)`（`z ∈ dom`）有
`c < ⟪a,z⟫ + b f z`，且对 `z₀`、比较 `p` 得 `⟪a,z₀⟫ + b (f z₀ - 1) < c`，
两式联立由 `affineVerticalCoeff_pos` 得 `b > 0`，再由
`affineLowerBound_of_strictSeparation` 得 `f z ≥ (c - ⟪a,z⟫)/b`。 -/
theorem affine_minorant_of_lsc_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (dom : Set E) (f : E → ℝ)
    (hdom_ne : dom.Nonempty) (hdom_cvx : Convex ℝ dom)
    (hcvx : ConvexOn ℝ dom f)
    (hlsc : ∀ c : ℝ, IsClosed {z : E | z ∈ dom ∧ f z ≤ c}) :
    ∃ (a : E) (b : ℝ), ∀ z ∈ dom, f z ≥ ⟪a, z⟫_ℝ + b := by
  -- 上镜图：闭凸集
  set epi : Set (WithLp 2 (E × ℝ)) :=
    {p : WithLp 2 (E × ℝ) | (WithLp.ofLp p).1 ∈ dom ∧ f (WithLp.ofLp p).1 ≤ (WithLp.ofLp p).2}
  have hepi_cvx : Convex ℝ epi := by
    intro p hp q hq r s hrs hs hrsq
    obtain ⟨hzp, hfp⟩ := hp
    obtain ⟨hzq, hfq⟩ := hq
    -- transfer convexity from dom and f via ofLp linearity
    have hof : WithLp.ofLp (r • p + s • q) = r • (WithLp.ofLp p) + s • (WithLp.ofLp q) := by
      rw [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul]
    have hpair_eq : WithLp.ofLp (r • p + s • q)
        = (r • (WithLp.ofLp p).1 + s • (WithLp.ofLp q).1,
           r * (WithLp.ofLp p).2 + s * (WithLp.ofLp q).2) := by
      rw [hof]
      simp [Prod.smul_def, smul_eq_mul, Prod.add_def]
    -- 从 ofLp 表示恢复成员关系
    have hzmem : r • (WithLp.ofLp p).1 + s • (WithLp.ofLp q).1 ∈ dom :=
      convex_iff_add_mem.mp hdom_cvx hzp hzq hrs hs hrsq
    -- f 凸性：ConvexOn 展开为函数部分
    obtain ⟨_, hcvxfun⟩ := hcvx
    have hfmem : f (r • (WithLp.ofLp p).1 + s • (WithLp.ofLp q).1)
        ≤ r * f (WithLp.ofLp p).1 + s * f (WithLp.ofLp q).1 := by
      have h := hcvxfun hzp hzq hrs hs hrsq
      simpa [smul_eq_mul] using h
    have hmem' : (r • p + s • q).ofLp.1 = r • (WithLp.ofLp p).1 + s • (WithLp.ofLp q).1 ∧
        f (r • p + s • q).ofLp.1 ≤ (r • p + s • q).ofLp.2 := by
      rw [hpair_eq]
      refine ⟨rfl, ?_⟩
      show f (r • (WithLp.ofLp p).1 + s • (WithLp.ofLp q).1)
          ≤ r * (WithLp.ofLp p).2 + s * (WithLp.ofLp q).2
      have h1 : f (WithLp.ofLp p).1 ≤ (WithLp.ofLp p).2 := hfp
      have h2 : f (WithLp.ofLp q).1 ≤ (WithLp.ofLp q).2 := hfq
      calc f (r • (WithLp.ofLp p).1 + s • (WithLp.ofLp q).1)
          ≤ r * f (WithLp.ofLp p).1 + s * f (WithLp.ofLp q).1 := hfmem
        _ ≤ r * (WithLp.ofLp p).2 + s * (WithLp.ofLp q).2 := by
            nlinarith
    -- epi 成员关系：ofLp 分量满足定义
    show (r • p + s • q).ofLp.1 ∈ dom ∧
      f (r • p + s • q).ofLp.1 ≤ (r • p + s • q).ofLp.2
    rw [hpair_eq]
    constructor
    · exact hzmem
    · -- 目标：r * p.ofLp.2 + s * q.ofLp.2 ≤ f (组合点)；由 hfmem 与 hfp, hfq 线性组合
      have h1 : f (WithLp.ofLp p).1 ≤ (WithLp.ofLp p).2 := hfp
      have h2 : f (WithLp.ofLp q).1 ≤ (WithLp.ofLp q).2 := hfq
      calc f (r • (WithLp.ofLp p).1 + s • (WithLp.ofLp q).1)
          ≤ r * f (WithLp.ofLp p).1 + s * f (WithLp.ofLp q).1 := hfmem
        _ ≤ r * (WithLp.ofLp p).2 + s * (WithLp.ofLp q).2 := by
            have hrnn : 0 ≤ r := hrs
            have hsnn : 0 ≤ s := hs
            nlinarith
  -- 至此上镜图凸性证明完成
  obtain ⟨z₀, hz₀⟩ := hdom_ne
  -- 闭性：由 isClosed_epigraph_of_lsc（同文件中已证明的一般结论）
  have hepi_closed : IsClosed epi :=
    isClosed_epigraph_of_lsc (E := E) dom f hlsc
  -- 检查：该定理在文件后部定义；若前向引用失败需移动定义顺序
  -- 点 p = (z₀, f z₀ - 1) 不属于上镜图
  set p : WithLp 2 (E × ℝ) := WithLp.toLp 2 (z₀, f z₀ - 1) with hp_def
  have hp_not : p ∉ epi := by
    intro hmem
    simp only [epi, Set.mem_setOf_eq] at hmem
    rw [show p.ofLp = (z₀, f z₀ - 1) from rfl] at hmem
    -- f z₀ ≤ f z₀ - 1 矛盾
    linarith
  -- 严格分离
  obtain ⟨ℓ, u, hsep⟩ := geometric_hahn_banach_point_closed hepi_cvx hepi_closed hp_not
  obtain ⟨a, b, hℓ⟩ := strongDual_repr_prod' ℓ
  -- q₁ = (z₀, f z₀) ∈ epi
  have hq1 : WithLp.toLp 2 (z₀, f z₀) ∈ epi := by
    simp only [epi, Set.mem_setOf_eq, WithLp.ofLp_toLp]
    exact ⟨hz₀, le_rfl⟩
  -- qz = (z, f z) ∈ epi 对一切 z ∈ dom
  have hqz : ∀ z ∈ dom, WithLp.toLp 2 (z, f z) ∈ epi := by
    intro z hz
    simp only [epi, Set.mem_setOf_eq, WithLp.ofLp_toLp]
    exact ⟨hz, le_rfl⟩
  -- 竖直系数 b > 0
  have hb : 0 < b := by
    have h1 : ℓ p < u := hsep.1
    rw [hp_def] at h1
    rw [hℓ z₀ (f z₀ - 1)] at h1
    have h2 : u < ℓ (WithLp.toLp 2 (z₀, f z₀)) := hsep.2 _ hq1
    rw [hℓ z₀ (f z₀)] at h2
    exact affineVerticalCoeff_pos (a := ⟪a, z₀⟫_ℝ) (b := b) (c := u) (r := f z₀) h1 h2
  -- 仿射下界：由 ℓ(z, f z) = ⟪a,z⟫ + b f z > u 及 b > 0 得
  -- f z > (u - ⟪a,z⟫)/b，即 f z ≥ ⟪-(1/b)•a, z⟫_ℝ + u/b。
  refine ⟨(-(1/b)) • a, u / b, fun z hz => ?_⟩
  have hsep_z : u < ℓ (WithLp.toLp 2 (z, f z)) := hsep.2 _ (hqz z hz)
  rw [hℓ z (f z)] at hsep_z
  -- 目标：f z ≥ -(1/b)*⟪a,z⟫ + u/b，等价于 b * f z ≥ -⟪a,z⟫ + u，即 ⟪a,z⟫ + b f z ≥ u（由 hsep_z 严格不等给出 ≥）
  have hinner' : ⟪(-(1/b)) • a, z⟫_ℝ = -(1/b) * ⟪a, z⟫_ℝ := by
    rw [inner_smul_left, real_inner_comm]; simp
  have hgoal : -(1/b) * ⟪a, z⟫_ℝ + u / b ≤ f z := by
    have h1 : u ≤ ⟪a, z⟫_ℝ + b * f z := le_of_lt hsep_z
    have h2 : -(1/b) * ⟪a, z⟫_ℝ + u / b = (u - ⟪a, z⟫_ℝ) / b := by ring
    rw [h2]
    have h3 : u - ⟪a, z⟫_ℝ ≤ b * f z := by linarith
    rw [div_le_iff₀ hb, mul_comm]
    exact h3
  rw [hinner']
  exact hgoal

#print axioms isClosed_epigraph_of_lsc
#print axioms affine_minorant_of_lsc_convex
