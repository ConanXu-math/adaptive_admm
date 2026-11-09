import UFGM.CompactMin

open Set Filter Topology

namespace UFGM

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

structure Kernel (Q : Set E) where
  value : E → ℝ
  derivative : E → E →L[ℝ] ℝ
  hasDerivative : ∀ x ∈ Q, HasFDerivWithinAt value (derivative x) Q x
  strong : ∀ x ∈ Q, ∀ y ∈ Q,
    value x + derivative x (y - x) + ‖y - x‖^2 / 2 ≤ value y

structure Regularizer (Q : Set E) where
  dom : Set E
  value : E → ℝ
  nonempty : dom.Nonempty
  subset : dom ⊆ Q
  convex : ConvexOn ℝ dom value
  lsc : ∀ c : ℝ, IsClosed {x | x ∈ dom ∧ value x ≤ c}

def bregman {Q : Set E} (d : Kernel Q) (x y : E) : ℝ :=
  d.value y - d.value x - d.derivative x (y - x)

theorem bregman_lower {Q : Set E} (d : Kernel Q) {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖y - x‖^2 / 2 ≤ bregman d x y := by
  unfold bregman
  linarith only [d.strong x hx y hy]

@[simp] theorem bregman_self {Q : Set E} (d : Kernel Q) (x : E) : bregman d x x = 0 := by
  simp [bregman]

theorem kernel_strongJensen {Q : Set E} (hQ : Convex ℝ Q) (d : Kernel Q) : StrongJensen Q d.value := by
  intro x hx y hy t ht ht₁
  let z := (1 - t) • x + t • y
  have hz : z ∈ Q := hQ hx hy (sub_nonneg.mpr ht₁) ht (by ring)
  have hxz : x - z = (-t) • (y - x) := by
    dsimp only [z]
    simp only [sub_smul, smul_sub, one_smul, neg_smul]
    abel
  have hyz : y - z = (1 - t) • (y - x) := by
    dsimp only [z]
    simp only [sub_smul, smul_sub, one_smul]
    abel
  have hx' := d.strong z hz x hx
  have hy' := d.strong z hz y hy
  rw [hxz, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht, mul_pow] at hx'
  rw [hyz, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht₁), mul_pow] at hy'
  have hxx := mul_le_mul_of_nonneg_left hx' (sub_nonneg.mpr ht₁)
  have hyy := mul_le_mul_of_nonneg_left hy' ht
  change d.value z ≤ (1 - t) * d.value x + t * d.value y - t * (1 - t) * ‖y - x‖^2 / 2
  nlinarith only [hxx, hyy]

def affineReg {Q : Set E} (ψ : Regularizer Q) (l : E →L[ℝ] ℝ) (c A : ℝ) (x : E) : ℝ :=
  l x + c + A * ψ.value x

theorem affineReg_convex {Q : Set E} (ψ : Regularizer Q) (l : E →L[ℝ] ℝ) (c : ℝ)
    {A : ℝ} (hA : 0 ≤ A) : ConvexOn ℝ ψ.dom (affineReg ψ l c A) := by
  refine ⟨ψ.convex.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hψ := ψ.convex.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hψ
  have hm := mul_le_mul_of_nonneg_left hψ hA
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  simp only [affineReg, smul_eq_mul, map_add, map_smul] at *
  nlinarith only [hm, hc]

theorem kernel_reg_closed_sublevel {Q : Set E} (hQc : IsClosed Q) (d : Kernel Q)
    (ψ : Regularizer Q) (l : E →L[ℝ] ℝ) (c : ℝ) {A : ℝ} (hA : 0 < A) (b : ℝ) :
    IsClosed {x | x ∈ ψ.dom ∧ d.value x + affineReg ψ l c A x ≤ b} := by
  let g := fun x : E => d.value x + l x + c
  let S : Set E := {x | x ∈ ψ.dom ∧ g x + A * ψ.value x ≤ b}
  have he : {x | x ∈ ψ.dom ∧ d.value x + affineReg ψ l c A x ≤ b} = S := by
    ext x
    simp only [S, mem_setOf_eq, g, affineReg, add_assoc]
  rw [he]
  apply closure_subset_iff_isClosed.mp
  intro z hz
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hz
  have hdom (n : ℕ) : u n ∈ ψ.dom := (hu n).1
  have huQ (n : ℕ) : u n ∈ Q := ψ.subset (hdom n)
  have hzQ := hQc.mem_of_tendsto hlim (Eventually.of_forall huQ)
  have hlimQ : Tendsto u atTop (𝓝[Q] z) := tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall huQ⟩
  have hg : ContinuousOn g Q := by
    have hd : ContinuousOn d.value Q := fun x hx => (d.hasDerivative x hx).continuousWithinAt
    exact (hd.add l.continuous.continuousOn).add continuousOn_const
  have hglim := (hg z hzQ).tendsto.comp hlimQ
  have hh (ε : ℝ) (hε : 0 < ε) : z ∈ ψ.dom ∧ ψ.value z ≤ (b - g z + ε) / A := by
    apply (ψ.lsc ((b - g z + ε) / A)).mem_of_tendsto hlim
    apply (hglim.eventually (eventually_gt_nhds (show g z - ε < g z by linarith))).mono
    intro n hn
    have hn' : g z - ε < g (u n) := hn
    refine ⟨hdom n, ?_⟩
    apply (le_div_iff₀ hA).2
    have h := (hu n).2
    nlinarith only [hn', h]
  refine ⟨(hh 1 zero_lt_one).1, ?_⟩
  change g z + A * ψ.value z ≤ b
  by_contra! hn
  let ε := (g z + A * ψ.value z - b) / 2
  have hε : 0 < ε := div_pos (sub_pos.mpr hn) (by norm_num)
  have h := (le_div_iff₀ hA).1 (hh ε hε).2
  dsimp only [ε] at h
  nlinarith only [h, hn]

theorem kernel_reg_min {Q : Set E} (hQc : IsClosed Q) (hQ : Convex ℝ Q) (d : Kernel Q)
    (ψ : Regularizer Q) (l : E →L[ℝ] ℝ) (c : ℝ) {A : ℝ} (hA : 0 < A) :
    ∃! v, v ∈ ψ.dom ∧ IsMinOn (fun x => d.value x + affineReg ψ l c A x) ψ.dom v := by
  apply strong_min_exists_unique ψ.dom _ ψ.convex.1 ψ.nonempty _
    (kernel_reg_closed_sublevel hQc d ψ l c hA)
  intro x hx y hy t ht ht₁
  have hd := kernel_strongJensen hQ d x (ψ.subset hx) y (ψ.subset hy) t ht ht₁
  have hg := (affineReg_convex ψ l c hA.le).2 hx hy (sub_nonneg.mpr ht₁) ht (show (1 - t) + t = 1 by ring)
  simp only [smul_eq_mul] at hg
  nlinarith only [hd, hg]

theorem min_bregman_support {Q D : Set E} (d : Kernel Q) (hD : D ⊆ Q)
    {G : E → ℝ} (hG : ConvexOn ℝ D G) {v w : E} (hv : v ∈ D) (hw : w ∈ D)
    (hm : IsMinOn (fun x => d.value x + G x) D v) :
    d.value v + G v + bregman d v w ≤ d.value w + G w := by
  let I := Ioc (0 : ℝ) 1
  let z := fun t : ℝ => v + t • (w - v)
  have hz (t : ℝ) (ht : t ∈ I) : z t ∈ D := by
    have h := hG.1 hv hw (sub_nonneg.mpr ht.2) ht.1.le (show (1 - t) + t = 1 by ring)
    have he : (1 - t) • v + t • w = z t := by dsimp only [z]; rw [sub_smul, one_smul, smul_sub]; abel
    rwa [he] at h
  have hz₀ : z 0 = v := by simp [z]
  have hzD : HasDerivWithinAt z (w - v) I 0 := by
    have H := (hasDerivAt_const (0 : ℝ) v).add ((hasDerivAt_id (0 : ℝ)).smul_const (w - v))
    simpa only [z, id_eq, zero_add, one_smul] using H.hasDerivWithinAt
  have hcomp := (d.hasDerivative v (hD hv)).comp_hasDerivWithinAt_of_eq (0 : ℝ) hzD
    (fun t ht => hD (hz t ht)) hz₀.symm
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ I by simp [I])).1 hcomp
  haveI : NeBot (𝓝[I] (0 : ℝ)) := left_nhdsWithin_Ioc_neBot zero_lt_one
  have hev : ∀ᶠ t in 𝓝[I] (0 : ℝ), G v - G w ≤ slope (d.value ∘ z) 0 t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hmin := (isMinOn_iff.1 hm) (z t) (hz t ht)
    have hcv := hG.2 hv hw (sub_nonneg.mpr ht.2) ht.1.le (show (1 - t) + t = 1 by ring)
    have he : (1 - t) • v + t • w = z t := by dsimp only [z]; rw [sub_smul, one_smul, smul_sub]; abel
    rw [he, smul_eq_mul, smul_eq_mul] at hcv
    rw [slope_def_field, Function.comp_apply, Function.comp_apply, hz₀, sub_zero]
    apply (le_div_iff₀ ht.1).2
    nlinarith only [hmin, hcv]
  have h := le_of_tendsto_of_tendsto tendsto_const_nhds hlim hev
  unfold bregman
  linarith only [h]

end
end UFGM
