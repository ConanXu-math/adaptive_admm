import Mathlib
import Optlib.Function.MinimaClosedFunction

open Set Filter Topology

namespace UFGM

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def StrongJensen (D : Set E) (J : E → ℝ) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    J ((1 - t) • x + t • y) ≤ (1 - t) * J x + t * J y - t * (1 - t) * ‖y - x‖^2 / 2

def extended (D : Set E) (J : E → ℝ) (x : E) : EReal := by
  classical
  exact if x ∈ D then (J x : EReal) else ⊤

theorem extended_sublevel (D : Set E) (J : E → ℝ) (c : ℝ) :
    extended D J ⁻¹' Iic (c : EReal) = {x | x ∈ D ∧ J x ≤ c} := by
  ext x
  by_cases hx : x ∈ D <;> simp [extended, hx, EReal.coe_le_coe_iff]

theorem extended_lsc (D : Set E) (J : E → ℝ)
    (hlsc : ∀ c : ℝ, IsClosed {x | x ∈ D ∧ J x ≤ c}) : LowerSemicontinuous (extended D J) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  cases c using EReal.rec with
  | bot =>
    have he : extended D J ⁻¹' Iic (⊥ : EReal) = ∅ := by
      ext x
      by_cases hx : x ∈ D <;> simp [extended, hx]
    rw [he]
    exact isClosed_empty
  | coe c => rw [extended_sublevel]; exact hlsc c
  | top => simp

theorem compact_sublevel (D : Set E) (J : E → ℝ) (hD : Convex ℝ D)
    (hJ : StrongJensen D J) (hlsc : ∀ c : ℝ, IsClosed {x | x ∈ D ∧ J x ≤ c})
    (b : E) (hb : b ∈ D) : IsCompact {x | x ∈ D ∧ J x ≤ J b} := by
  let low : Set E := {x | x ∈ D ∧ J x ≤ J b - 1}
  have hlow : IsClosed low := hlsc _
  have hbN : b ∈ lowᶜ := by
    intro H
    change b ∈ D ∧ J b ≤ J b - 1 at H
    linarith only [H.2]
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hlow.isOpen_compl.mem_nhds hbN)
  let R := max ρ (8 / ρ)
  have hsub : {x | x ∈ D ∧ J x ≤ J b} ⊆ Metric.closedBall b R := by
    intro y hy
    change y ∈ D ∧ J y ≤ J b at hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    by_contra! hn
    let r := ‖y - b‖
    change R < r at hn
    have hr : 0 < r := hρ.trans ((le_max_left ρ (8 / ρ)).trans_lt hn)
    have hρr : ρ < r := (le_max_left _ _).trans_lt hn
    have hlarge : 8 < ρ * r := by
      have h := (div_lt_iff₀ hρ).1 ((le_max_right ρ (8 / ρ)).trans_lt hn)
      simpa only [mul_comm] using h
    let t := ρ / (2 * r)
    have ht : 0 < t := div_pos hρ (by positivity)
    have ht2 : t ≤ 1 / 2 := by
      apply (div_le_iff₀ (show 0 < 2 * r by positivity)).2
      linarith only [hρr]
    have ht1 : t ≤ 1 := by linarith only [ht2]
    have htr : t * r = ρ / 2 := by
      dsimp only [t]
      field_simp [hr.ne'] <;> ring
    let z := (1 - t) • b + t • y
    have hzD : z ∈ D := hD hb hy.1 (sub_nonneg.mpr ht1) ht.le (by ring)
    have hzball : z ∈ Metric.ball b ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have he : z - b = t • (y - b) := by
        dsimp only [z]
        rw [sub_smul, one_smul, smul_sub]
        abel
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le]
      change t * r < ρ
      linarith only [htr, hρ]
    have hcoef : 1 / 2 ≤ 1 - t := by linarith only [ht2]
    have hprod := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hρ.le hr.le)
    have hdrop : 1 < t * (1 - t) * r^2 / 2 := by
      have he : t * (1 - t) * r^2 / 2 = (1 - t) * (ρ * r) / 4 := by
        calc
          _ = (t * r) * (1 - t) * r / 2 := by ring
          _ = _ := by rw [htr]; ring
      rw [he]
      linarith only [hprod, hlarge]
    have hJz := hJ b hb y hy.1 t ht.le ht1
    change J z ≤ (1 - t) * J b + t * J y - t * (1 - t) * r^2 / 2 at hJz
    have hy' := mul_le_mul_of_nonneg_left hy.2 ht.le
    have hzlow : z ∈ low := by
      refine ⟨hzD, ?_⟩
      nlinarith only [hJz, hy', hdrop]
    exact (hball hzball) hzlow
  exact Metric.isCompact_of_isClosed_isBounded (hlsc _) (Metric.isBounded_closedBall.subset hsub)

theorem strong_min_exists_unique (D : Set E) (J : E → ℝ) (hD : Convex ℝ D) (hne : D.Nonempty)
    (hJ : StrongJensen D J) (hlsc : ∀ c : ℝ, IsClosed {x | x ∈ D ∧ J x ≤ c}) :
    ∃! x, x ∈ D ∧ IsMinOn J D x := by
  obtain ⟨b, hb⟩ := hne
  have hbS : b ∈ extended D J ⁻¹' Iic (J b : EReal) := by
    rw [extended_sublevel]
    exact ⟨hb, le_rfl⟩
  have hc : IsCompact (extended D J ⁻¹' Iic (J b : EReal)) := by
    rw [extended_sublevel]
    exact compact_sublevel D J hD hJ hlsc b hb
  obtain ⟨x, hx⟩ := IsMinOn.of_isCompact_preimage (extended_lsc D J hlsc) ⟨b, hbS⟩ hc
  have hxS : x ∈ extended D J ⁻¹' Iic (J b : EReal) := by
    change extended D J x ≤ (J b : EReal)
    simpa only [extended, if_pos hb] using (isMinOn_iff.mp hx) b (mem_univ b)
  rw [extended_sublevel] at hxS
  have hxD : x ∈ D := hxS.1
  have hmin : IsMinOn J D x := isMinOn_iff.2 fun y hy => by
    have he := (isMinOn_iff.1 hx) y (mem_univ y)
    simpa only [extended, if_pos hxD, if_pos hy, EReal.coe_le_coe_iff] using he
  refine ⟨x, ⟨hxD, hmin⟩, ?_⟩
  intro y hy
  have hxy := (isMinOn_iff.1 hmin) y hy.1
  have hyx := (isMinOn_iff.1 hy.2) x hxD
  have he : J y = J x := le_antisymm hyx hxy
  let z := (1 - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y
  have hz : z ∈ D := hD hxD hy.1 (by norm_num) (by norm_num) (by norm_num)
  have hval := (isMinOn_iff.1 hmin) z hz
  have hmid := hJ x hxD y hy.1 (1 / 2) (by norm_num) (by norm_num)
  change J z ≤ (1 - (1 / 2 : ℝ)) * J x + (1 / 2 : ℝ) * J y -
    (1 / 2 : ℝ) * (1 - 1 / 2) * ‖y - x‖^2 / 2 at hmid
  rw [he] at hmid
  by_contra hne'
  have hpos : 0 < ‖y - x‖^2 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne')) 2
  linarith only [hval, hmid, hpos]

end
end UFGM
