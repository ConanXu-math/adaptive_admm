import DRS.Relations
import DRS.BallExtension

/-!
# Minty's theorem: full domain of the resolvent of a maximal monotone relation

For a maximal monotone relation `A` on a complete real inner product space and `t > 0`,
every point `p` admits `x` with `(1/t) • (p - x) ∈ A x`.
-/

open scoped InnerProductSpace

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E → Set E}

theorem IsMaximalMonotoneRel.resolvent_exists (hA : IsMaximalMonotoneRel A)
    {t : ℝ} (ht : 0 < t) (p : E) : ∃ x, (1 / t) • (p - x) ∈ A x := by
  classical
  let G := {z : E × E // z.2 ∈ A z.1}
  let plus (u : G) := u.1.1 + t • u.1.2
  let minus (u : G) := u.1.1 - t • u.1.2
  obtain ⟨q, hq⟩ := ball_family_intersection plus minus p
    (fun u v => hA.1.cayley_nonexpansive ht u.2 v.2 rfl rfl)
  let x := (1 / 2 : ℝ) • (p + q)
  let c := (1 / t) • (p - x)
  have hs : t • c = p - x := by
    dsimp [c]
    rw [smul_smul, mul_one_div_cancel ht.ne', one_smul]
  have hp : p = x + t • c := by
    rw [hs]
    module
  have hqeq : q = x - t • c := by
    rw [hs]
    dsimp [x]
    module
  refine ⟨x, hA.2 x c ?_⟩
  intro y b hb
  have hineq := hq (⟨(y, b), hb⟩ : G)
  change ‖q - (y - t • b)‖ ≤ ‖p - (y + t • b)‖ at hineq
  rw [hp, hqeq] at hineq
  have hL : (x - t • c) - (y - t • b) = (x - y) - t • (c - b) := by module
  have hR : (x + t • c) - (y + t • b) = (x - y) + t • (c - b) := by module
  rw [hL, hR] at hineq
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hineq 2
  rw [norm_sub_sq_real, norm_add_sq_real, real_inner_smul_right] at hsq
  have hn : 0 ≤ t * ⟪x - y, c - b⟫_ℝ := by linarith
  exact nonneg_of_mul_nonneg_right hn ht

theorem IsMaximalMonotoneRel.resolvent_existsUnique (hA : IsMaximalMonotoneRel A)
    {t : ℝ} (ht : 0 < t) (p : E) : ∃! x, (1 / t) • (p - x) ∈ A x := by
  obtain ⟨x, hx⟩ := hA.resolvent_exists ht p
  exact ⟨x, hx, fun y hy => hA.1.resolvent_unique ht hy hx⟩

noncomputable def IsMaximalMonotoneRel.resolvent (hA : IsMaximalMonotoneRel A)
    {t : ℝ} (ht : 0 < t) (p : E) : E :=
  Classical.choose (hA.resolvent_exists ht p)

theorem IsMaximalMonotoneRel.resolvent_mem (hA : IsMaximalMonotoneRel A)
    {t : ℝ} (ht : 0 < t) (p : E) :
    (1 / t) • (p - hA.resolvent ht p) ∈ A (hA.resolvent ht p) :=
  Classical.choose_spec (hA.resolvent_exists ht p)

theorem IsMaximalMonotoneRel.resolvent_eq_of_mem (hA : IsMaximalMonotoneRel A)
    {t : ℝ} (ht : 0 < t) {x p : E} (hx : (1 / t) • (p - x) ∈ A x) :
    hA.resolvent ht p = x :=
  hA.1.resolvent_unique ht (hA.resolvent_mem ht p) hx

theorem IsMaximalMonotoneRel.resolvent_graph (hA : IsMaximalMonotoneRel A)
    {t : ℝ} (ht : 0 < t) {x a : E} (ha : a ∈ A x) :
    hA.resolvent ht (x + t • a) = x := by
  apply hA.resolvent_eq_of_mem ht
  rw [show x + t • a - x = t • a by module, smul_smul]
  rw [one_div_mul_cancel ht.ne', one_smul]
  exact ha

theorem IsMaximalMonotoneRel.resolvent_nonexpansive (hA : IsMaximalMonotoneRel A)
    {t : ℝ} (ht : 0 < t) (p q : E) :
    ‖hA.resolvent ht p - hA.resolvent ht q‖ ≤ ‖p - q‖ := by
  let x := hA.resolvent ht p
  let y := hA.resolvent ht q
  change ‖x - y‖ ≤ ‖p - q‖
  have hm := hA.1 x ((1 / t) • (p - x)) y ((1 / t) • (q - y))
    (hA.resolvent_mem ht p) (hA.resolvent_mem ht q)
  have hv : (1 / t) • (p - x) - (1 / t) • (q - y) =
      (1 / t) • ((p - q) - (x - y)) := by module
  rw [hv, real_inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq] at hm
  have hfirm := nonneg_of_mul_nonneg_right hm (one_div_pos.mpr ht)
  have hsq : ‖x - y‖ ^ 2 ≤ ‖x - y‖ * ‖p - q‖ := by
    linarith [real_inner_le_norm (x - y) (p - q)]
  by_contra hnot
  have hlt : ‖p - q‖ < ‖x - y‖ := lt_of_not_ge hnot
  have hpos : 0 < ‖x - y‖ := (norm_nonneg _).trans_lt hlt
  have hbad := mul_lt_mul_of_pos_left hlt hpos
  nlinarith only [hsq, hbad]

end DRS
