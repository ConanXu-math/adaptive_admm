import DRS.Minty

/-!
# The Douglas–Rachford recursion of equation (12)

For maximal monotone relations `A`, `B` on a complete real inner product space, with any
initial graph point `b ∈ B u₀` and any strictly positive step size sequence `τ`, we
construct the recursion of equation (12): for `n ≥ 0` with `t = τ (n+1)`,

* `v (n+1) = J_{t A} (u n - t • b n)`, `a (n+1) = (u n - t • b n - v (n+1)) / t`,
* `u (n+1) = J_{t B} (v (n+1) + t • b n)`, `b (n+1) = (v (n+1) + t • b n - u (n+1)) / t`.
-/

open scoped InnerProductSpace

namespace DRS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure DRState (B : E → Set E) where
  u : E
  b : E
  hb : b ∈ B u

structure DRTransition (A B : E → Set E) (t : ℝ) (s : DRState B) where
  v : E
  a : E
  ha : a ∈ A v
  next : DRState B
  eqA : v + t • a = s.u - t • s.b
  eqB : next.u + t • next.b = v + t • s.b

variable {A B : E → Set E}

noncomputable def drStep (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    (t : ℝ) (ht : 0 < t) (s : DRState B) : DRTransition A B t s := by
  let p := s.u - t • s.b
  let v := hA.resolvent ht p
  let a := (1 / t) • (p - v)
  let q := v + t • s.b
  let u := hB.resolvent ht q
  let b := (1 / t) • (q - u)
  have ha : t • a = p - v := by
    dsimp [a]
    rw [smul_smul, mul_one_div_cancel ht.ne', one_smul]
  have hb : t • b = q - u := by
    dsimp [b]
    rw [smul_smul, mul_one_div_cancel ht.ne', one_smul]
  exact {
    v := v
    a := a
    ha := hA.resolvent_mem ht p
    next := ⟨u, b, hB.resolvent_mem ht q⟩
    eqA := by
      rw [ha]
      dsimp [p]
      module
    eqB := by
      rw [hb]
      dsimp [q]
      module
  }

noncomputable def drStates (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 < τ n) (s₀ : DRState B) : ℕ → DRState B
  | 0 => s₀
  | n + 1 =>
    (drStep hA hB (τ (n + 1)) (hτ (n + 1)) (drStates hA hB τ hτ s₀ n)).next

noncomputable def drTraceStep (hA : IsMaximalMonotoneRel A) (hB : IsMaximalMonotoneRel B)
    (τ : ℕ → ℝ) (hτ : ∀ n, 0 < τ n) (s₀ : DRState B) (n : ℕ) :
    DRTransition A B (τ (n + 1)) (drStates hA hB τ hτ s₀ n) :=
  drStep hA hB (τ (n + 1)) (hτ (n + 1)) (drStates hA hB τ hτ s₀ n)

def ExtendedSolution (A B : E → Set E) (z w : E) : Prop :=
  -w ∈ A z ∧ w ∈ B z

theorem DRTransition.u_sub_next {t : ℝ} {s : DRState B}
    (d : DRTransition A B t s) :
    s.u - d.next.u = t • (d.a + d.next.b) := by
  calc
    _ = (s.u - t • s.b - d.v) + (d.v + t • s.b - d.next.u) := by module
    _ = _ := by
      rw [← d.eqA, ← d.eqB]
      module

theorem DRTransition.next_sub_v {t : ℝ} {s : DRState B}
    (d : DRTransition A B t s) :
    d.next.u - d.v = t • (s.b - d.next.b) := by
  calc
    _ = (d.next.u + t • d.next.b) - (d.v + t • s.b) + t • (s.b - d.next.b) := by
      module
    _ = _ := by
      rw [d.eqB]
      module

theorem DRTransition.energy_descent (hA : IsMonotoneRel A) (hB : IsMonotoneRel B)
    {t : ℝ} (ht : 0 < t) {s : DRState B} (d : DRTransition A B t s)
    {z w : E} (hsol : ExtendedSolution A B z w) :
    ‖d.next.u - z‖ ^ 2 + t ^ 2 * ‖d.next.b - w‖ ^ 2 + ‖s.u - d.v‖ ^ 2 ≤
      ‖s.u - z‖ ^ 2 + t ^ 2 * ‖s.b - w‖ ^ 2 := by
  have ha : 0 ≤ ⟪d.a + w, d.v - z⟫_ℝ := by
    rw [real_inner_comm, ← sub_neg_eq_add]
    exact hA d.v d.a z (-w) d.ha hsol.1
  have hb : 0 ≤ ⟪d.next.b - w, d.next.u - z⟫_ℝ := by
    rw [real_inner_comm]
    exact hB d.next.u d.next.b z w d.next.hb hsol.2
  have hcross :
      ⟪s.u - d.next.u, d.next.u - z⟫_ℝ +
        t * ⟪d.next.u - d.v, d.next.b - w⟫_ℝ -
          ⟪s.u - d.next.u, d.next.u - d.v⟫_ℝ =
        t * (⟪d.a + w, d.v - z⟫_ℝ + ⟪d.next.b - w, d.next.u - z⟫_ℝ) := by
    rw [d.u_sub_next]
    simp only [real_inner_smul_left, inner_add_left, inner_sub_left, inner_sub_right]
    rw [real_inner_comm d.next.u d.next.b, real_inner_comm d.v d.next.b,
      real_inner_comm d.next.u w, real_inner_comm d.v w]
    ring
  have hscale : t * ⟪d.next.u - d.v, d.next.b - w⟫_ℝ =
      t ^ 2 * ⟪s.b - d.next.b, d.next.b - w⟫_ℝ := by
    rw [d.next_sub_v, real_inner_smul_left]
    ring
  have hpos : 0 ≤ ⟪s.u - d.next.u, d.next.u - z⟫_ℝ +
      t ^ 2 * ⟪s.b - d.next.b, d.next.b - w⟫_ℝ -
        ⟪s.u - d.next.u, d.next.u - d.v⟫_ℝ := by
    rw [← hscale, hcross]
    exact mul_nonneg ht.le (add_nonneg ha hb)
  have hu : ‖s.u - z‖ ^ 2 =
      ‖s.u - d.next.u‖ ^ 2 + 2 * ⟪s.u - d.next.u, d.next.u - z⟫_ℝ +
        ‖d.next.u - z‖ ^ 2 := by
    rw [show s.u - z = (s.u - d.next.u) + (d.next.u - z) by module, norm_add_sq_real]
  have hbexp : ‖s.b - w‖ ^ 2 =
      ‖s.b - d.next.b‖ ^ 2 + 2 * ⟪s.b - d.next.b, d.next.b - w⟫_ℝ +
        ‖d.next.b - w‖ ^ 2 := by
    rw [show s.b - w = (s.b - d.next.b) + (d.next.b - w) by module, norm_add_sq_real]
  have hr : ‖s.u - d.v‖ ^ 2 =
      ‖s.u - d.next.u‖ ^ 2 + 2 * ⟪s.u - d.next.u, d.next.u - d.v⟫_ℝ +
        ‖d.next.u - d.v‖ ^ 2 := by
    rw [show s.u - d.v = (s.u - d.next.u) + (d.next.u - d.v) by module, norm_add_sq_real]
  have hnorm : ‖d.next.u - d.v‖ ^ 2 = t ^ 2 * ‖s.b - d.next.b‖ ^ 2 := by
    rw [d.next_sub_v, norm_smul]
    simp only [mul_pow, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ _ + 2 * (⟪s.u - d.next.u, d.next.u - z⟫_ℝ +
        t ^ 2 * ⟪s.b - d.next.b, d.next.b - w⟫_ℝ -
          ⟪s.u - d.next.u, d.next.u - d.v⟫_ℝ) :=
      le_add_of_nonneg_right (mul_nonneg (by norm_num) hpos)
    _ = _ := by
      rw [hu, hbexp, hr, hnorm]
      ring

end DRS
