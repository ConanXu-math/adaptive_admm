import APDAL.Iteration
import APDAL.EnergyLocal
import APDAL.Growth

/-!
# 单步能量与原始递归的连接

`states n` 内的 `y` 是论文的 `y_(n+1)`。局部能量 `local_energy` 传
`u=states n`、`v=states (n+1)`、`w=states (n+2)`。从第二轮开始，
`u.x` 的有效域条件由近端规格推出。
-/

open scoped BigOperators InnerProduct

namespace APDAL

noncomputable section

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable {K : X →L[ℝ] Y} {g : ProperConvex X} {h : ProperConvex Y}

def extrapolated (u v : State X Y) : X := v.x + v.theta • (v.x - u.x)

def energy (sp : SaddlePoint K g h) (s : ℕ → State X Y) (k : ℕ) : ℝ :=
  (s k).beta * ‖(s k).x - sp.xhat‖^2 / 2 + ‖(s (k - 1)).y - sp.yhat‖^2 / 2

lemma energy_nonneg (sp : SaddlePoint K g h) (s : ℕ → State X Y) (k : ℕ) :
    0 ≤ energy sp s k := by
  have hb := (s k).beta_pos
  unfold energy
  positivity

def gapTerm (sp : SaddlePoint K g h) (u v : State X Y) : ℝ :=
  sigma v * ((1 + v.theta) * primal_gap K g v.x sp.xhat sp.yhat
    - v.theta * primal_gap K g u.x sp.xhat sp.yhat + dual_gap K h v.y sp.yhat sp.xhat)

theorem states_x_dom (p : Params X Y) (n : ℕ) : (states K g h p (n + 1)).x ∈ g.dom :=
  (next_primal K g h p (n + 1) (states K g h p n)).1

theorem states_y_dom (p : Params X Y) (n : ℕ) : (states K g h p (n + 1)).y ∈ h.dom :=
  (next_dual K g h p (n + 1) (states K g h p n)).1

theorem state_energy (p : Params X Y) (sp : SaddlePoint K g h)
    (hs : StrongSupport g p.gamma) (n : ℕ) (hd : (states K g h p n).x ∈ g.dom) :
    let s := states K g h p
    energy sp s (n + 2) + gapTerm sp (s n) (s (n + 1)) ≤ energy sp s (n + 1) := by
  let s := states K g h p
  let u := s n
  let v := next K g h p (n + 1) u
  let w := next K g h p (n + 2) v
  have ht : v.theta * u.tau = v.tau := by
    change v.tau / u.tau * u.tau = v.tau
    exact div_mul_cancel₀ _ u.tau_pos.ne'
  have H := local_energy K g h sp hs v.beta_pos v.tau_pos u.tau_pos v.theta_nonneg ht hd
    (next_primal K g h p (n + 1) u) (next_primal K g h p (n + 2) v)
    (next_dual K g h p (n + 1) u) (next_accept K g h p (n + 1) u)
  change energy sp s (n + 2) + gapTerm sp u v + v.beta * ‖extrapolated u v - v.x‖^2 / 2
    ≤ energy sp s (n + 1) at H
  change energy sp s (n + 2) + gapTerm sp u v ≤ energy sp s (n + 1)
  have hb := v.beta_pos
  have hn : 0 ≤ v.beta * ‖extrapolated u v - v.x‖^2 / 2 := by positivity
  exact (le_add_of_nonneg_right hn).trans H

theorem energy_sum_from (p : Params X Y) (sp : SaddlePoint K g h)
    (hs : StrongSupport g p.gamma) (m : ℕ)
    (hd : ∀ n, (states K g h p (m + n)).x ∈ g.dom) (N : ℕ) :
    let s := states K g h p
    energy sp s (m + N + 1) + ∑ i ∈ Finset.range N, gapTerm sp (s (m + i)) (s (m + i + 1))
      ≤ energy sp s (m + 1) := by
  let s := states K g h p
  change energy sp s (m + N + 1) + ∑ i ∈ Finset.range N, gapTerm sp (s (m + i)) (s (m + i + 1))
      ≤ energy sp s (m + 1)
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hstep := state_energy p sp hs (m + N) (hd N)
    change energy sp s (m + N + 2) + gapTerm sp (s (m + N)) (s (m + N + 1))
      ≤ energy sp s (m + N + 1) at hstep
    change energy sp s (m + N + 2) +
        ((∑ i ∈ Finset.range N, gapTerm sp (s (m + i)) (s (m + i + 1)))
          + gapTerm sp (s (m + N)) (s (m + N + 1))) ≤ energy sp s (m + 1)
    linarith only [hstep, ih]

end
end APDAL
