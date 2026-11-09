import APDAL.Energy
import APDAL.Weights

/-!
# 原平均点的定义域、非负间隙、原式（39）与任意初始化联合界

引用 `Weights.lean` 的三个通用恒等式及 `Energy.lean` 的状态能量连接。
平均点由非负权构成凸组合，`avgX` 用从 x₁ 至 x_N 的外推点，`avgY` 属于 dom h。
任意初始化常数不使用域外函数值。
-/

open scoped BigOperators InnerProduct

namespace APDAL

noncomputable section

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
variable {K : X →L[ℝ] Y} {g : ProperConvex X} {h : ProperConvex Y}

def initialWeight (s : ℕ → State X Y) : ℝ := sigma (s 1) * (s 1).theta

def avgX (s : ℕ → State X Y) (N : ℕ) : X :=
  (1 / (initialWeight s + sumSigma s N)) •
    (initialWeight s • (s 0).x + ∑ i ∈ Finset.range N,
      sigma (s (i + 1)) • extrapolated (s i) (s (i + 1)))

def avgY (s : ℕ → State X Y) (N : ℕ) : Y :=
  (1 / sumSigma s N) • ∑ i ∈ Finset.range N, sigma (s (i + 1)) • (s (i + 1)).y

lemma sumSigma_pos (s : ℕ → State X Y) {N : ℕ} (hN : 0 < N) : 0 < sumSigma s N := by
  unfold sumSigma
  exact Finset.sum_pos' (fun i _ => (sigma_pos (s (i + 1))).le)
    ⟨0, Finset.mem_range.mpr hN, sigma_pos (s 1)⟩

theorem averaged_gap_le_sum (p : Params X Y) (sp : SaddlePoint K g h) (m : ℕ) :
    let s := states K g h p
    let N := m + 1
    avgX s N ∈ g.dom ∧ avgY s N ∈ h.dom ∧
    0 ≤ pd_gap K g h (avgX s N) (avgY s N) sp.xhat sp.yhat ∧
    sumSigma s N * pd_gap K g h (avgX s N) (avgY s N) sp.xhat sp.yhat
      ≤ initialWeight s * primal_gap K g (s 0).x sp.xhat sp.yhat
        + ∑ i ∈ Finset.range N, gapTerm sp (s i) (s (i + 1)) := by
  let s := states K g h p
  let N := m + 1
  let σ : ℕ → ℝ := fun i => sigma (s i)
  let θ : ℕ → ℝ := fun i => (s i).theta
  let w := ergWeight σ θ N
  let P := fun x => primal_gap K g x sp.xhat sp.yhat
  let D := fun y => dual_gap K h y sp.yhat sp.xhat
  have hs : 0 < sumSigma s N := sumSigma_pos s (Nat.succ_pos m)
  have ha : 0 ≤ initialWeight s := mul_nonneg (sigma_pos (s 1)).le (s 1).theta_nonneg
  have hW : 0 < initialWeight s + sumSigma s N := add_pos_of_nonneg_of_pos ha hs
  have hw : ∀ i, 0 ≤ w i := ergWeight_nonneg σ θ
    (fun i => (sigma_pos (s i)).le) (fun i => (s i).theta_nonneg)
    (fun i => weighted_theta_next K g h p (i + 2) (s (i + 1))) N
  have hwsum : (∑ i ∈ Finset.range N, w i) = initialWeight s + sumSigma s N :=
    ergWeight_sum σ θ m
  have hxvec : (∑ i ∈ Finset.range N, w i • (s (i + 1)).x)
      = initialWeight s • (s 0).x + ∑ i ∈ Finset.range N,
          sigma (s (i + 1)) • extrapolated (s i) (s (i + 1)) :=
    ergWeight_smul_sum σ θ (fun i => (s i).x) m
  have hJX := pdal_jensen_sum g.dom P (primal_gap_convex K g sp.xhat sp.yhat) w
    (fun i => (s (i + 1)).x) N (fun i _ => hw i) (hwsum.symm ▸ hW)
    (fun i _ => states_x_dom (K := K) (g := g) (h := h) p i)
  rw [hwsum, hxvec] at hJX
  have hJY := pdal_jensen_sum h.dom D (dual_gap_convex K h sp.yhat sp.xhat)
    (fun i => σ (i + 1)) (fun i => (s (i + 1)).y) N
    (fun i _ => (sigma_pos (s (i + 1))).le) hs
    (fun i _ => states_y_dom (K := K) (g := g) (h := h) p i)
  have hx : avgX s N ∈ g.dom := hJX.1
  have hy : avgY s N ∈ h.dom := hJY.1
  have hP : 0 ≤ P (avgX s N) := primal_gap_nonneg K g h sp _ hx
  have hD : 0 ≤ D (avgY s N) := dual_gap_nonneg K g h sp _ hy
  let A := ∑ i ∈ Finset.range N, w i * P (s (i + 1)).x
  let B := ∑ i ∈ Finset.range N, σ (i + 1) * D (s (i + 1)).y
  have hxp : P (avgX s N) ≤ A / (initialWeight s + sumSigma s N) := by
    simpa only [avgX, A, one_div_mul_eq_div] using hJX.2
  have hyp : D (avgY s N) ≤ B / sumSigma s N := by
    simpa only [avgY, B, sumSigma, one_div_mul_eq_div] using hJY.2
  have hxa : sumSigma s N * P (avgX s N) ≤ A := by
    calc
      _ ≤ (initialWeight s + sumSigma s N) * P (avgX s N) :=
        mul_le_mul_of_nonneg_right (by linarith only [ha]) hP
      _ ≤ _ := by rw [mul_comm]; exact (le_div_iff₀ hW).1 hxp
  have hyb : sumSigma s N * D (avgY s N) ≤ B := by
    rw [mul_comm]
    exact (le_div_iff₀ hs).1 hyp
  have hvalues := ergWeight_values σ θ (fun i => P (s i).x) m
  have hAB : A + B = initialWeight s * P (s 0).x +
      ∑ i ∈ Finset.range N, gapTerm sp (s i) (s (i + 1)) := by
    change (∑ i ∈ Finset.range N, w i * P (s (i + 1)).x) + B = _
    rw [hvalues, add_assoc]
    apply congrArg (fun t : ℝ => initialWeight s * P (s 0).x + t)
    change (∑ i ∈ Finset.range N, σ (i + 1) *
        ((1 + θ (i + 1)) * P (s (i + 1)).x - θ (i + 1) * P (s i).x)) +
        (∑ i ∈ Finset.range N, σ (i + 1) * D (s (i + 1)).y) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    unfold gapTerm
    change σ (i + 1) * ((1 + θ (i + 1)) * P (s (i + 1)).x - θ (i + 1) * P (s i).x)
      + σ (i + 1) * D (s (i + 1)).y =
        σ (i + 1) * ((1 + θ (i + 1)) * P (s (i + 1)).x - θ (i + 1) * P (s i).x + D (s (i + 1)).y)
    ring
  refine ⟨hx, hy, add_nonneg hP hD, ?_⟩
  change sumSigma s N * (P (avgX s N) + D (avgY s N)) ≤ _
  rw [mul_add]
  exact (add_le_add hxa hyb).trans_eq hAB

def arbitraryConstant (sp : SaddlePoint K g h) (s : ℕ → State X Y) : ℝ :=
  energy sp s 2 + sigma (s 1) * ((1 + (s 1).theta) *
    primal_gap K g (s 1).x sp.xhat sp.yhat + dual_gap K h (s 1).y sp.yhat sp.xhat)

theorem joint_bound_dom (p : Params X Y) (sp : SaddlePoint K g h)
    (hs : StrongSupport g p.gamma) (h0 : p.x0 ∈ g.dom) (m : ℕ) :
    let s := states K g h p
    let N := m + 1
    energy sp s (N + 1) + sumSigma s N * pd_gap K g h (avgX s N) (avgY s N) sp.xhat sp.yhat
      ≤ energy sp s 1 + initialWeight s * primal_gap K g p.x0 sp.xhat sp.yhat := by
  let s := states K g h p
  have hd (n : ℕ) : (s (0 + n)).x ∈ g.dom := by
    rw [Nat.zero_add]
    cases n with
    | zero => exact h0
    | succ n => exact states_x_dom (K := K) (g := g) (h := h) p n
  have hsum := energy_sum_from p sp hs 0 hd (m + 1)
  simp only [Nat.zero_add] at hsum
  have hgap := (averaged_gap_le_sum p sp m).2.2.2
  change energy sp s (m + 2) + sumSigma s (m + 1) *
    pd_gap K g h (avgX s (m + 1)) (avgY s (m + 1)) sp.xhat sp.yhat
    ≤ energy sp s 1 + initialWeight s * primal_gap K g (s 0).x sp.xhat sp.yhat
  linarith only [hsum, hgap]

theorem joint_bound_arbitrary (p : Params X Y) (sp : SaddlePoint K g h)
    (hs : StrongSupport g p.gamma) (m : ℕ) :
    let s := states K g h p
    let N := m + 1
    energy sp s (N + 1) + sumSigma s N * pd_gap K g h (avgX s N) (avgY s N) sp.xhat sp.yhat
      ≤ arbitraryConstant sp s := by
  let s := states K g h p
  have hd (n : ℕ) : (s (1 + n)).x ∈ g.dom := by
    rw [Nat.add_comm]
    exact states_x_dom (K := K) (g := g) (h := h) p n
  have hsum := energy_sum_from p sp hs 1 hd m
  simp only [Nat.add_comm 1] at hsum
  have hgap := (averaged_gap_le_sum p sp m).2.2.2
  let F := fun i => gapTerm sp (s i) (s (i + 1))
  have he : (∑ i ∈ Finset.range (m + 1), F i) = (∑ i ∈ Finset.range m, F (i + 1)) + F 0 :=
    Finset.sum_range_succ' F m
  have hleft : initialWeight s * primal_gap K g (s 0).x sp.xhat sp.yhat + F 0 =
      arbitraryConstant sp s - energy sp s 2 := by
    dsimp only [F, initialWeight, gapTerm, arbitraryConstant]
    ring
  change sumSigma s (m + 1) * pd_gap K g h (avgX s (m + 1)) (avgY s (m + 1)) sp.xhat sp.yhat
    ≤ initialWeight s * primal_gap K g (s 0).x sp.xhat sp.yhat + ∑ i ∈ Finset.range (m + 1), F i at hgap
  rw [he] at hgap
  change energy sp s (m + 2) + ∑ i ∈ Finset.range m, F (i + 1) ≤ energy sp s 2 at hsum
  change energy sp s (m + 2) + sumSigma s (m + 1) *
    pd_gap K g h (avgX s (m + 1)) (avgY s (m + 1)) sp.xhat sp.yhat ≤ arbitraryConstant sp s
  linarith only [hsum, hgap, hleft]

end
end APDAL
