import APDAL.Iteration
import APDAL.Scalar

/-!
# 步长下界、相邻加权步长不等式与二次增长

每轮零次接受由试探下端给出下界；正次接受由前一候选失败给出下界，包含 K=0 情形。
由 q 下界推出 β 的递推增长，再用 Scalar.lean 的标量定理得二次增长。
-/

open scoped BigOperators InnerProduct

namespace APDAL

noncomputable section

variable {X Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

def q (s : State X Y) : ℝ := s.tau * Real.sqrt s.beta
def sigma (s : State X Y) : ℝ := s.beta * s.tau

lemma q_pos (s : State X Y) : 0 < q s :=
  mul_pos s.tau_pos (Real.sqrt_pos.mpr s.beta_pos)

lemma sigma_pos (s : State X Y) : 0 < sigma s := mul_pos s.beta_pos s.tau_pos

lemma sigma_eq_q_mul_sqrt (s : State X Y) : sigma s = q s * Real.sqrt s.beta := by
  unfold sigma q
  rw [mul_assoc, Real.mul_self_sqrt s.beta_pos.le, mul_comm s.tau s.beta]

lemma trialLower_mul_sqrt {γ : ℝ} (hγ : 0 < γ) (s : State X Y) :
    trialLower γ s * Real.sqrt (betaNext γ s) = q s := by
  unfold trialLower q
  rw [mul_assoc, ← Real.sqrt_mul (div_nonneg s.beta_pos.le (betaNext_pos hγ s).le),
    div_mul_cancel₀ _ (betaNext_pos hγ s).ne']

theorem q_next_lower (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (p : Params X Y) (j : ℕ) (s : State X Y) :
    min (q s) (p.mu / (1 + ‖K‖)) ≤ q (next K g h p j s) := by
  let t := next K g h p j s
  have hsq : 0 < Real.sqrt (betaNext p.gamma s) := Real.sqrt_pos.mpr (betaNext_pos p.gamma_pos s)
  cases hi : t.index with
  | zero =>
    apply (min_le_left _ _).trans
    have heq : t.tau = trial K g p j s := by
      change trial K g p j s * p.mu ^ t.index = trial K g p j s
      rw [hi, pow_zero, mul_one]
    calc
      q s = trialLower p.gamma s * Real.sqrt (betaNext p.gamma s) :=
        (trialLower_mul_sqrt p.gamma_pos s).symm
      _ ≤ trial K g p j s * Real.sqrt (betaNext p.gamma s) :=
        mul_le_mul_of_nonneg_right (p.trial_range j s _).1 hsq.le
      _ = q t := by rw [← heq]; rfl
  | succ i =>
    let u := candidateTau K g p j s i
    have hu := candidateTau_pos K g p j s i
    have him : i < t.index := by rw [hi]; omega
    have hr := next_minimal K g h p j s i him
    have hsmall : 1 < (Real.sqrt (betaNext p.gamma s) * u) * ‖K‖ := by
      apply lt_of_not_ge
      intro hbound
      exact hr (accept_cond_of_small_tau K (betaNext_pos p.gamma_pos s) zero_lt_one hu
        s.y (candidateY K g h p j s i) hbound)
    have hden : 0 < 1 + ‖K‖ := by positivity
    have hp : 0 < Real.sqrt (betaNext p.gamma s) * u := mul_pos hsq hu
    have hdiv : 1 / (1 + ‖K‖) < Real.sqrt (betaNext p.gamma s) * u :=
      (div_lt_iff₀ hden).2 (by nlinarith only [hsmall, hp])
    have hqt : q t = p.mu * (Real.sqrt (betaNext p.gamma s) * u) := by
      change (trial K g p j s * p.mu ^ t.index) * Real.sqrt (betaNext p.gamma s) = _
      rw [hi, pow_succ]
      unfold u candidateTau
      ring
    have hl := mul_lt_mul_of_pos_left hdiv p.mu_range.1
    rw [← hqt] at hl
    have hdiv' : p.mu / (1 + ‖K‖) < q t := by
      simpa only [mul_one_div] using hl
    exact (min_le_right _ _).trans hdiv'.le

theorem q_next_upper (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (p : Params X Y) (j : ℕ) (s : State X Y) :
    q (next K g h p j s) ≤ q s * Real.sqrt (1 + s.theta) := by
  let t := next K g h p j s
  have ht : t.tau ≤ trial K g p j s := by
    change trial K g p j s * p.mu ^ t.index ≤ trial K g p j s
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (pow_le_one₀ p.mu_range.1.le p.mu_range.2.le : p.mu ^ t.index ≤ 1)
        (trial_pos K g p j s).le
  calc
    q t ≤ (trialLower p.gamma s * Real.sqrt (1 + s.theta)) * Real.sqrt (betaNext p.gamma s) :=
      mul_le_mul_of_nonneg_right (ht.trans (p.trial_range j s _).2) (Real.sqrt_nonneg _)
    _ = (trialLower p.gamma s * Real.sqrt (betaNext p.gamma s)) * Real.sqrt (1 + s.theta) := by ring
    _ = _ := by rw [trialLower_mul_sqrt p.gamma_pos s]

theorem weighted_theta_next (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (p : Params X Y) (j : ℕ) (s : State X Y) :
    let t := next K g h p j s
    sigma t * t.theta ≤ sigma s * (1 + s.theta) := by
  let t := next K g h p j s
  have hθ : 0 ≤ 1 + s.theta := by linarith only [s.theta_nonneg]
  have hr := Real.sqrt_nonneg (1 + s.theta)
  have hu := (sq_le_sq₀ (q_pos t).le (mul_nonneg (q_pos s).le hr)).2
    (q_next_upper K g h p j s)
  have he (u : State X Y) : (q u)^2 = sigma u * u.tau := by
    unfold q sigma
    rw [mul_pow, Real.sq_sqrt u.beta_pos.le]
    ring
  rw [mul_pow, he t, he s, Real.sq_sqrt hθ] at hu
  change sigma t * (t.tau / s.tau) ≤ sigma s * (1 + s.theta)
  rw [← mul_div_assoc, div_le_iff₀ s.tau_pos]
  calc
    sigma t * t.tau ≤ sigma s * s.tau * (1 + s.theta) := hu
    _ = sigma s * (1 + s.theta) * s.tau := by ring

theorem q_lower_all (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (p : Params X Y) :
    let c := min (q (initial p)) (p.mu / (1 + ‖K‖))
    0 < c ∧ ∀ n, c ≤ q (states K g h p n) := by
  let c := min (q (initial p)) (p.mu / (1 + ‖K‖))
  have hc0 : c ≤ q (initial p) := min_le_left _ _
  have hcK : c ≤ p.mu / (1 + ‖K‖) := min_le_right _ _
  refine ⟨lt_min (q_pos (initial p)) (div_pos p.mu_range.1 (by positivity)), ?_⟩
  intro n
  induction n with
  | zero => simpa only [states_zero] using hc0
  | succ n ih =>
    rw [states_succ]
    exact (le_min ih hcK).trans (q_next_lower K g h p (n + 1) (states K g h p n))

def sumSigma (s : ℕ → State X Y) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, sigma (s (i + 1))

theorem quadratic_growth (K : X →L[ℝ] Y) (g : ProperConvex X) (h : ProperConvex Y)
    (p : Params X Y) :
    ∃ b d : ℝ, 0 < b ∧ 0 < d ∧
      ∀ n : ℕ, b * ((n : ℝ) + 1)^2 ≤ (states K g h p n).beta ∧
        d * ((n : ℝ))^2 ≤ sumSigma (states K g h p) n := by
  let s := states K g h p
  let c := min (q (initial p)) (p.mu / (1 + ‖K‖))
  have hq : 0 < c ∧ ∀ n, c ≤ q (s n) := q_lower_all K g h p
  have hstep (n : ℕ) : (s n).beta + p.gamma * c * Real.sqrt (s n).beta ≤ (s (n + 1)).beta := by
    have hm := mul_le_mul_of_nonneg_right (hq.2 n) (Real.sqrt_nonneg (s n).beta)
    rw [← sigma_eq_q_mul_sqrt] at hm
    have hg := mul_le_mul_of_nonneg_left hm p.gamma_pos.le
    have he : (s (n + 1)).beta = betaNext p.gamma (s n) := rfl
    rw [he]
    unfold betaNext
    unfold sigma at hg
    nlinarith only [hg]
  obtain ⟨b, hb, hbnd⟩ := scalar_growth (fun n => (s n).beta) p.gamma_pos hq.1 p.beta0_pos hstep
  let a := c * Real.sqrt b
  have ha : 0 < a := mul_pos hq.1 (Real.sqrt_pos.mpr hb)
  have hσ (n : ℕ) : a * ((n : ℝ) + 1) ≤ sigma (s n) := by
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    have hs : Real.sqrt b * ((n : ℝ) + 1) ≤ Real.sqrt (s n).beta := by
      calc
        _ = Real.sqrt (b * ((n : ℝ) + 1)^2) := by rw [Real.sqrt_mul hb.le, Real.sqrt_sq hn]
        _ ≤ _ := Real.sqrt_le_sqrt (hbnd n)
    rw [sigma_eq_q_mul_sqrt]
    calc
      _ = c * (Real.sqrt b * ((n : ℝ) + 1)) := by unfold a; ring
      _ ≤ _ := mul_le_mul (hq.2 n) hs (mul_nonneg (Real.sqrt_nonneg _) hn) (q_pos (s n)).le
  have hsN (n : ℕ) : a / 2 * (n : ℝ)^2 ≤ sumSigma s n := by
    induction n with
    | zero => simp [sumSigma]
    | succ n ih =>
      rw [sumSigma, Finset.sum_range_succ, Nat.cast_succ]
      have h1 := hσ (n + 1)
      rw [Nat.cast_add, Nat.cast_one] at h1
      change a / 2 * (n : ℝ)^2 ≤ ∑ i ∈ Finset.range n, sigma (s (i + 1)) at ih
      nlinarith only [ih, h1, ha]
  exact ⟨b, a / 2, hb, div_pos ha (by norm_num), fun n => ⟨hbnd n, hsN n⟩⟩

end

end APDAL
