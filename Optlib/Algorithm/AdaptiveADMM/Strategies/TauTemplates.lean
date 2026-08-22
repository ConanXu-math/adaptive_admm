import Optlib.Algorithm.AdaptiveADMM.Strategies.VerificationLib

namespace AdaptiveADMM_Verification

noncomputable section

open Real Topology Filter BigOperators

def tau_seq (c p : ℝ) (n : ℕ) : ℝ :=
  c / Real.rpow ((n : ℝ) + 1) p

theorem h_tau_summable (c p : ℝ) (hp : 1 < p) : Summable (tau_seq c p) := by
  simpa [tau_seq] using p_series_summable_template c p hp

def tau_seq_sum2 (c1 p1 c2 p2 : ℝ) (n : ℕ) : ℝ :=
  c1 / Real.rpow ((n : ℝ) + 1) p1 +
  c2 / Real.rpow ((n : ℝ) + 1) p2

theorem h_tau_summable_sum2
    (c1 p1 c2 p2 : ℝ) (hp1 : 1 < p1) (hp2 : 1 < p2) :
    Summable (tau_seq_sum2 c1 p1 c2 p2) := by
  simpa [tau_seq_sum2] using
    (p_series_summable_template c1 p1 hp1).add
      (p_series_summable_template c2 p2 hp2)

def tau_seq_sum3 (c1 p1 c2 p2 c3 p3 : ℝ) (n : ℕ) : ℝ :=
  c1 / Real.rpow ((n : ℝ) + 1) p1 +
  (c2 / Real.rpow ((n : ℝ) + 1) p2 +
  c3 / Real.rpow ((n : ℝ) + 1) p3)

theorem h_tau_summable_sum3
    (c1 p1 c2 p2 c3 p3 : ℝ)
    (hp1 : 1 < p1) (hp2 : 1 < p2) (hp3 : 1 < p3) :
    Summable (tau_seq_sum3 c1 p1 c2 p2 c3 p3) := by
  simpa [tau_seq_sum3, add_assoc] using
    (p_series_summable_template c1 p1 hp1).add
      ((p_series_summable_template c2 p2 hp2).add
        (p_series_summable_template c3 p3 hp3))

def tau_seq_sum4 (c1 p1 c2 p2 c3 p3 c4 p4 : ℝ) (n : ℕ) : ℝ :=
  c1 / Real.rpow ((n : ℝ) + 1) p1 +
  (c2 / Real.rpow ((n : ℝ) + 1) p2 +
  (c3 / Real.rpow ((n : ℝ) + 1) p3 +
  c4 / Real.rpow ((n : ℝ) + 1) p4))

theorem h_tau_summable_sum4
    (c1 p1 c2 p2 c3 p3 c4 p4 : ℝ)
    (hp1 : 1 < p1) (hp2 : 1 < p2) (hp3 : 1 < p3) (hp4 : 1 < p4) :
    Summable (tau_seq_sum4 c1 p1 c2 p2 c3 p3 c4 p4) := by
  simpa [tau_seq_sum4, add_assoc] using
    (p_series_summable_template c1 p1 hp1).add
      ((p_series_summable_template c2 p2 hp2).add
        ((p_series_summable_template c3 p3 hp3).add
          (p_series_summable_template c4 p4 hp4)))

def tau_seq_sum5 (c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : ℝ) (n : ℕ) : ℝ :=
  c1 / Real.rpow ((n : ℝ) + 1) p1 +
  (c2 / Real.rpow ((n : ℝ) + 1) p2 +
  (c3 / Real.rpow ((n : ℝ) + 1) p3 +
  (c4 / Real.rpow ((n : ℝ) + 1) p4 +
  c5 / Real.rpow ((n : ℝ) + 1) p5)))

theorem h_tau_summable_sum5
    (c1 p1 c2 p2 c3 p3 c4 p4 c5 p5 : ℝ)
    (hp1 : 1 < p1) (hp2 : 1 < p2) (hp3 : 1 < p3)
    (hp4 : 1 < p4) (hp5 : 1 < p5) :
    Summable (tau_seq_sum5 c1 p1 c2 p2 c3 p3 c4 p4 c5 p5) := by
  simpa [tau_seq_sum5, add_assoc] using
    (p_series_summable_template c1 p1 hp1).add
      ((p_series_summable_template c2 p2 hp2).add
        ((p_series_summable_template c3 p3 hp3).add
          ((p_series_summable_template c4 p4 hp4).add
            (p_series_summable_template c5 p5 hp5))))

def tau_seq_shifted (c p a : ℝ) (n : ℕ) : ℝ :=
  c / Real.rpow ((n : ℝ) + a) p

theorem h_tau_summable_shifted (c p a : ℝ) (hp : 1 < p) (ha : 0 < a) :
    Summable (tau_seq_shifted c p a) := by
  have h_abs : Summable (fun n : ℕ => 1 / |(n : ℝ) + a| ^ p) :=
    (Real.summable_one_div_nat_add_rpow a p).2 hp
  have h_shift : Summable (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + a) p) := by
    refine Summable.congr h_abs ?_
    intro n
    have hpos : 0 < (n : ℝ) + a := add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) ha
    simp [abs_of_pos hpos]
  simpa [tau_seq_shifted, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (h_shift.mul_left c)

def tau_seq_shifted_sum2 (c1 p1 a1 c2 p2 a2 : ℝ) (n : ℕ) : ℝ :=
  tau_seq_shifted c1 p1 a1 n + tau_seq_shifted c2 p2 a2 n

theorem h_tau_summable_shifted_sum2
    (c1 p1 a1 c2 p2 a2 : ℝ)
    (hp1 : 1 < p1) (hp2 : 1 < p2) (ha1 : 0 < a1) (ha2 : 0 < a2) :
    Summable (tau_seq_shifted_sum2 c1 p1 a1 c2 p2 a2) := by
  simpa [tau_seq_shifted_sum2] using
    (h_tau_summable_shifted c1 p1 a1 hp1 ha1).add
      (h_tau_summable_shifted c2 p2 a2 hp2 ha2)

def tau_seq_shifted_sum3
    (c1 p1 a1 c2 p2 a2 c3 p3 a3 : ℝ) (n : ℕ) : ℝ :=
  tau_seq_shifted c1 p1 a1 n +
  (tau_seq_shifted c2 p2 a2 n + tau_seq_shifted c3 p3 a3 n)

theorem h_tau_summable_shifted_sum3
    (c1 p1 a1 c2 p2 a2 c3 p3 a3 : ℝ)
    (hp1 : 1 < p1) (hp2 : 1 < p2) (hp3 : 1 < p3)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) :
    Summable (tau_seq_shifted_sum3 c1 p1 a1 c2 p2 a2 c3 p3 a3) := by
  simpa [tau_seq_shifted_sum3, add_assoc] using
    (h_tau_summable_shifted c1 p1 a1 hp1 ha1).add
      ((h_tau_summable_shifted c2 p2 a2 hp2 ha2).add
        (h_tau_summable_shifted c3 p3 a3 hp3 ha3))

def tau_seq_shifted_sum4
    (c1 p1 a1 c2 p2 a2 c3 p3 a3 c4 p4 a4 : ℝ) (n : ℕ) : ℝ :=
  tau_seq_shifted c1 p1 a1 n +
  (tau_seq_shifted c2 p2 a2 n +
  (tau_seq_shifted c3 p3 a3 n + tau_seq_shifted c4 p4 a4 n))

theorem h_tau_summable_shifted_sum4
    (c1 p1 a1 c2 p2 a2 c3 p3 a3 c4 p4 a4 : ℝ)
    (hp1 : 1 < p1) (hp2 : 1 < p2) (hp3 : 1 < p3) (hp4 : 1 < p4)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3) (ha4 : 0 < a4) :
    Summable (tau_seq_shifted_sum4 c1 p1 a1 c2 p2 a2 c3 p3 a3 c4 p4 a4) := by
  simpa [tau_seq_shifted_sum4, add_assoc] using
    (h_tau_summable_shifted c1 p1 a1 hp1 ha1).add
      ((h_tau_summable_shifted c2 p2 a2 hp2 ha2).add
        ((h_tau_summable_shifted c3 p3 a3 hp3 ha3).add
          (h_tau_summable_shifted c4 p4 a4 hp4 ha4)))

def tau_seq_shifted_sum5
    (c1 p1 a1 c2 p2 a2 c3 p3 a3 c4 p4 a4 c5 p5 a5 : ℝ) (n : ℕ) : ℝ :=
  tau_seq_shifted c1 p1 a1 n +
  (tau_seq_shifted c2 p2 a2 n +
  (tau_seq_shifted c3 p3 a3 n +
  (tau_seq_shifted c4 p4 a4 n + tau_seq_shifted c5 p5 a5 n)))

theorem h_tau_summable_shifted_sum5
    (c1 p1 a1 c2 p2 a2 c3 p3 a3 c4 p4 a4 c5 p5 a5 : ℝ)
    (hp1 : 1 < p1) (hp2 : 1 < p2) (hp3 : 1 < p3)
    (hp4 : 1 < p4) (hp5 : 1 < p5)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (ha3 : 0 < a3)
    (ha4 : 0 < a4) (ha5 : 0 < a5) :
    Summable
      (tau_seq_shifted_sum5 c1 p1 a1 c2 p2 a2 c3 p3 a3 c4 p4 a4 c5 p5 a5) := by
  simpa [tau_seq_shifted_sum5, add_assoc] using
    (h_tau_summable_shifted c1 p1 a1 hp1 ha1).add
      ((h_tau_summable_shifted c2 p2 a2 hp2 ha2).add
        ((h_tau_summable_shifted c3 p3 a3 hp3 ha3).add
          ((h_tau_summable_shifted c4 p4 a4 hp4 ha4).add
            (h_tau_summable_shifted c5 p5 a5 hp5 ha5))))

def tau_seq_geom (c q : ℝ) (n : ℕ) : ℝ :=
  c * q ^ n

theorem h_tau_summable_geom (c q : ℝ) (hq : ‖q‖ < 1) :
    Summable (tau_seq_geom c q) := by
  simpa [tau_seq_geom, mul_comm, mul_left_comm, mul_assoc] using
    (summable_geometric_of_norm_lt_one hq).mul_left c

def tau_seq_geom_sum2 (c1 q1 c2 q2 : ℝ) (n : ℕ) : ℝ :=
  tau_seq_geom c1 q1 n + tau_seq_geom c2 q2 n

theorem h_tau_summable_geom_sum2
    (c1 q1 c2 q2 : ℝ) (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) :
    Summable (tau_seq_geom_sum2 c1 q1 c2 q2) := by
  simpa [tau_seq_geom_sum2] using
    (h_tau_summable_geom c1 q1 hq1).add
      (h_tau_summable_geom c2 q2 hq2)

def tau_seq_geom_sum3 (c1 q1 c2 q2 c3 q3 : ℝ) (n : ℕ) : ℝ :=
  tau_seq_geom c1 q1 n + (tau_seq_geom c2 q2 n + tau_seq_geom c3 q3 n)

theorem h_tau_summable_geom_sum3
    (c1 q1 c2 q2 c3 q3 : ℝ)
    (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) (hq3 : ‖q3‖ < 1) :
    Summable (tau_seq_geom_sum3 c1 q1 c2 q2 c3 q3) := by
  simpa [tau_seq_geom_sum3, add_assoc] using
    (h_tau_summable_geom c1 q1 hq1).add
      ((h_tau_summable_geom c2 q2 hq2).add
        (h_tau_summable_geom c3 q3 hq3))

def tau_seq_geom_sum4 (c1 q1 c2 q2 c3 q3 c4 q4 : ℝ) (n : ℕ) : ℝ :=
  tau_seq_geom c1 q1 n +
  (tau_seq_geom c2 q2 n + (tau_seq_geom c3 q3 n + tau_seq_geom c4 q4 n))

theorem h_tau_summable_geom_sum4
    (c1 q1 c2 q2 c3 q3 c4 q4 : ℝ)
    (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) (hq3 : ‖q3‖ < 1)
    (hq4 : ‖q4‖ < 1) :
    Summable (tau_seq_geom_sum4 c1 q1 c2 q2 c3 q3 c4 q4) := by
  simpa [tau_seq_geom_sum4, add_assoc] using
    (h_tau_summable_geom c1 q1 hq1).add
      ((h_tau_summable_geom c2 q2 hq2).add
        ((h_tau_summable_geom c3 q3 hq3).add
          (h_tau_summable_geom c4 q4 hq4)))

def tau_seq_geom_sum5 (c1 q1 c2 q2 c3 q3 c4 q4 c5 q5 : ℝ) (n : ℕ) : ℝ :=
  tau_seq_geom c1 q1 n +
  (tau_seq_geom c2 q2 n +
  (tau_seq_geom c3 q3 n + (tau_seq_geom c4 q4 n + tau_seq_geom c5 q5 n)))

theorem h_tau_summable_geom_sum5
    (c1 q1 c2 q2 c3 q3 c4 q4 c5 q5 : ℝ)
    (hq1 : ‖q1‖ < 1) (hq2 : ‖q2‖ < 1) (hq3 : ‖q3‖ < 1)
    (hq4 : ‖q4‖ < 1) (hq5 : ‖q5‖ < 1) :
    Summable (tau_seq_geom_sum5 c1 q1 c2 q2 c3 q3 c4 q4 c5 q5) := by
  simpa [tau_seq_geom_sum5, add_assoc] using
    (h_tau_summable_geom c1 q1 hq1).add
      ((h_tau_summable_geom c2 q2 hq2).add
        ((h_tau_summable_geom c3 q3 hq3).add
          ((h_tau_summable_geom c4 q4 hq4).add
            (h_tau_summable_geom c5 q5 hq5))))

def tau_seq_smooth_as_sum (c p a q : ℝ) (n : ℕ) : ℝ :=
  c / Real.rpow ((n : ℝ) + 1) p +
  (c * a) / Real.rpow ((n : ℝ) + 1) (p + q)

theorem h_tau_summable_smooth_as_sum
    (c p a q : ℝ) (hp : 1 < p) (hq : 0 < q) :
    Summable (tau_seq_smooth_as_sum c p a q) := by
  have hpq : 1 < p + q := lt_trans hp (lt_add_of_pos_right p hq)
  simpa [tau_seq_smooth_as_sum] using
    (p_series_summable_template c p hp).add
      (p_series_summable_template (c * a) (p + q) hpq)

def tau_seq_bounded_modulation
    (base scale : ℕ → ℝ) (n : ℕ) : ℝ :=
  base n * scale n

theorem h_tau_summable_bounded_modulation
    (base scale : ℕ → ℝ) (bound : ℝ)
    (h_base_nonneg : ∀ n, 0 ≤ base n)
    (h_base_summable : Summable base)
    (h_scale_nonneg : ∀ n, 0 ≤ scale n)
    (h_scale_bound : ∀ n, scale n ≤ bound) :
    Summable (tau_seq_bounded_modulation base scale) := by
  refine (h_base_summable.mul_left bound).of_nonneg_of_le ?_ ?_
  · intro n
    exact mul_nonneg (h_base_nonneg n) (h_scale_nonneg n)
  · intro n
    calc
      tau_seq_bounded_modulation base scale n
          ≤ base n * bound := by
            exact mul_le_mul_of_nonneg_left (h_scale_bound n) (h_base_nonneg n)
      _ = bound * base n := by ring

end

end AdaptiveADMM_Verification
