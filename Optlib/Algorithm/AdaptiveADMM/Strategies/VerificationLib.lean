import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

namespace AdaptiveADMM_Verification

noncomputable section

open Real Topology Filter BigOperators

-- 【L1】P-级数模板：c / (n+1)^p，可和需 p > 1
lemma p_series_summable_template (c p : ℝ) (hp : 1 < p) :
    Summable (fun (n : ℕ) => c / Real.rpow ((n : ℝ) + 1) p) := by
  have h0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
    (summable_one_div_nat_rpow.mpr hp)
  have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ p) := by
    simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using
      (summable_nat_add_iff 1).mpr h0
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (h1.mul_left c)

-- 【L2】几何级数模板：c * r^n, 需 0 ≤ r < 1
lemma geometric_summable_template (c r : ℝ) (h_nonneg : 0 ≤ r) (h_lt_one : r < 1) :
    Summable (fun (n : ℕ) => c * r ^ n) := by
  exact (summable_geometric_of_lt_one h_nonneg h_lt_one).mul_left c

-- 【通用工具】若 f 最终等于 g 且 g 可和，则 f 可和
lemma summable_of_eventually_eq_template {f g : ℕ → ℝ} (N : ℕ)
    (h_g_sum : Summable g)
    (h_eq : ∀ n, N ≤ n → f n = g n) : Summable f := by
  have h_tail_g : Summable (fun n => g (n + N)) :=
    (summable_nat_add_iff N).2 h_g_sum
  have h_tail_f : Summable (fun n => f (n + N)) := by
    refine Summable.congr h_tail_g ?_
    intro n
    have hn : N ≤ n + N := Nat.le_add_left _ _
    exact (h_eq _ hn).symm
  exact (summable_nat_add_iff N).1 h_tail_f
end
