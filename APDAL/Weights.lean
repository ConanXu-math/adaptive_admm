import PDAL.Definitions

/-!
# 原始加权平均的望远求和

`σ, θ` 的索引从论文原索引开始，`i` 遍历 `range N` 时实际加权索引为 `i+1`。
一个向量恒等式同时给出总权、原平均分子和函数值求和。
-/

open scoped BigOperators

namespace APDAL

noncomputable section

def ergWeight (σ θ : ℕ → ℝ) (N i : ℕ) : ℝ :=
  σ (i + 1) * (1 + θ (i + 1)) -
    (if i + 1 < N then σ (i + 2) * θ (i + 2) else 0)

theorem ergWeight_nonneg (σ θ : ℕ → ℝ)
    (hσ : ∀ i, 0 ≤ σ i) (hθ : ∀ i, 0 ≤ θ i)
    (hbound : ∀ i, σ (i + 2) * θ (i + 2) ≤ σ (i + 1) * (1 + θ (i + 1)))
    (N i : ℕ) : 0 ≤ ergWeight σ θ N i := by
  unfold ergWeight
  split_ifs
  · exact sub_nonneg.mpr (hbound i)
  · rw [sub_zero]
    exact mul_nonneg (hσ _) (add_nonneg zero_le_one (hθ _))

theorem ergWeight_smul_sum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (σ θ : ℕ → ℝ) (f : ℕ → V) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ergWeight σ θ (m + 1) i • f (i + 1))
      = (σ 1 * θ 1) • f 0 + ∑ i ∈ Finset.range (m + 1),
        σ (i + 1) • (f (i + 1) + θ (i + 1) • (f (i + 1) - f i)) := by
  let z (i : ℕ) : V := (σ (i + 1) * θ (i + 1)) • f i
  let a (i : ℕ) : V := σ (i + 1) • (f (i + 1) + θ (i + 1) • (f (i + 1) - f i))
  have hstep (i : ℕ) (hi : i ∈ Finset.range m) :
      ergWeight σ θ (m + 1) i • f (i + 1) = a i + (z i - z (i + 1)) := by
    have hi' : i + 1 < m + 1 := by have := Finset.mem_range.mp hi; omega
    simp only [ergWeight, if_pos hi', a, z, Nat.add_assoc, sub_smul,
      mul_smul, add_smul, one_smul, smul_add, smul_sub]
    abel
  have hlast : ergWeight σ θ (m + 1) m • f (m + 1) = a m + z m := by
    simp only [ergWeight, if_neg (Nat.lt_irrefl (m + 1)), sub_zero,
      a, z, mul_smul, add_smul, one_smul, smul_add, smul_sub]
    abel
  have hinner : (∑ i ∈ Finset.range m, ergWeight σ θ (m + 1) i • f (i + 1))
      = (∑ i ∈ Finset.range m, a i) + (z 0 - z m) := by
    calc
      _ = ∑ x ∈ Finset.range m, (a x + (z x - z (x + 1))) :=
        Finset.sum_congr rfl hstep
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub' z m]
  change (∑ i ∈ Finset.range (m + 1), ergWeight σ θ (m + 1) i • f (i + 1))
    = z 0 + ∑ i ∈ Finset.range (m + 1), a i
  rw [Finset.sum_range_succ, hlast, hinner, Finset.sum_range_succ a m]
  abel

theorem ergWeight_sum (σ θ : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ergWeight σ θ (m + 1) i)
      = σ 1 * θ 1 + ∑ i ∈ Finset.range (m + 1), σ (i + 1) := by
  simpa only [smul_eq_mul, mul_one, sub_self, mul_zero, add_zero] using
    ergWeight_smul_sum σ θ (fun _ => (1 : ℝ)) m

theorem ergWeight_values (σ θ f : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ergWeight σ θ (m + 1) i * f (i + 1))
      = σ 1 * θ 1 * f 0 + ∑ i ∈ Finset.range (m + 1),
        σ (i + 1) * ((1 + θ (i + 1)) * f (i + 1) - θ (i + 1) * f i) := by
  have h := ergWeight_smul_sum σ θ f m
  simp only [smul_eq_mul] at h
  rw [h]
  apply congrArg (fun t : ℝ => σ 1 * θ 1 * f 0 + t)
  apply Finset.sum_congr rfl
  intro i hi
  ring

end
end APDAL
