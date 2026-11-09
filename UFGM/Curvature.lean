import UFGM.Iteration
import UFGM.Growth

namespace UFGM

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem acceptedH_zero (p : Problem E) (h : HasHolder p) (s : State p)
    (hi : acceptedIndex p h s = 0) : acceptedH p h s = s.L := by
  simp [acceptedH, trialH, hi]

theorem positive_index_bound (p : Problem E) (h : HasHolder p) (s : State p)
    {ν M : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M) (hh : Holder p.oracle ν M)
    (hi : 0 < acceptedIndex p h s) :
    scaledTrial s.A (acceptedH p h s) (holderPower ν) ≤ 2 * smoothConstant ν M p.ε := by
  cases ei : acceptedIndex p h s with
  | zero => omega
  | succ i =>
    let H₀ := trialH s i
    let H := acceptedH p h s
    let r := holderPower ν
    let C := smoothConstant ν M p.ε
    have hp₀ : 0 < H₀ := trialH_pos s i
    have hp : 0 < H := acceptedH_pos p h s
    have he : H = 2 * H₀ := by
      dsimp only [H, H₀, acceptedH, trialH]
      rw [ei, pow_succ]
      ring
    have hmin : i < acceptedIndex p h s := by rw [ei]; exact Nat.lt_succ_self i
    have hprev : scaledTrial s.A H₀ r < C := by
      apply lt_of_not_ge
      intro hbound
      exact (accepted_minimal p h s i hmin) (accept_of_threshold p s hp₀ hν hν' hM hh hbound)
    have hH : H₀ ≤ H := by linarith only [he, hp₀]
    have hτ := trialRatio_antitone s.A_nonneg hp₀ hH
    have hpow := Real.rpow_le_rpow (trialRatio_range s.A_nonneg hp).1.le hτ (holderPower_range hν hν').1
    change scaledTrial s.A H r ≤ 2 * C
    calc
      _ ≤ H * (trialRatio s.A H₀)^r := mul_le_mul_of_nonneg_left hpow hp.le
      _ = 2 * scaledTrial s.A H₀ r := by unfold scaledTrial; rw [he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprev.le (by norm_num)

theorem trialRatio_zero (H : ℝ) (hH : 0 < H) : trialRatio 0 H = 1 := by
  unfold trialRatio
  rw [zero_add, div_self (trialWeight_pos hH).ne']

theorem uniform_curvature (p : Problem E) (h : HasHolder p)
    {ν M : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M) (hh : Holder p.oracle ν M) (n : ℕ) :
    let s := states p h n
    scaledTrial s.A (acceptedH p h s) (holderPower ν) ≤ max p.L0 (2 * smoothConstant ν M p.ε) := by
  let C := smoothConstant ν M p.ε
  let D := max p.L0 (2 * C)
  let r := holderPower ν
  change scaledTrial (states p h n).A (acceptedH p h (states p h n)) r ≤ D
  induction n with
  | zero =>
    let s := initial p
    change scaledTrial s.A (acceptedH p h s) r ≤ D
    by_cases hi : acceptedIndex p h s = 0
    · have he := acceptedH_zero p h s hi
      change acceptedH p h s = p.L0 at he
      unfold scaledTrial
      change acceptedH p h s * (trialRatio 0 (acceptedH p h s))^r ≤ D
      rw [trialRatio_zero _ (acceptedH_pos p h s), Real.one_rpow, mul_one, he]
      exact le_max_left _ _
    · exact (positive_index_bound p h s hν hν' hM hh (Nat.pos_of_ne_zero hi)).trans (le_max_right _ _)
  | succ n ih =>
    let s := states p h n
    let v := next p h s
    let H₀ := acceptedH p h s
    let H := acceptedH p h v
    change scaledTrial v.A H r ≤ D
    by_cases hi : acceptedIndex p h v = 0
    · have he : H = H₀ / 2 := acceptedH_zero p h v hi
      have hH₀ : 0 < H₀ := acceptedH_pos p h s
      have hH : 0 < H := acceptedH_pos p h v
      have hle : H ≤ H₀ := by linarith only [he, hH₀]
      have hB : s.A + trialWeight s.A H₀ ≤ v.A + trialWeight v.A H :=
        le_add_of_nonneg_right (trialWeight_pos hH).le
      have hr := holderPower_range hν hν'
      exact (scaledTrial_first_monotone s.A_nonneg v.A_nonneg hH₀ hH hr.1 hr.2 hle hB).trans ih
    · exact (positive_index_bound p h v hν hν' hM hh (Nat.pos_of_ne_zero hi)).trans (le_max_right _ _)

theorem states_growth (p : Problem E) (h : HasHolder p)
    {ν M : ℝ} (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M) (hh : Holder p.oracle ν M) (n : ℕ) :
    let D := max p.L0 (2 * smoothConstant ν M p.ε)
    let γ := 1 / (2 - holderPower ν)
    ((n : ℝ) / 2)^(1 / γ) / D ≤ (states p h n).A := by
  let D := max p.L0 (2 * smoothConstant ν M p.ε)
  let r := holderPower ν
  let γ := 1 / (2 - r)
  have hr := holderPower_range hν hν'
  have hD : 0 < D := p.L0_pos.trans_le (le_max_left _ _)
  have hγ : 0 < γ := one_div_pos.mpr (by linarith only [hr.2])
  apply accumulate_power hD hγ rfl (fun k => (states p h k).A_nonneg) _ n
  intro k
  let s := states p h k
  let H := acceptedH p h s
  let a := trialWeight s.A H
  have hH : 0 < H := acceptedH_pos p h s
  have ha : 0 < a := trialWeight_pos hH
  have hroot : H * a^2 = s.A + a := trialWeight_eq s.A_nonneg hH
  have hb : H * (a / (s.A + a))^r ≤ D := uniform_curvature p h hν hν' hM hh k
  exact power_increment s.A_nonneg ha hH hD hr.1 hr.2 hroot hb

end
end UFGM
