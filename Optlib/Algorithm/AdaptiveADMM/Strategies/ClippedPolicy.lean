import Optlib.Algorithm.AdaptiveADMM.Strategies.StrategyPolicy

/-!
Clipping a Strategy3 update changes its effective modulation.  On a positive
interval, that modulation remains between zero and the nominal modulation.
The resulting policy is defined along the supplied penalty sequence; these
lemmas concern the real-valued recurrence, not Python program equivalence.
-/

noncomputable section

namespace AdaptiveADMM.ClippedPolicy

def clamp (lower upper value : ℝ) : ℝ :=
  min upper (max lower value)

lemma clamp_bounds {lower upper value : ℝ} (hBounds : lower ≤ upper) :
    lower ≤ clamp lower upper value ∧ clamp lower upper value ≤ upper := by
  exact ⟨le_min hBounds (le_max_left lower value), min_le_left _ _⟩

lemma clamp_eq_of_bounds {lower upper value : ℝ}
    (hValue : lower ≤ value ∧ value ≤ upper) :
    clamp lower upper value = value := by
  simp [clamp, hValue.1, hValue.2]

lemma clamp_pos {lower upper value : ℝ}
    (hLower : 0 < lower) (hBounds : lower ≤ upper) :
    0 < clamp lower upper value :=
  hLower.trans_le (clamp_bounds hBounds).1

/-- For an input already in the interval, only the bound in the direction of
the action can clip the nominal update. -/
def update (lower upper : ℝ) (action : RhoAction) (tau rho : ℝ) : ℝ :=
  match action with
  | .increase => min upper (rho * (1 + tau))
  | .decrease => max lower (rho / (1 + tau))
  | .keep => rho

def effectiveAux (lower upper : ℝ) (action : RhoAction) (tau rho : ℝ) : ℝ :=
  match action with
  | .increase => update lower upper .increase tau rho / rho - 1
  | .decrease => rho / update lower upper .decrease tau rho - 1
  | .keep => 0

variable {lower upper tau rho : ℝ}

lemma increase_bounds (hRho : 0 ≤ rho) (hUpper : rho ≤ upper)
    (hTau : 0 ≤ tau) :
    rho ≤ update lower upper .increase tau rho ∧
      update lower upper .increase tau rho ≤ rho * (1 + tau) := by
  constructor
  · apply le_min hUpper
    nlinarith
  · exact min_le_right _ _

lemma decrease_bounds (hRho : 0 ≤ rho) (hLower : lower ≤ rho)
    (hTau : 0 ≤ tau) :
    rho / (1 + tau) ≤ update lower upper .decrease tau rho ∧
      update lower upper .decrease tau rho ≤ rho := by
  constructor
  · exact le_max_right _ _
  · exact max_le hLower (div_le_self hRho (by linarith))

theorem update_bounds (action : RhoAction) (hLower : 0 < lower)
    (hRho : lower ≤ rho ∧ rho ≤ upper) (hTau : 0 ≤ tau) :
    lower ≤ update lower upper action tau rho ∧
      update lower upper action tau rho ≤ upper := by
  have hRhoNonneg : 0 ≤ rho := hLower.le.trans hRho.1
  cases action with
  | increase =>
      exact ⟨hRho.1.trans (increase_bounds hRhoNonneg hRho.2 hTau).1,
        min_le_left _ _⟩
  | decrease =>
      exact ⟨le_max_left _ _,
        (decrease_bounds hRhoNonneg hRho.1 hTau).2.trans hRho.2⟩
  | keep => exact hRho

theorem update_pos (action : RhoAction) (hLower : 0 < lower)
    (hRho : lower ≤ rho ∧ rho ≤ upper) (hTau : 0 ≤ tau) :
    0 < update lower upper action tau rho :=
  hLower.trans_le (update_bounds action hLower hRho hTau).1

theorem update_eq_clamp (action : RhoAction) (hLower : 0 < lower)
    (hRho : lower ≤ rho ∧ rho ≤ upper) (hTau : 0 ≤ tau) :
    update lower upper action tau rho =
      clamp lower upper (action.update tau rho) := by
  have hRhoNonneg : 0 ≤ rho := hLower.le.trans hRho.1
  cases action with
  | increase =>
      have hNominal : lower ≤ rho * (1 + tau) := by
        have : rho ≤ rho * (1 + tau) := by nlinarith
        exact hRho.1.trans this
      simp [update, clamp, RhoAction.update, max_eq_right hNominal]
  | decrease =>
      have hNext : max lower (rho / (1 + tau)) ≤ upper :=
        (decrease_bounds (upper := upper) hRhoNonneg hRho.1 hTau).2.trans hRho.2
      simp [update, clamp, RhoAction.update, min_eq_right hNext]
  | keep => exact (clamp_eq_of_bounds hRho).symm

theorem effectiveAux_bounds (action : RhoAction) (hLower : 0 < lower)
    (hRho : lower ≤ rho ∧ rho ≤ upper) (hTau : 0 ≤ tau) :
    0 ≤ effectiveAux lower upper action tau rho ∧
      effectiveAux lower upper action tau rho ≤ tau := by
  have hRhoPos : 0 < rho := hLower.trans_le hRho.1
  cases action with
  | increase =>
      have hNext := increase_bounds (lower := lower) hRhoPos.le hRho.2 hTau
      change 0 ≤ update lower upper .increase tau rho / rho - 1 ∧
        update lower upper .increase tau rho / rho - 1 ≤ tau
      constructor
      · have : 1 ≤ update lower upper .increase tau rho / rho :=
          (le_div_iff₀ hRhoPos).2 (by simpa using hNext.1)
        linarith
      · have : update lower upper .increase tau rho / rho ≤ 1 + tau :=
          (div_le_iff₀ hRhoPos).2 (by simpa [mul_comm] using hNext.2)
        linarith
  | decrease =>
      have hNext := decrease_bounds (upper := upper) hRhoPos.le hRho.1 hTau
      have hNextPos := update_pos .decrease hLower hRho hTau
      have hFactor : 0 < 1 + tau := by linarith
      change 0 ≤ rho / update lower upper .decrease tau rho - 1 ∧
        rho / update lower upper .decrease tau rho - 1 ≤ tau
      constructor
      · have : 1 ≤ rho / update lower upper .decrease tau rho :=
          (le_div_iff₀ hNextPos).2 (by simpa using hNext.2)
        linarith
      · have hProduct : rho ≤ update lower upper .decrease tau rho * (1 + tau) :=
          (div_le_iff₀ hFactor).1 hNext.1
        have : rho / update lower upper .decrease tau rho ≤ 1 + tau :=
          (div_le_iff₀ hNextPos).2 (by simpa [mul_comm] using hProduct)
        linarith
  | keep => exact ⟨le_rfl, hTau⟩

theorem update_eq_action_update (action : RhoAction) (hLower : 0 < lower)
    (hRho : lower ≤ rho ∧ rho ≤ upper) (hTau : 0 ≤ tau) :
    update lower upper action tau rho =
      action.update (effectiveAux lower upper action tau rho) rho := by
  have hRhoPos : 0 < rho := hLower.trans_le hRho.1
  have hNextPos := update_pos action hLower hRho hTau
  cases action with
  | increase =>
      change update lower upper .increase tau rho =
        rho * (1 + (update lower upper .increase tau rho / rho - 1))
      field_simp [ne_of_gt hRhoPos]
      ring
  | decrease =>
      change update lower upper .decrease tau rho =
        rho / (1 + (rho / update lower upper .decrease tau rho - 1))
      field_simp [ne_of_gt hRhoPos, ne_of_gt hNextPos]
      ring
  | keep => rfl

/-- An in-bounds initial penalty remains in bounds under the stated recurrence. -/
theorem trajectory_bounds (lower upper : ℝ) (hLower : 0 < lower)
    (nominal rho : ℕ → ℝ) (action : ℕ → RhoAction)
    (hNominal : ∀ n, 0 ≤ nominal n)
    (hInitial : lower ≤ rho 0 ∧ rho 0 ≤ upper)
    (hRecurrence : ∀ n, rho (n + 1) = update lower upper (action n) (nominal n) (rho n)) :
    ∀ n, lower ≤ rho n ∧ rho n ≤ upper := by
  intro n
  induction n with
  | zero => exact hInitial
  | succ n ih =>
      change lower ≤ rho (n + 1) ∧ rho (n + 1) ≤ upper
      rw [hRecurrence n]
      exact update_bounds (action n) hLower ih (hNominal n)

theorem effectiveAux_summable (lower upper : ℝ) (hLower : 0 < lower)
    (nominal rho : ℕ → ℝ) (action : ℕ → RhoAction)
    (hNominal : ∀ n, 0 ≤ nominal n) (hSummable : Summable nominal)
    (hRho : ∀ n, lower ≤ rho n ∧ rho n ≤ upper) :
    Summable (fun n => effectiveAux lower upper (action n) (nominal n) (rho n)) := by
  exact hSummable.of_nonneg_of_le
    (fun n => (effectiveAux_bounds (action n) hLower (hRho n) (hNominal n)).1)
    (fun n => (effectiveAux_bounds (action n) hLower (hRho n) (hNominal n)).2)

def certifiedTau (lower upper : ℝ) (hLower : 0 < lower)
    (nominal : CertifiedTau) (rho : ℕ → ℝ) (action : ℕ → RhoAction)
    (hRho : ∀ n, lower ≤ rho n ∧ rho n ≤ upper) : CertifiedTau where
  seq n := effectiveAux lower upper (action n) (nominal.seq n) (rho n)
  nonneg n := (effectiveAux_bounds (action n) hLower (hRho n) (nominal.nonneg n)).1
  summable := effectiveAux_summable lower upper hLower nominal.seq rho action
    nominal.nonneg nominal.summable hRho

/-- The effective auxiliary sequence is evaluated along `rho`.  Equality with
the clipped update below is asserted at `rho n`, not at arbitrary inputs. -/
def toStrategyPolicy (lower upper : ℝ) (hLower : 0 < lower)
    (nominal : CertifiedTau) (rho : ℕ → ℝ) (action : ℕ → RhoAction)
    (hRho : ∀ n, lower ≤ rho n ∧ rho n ≤ upper) : StrategyPolicy where
  tau := certifiedTau lower upper hLower nominal rho action hRho
  action := action

theorem toStrategyPolicy_updateRho (lower upper : ℝ) (hLower : 0 < lower)
    (nominal : CertifiedTau) (rho : ℕ → ℝ) (action : ℕ → RhoAction)
    (hRho : ∀ n, lower ≤ rho n ∧ rho n ≤ upper) (n : ℕ) :
    (toStrategyPolicy lower upper hLower nominal rho action hRho).updateRho n (rho n) =
      update lower upper (action n) (nominal.seq n) (rho n) := by
  exact (update_eq_action_update (action n) hLower (hRho n) (nominal.nonneg n)).symm

/-- Ordered residual branches, including the denominator floor. -/
def residualAction (mu floor r s : ℝ) : RhoAction :=
  if mu * max s floor < r then .increase
  else if mu * max r floor < s then .decrease else .keep

/-- Delay increases only. Decreases retain the original nominal step. -/
def delayIncrease (startAt n : ℕ) (action : RhoAction) : RhoAction :=
  match action with
  | .increase => if n < startAt then .keep else .increase
  | .decrease => .decrease
  | .keep => .keep

@[simp] theorem delayIncrease_decrease (startAt n : ℕ) :
    delayIncrease startAt n .decrease = .decrease := rfl

/-- Exact real-arithmetic branch expression for an in-bounds input. This
does not assert floating-point equivalence, invalid-input behavior, or the
convergence of the full ADMM iterates. In particular the early decrease is
rho / (1 + tau), not rho / (1 + 0). -/
theorem delayed_residual_branches (startAt n : ℕ) (mu floor r s : ℝ)
    (hLower : 0 < lower) (hRho : lower ≤ rho ∧ rho ≤ upper) (hTau : 0 ≤ tau) :
    update lower upper (delayIncrease startAt n (residualAction mu floor r s)) tau rho =
      clamp lower upper
        (if mu * max s floor < r then rho * (1 + if n < startAt then 0 else tau)
         else if mu * max r floor < s then rho / (1 + tau) else rho) := by
  rw [update_eq_clamp _ hLower hRho hTau]
  by_cases hi : mu * max s floor < r
  · by_cases hn : n < startAt <;>
      simp [residualAction, delayIncrease, hi, hn, RhoAction.update]
  · by_cases hd : mu * max r floor < s <;>
      simp [residualAction, delayIncrease, hi, hd, RhoAction.update]

theorem delayed_effectiveAux_summable (lower upper : ℝ) (hLower : 0 < lower)
    (startAt : ℕ) (nominal rho : ℕ → ℝ) (action : ℕ → RhoAction)
    (hNominal : ∀ n, 0 ≤ nominal n) (hSummable : Summable nominal)
    (hRho : ∀ n, lower ≤ rho n ∧ rho n ≤ upper) :
    Summable (fun n => effectiveAux lower upper (delayIncrease startAt n (action n))
      (nominal n) (rho n)) := by
  exact effectiveAux_summable lower upper hLower nominal rho
    (fun n => delayIncrease startAt n (action n)) hNominal hSummable hRho

end AdaptiveADMM.ClippedPolicy
