import UFGM.StateTrial

namespace UFGM

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def trialH {p : Problem E} (s : State p) (i : ℕ) : ℝ := (2 : ℝ)^i * s.L

theorem trialH_pos {p : Problem E} (s : State p) (i : ℕ) : 0 < trialH s i :=
  mul_pos (pow_pos (by norm_num) _) s.L_pos

theorem accept_exists (p : Problem E) (h : HasHolder p) (s : State p) :
    ∃ i : ℕ, Accept p s (trialH s i) (trialH_pos s i) := by
  obtain ⟨ν, M, hν, hν', hM, hh⟩ := h
  obtain ⟨i, hi⟩ := threshold_candidate_exists s.A_nonneg s.L_pos (holderPower_range hν hν').2
    (smoothConstant_nonneg hM p.ε_pos)
  exact ⟨i, accept_of_threshold p s (trialH_pos s i) hν hν' hM hh hi⟩

def acceptedIndex (p : Problem E) (h : HasHolder p) (s : State p) : ℕ := by
  classical
  exact Nat.find (accept_exists p h s)

def acceptedH (p : Problem E) (h : HasHolder p) (s : State p) : ℝ := trialH s (acceptedIndex p h s)

theorem acceptedH_pos (p : Problem E) (h : HasHolder p) (s : State p) : 0 < acceptedH p h s :=
  trialH_pos s _

theorem accepted_spec (p : Problem E) (h : HasHolder p) (s : State p) :
    Accept p s (acceptedH p h s) (acceptedH_pos p h s) := by
  classical
  exact Nat.find_spec (accept_exists p h s)

theorem accepted_minimal (p : Problem E) (h : HasHolder p) (s : State p) (i : ℕ)
    (hi : i < acceptedIndex p h s) : ¬Accept p s (trialH s i) (trialH_pos s i) := by
  classical
  exact Nat.find_min (accept_exists p h s) hi

def next (p : Problem E) (h : HasHolder p) (s : State p) : State p :=
  let H := acceptedH p h s
  let hH := acceptedH_pos p h s
  let a := trialWeight s.A H
  let x := trialX p s H
  let y := trialY p s H hH
  let hy := trialY_dom p s H hH
  { A := s.A + a
    L := H / 2
    y := y
    lin := s.lin + a • p.oracle.grad x
    constant := s.constant + a * (p.oracle.value x - p.oracle.grad x x)
    A_nonneg := add_nonneg s.A_nonneg (trialWeight_pos hH).le
    L_pos := div_pos hH (by norm_num)
    y_mem := p.regularizer.subset hy
    y_dom := fun _ => hy
    zero_init := fun hz => False.elim ((add_pos_of_nonneg_of_pos s.A_nonneg (trialWeight_pos hH)).ne' hz) }

theorem next_A_pos (p : Problem E) (h : HasHolder p) (s : State p) : 0 < (next p h s).A :=
  add_pos_of_nonneg_of_pos s.A_nonneg (trialWeight_pos (acceptedH_pos p h s))

theorem estimate_update (p : Problem E) (h : HasHolder p) (s : State p) (w : E) :
    let H := acceptedH p h s
    let a := trialWeight s.A H
    let x := trialX p s H
    estimateFun p (next p h s) w = estimateFun p s w +
      a * (p.oracle.value x + p.oracle.grad x (w - x) + p.regularizer.value w) := by
  dsimp only [next, estimateFun, affineReg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub]
  ring

def states (p : Problem E) (h : HasHolder p) : ℕ → State p :=
  Nat.rec (initial p) (fun _ s => next p h s)

@[simp] theorem states_zero (p : Problem E) (h : HasHolder p) : states p h 0 = initial p := rfl

theorem states_succ (p : Problem E) (h : HasHolder p) (n : ℕ) :
    states p h (n + 1) = next p h (states p h n) := rfl

theorem accepted_zero_constant (p : Problem E) (h : HasHolder p) (s : State p) {ν : ℝ}
    (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hh : Holder p.oracle ν 0) : acceptedIndex p h s = 0 := by
  classical
  have he : smoothConstant ν 0 p.ε = 0 := by
    unfold smoothConstant
    rw [Real.zero_rpow (ne_of_gt (by positivity)), zero_mul]
  have hzero : Accept p s (trialH s 0) (trialH_pos s 0) := by
    apply accept_of_threshold p s (trialH_pos s 0) hν hν' (show (0 : ℝ) ≤ 0 from le_rfl) hh
    rw [he]
    unfold scaledTrial
    exact mul_nonneg (trialH_pos s 0).le (Real.rpow_nonneg (trialRatio_range s.A_nonneg (trialH_pos s 0)).1.le _)
  exact Nat.eq_zero_of_le_zero (Nat.find_min' (accept_exists p h s) hzero)

end
end UFGM
