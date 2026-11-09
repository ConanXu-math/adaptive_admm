import UFGM.Kernel
import UFGM.TrialBound

open Set

namespace UFGM

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

structure Problem (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  Q : Set E
  closedQ : IsClosed Q
  convexQ : Convex ℝ Q
  oracle : Oracle Q
  kernel : Kernel Q
  regularizer : Regularizer Q
  x0 : E
  x0_mem : x0 ∈ Q
  x0_min : IsMinOn kernel.value Q x0
  L0 : ℝ
  ε : ℝ
  L0_pos : 0 < L0
  ε_pos : 0 < ε

def HasHolder (p : Problem E) : Prop :=
  ∃ ν M : ℝ, 0 ≤ ν ∧ ν ≤ 1 ∧ 0 ≤ M ∧ Holder p.oracle ν M

structure State (p : Problem E) where
  A : ℝ
  L : ℝ
  y : E
  lin : E →L[ℝ] ℝ
  constant : ℝ
  A_nonneg : 0 ≤ A
  L_pos : 0 < L
  y_mem : y ∈ p.Q
  y_dom : 0 < A → y ∈ p.regularizer.dom
  zero_init : A = 0 → lin = 0 ∧ constant = 0 ∧ y = p.x0

def initial (p : Problem E) : State p where
  A := 0
  L := p.L0
  y := p.x0
  lin := 0
  constant := 0
  A_nonneg := le_rfl
  L_pos := p.L0_pos
  y_mem := p.x0_mem
  y_dom := fun h => (lt_irrefl 0 h).elim
  zero_init := fun _ => ⟨rfl, rfl, rfl⟩

def estimateDomain (p : Problem E) (s : State p) : Set E :=
  if s.A = 0 then p.Q else p.regularizer.dom

def estimateFun (p : Problem E) (s : State p) (x : E) : ℝ :=
  bregman p.kernel p.x0 x + affineReg p.regularizer s.lin s.constant s.A x

theorem estimateDomain_subset (p : Problem E) (s : State p) : estimateDomain p s ⊆ p.Q := by
  unfold estimateDomain
  split_ifs
  · exact Subset.rfl
  · exact p.regularizer.subset

theorem estimate_min_exists (p : Problem E) (s : State p) :
    ∃! v, v ∈ estimateDomain p s ∧ IsMinOn (estimateFun p s) (estimateDomain p s) v := by
  by_cases hA : s.A = 0
  · have hi := s.zero_init hA
    have he : estimateFun p s = bregman p.kernel p.x0 := by
      funext x
      simp [estimateFun, affineReg, hi.1, hi.2.1, hA]
    rw [estimateDomain, if_pos hA, he]
    have hx : IsMinOn (bregman p.kernel p.x0) p.Q p.x0 := by
      apply isMinOn_iff.2
      intro z hz
      rw [bregman_self]
      exact (by positivity : 0 ≤ ‖z - p.x0‖^2 / 2).trans (bregman_lower p.kernel p.x0_mem hz)
    refine ⟨p.x0, ⟨p.x0_mem, hx⟩, ?_⟩
    intro v hv
    have hh := (isMinOn_iff.1 hv.2) p.x0 p.x0_mem
    rw [bregman_self] at hh
    by_contra hn
    have hpos := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) 2
    have hlow := bregman_lower p.kernel p.x0_mem hv.1
    linarith only [hpos, hlow, hh]
  · have hpos : 0 < s.A := lt_of_le_of_ne s.A_nonneg (Ne.symm hA)
    let l := s.lin - p.kernel.derivative p.x0
    let c := s.constant - p.kernel.value p.x0 + p.kernel.derivative p.x0 p.x0
    have he : estimateFun p s = (fun x => p.kernel.value x + affineReg p.regularizer l c s.A x) := by
      funext x
      simp only [estimateFun, bregman, affineReg, l, c, ContinuousLinearMap.sub_apply, map_sub]
      ring
    rw [estimateDomain, if_neg hA, he]
    exact kernel_reg_min p.closedQ p.convexQ p.kernel p.regularizer l c hpos

def estimateMin (p : Problem E) (s : State p) : E :=
  Classical.choose (estimate_min_exists p s).exists

theorem estimateMin_spec (p : Problem E) (s : State p) :
    estimateMin p s ∈ estimateDomain p s ∧
      IsMinOn (estimateFun p s) (estimateDomain p s) (estimateMin p s) :=
  Classical.choose_spec (estimate_min_exists p s).exists

def trialX (p : Problem E) (s : State p) (H : ℝ) : E :=
  trialRatio s.A H • estimateMin p s + (1 - trialRatio s.A H) • s.y

theorem trialX_mem (p : Problem E) (s : State p) {H : ℝ} (hH : 0 < H) : trialX p s H ∈ p.Q := by
  have ht := trialRatio_range s.A_nonneg hH
  exact p.convexQ (estimateDomain_subset p s (estimateMin_spec p s).1) s.y_mem
    ht.1.le (sub_nonneg.mpr ht.2) (by ring)

def trialObjective (p : Problem E) (s : State p) (H : ℝ) (u : E) : ℝ :=
  bregman p.kernel (estimateMin p s) u +
    trialWeight s.A H * (p.oracle.grad (trialX p s H) u + p.regularizer.value u)

theorem trial_min_exists (p : Problem E) (s : State p) {H : ℝ} (hH : 0 < H) :
    ∃! u, u ∈ p.regularizer.dom ∧ IsMinOn (trialObjective p s H) p.regularizer.dom u := by
  let v := estimateMin p s
  let a := trialWeight s.A H
  let l := a • p.oracle.grad (trialX p s H) - p.kernel.derivative v
  let c := -p.kernel.value v + p.kernel.derivative v v
  have ha : 0 < a := trialWeight_pos hH
  have he : trialObjective p s H = (fun u => p.kernel.value u + affineReg p.regularizer l c a u) := by
    funext u
    simp only [trialObjective, bregman, affineReg, l, c, v, a, map_sub,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact kernel_reg_min p.closedQ p.convexQ p.kernel p.regularizer l c ha

def trialU (p : Problem E) (s : State p) (H : ℝ) (hH : 0 < H) : E :=
  Classical.choose (trial_min_exists p s hH).exists

theorem trialU_spec (p : Problem E) (s : State p) (H : ℝ) (hH : 0 < H) :
    trialU p s H hH ∈ p.regularizer.dom ∧
      IsMinOn (trialObjective p s H) p.regularizer.dom (trialU p s H hH) :=
  Classical.choose_spec (trial_min_exists p s hH).exists

def trialY (p : Problem E) (s : State p) (H : ℝ) (hH : 0 < H) : E :=
  trialRatio s.A H • trialU p s H hH + (1 - trialRatio s.A H) • s.y

theorem trialY_dom (p : Problem E) (s : State p) (H : ℝ) (hH : 0 < H) :
    trialY p s H hH ∈ p.regularizer.dom := by
  by_cases hA : s.A = 0
  · have ht : trialRatio s.A H = 1 := by
      unfold trialRatio
      rw [hA, zero_add, div_self (trialWeight_pos hH).ne']
    have h := (trialU_spec p s H hH).1
    rw [trialY, ht]
    simpa only [one_smul, sub_self, zero_smul, add_zero] using h
  · have ht := trialRatio_range s.A_nonneg hH
    exact p.regularizer.convex.1 (trialU_spec p s H hH).1
      (s.y_dom (lt_of_le_of_ne s.A_nonneg (Ne.symm hA))) ht.1.le (sub_nonneg.mpr ht.2) (by ring)

def Accept (p : Problem E) (s : State p) (H : ℝ) (hH : 0 < H) : Prop :=
  let x := trialX p s H
  let y := trialY p s H hH
  p.oracle.value y ≤ p.oracle.value x + p.oracle.grad x (y - x) +
    H * ‖y - x‖^2 / 2 + p.ε * trialRatio s.A H / 2

theorem accept_of_threshold (p : Problem E) (s : State p) {H ν M : ℝ} (hH : 0 < H)
    (hν : 0 ≤ ν) (hν' : ν ≤ 1) (hM : 0 ≤ M) (hh : Holder p.oracle ν M)
    (hbound : smoothConstant ν M p.ε ≤ scaledTrial s.A H (holderPower ν)) : Accept p s H hH := by
  let x := trialX p s H
  let y := trialY p s H hH
  have hf := holder_model p.convexQ p.oracle hν hM hh x y (trialX_mem p s hH)
    (p.regularizer.subset (trialY_dom p s H hH))
  have ht := (trialRatio_range s.A_nonneg hH).1
  have hmodel := tolerance_model hν hν' hM p.ε_pos ht (norm_nonneg (y - x)) hbound
  change p.oracle.value y ≤ p.oracle.value x + p.oracle.grad x (y - x) +
    H * ‖y - x‖^2 / 2 + p.ε * trialRatio s.A H / 2
  linarith only [hf, hmodel]

end
end UFGM
