import UFGM.Curvature

namespace UFGM

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def objective (p : Problem E) (x : E) : ℝ := p.oracle.value x + p.regularizer.value x

theorem estimateMin_at_zero (p : Problem E) (s : State p) (hA : s.A = 0) : estimateMin p s = p.x0 := by
  let v := estimateMin p s
  have hvQ : v ∈ p.Q := estimateDomain_subset p s (estimateMin_spec p s).1
  have hx0 : p.x0 ∈ estimateDomain p s := by simp [estimateDomain, hA, p.x0_mem]
  have hi := s.zero_init hA
  have he : estimateFun p s = bregman p.kernel p.x0 := by
    funext x
    simp [estimateFun, affineReg, hi.1, hi.2.1, hA]
  have H := (isMinOn_iff.1 (estimateMin_spec p s).2) p.x0 hx0
  rw [he, bregman_self] at H
  change v = p.x0
  by_contra hn
  have hp := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hn)) 2
  linarith only [H, hp, bregman_lower p.kernel p.x0_mem hvQ]

theorem estimate_min_support (p : Problem E) (s : State p) (w : E) (hw : w ∈ p.regularizer.dom) :
    estimateFun p s (estimateMin p s) + bregman p.kernel (estimateMin p s) w ≤ estimateFun p s w := by
  by_cases hA : s.A = 0
  · have hi := s.zero_init hA
    have he : estimateFun p s = bregman p.kernel p.x0 := by
      funext x
      simp [estimateFun, affineReg, hi.1, hi.2.1, hA]
    rw [he, estimateMin_at_zero p s hA, bregman_self, zero_add]
  · have hpos : 0 < s.A := lt_of_le_of_ne s.A_nonneg (Ne.symm hA)
    let l := s.lin - p.kernel.derivative p.x0
    let c := s.constant - p.kernel.value p.x0 + p.kernel.derivative p.x0 p.x0
    have he : estimateFun p s = (fun x => p.kernel.value x + affineReg p.regularizer l c s.A x) := by
      funext x
      simp only [estimateFun, bregman, affineReg, l, c, ContinuousLinearMap.sub_apply, map_sub]
      ring
    have H := estimateMin_spec p s
    have hD : estimateDomain p s = p.regularizer.dom := by rw [estimateDomain, if_neg hA]
    rw [hD, he] at H
    rw [he]
    exact min_bregman_support p.kernel p.regularizer.subset (affineReg_convex p.regularizer l c hpos.le) H.1 hw H.2

def EstimateLower (p : Problem E) (s : State p) : Prop :=
  s.A * (objective p s.y - p.ε / 2) ≤ estimateFun p s (estimateMin p s)

theorem estimate_lower_step (p : Problem E) (h : HasHolder p) (s : State p)
    (hinv : EstimateLower p s) : EstimateLower p (next p h s) := by
  let H := acceptedH p h s
  let hH := acceptedH_pos p h s
  let A := s.A
  let a := trialWeight A H
  let B := A + a
  let τ := trialRatio A H
  let v := estimateMin p s
  let y := s.y
  let x := trialX p s H
  let u := trialU p s H hH
  let z := trialY p s H hH
  let w := estimateMin p (next p h s)
  let f := p.oracle.value
  let ψ := p.regularizer.value
  let l := p.oracle.grad x
  let ξ := bregman p.kernel v
  have ha : 0 < a := trialWeight_pos hH
  have hB : 0 < B := add_pos_of_nonneg_of_pos s.A_nonneg ha
  have ht : 0 < τ ∧ τ ≤ 1 := trialRatio_range s.A_nonneg hH
  have hvQ : v ∈ p.Q := estimateDomain_subset p s (estimateMin_spec p s).1
  have huD : u ∈ p.regularizer.dom := (trialU_spec p s H hH).1
  have huQ : u ∈ p.Q := p.regularizer.subset huD
  have hwD : w ∈ p.regularizer.dom := by
    have Hm := (estimateMin_spec p (next p h s)).1
    have hD : estimateDomain p (next p h s) = p.regularizer.dom := by
      rw [estimateDomain, if_neg (next_A_pos p h s).ne']
    rwa [hD] at Hm
  have hτB : B * τ = a := by
    change B * (a / B) = a
    field_simp [hB.ne'] <;> ring
  have hτB' : B * (1 - τ) = A := by
    have h : B * (1 - τ) = B - B * τ := by ring
    dsimp only [B] at h ⊢
    rw [h, hτB]
    ring
  have hlinX : l x = τ * l v + (1 - τ) * l y := by
    change l (τ • v + (1 - τ) • y) = _
    simp only [map_add, map_smul, smul_eq_mul]
  have hlinX' : B * l x = a * l v + A * l y := by
    rw [hlinX]
    calc
      _ = (B * τ) * l v + (B * (1 - τ)) * l y := by ring
      _ = _ := by rw [hτB, hτB']
  have hlinW : A * l (y - x) + a * l (w - x) = a * l (w - v) := by
    simp only [map_sub]
    calc
      _ = A * l y + a * l w - B * l x := by dsimp only [B]; ring
      _ = _ := by rw [hlinX']; ring
  have hsup := mul_le_mul_of_nonneg_left (p.oracle.support x (trialX_mem p s hH) y s.y_mem) s.A_nonneg
  change A * (f x + l (y - x)) ≤ A * f y at hsup
  have hφ := estimate_min_support p s w hwD
  change estimateFun p s v + ξ w ≤ estimateFun p s w at hφ
  change A * (f y + ψ y - p.ε / 2) ≤ estimateFun p s v at hinv
  have hupdate := estimate_update p h s w
  change estimateFun p (next p h s) w = estimateFun p s w + a * (f x + l (w - x) + ψ w) at hupdate
  have hlo : ξ w + B * f x + a * l (w - v) + A * ψ y + a * ψ w - A * p.ε / 2
      ≤ estimateFun p (next p h s) w := by
    dsimp only [B]
    nlinarith only [hφ, hinv, hsup, hupdate, hlinW]
  have hmin := (isMinOn_iff.1 (trialU_spec p s H hH).2) w hwD
  change ξ u + a * (l u + ψ u) ≤ ξ w + a * (l w + ψ w) at hmin
  have hlu : ξ u + B * f x + a * l (u - v) + A * ψ y + a * ψ u - A * p.ε / 2
      ≤ estimateFun p (next p h s) w := by
    simp only [map_sub] at hlo ⊢
    nlinarith only [hlo, hmin]
  have hψ : B * ψ z ≤ a * ψ u + A * ψ y := by
    by_cases hA : A = 0
    · have ht₁ : τ = 1 := by change trialRatio A H = 1; rw [hA, trialRatio_zero H hH]
      have hzu : z = u := by change τ • u + (1 - τ) • y = u; simp [ht₁]
      dsimp only [B]
      rw [hA, hzu, zero_add, zero_mul, add_zero]
    · have hAp : 0 < A := lt_of_le_of_ne s.A_nonneg (Ne.symm hA)
      have hc := p.regularizer.convex.2 huD (s.y_dom hAp) ht.1.le (sub_nonneg.mpr ht.2)
        (show τ + (1 - τ) = 1 by ring)
      change ψ z ≤ τ • ψ u + (1 - τ) • ψ y at hc
      simp only [smul_eq_mul] at hc
      calc
        _ ≤ B * (τ * ψ u + (1 - τ) * ψ y) := mul_le_mul_of_nonneg_left hc hB.le
        _ = (B * τ) * ψ u + (B * (1 - τ)) * ψ y := by ring
        _ = _ := by rw [hτB, hτB']
  have hdiff : z - x = τ • (u - v) := by
    change (τ • u + (1 - τ) • y) - (τ • v + (1 - τ) • y) = _
    rw [smul_sub]
    abel
  have hlinZ : B * l (z - x) = a * l (u - v) := by
    rw [hdiff, map_smul, smul_eq_mul, ← mul_assoc, hτB]
  have hroot : H * a^2 = B := trialWeight_eq s.A_nonneg hH
  have hsc : B * H * τ^2 = 1 := by
    change B * H * (a / B)^2 = 1
    rw [div_pow]
    calc
      _ = (H * a^2) * B / B^2 := by ring
      _ = _ := by rw [hroot, ← pow_two, div_self (pow_ne_zero 2 hB.ne')]
  have hNorm : B * (H * ‖z - x‖^2 / 2) = ‖u - v‖^2 / 2 := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1.le, mul_pow]
    calc
      _ = (B * H * τ^2) * ‖u - v‖^2 / 2 := by ring
      _ = _ := by rw [hsc, one_mul]
  have hacc := accepted_spec p h s
  change f z ≤ f x + l (z - x) + H * ‖z - x‖^2 / 2 + p.ε * τ / 2 at hacc
  have hacc' : B * f z ≤ B * f x + a * l (u - v) + ‖u - v‖^2 / 2 + a * p.ε / 2 := by
    calc
      _ ≤ B * (f x + l (z - x) + H * ‖z - x‖^2 / 2 + p.ε * τ / 2) :=
        mul_le_mul_of_nonneg_left hacc hB.le
      _ = B * f x + B * l (z - x) + B * (H * ‖z - x‖^2 / 2) + (B * τ) * p.ε / 2 := by ring
      _ = _ := by rw [hlinZ, hNorm, hτB]
  have hξ : ‖u - v‖^2 / 2 ≤ ξ u := bregman_lower p.kernel hvQ huQ
  change B * (f z + ψ z - p.ε / 2) ≤ estimateFun p (next p h s) w
  dsimp only [B] at hacc' hψ hlu ⊢
  nlinarith only [hacc', hψ, hξ, hlu]

theorem estimate_lower (p : Problem E) (h : HasHolder p) (n : ℕ) : EstimateLower p (states p h n) := by
  induction n with
  | zero =>
    have he := estimateMin_at_zero p (initial p) rfl
    unfold EstimateLower
    rw [states_zero, he]
    simp [estimateFun, affineReg, initial]
  | succ n ih => exact estimate_lower_step p h (states p h n) ih

theorem estimate_upper (p : Problem E) (h : HasHolder p) (w : E) (hw : w ∈ p.regularizer.dom) (n : ℕ) :
    estimateFun p (states p h n) w ≤ bregman p.kernel p.x0 w + (states p h n).A * objective p w := by
  induction n with
  | zero => simp [estimateFun, affineReg, initial]
  | succ n ih =>
    let s := states p h n
    let H := acceptedH p h s
    let a := trialWeight s.A H
    let x := trialX p s H
    have ha : 0 < a := trialWeight_pos (acceptedH_pos p h s)
    have hs := p.oracle.support x (trialX_mem p s (acceptedH_pos p h s)) w (p.regularizer.subset hw)
    have hu := estimate_update p h s w
    change estimateFun p (next p h s) w = estimateFun p s w +
      a * (p.oracle.value x + p.oracle.grad x (w - x) + p.regularizer.value w) at hu
    change estimateFun p (next p h s) w ≤ bregman p.kernel p.x0 w + (s.A + a) * objective p w
    unfold objective at ih ⊢
    nlinarith only [ih, hu, mul_le_mul_of_nonneg_left hs ha.le]

end
end UFGM
