import AdaRES.Scalar
import AdaRES.Prox

open InnerProductSpace
open scoped InnerProduct

namespace AdaRES

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

structure FState (E : Type*) where
  x : E
  z : E

def fistaNext (data : Smooth E) (ψ : ProperConvex E) (n : ℕ) (s : FState E) : FState E :=
  let t := theta n
  let y := (1 - t) • s.x + t • s.z
  let x := step data ψ y
  ⟨x, s.z + t⁻¹ • (x - y)⟩

def fistaState (data : Smooth E) (ψ : ProperConvex E) (x0 : E) : ℕ → FState E :=
  Nat.rec ⟨x0, x0⟩ (fun n s => fistaNext data ψ n s)

theorem fista_x_dom (data : Smooth E) (ψ : ProperConvex E) (x0 : E) (hx0 : x0 ∈ ψ.dom)
    (n : ℕ) : (fistaState data ψ x0 n).x ∈ ψ.dom := by
  cases n with
  | zero => exact hx0
  | succ n => exact step_dom data ψ _

theorem fista_scaled_step (data : Smooth E) (ψ : ProperConvex E)
    (n : ℕ) (s : FState E) (hx : s.x ∈ ψ.dom) (u : E) (hu : u ∈ ψ.dom) :
    let q := fistaNext data ψ n s
    (accelInv n)^2 * (objective data ψ q.x - objective data ψ u) + ‖q.z - u‖^2 / 2
      ≤ ((accelInv n)^2 - accelInv n) * (objective data ψ s.x - objective data ψ u)
        + ‖s.z - u‖^2 / 2 := by
  let t := theta n
  let q := fistaNext data ψ n s
  let y := (1 - t) • s.x + t • s.z
  let v := (1 - t) • s.x + t • u
  let F := objective data ψ
  have ht : 0 < t := theta_pos n
  have ha : 0 ≤ 1 - t := sub_nonneg.mpr (theta_le_one n)
  have hab : (1 - t) + t = 1 := by ring
  have hv : v ∈ ψ.dom := ψ.dom_convex hx hu ha ht.le hab
  have hf := data.convex.2 (Set.mem_univ s.x) (Set.mem_univ u) ha ht.le hab
  have hψ := ψ.convex_on.2 hx hu ha ht.le hab
  have hF : F v ≤ (1 - t) * F s.x + t * F u := by
    change data.f v ≤ (1 - t) • data.f s.x + t • data.f u at hf
    change ψ.f v ≤ (1 - t) • ψ.f s.x + t • ψ.f u at hψ
    simp only [smul_eq_mul] at hf hψ
    dsimp only [F, objective]
    nlinarith only [hf, hψ]
  have hthree := step_three_point data ψ y v hv
  change F q.x - F v ≤ (‖y - v‖^2 - ‖q.x - v‖^2) / 2 at hthree
  have hyv : y - v = t • (s.z - u) := by
    dsimp only [y, v]
    rw [smul_sub]
    abel
  have hxv : q.x - v = t • (q.z - u) := by
    have hqz : q.z = s.z + t⁻¹ • (q.x - y) := rfl
    rw [hqz, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    dsimp only [y, v]
    abel
  rw [hyv, hxv, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.le, mul_pow, mul_pow] at hthree
  have hstep : F q.x - F u ≤ (1 - t) * (F s.x - F u)
      + t^2 * ((‖s.z - u‖^2 - ‖q.z - u‖^2) / 2) := by
    nlinarith only [hthree, hF]
  let a := accelInv n
  have hap : 0 < a := accelInv_pos n
  have haθ : a^2 * t^2 = 1 := by
    change a^2 * (a⁻¹)^2 = 1
    field_simp [hap.ne']
  have ha1 : a^2 * (1 - t) = a^2 - a := by
    change a^2 * (1 - a⁻¹) = a^2 - a
    field_simp [hap.ne']
  have hm := mul_le_mul_of_nonneg_left hstep (sq_nonneg a)
  have hrhs : a^2 * ((1 - t) * (F s.x - F u)
      + t^2 * ((‖s.z - u‖^2 - ‖q.z - u‖^2) / 2))
      = (a^2 - a) * (F s.x - F u) + (‖s.z - u‖^2 - ‖q.z - u‖^2) / 2 := by
    calc
      _ = (a^2 * (1 - t)) * (F s.x - F u)
          + (a^2 * t^2) * ((‖s.z - u‖^2 - ‖q.z - u‖^2) / 2) := by ring
      _ = _ := by rw [ha1, haθ, one_mul]
  change a^2 * (F q.x - F u) ≤ _ at hm
  rw [hrhs] at hm
  change a^2 * (F q.x - F u) + ‖q.z - u‖^2 / 2
    ≤ (a^2 - a) * (F s.x - F u) + ‖s.z - u‖^2 / 2
  linarith only [hm]

theorem fista_potential (data : Smooth E) (ψ : ProperConvex E) (x0 u : E)
    (hx0 : x0 ∈ ψ.dom) (hu : u ∈ ψ.dom) (n : ℕ) :
    let s := fistaState data ψ x0
    (accelInv n)^2 * (objective data ψ (s (n + 1)).x - objective data ψ u)
      + ‖(s (n + 1)).z - u‖^2 / 2 ≤ ‖x0 - u‖^2 / 2 := by
  let s := fistaState data ψ x0
  change (accelInv n)^2 * (objective data ψ (s (n + 1)).x - objective data ψ u)
      + ‖(s (n + 1)).z - u‖^2 / 2 ≤ ‖x0 - u‖^2 / 2
  induction n with
  | zero =>
    have H := fista_scaled_step data ψ 0 (s 0) hx0 u hu
    change (accelInv 0)^2 * (objective data ψ (s 1).x - objective data ψ u)
        + ‖(s 1).z - u‖^2 / 2 ≤ ((accelInv 0)^2 - accelInv 0) *
          (objective data ψ x0 - objective data ψ u) + ‖x0 - u‖^2 / 2 at H
    norm_num [accelInv] at H ⊢
    exact H
  | succ n ih =>
    have H := fista_scaled_step data ψ (n + 1) (s (n + 1)) (fista_x_dom data ψ x0 hx0 (n + 1)) u hu
    change (accelInv (n + 1))^2 * (objective data ψ (s (n + 2)).x - objective data ψ u)
      + ‖(s (n + 2)).z - u‖^2 / 2 ≤
        ((accelInv (n + 1))^2 - accelInv (n + 1)) *
          (objective data ψ (s (n + 1)).x - objective data ψ u) + ‖(s (n + 1)).z - u‖^2 / 2 at H
    rw [accelInv_identity] at H
    exact H.trans ih

def fista (data : Smooth E) (ψ : ProperConvex E) (x0 : E) (K : ℕ) : E :=
  (fistaState data ψ x0 K).x

theorem fista_first_step (data : Smooth E) (ψ : ProperConvex E) (x0 : E) :
    fista data ψ x0 1 = step data ψ x0 := by
  simp [fista, fistaState, fistaNext]

theorem fista_bound (data : Smooth E) (ψ : ProperConvex E) (x0 u : E)
    (hx0 : x0 ∈ ψ.dom) (hu : u ∈ ψ.dom) (n : ℕ) :
    objective data ψ (fista data ψ x0 (n + 1)) - objective data ψ u
      ≤ (theta n)^2 * ‖x0 - u‖^2 / 2 := by
  have H := fista_potential data ψ x0 u hx0 hu n
  let a := accelInv n
  have ha : 0 < a := accelInv_pos n
  have hr : 0 ≤ ‖(fistaState data ψ x0 (n + 1)).z - u‖^2 / 2 := by positivity
  have hle : a^2 * (objective data ψ (fista data ψ x0 (n + 1)) - objective data ψ u)
      ≤ ‖x0 - u‖^2 / 2 := (le_add_of_nonneg_right hr).trans H
  calc
    _ ≤ (‖x0 - u‖^2 / 2) / a^2 :=
      (le_div_iff₀ (pow_pos ha 2)).2 (by simpa only [mul_comm] using hle)
    _ = _ := by change _ = (a⁻¹)^2 * ‖x0 - u‖^2 / 2; field_simp [ha.ne']

theorem theta_original (n : ℕ) :
    theta (n + 1) = (Real.sqrt ((theta n)^4 + 4 * (theta n)^2) - (theta n)^2) / 2 := by
  let t := theta n
  let u := theta (n + 1)
  let v := (Real.sqrt (t^4 + 4 * t^2) - t^2) / 2
  have ht : 0 < t := theta_pos n
  have hu : 0 < u := theta_pos (n + 1)
  have hm : (1 - u) * t^2 = 1 * u^2 :=
    (div_eq_div_iff (pow_ne_zero 2 hu.ne') (pow_ne_zero 2 ht.ne')).1
      (theta_potential_identity n)
  have hp : u^2 + t^2 * u - t^2 = 0 := by nlinarith only [hm]
  have hr := Real.sq_sqrt (show 0 ≤ t^4 + 4 * t^2 by positivity)
  have hpv : v^2 + t^2 * v - t^2 = 0 := by
    dsimp only [v]
    nlinarith only [hr]
  have hlt : t^2 < Real.sqrt (t^4 + 4 * t^2) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith only [pow_pos ht 2])
  have hv : 0 < v := div_pos (sub_pos.mpr hlt) (by norm_num)
  have hfactor : (u - v) * (u + v + t^2) = 0 := by
    calc
      _ = (u^2 + t^2 * u - t^2) - (v^2 + t^2 * v - t^2) := by ring
      _ = 0 := by rw [hp, hpv, sub_self]
  have hnon : u + v + t^2 ≠ 0 := ne_of_gt (by positivity)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hnon)

end
end AdaRES
