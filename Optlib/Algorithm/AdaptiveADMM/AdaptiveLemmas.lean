import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Optlib.Algorithm.AdaptiveADMM.AdaptiveScheme
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Optlib.Convex.FiniteDimensionalConvexFunctionsLocallyLipschitz
import Optlib.Convex.Subgradient
import Mathlib.Data.Real.Basic


noncomputable section
open Set InnerProductSpace Topology Filter InnerProduct
open scoped Pointwise

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F ]

variable (admm : ADMM E₁ E₂ F)

structure Existance_of_kkt where
  x₁ : E₁
  x₂ : E₂
  y : F
  h : Convex_KKT x₁ x₂ y admm.toOptProblem

variable (admm_kkt : Existance_of_kkt admm)

namespace AdaptiveADMM_Convergence_Proof

variable {admm admm_kkt}

class Setting (E₁ E₂ F : outParam Type*)
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F ]
    (admm : outParam (ADMM E₁ E₂ F))
    (admm_kkt : outParam (Existance_of_kkt admm)) where

-- shorthand
local notation "f₁" => admm.f₁
local notation "f₂" => admm.f₂
local notation "A₁" => admm.A₁
local notation "A₂" => admm.A₂
local notation "x₁" => admm.x₁
local notation "x₂" => admm.x₂
local notation "b" => admm.b
local notation "y"  => admm.y
local notation "τ"  => admm.τ
local notation "ρₙ" => admm.ρₙ
local notation "ρmin" => admm.ρmin

local notation "x₁'" => admm_kkt.x₁
local notation "x₂'" => admm_kkt.x₂
local notation "y'"  => admm_kkt.y

local notation "A₁†" => ContinuousLinearMap.adjoint A₁
local notation "A₂†" => ContinuousLinearMap.adjoint A₂
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

--辅助变量
def T_HWY [Setting E₁ E₂ F admm admm_kkt]  := 2 - (1/2) * (1 + τ - τ^2)

def e₁ [Setting E₁ E₂ F admm admm_kkt] : ℕ → E₁ := fun n => (x₁ n) - x₁'

def e₂ [Setting E₁ E₂ F admm admm_kkt]: ℕ → E₂ := fun n => (x₂ n) - x₂'

def ey [Setting E₁ E₂ F admm admm_kkt]: ℕ → F :=  fun n => (y  n) - y'

def g1 [Setting E₁ E₂ F admm admm_kkt] : ℕ → ℝ := fun n => (‖ey n‖^2 + τ * ρₙ n^2  * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2)

def g2 [Setting E₁ E₂ F admm admm_kkt] : ℕ → ℝ := fun n => 1 / ρₙ n^2 * ‖ey n‖^2 + τ * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2

def u [Setting E₁ E₂ F admm admm_kkt]: ℕ+ → E₁ :=
  fun n => -A₁† (y n + ((1 - τ) * (ρₙ n)) • (A₁ (e₁ n) + A₂ (e₂ n))
               + (ρₙ n) • (A₂ (x₂ (n - 1) - x₂ n)))

def v [Setting E₁ E₂ F admm admm_kkt]: ℕ → E₂ :=
  fun n => -A₂† (y n + ((1 - τ) * (ρₙ n)) • (A₁ (e₁ n) + A₂ (e₂ n)))

def Ψ [Setting E₁ E₂ F admm admm_kkt]: ℕ → ℝ :=
  fun n => 1 / (τ * (ρₙ n)) * ‖ey n‖^2 + (ρₙ n) * ‖A₂ (e₂ n)‖^2

def Φ [Setting E₁ E₂ F admm admm_kkt]: ℕ → ℝ :=
  fun n => Ψ n + ((max (1 - τ) (1 - 1/τ)) * (ρₙ n)) * ‖A₁ (e₁ n) + A₂ (e₂ n)‖^2

def υ [Setting E₁ E₂ F admm admm_kkt]: ℕ → F :=
  fun n => (y n) + ((1 - τ) * (ρₙ n)) • (A₁ (x₁ n) + A₂ (x₂ n) - admm.b)

def M [Setting E₁ E₂ F admm admm_kkt]: ℕ+ → ℝ :=
  fun n => ((1 - τ) * (ρₙ (n-1)))* ⟪(A₂ ((x₂ n) - (x₂ (n-1)))),(A₁ (x₁ (n-1)) + A₂ (x₂ (n-1)) - admm.b)⟫

def Φ_HWY [Setting E₁ E₂ F admm admm_kkt]: ℕ → ℝ :=
  fun n => ‖ey n‖^2 + τ * ρₙ n^2 * ‖A₂ (e₂ n)‖^2
  + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2

-- #check

lemma f₁_continuous : ContinuousOn f₁ univ :=
   FiniteDimensionalConvexFunctionsContinous convex_univ isOpen_univ OptProblem.cf₁

lemma f₂_continuous : ContinuousOn f₂ univ :=
   FiniteDimensionalConvexFunctionsContinous convex_univ isOpen_univ OptProblem.cf₂

lemma inner_convex1 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ConvexOn ℝ univ (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) := by
   dsimp [ConvexOn]
   intro n
   constructor
   · apply convex_univ
   intro xx _ yy _ aa bb _ _ abh
   have :=
      calc
         (A₁ (aa • xx + bb • yy)) + (A₂ (x₂ n.natPred)) - b
         = aa • A₁ (xx) + bb • A₁ (yy) + (A₂ (x₂ n.natPred)) - b := by continuity
         _= aa • A₁ (xx) + bb • A₁ (yy) + (aa + bb) • (A₂ (x₂ n.natPred) - b) := by
            rw [abh]
            rw [one_smul]
            rw [add_sub]
         _= aa • A₁ (xx) + bb • A₁ (yy) + aa • (A₂ (x₂ n.natPred) - b) + bb • (A₂ (x₂ n.natPred) - b) := by
            rw [add_smul]
            rw [add_assoc (aa • A₁ (xx) + bb • A₁ (yy))]
         _= aa • (A₁ (xx) + (A₂ (x₂ n.natPred) - b)) + bb • (A₁ (yy) + (A₂ (x₂ n.natPred) - b)) := by
            repeat rw [smul_add]
            rw [← add_assoc, add_assoc (aa • A₁ (xx)), add_comm (bb • A₁ (yy)), ← add_assoc]
   calc
      _= ⟪y n.natPred , aa • (A₁ (xx) + (A₂ (x₂ n.natPred) - b))
          + bb • (A₁ (yy) + (A₂ (x₂ n.natPred) - b))⟫ := by rw [this]
      _= ⟪y n.natPred , aa • (A₁ (xx) + (A₂ (x₂ n.natPred) - b))⟫
          + ⟪y n.natPred , bb • (A₁ (yy) + (A₂ (x₂ n.natPred) - b))⟫ := by rw [inner_add_right]
      _= aa * ⟪y n.natPred , (A₁ (xx) + (A₂ (x₂ n.natPred) - b))⟫
          + bb * ⟪y n.natPred , (A₁ (yy) + (A₂ (x₂ n.natPred) - b))⟫ := by
         rw [inner_smul_right]; rw [inner_smul_right]
      _= aa * ⟪y n.natPred , A₁ (xx) + A₂ (x₂ n.natPred) - b⟫ + bb * ⟪y n.natPred , A₁ (yy) + A₂ (x₂ n.natPred) - b⟫ := by
         rw [add_sub, add_sub]
   rfl

lemma inner_convex2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ConvexOn ℝ univ (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) := by
   intro n
   let c := y n.natPred
   let a := (A₁ (x₁ n)) - b
   have : (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) =
         (fun x => ⟪y n.natPred , (A₂ x) + ((A₁ (x₁ n)) - b)⟫) := by
      ext x;rw[add_comm,← add_sub]
   rw[this]
   show ConvexOn ℝ univ (fun x => ⟪c , (A₂ x) + a⟫)
   have h : (fun x => ⟪c , (A₂ x) + a⟫) = (fun x => ⟪c , (A₂ x)⟫ + ⟪c , a⟫):= by
      ext x
      rw[← inner_add_right]
   let p := ⟪c , a⟫
   rw[h]
   show ConvexOn ℝ univ (fun x => ⟪c , (A₂ x)⟫ + p)
   apply ConvexOn.add _
   apply convexOn_const
   apply convex_univ
   let f : E₂ →ₗ[ℝ] ℝ :={
      toFun := (fun x => ⟪c , A₂ x⟫)
      map_add' := by
         intro u v
         simp only [map_add]
         rw[inner_add_right]
      map_smul' := by
         intro u v
         simp only [LinearMapClass.map_smul, RingHom.id_apply, smul_eq_mul]
         apply inner_smul_right
   }
   show ConvexOn ℝ univ f
   apply LinearMap.convexOn
   apply convex_univ

-- ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2
lemma norm_covex1 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ConvexOn ℝ univ (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) := by
   intro n
   let c := - ((A₂ (x₂ n.natPred)) - b)
   have h : (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) =
         (fun x => ρₙ n  * ‖(A₁ x) - c‖ ^ 2 / 2) := by
      ext x
      simp only [c]
      rw[sub_neg_eq_add, add_sub]
      ring
   rw[h]
   let f := (fun x => ‖(A₁ x) - c‖ ^ 2 / 2)
   show ConvexOn ℝ univ (fun x => ρₙ n • ‖(A₁ x) - c‖ ^ 2 / 2)
   have h1 : (fun x => ρₙ n • ‖(A₁ x) - c‖ ^ 2 / 2) =
         (fun x => ρₙ n • f x) := by
      ext x
      simp only [f,smul_eq_mul]
      ring_nf
   rw[h1]
   apply ConvexOn.smul (le_of_lt (admm.hρₙ_pos n))
   let u := fun x => ‖x - c‖ ^ 2 / 2
   let g := A₁
   have h2 : u ∘ g = f := by
      ext x
      simp only [Function.comp_apply]
      exact rfl
   rw[← h2]
   have h3 : ⇑g ⁻¹' univ = univ := by
      simp only [preimage_univ]
   rw[← h3]
   have h4 : Convex ℝ (univ (α := F)) := by
      apply convex_univ
   apply ConvexOn.comp_linearMap (convex_of_norm_sq c h4)

lemma norm_covex2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ConvexOn ℝ univ (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) := by
   intro n
   let c := - ((A₁ (x₁ n)) - b)
   have h : (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) =
         (fun x => ρₙ n  * ‖(A₂ x) - c‖ ^ 2 / 2) := by
      ext x
      rw[add_comm]
      simp only [c]
      rw[sub_neg_eq_add, add_sub]
      ring
   rw[h]
   let f := (fun x => ‖(A₂ x) - c‖ ^ 2 / 2)
   show ConvexOn ℝ univ (fun x => ρₙ n • ‖(A₂ x) - c‖ ^ 2 / 2)
   have h1 : (fun x => ρₙ n • ‖(A₂ x) - c‖ ^ 2 / 2) =
         (fun x => ρₙ n • f x) := by
      ext x
      simp only [f,smul_eq_mul]
      ring_nf
   rw[h1]
   apply ConvexOn.smul (le_of_lt (admm.hρₙ_pos n))
   let u := fun x => ‖x - c‖ ^ 2 / 2
   let g := A₂
   have h2 : u ∘ g = f := by
      ext x
      simp only [Function.comp_apply]
      exact rfl
   rw[← h2]
   have h3 : ⇑g ⁻¹' univ = univ := by
      simp only [preimage_univ]
   rw[← h3]
   have h4 : Convex ℝ (univ (α := F)) := by
      apply convex_univ
   apply ConvexOn.comp_linearMap (convex_of_norm_sq c h4)

lemma ADMM_iter_process₁'_eq3_1' [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+ ,
      HasGradientAt (fun _ => f₂ (x₂ n.natPred)) 0 (x₁ n) := by
   intro n
   apply hasGradientAt_const
lemma ADMM_iter_process₁'_eq3_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun _ => f₂ (x₂ n.natPred)) (x₁ n) = 0 := by
   intro n
   apply SubderivAt_eq_gradient (convexOn_const (f₂ (x₂ n.natPred)) (convex_univ))
   apply ADMM_iter_process₁'_eq3_1'

lemma inner_gradient { α β : Type*}
      [NormedAddCommGroup α]  [NormedAddCommGroup β]
      [InnerProductSpace ℝ α] [InnerProductSpace ℝ β]
      [CompleteSpace α]  [CompleteSpace β] (A : α →L[ℝ] β)(c : β) :∀ x,
      HasGradientAt ((fun x => ⟪c , A x⟫)) ((A†) c) x := by
   intro x
   rw[HasGradient_iff_Convergence_Point]
   intro ε εpos
   use ε,εpos
   intro x1 _
   rw[← inner_sub_right,ContinuousLinearMap.adjoint_inner_left,← inner_sub_right]
   simp only [map_sub, sub_self, inner_zero_right, norm_zero]
   have := norm_nonneg (x - x1)
   rwa[mul_nonneg_iff_right_nonneg_of_pos εpos]

#check HasGradient_iff_Convergence_Point
lemma ADMM_iter_process₁'_eq3_2'_1 [Setting E₁ E₂ F admm admm_kkt](c : F) :∀ x,
      HasGradientAt ((fun x => ⟪c , (A₁ x)⟫)) (A₁† c) x := by
   apply inner_gradient

#check HasDerivAt.hasGradientAt'
lemma ADMM_iter_process₁'_eq3_2' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , ∀ x ,
      HasGradientAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (A₁† (y n.natPred)) x := by
   intro n x
   let c := y n.natPred
   let c₁ := ⟪y n.natPred ,(A₂ (x₂ n.natPred)) - b⟫
   have :(fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫)
   = (fun x => ⟪y n.natPred , (A₁ x)⟫) + (fun _ => ⟪y n.natPred ,(A₂ (x₂ n.natPred)) - b⟫) := by
      ext x
      simp only [Pi.add_apply]
      rw[← add_sub (A₁ x) (A₂ (x₂ n.natPred)) b]
      exact inner_add_right (ADMM.y E₁ E₂ n.natPred) ((OptProblem.A₁ E₂) x)
            ((OptProblem.A₂ E₁) (ADMM.x₂ E₁ F n.natPred) - OptProblem.b E₁ E₂)
   rw[this]
   show HasGradientAt ((fun x => ⟪c , (A₁ x)⟫ + c₁)) (A₁† c) x
   rw[hasGradientAt_iff_hasFDerivAt]
   refine HasFDerivAt.add_const c₁ ?_
   show HasGradientAt ((fun x => ⟪c , (A₁ x)⟫)) (A₁† c) x
   apply ADMM_iter_process₁'_eq3_2'_1

lemma inner_continuous1 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ContinuousOn (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) univ:= by
   intro n
   have :∀ x ∈ univ,HasGradientAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (A₁† (y n.natPred)) x := by
      intro x _
      apply ADMM_iter_process₁'_eq3_2' n
   apply HasGradientAt.continuousOn
   exact this

lemma ADMM_iter_process₁'_eq3_2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (x₁ n) = { A₁† (y n.natPred)} := by
   intro n
   apply SubderivAt_eq_gradient (inner_convex1 n)
   apply ADMM_iter_process₁'_eq3_2'

lemma norm_comm {α β: Type*}
      [NormedAddCommGroup α] [InnerProductSpace ℝ α]
      [NormedAddCommGroup β] [InnerProductSpace ℝ β]
      (A : α →L[ℝ] β) (a₁ a₂ : α): ‖A (a₁ - a₂)‖ =‖A (a₂ - a₁)‖ := by
   rw [map_sub, map_sub , ←neg_sub (A a₂) (A a₁)]; apply norm_neg

#check norm_eq_zero
#check le_iff_eq_or_lt.1 $ norm_nonneg (1 : ℝ)
/-Derivatives of quadratic forms-/
lemma Gradient_of_quadratic_forms { α β : Type*}
      [NormedAddCommGroup α]  [NormedAddCommGroup β]
      [InnerProductSpace ℝ α] [InnerProductSpace ℝ β]
      [CompleteSpace α]  [CompleteSpace β] (A : α →L[ℝ] β):
      ∀ s , HasGradientAt ((fun x => ⟪ A x , A x⟫)) ((2 : ℝ ) • (A†) (A s)) s:= by
   intro s
   rw[HasGradient_iff_Convergence_Point]
   intro ε εpos
   rcases (le_iff_eq_or_lt.1 $ norm_nonneg A) with h | h
   ·  use ε
      constructor
      · exact εpos
      · intro x hx
        symm at h
        rw[norm_eq_zero] at h
        simp[h]
        have := norm_nonneg (s - x)
        rwa[mul_nonneg_iff_right_nonneg_of_pos εpos]
   ·  use ε / ‖A‖ ^ 2
      constructor
      ·
        have hzero : 0 < ‖A‖ ^ 2 := by apply sq_pos_of_pos h
        exact div_pos εpos hzero
      · intro x hx
        have hzero : 0 < ‖A‖ ^ 2 := by apply sq_pos_of_pos h
        let t := x - s
        have t1 : s + t = x := by
           show s + (x - s) = x
           simp only [add_sub_cancel]
        have : ⟪A x, A x⟫ - ⟪A s, A s⟫ - ⟪(2 : ℝ) • (A†) (A s), x - s⟫ =
              ⟪A (x - s) , A (x - s)⟫ := by
           rw[← t1]
           simp only [map_add, add_sub_cancel_left]
           show ⟪A s + A t , A s + A t⟫ - ⟪A s, A s⟫ - ⟪(2 : ℝ) • (A†) (A s), t⟫ =
              ⟪A t , A t⟫
           rw[real_inner_add_add_self]
           rw[real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
           ring
        rw[this,real_inner_self_eq_norm_sq]
        simp only [ge_iff_le]
        calc
           _ = ‖A (s - x)‖ ^ 2 := by
              rw[norm_comm]; simp
           _ ≤ (‖A‖ * ‖s - x‖) ^ 2:= by
              rw[sq,sq,← mul_self_le_mul_self_iff]
              apply ContinuousLinearMap.le_opNorm
              apply norm_nonneg
              simp[h , norm_nonneg (s - x)]
           _ = ‖A‖ ^ 2 * ‖s - x‖ ^ 2 := by
              linarith
        rcases (le_iff_eq_or_lt.1 $ norm_nonneg (s - x)) with h1 | _
        ·  rw[← h1]
           simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, le_refl]
        ·  calc
              _ = ‖A‖ ^ 2 * ‖s - x‖ * ‖s - x‖:= by
                 nth_rw 2 [sq];
                 rw[mul_assoc]
              _ ≤ ‖A‖ ^ 2 * ‖s - x‖ * (ε / ‖A‖ ^ 2) :=by
                 have :0 ≤ ‖A‖ ^ 2 * ‖s - x‖ := by
                    simp[hzero,norm_nonneg (s - x)]
                 apply mul_le_mul_of_nonneg_left hx this
              _ = _ := by
                 field_simp[hzero]

#check add_sub
lemma ADMM_iter_process₁'_eq3_3' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      HasGradientAt (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2)
      (ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))) (x₁ n) := by
   intro n
   let c := (A₂ (x₂ n.natPred)) - b
   have h1: (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) =
         (fun x => ρₙ n / 2 * ‖(A₁ x) + ((A₂ (x₂ n.natPred)) - b)‖ ^ 2) := by
      ext x
      rw[← add_sub]
   rw[← add_sub (A₁ (x₁ n))  (A₂ (x₂ n.natPred))  b ,h1]
   show HasGradientAt (fun x => ρₙ n / 2 * ‖(A₁ x) + c‖ ^ 2) (ρₙ n • (A₁† (A₁ (x₁ n) + c))) (x₁ n)
   have h2 : (fun x => ρₙ n / 2 * ‖(A₁ x) + c‖ ^ 2) =
         (fun x => ρₙ n / 2 * (⟪(A₁ x) , (A₁ x)⟫ + 2 * ⟪c , A₁ x⟫ + ⟪c , c⟫)):= by
      ext x
      rw[← real_inner_self_eq_norm_sq ((A₁ x) + c)]
      rw[ real_inner_add_add_self]
      rw[real_inner_comm c (A₁ x)]
   rw[h2]
   have h3 : ρₙ n • (A₁† (A₁ (x₁ n) + c)) = (ρₙ n / 2) • ((2 : ℝ ) • A₁† (A₁ (x₁ n) + c)) := by
      rw [smul_smul]; simp only [map_add, smul_add, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
         not_false_eq_true, IsUnit.div_mul_cancel]
   rw[h3]
   apply HasGradientAt.const_mul' (ρₙ n / 2)
   apply HasGradientAt.add_const
   have h4 : (2 : ℝ ) • A₁† (A₁ (x₁ n) + c) = (2 : ℝ ) • A₁† (A₁ (x₁ n)) + (2 : ℝ ) • A₁† c := by
      calc
         _ = (2 : ℝ ) • (A₁† (A₁ (x₁ n))  + A₁† c) := by
            simp only [map_add, smul_add]
         _ = _ := by
            simp only [smul_add]
   rw[h4]
   apply HasGradientAt.add
   ·  apply Gradient_of_quadratic_forms
   ·  let a := (fun x => ⟪c, A₁ x⟫)
      show HasGradientAt (fun x ↦ 2 * a x) ((2 : ℝ)• (A₁† c)) (x₁ n)
      apply HasGradientAt.const_mul' 2
      apply inner_gradient

-- ⟪a+b,a+b⟫=⟪a,a⟫+2*⟪a,b⟫+⟪b,b⟫

lemma ADMM_iter_process₁'_eq3_3
      [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) (x₁ n) = {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))} := by
   intro n
   apply SubderivAt_eq_gradient (norm_covex1 n)
   apply ADMM_iter_process₁'_eq3_3'

lemma ADMM_iter_process₁'_eq2_1' --xkn迷迷糊糊阅
       [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (fun x => (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x , x₂ n.natPred , y n.natPred)) =
      (fun x => (f₁ x) + (f₂ (x₂ n.natPred))+ ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫ + ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) := by
   intro n
   rfl


lemma ADMM_iter_process₁'_eq2_1'_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (fun x => (f₁ x) + (f₂ (x₂ n.natPred))+ ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫ + ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2)
      = f₁ + (fun _ => f₂ (x₂ n.natPred)) + (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) + (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2)
      := by
   intro n
   congr


#check SubderivAt.add
#check continuousOn_const
#check convexOn_const
#check convex_univ
#check ConvexOn.add
#check ContinuousOn.add
--(@continuousOn_const E₁ ℝ _ _ univ (f₂ (x₂ n.natPred)) )

lemma ADMM_iter_process₁'_eq2_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x , x₂ n.natPred , y n.natPred)) (x₁ n) =
      SubderivAt f₁ (x₁ n) + SubderivAt (fun _ => f₂ (x₂ n.natPred)) (x₁ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (x₁ n) +
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) (x₁ n) := by
   intro n
   rw[ADMM_iter_process₁'_eq2_1' n , ADMM_iter_process₁'_eq2_1'_1 n]
   rw[SubderivAt.add admm.cf₁ (convexOn_const (f₂ (x₂ n.natPred)) (convex_univ))
   f₁_continuous (x₁ n)]
   rw[SubderivAt.add (ConvexOn.add admm.cf₁ (convexOn_const (f₂ (x₂ n.natPred)) (convex_univ)))
   (inner_convex1 n) (ContinuousOn.add f₁_continuous (@continuousOn_const E₁ ℝ _ _ univ (f₂ (x₂ n.natPred)))) (x₁ n)]
   rw[SubderivAt.add (ConvexOn.add (ConvexOn.add admm.cf₁ (convexOn_const (f₂ (x₂ n.natPred)) (convex_univ))) (inner_convex1 n))
   (norm_covex1 n) (ContinuousOn.add (ContinuousOn.add f₁_continuous (@continuousOn_const E₁ ℝ _ _ univ (f₂ (x₂ n.natPred)))) (inner_continuous1 n)) (x₁ n)]

lemma ADMM_iter_process₁'_eq2_2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + SubderivAt (fun _ => f₂ (x₂ n.natPred)) (x₁ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (x₁ n) +
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) (x₁ n) =
      SubderivAt f₁ (x₁ n) + 0 + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}:= by
   intro n
   rw[ADMM_iter_process₁'_eq3_1 n,ADMM_iter_process₁'_eq3_2 n,ADMM_iter_process₁'_eq3_3 n]

lemma ADMM_iter_process₁'_eq2_3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + 0 + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}
      = SubderivAt f₁ (x₁ n) + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}:= by
   intro n
   rw[add_zero]

lemma ADMM_iter_process₁'_eq1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}
      = SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x , x₂ n.natPred , y n.natPred)) (x₁ n):=by
   intro n
   rw[← ADMM_iter_process₁'_eq2_3 n,← ADMM_iter_process₁'_eq2_2 n,← ADMM_iter_process₁'_eq2_1 n]

#check first_order_convex_iff_subgradient
lemma ADMM_iter_process₁' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,0 ∈
      SubderivAt f₁ (x₁ n) + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}:= by
   intro n
   have := first_order_convex_iff_subgradient (f := (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x , x₂ n.natPred , y n.natPred)) ) (x₁ n)
   have h := admm.itex₁ n.natPred
   have eq : n.natPred + 1 = n := by apply PNat.natPred_add_one
   rw[eq , this , ← ADMM_iter_process₁'_eq1 n] at h
   exact h

lemma set_add_assoc {E : Type*}[NormedAddCommGroup E]
(p q r : Set E): p + q + r = p + (q + r) := by
   rw[superset_antisymm_iff]
   constructor
   ·  intro x hx
      rw[Set.mem_add] at hx
      rcases hx with ⟨px,hpx,⟨py,hpy,h1⟩⟩
      rw[Set.mem_add] at hpy
      rcases hpy with ⟨qy,hqy,⟨rz,hrz,h2⟩⟩
      rw[Set.mem_add]
      use px + qy , Set.add_mem_add hpx hqy
      use rz,hrz
      rw[← h1,← h2]
      exact add_assoc px qy rz
   ·  intro x hx
      rw[Set.mem_add] at hx
      rcases hx with ⟨px,hpx,⟨py,hpy,h1⟩⟩
      rw[Set.mem_add] at hpx
      rcases hpx with ⟨qy,hqy,⟨rz,hrz,h2⟩⟩
      rw[Set.mem_add]
      use qy,hqy
      use rz + py , Set.add_mem_add hrz hpy
      rw[← h1,← h2]
      exact Eq.symm (add_assoc qy rz py)

lemma zero_in_add {E : Type*}[NormedAddCommGroup E]{a : E}{s : Set E}
   (h : 0 ∈ s + {a}) : -a ∈ s:= by
   simp only [add_singleton, image_add_right, mem_preimage, zero_add] at h
   exact h;

lemma change_item {α : Type*}[NormedAddCommGroup α]{S : Set α}{p q : α}(h : 0 ∈ S + {p} + {q}):
      - p - q ∈ S := by
   rw[set_add_assoc S {p} {q},Set.singleton_add_singleton] at h
   apply zero_in_add at h
   rwa[← neg_add' p q]


lemma ADMM_iter_process₁ [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      ( - A₁† (y (n - 1)) - ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ (n - 1)) - b))) ∈ SubderivAt f₁ (x₁ n) := by
   intro n
   let S := SubderivAt f₁ (x₁ n)
   let p := A₁† (y (n - 1))
   let q := ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ (n - 1)) - b))
   show - p - q ∈ S
   have := ADMM_iter_process₁' n
   change 0 ∈ S + {p} + {q} at this
   apply change_item this

lemma ADMM_iter_process₂'_eq3_1' [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+ ,
      HasGradientAt (fun _ => f₁ (x₁ n)) 0 (x₂ n) := by
   intro n
   apply hasGradientAt_const

lemma ADMM_iter_process₂'_eq3_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun _ => f₁ (x₁ n)) (x₂ n) = 0 := by
   intro n
   apply SubderivAt_eq_gradient (convexOn_const (f₁ (x₁ n)) (convex_univ))
   apply ADMM_iter_process₂'_eq3_1'

#check ADMM_iter_process₁'_eq3_2'
lemma ADMM_iter_process₂'_eq3_2' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , ∀ x ,
      HasGradientAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (A₂† (y n.natPred)) x := by
   intro n x
   let c := y n.natPred
   let c₁ := ⟪c ,(A₁ (x₁ n)) - b⟫
   have :(fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫)
   = (fun x => ⟪y n.natPred , (A₂ x)⟫) + (fun _ => ⟪y n.natPred ,(A₁ (x₁ n)) - b⟫) := by
      ext x
      simp only [Pi.add_apply]
      rw[add_comm]
      rw[← add_sub (A₂ x) (A₁ (x₁ n))  b]
      exact inner_add_right (y n.natPred) (A₂ x) (A₁ (x₁ n) - b)
   rw[this]
   show HasGradientAt (fun x => ⟪c , (A₂ x)⟫ + c₁) (A₂† c) x
   rw[hasGradientAt_iff_hasFDerivAt]
   apply HasFDerivAt.add_const c₁ _
   show HasGradientAt ((fun x => ⟪c , (A₂ x)⟫)) (A₂† c) x
   apply inner_gradient

lemma inner_continuous2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ContinuousOn (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) univ:= by
   intro n
   have :∀ x ∈ univ,HasGradientAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (A₂† (y n.natPred)) x := by
      intro x _
      apply ADMM_iter_process₂'_eq3_2' n
   apply HasGradientAt.continuousOn
   exact this

lemma ADMM_iter_process₂'_eq3_2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (x₂ n) = { A₂† (y n.natPred)} := by
   intro n
   apply SubderivAt_eq_gradient (inner_convex2 n)
   apply ADMM_iter_process₂'_eq3_2'

#check ADMM_iter_process₁'_eq3_3'
lemma ADMM_iter_process₂'_eq3_3' --xkn阅
   [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      HasGradientAt (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2)
      (ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))) (x₂ n) := by
   intro n
   let c := (A₁ (x₁ n)) - b
   have h1: (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) =
         (fun x => ρₙ n / 2 * ‖(A₂ x) + ((A₁ (x₁ n)) - b)‖ ^ 2) := by
      ext x
      rw[add_comm,← add_sub]
   rw[h1]
   have h1' : (ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))) =
         (ρₙ n • (A₂† (A₂ (x₂ n) + (A₁ (x₁ n) - b)))):= by
      rw[add_comm,← add_sub]
   rw[h1']
   show HasGradientAt (fun x => ρₙ n / 2 * ‖(A₂ x) + c‖ ^ 2) (ρₙ n • (A₂† (A₂ (x₂ n) + c))) (x₂ n)
   have h2 : (fun x => ρₙ n / 2 * ‖(A₂ x) + c‖ ^ 2) =
         (fun x => ρₙ n / 2 * (⟪(A₂ x) , (A₂ x)⟫ + 2 * ⟪c , A₂ x⟫ + ⟪c , c⟫)):= by
      ext x
      rw[← real_inner_self_eq_norm_sq ((A₂ x) + c)]
      rw[ real_inner_add_add_self]
      rw[real_inner_comm c (A₂ x)]
   rw[h2]
   have h3 : ρₙ n • (A₂† (A₂ (x₂ n) + c)) = (ρₙ n / 2) • ((2 : ℝ ) • A₂† (A₂ (x₂ n) + c)) := by
      rw [smul_smul]; simp only [map_add, smul_add, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
         not_false_eq_true, IsUnit.div_mul_cancel]
   rw[h3]
   apply HasGradientAt.const_mul (ρₙ n / 2)
   apply HasGradientAt.add_const
   have h4 : (2 : ℝ ) • A₂† (A₂ (x₂ n) + c) = (2 : ℝ ) • A₂† (A₂ (x₂ n)) + (2 : ℝ ) • A₂† c := by
      calc
         _ = (2 : ℝ ) • (A₂† (A₂ (x₂ n))  + A₂† c) := by
            simp only [map_add, smul_add]
         _ = _ := by
            simp only [smul_add]
   rw[h4]
   apply HasGradientAt.add
   ·  apply Gradient_of_quadratic_forms
   ·  apply HasGradientAt.const_mul 2
      apply inner_gradient

lemma ADMM_iter_process₂'_eq3_3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) (x₂ n) = {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))} := by
   intro n
   apply SubderivAt_eq_gradient (norm_covex2 n)
   apply ADMM_iter_process₂'_eq3_3'

lemma ADMM_iter_process₂'_eq2_1' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x₁ n , x , y n.natPred)) =
      (fun x => f₁ (x₁ n) + (f₂ x) + ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫ + ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) := by
   intro n
   rfl

lemma ADMM_iter_process₂'_eq2_1'_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      (fun x => f₁ (x₁ n) + (f₂ x)+ ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫ + ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2)
      = (fun _ => f₁ (x₁ n)) + f₂ + (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) + (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2):= by
   intro n
   congr

lemma ADMM_iter_process₂'_eq2_1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x₁ n , x , y n.natPred)) (x₂ n) =
      SubderivAt (fun _ => f₁ (x₁ n)) (x₂ n) + SubderivAt f₂ (x₂ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (x₂ n) +
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) (x₂ n):= by
   intro n
   rw[ADMM_iter_process₂'_eq2_1' n , ADMM_iter_process₂'_eq2_1'_1 n]
   rw[SubderivAt.add (convexOn_const (f₁ (x₁ n)) (convex_univ)) admm.cf₂
   (@continuousOn_const E₂ ℝ _ _ univ (f₁ (x₁ n))) (x₂ n)]
   rw[SubderivAt.add (ConvexOn.add (convexOn_const (f₁ (x₁ n)) (convex_univ)) admm.cf₂)
   (inner_convex2 n) (ContinuousOn.add (@continuousOn_const E₂ ℝ _ _ univ (f₁ (x₁ n)))  f₂_continuous) (x₂ n)]
   rw[SubderivAt.add (ConvexOn.add (ConvexOn.add (convexOn_const (f₁ (x₁ n)) (convex_univ)) admm.cf₂) (inner_convex2 n))
   (norm_covex2 n) (ContinuousOn.add (ContinuousOn.add (@continuousOn_const E₂ ℝ _ _ univ (f₁ (x₁ n)))  f₂_continuous) (inner_continuous2 n)) (x₂ n)]

-- #check
lemma ADMM_iter_process₂'_eq2_2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt (fun _ => f₁ (x₁ n)) (x₂ n) + SubderivAt f₂ (x₂ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (x₂ n) +
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) (x₂ n) =
      0 + SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   rw[ADMM_iter_process₂'_eq3_1 n,ADMM_iter_process₂'_eq3_2 n,ADMM_iter_process₂'_eq3_3 n]

lemma ADMM_iter_process₂'_eq2_3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      0 + SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}
      = SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   rw[zero_add]

lemma ADMM_iter_process₂'_eq1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}
      = SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x₁ n , x , y n.natPred)) (x₂ n):=by
   intro n
   rw[← ADMM_iter_process₂'_eq2_3 n,← ADMM_iter_process₂'_eq2_2 n , ← ADMM_iter_process₂'_eq2_1 n]

lemma ADMM_iter_process₂' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , 0 ∈
      SubderivAt f₂ (x₂ n) + { A₂† (y (n - 1))} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   have := first_order_convex_iff_subgradient (f := (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x₁ n , x , y n.natPred))) (x₂ n)
   have h := admm.itex₂ n.natPred
   have eq : n.natPred + 1 = n := by apply PNat.natPred_add_one
   rw[eq , this , ← ADMM_iter_process₂'_eq1 n] at h
   exact h

lemma ADMM_iter_process₂ [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+ ,
      (- A₂† (y (n - 1))- ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) -b))) ∈ SubderivAt f₂ (x₂ n) := by
   intro n
   let S := SubderivAt f₂ (x₂ n)
   let p := A₂† (y (n - 1))
   let q := ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) -b))
   show - p - q ∈ S
   have := ADMM_iter_process₂' n
   change 0 ∈ S + {p} + {q} at this
   apply change_item this

lemma u_inthesubgradient [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , u n ∈ SubderivAt f₁ (x₁ n) := by
  intro n
  have : (↑n : Nat) - 1 + 1 = (↑n : Nat) := PNat.natPred_add_one n
  let un := u n
  have h₁ : un = u n := rfl
  let yn := y n; let yn' := y (n-1)
  have h₂ : yn = y n := rfl; have h₃ : yn' = y (n-1) := rfl
  let x₁n := x₁ n; let x₂n := x₂ n; let x₂n' := x₂ (n-1)
  have h₄ : x₁n = x₁ n := rfl; have h₅ : x₂n = x₂ n := rfl
  have aux : yn' = yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) := by
      rw [h₂, ← this, admm.itey (n - 1), ← h₃, this, ← h₄, ← h₅]
      exact eq_sub_of_add_eq rfl
  have : -A₁†  yn' - ρₙ n • A₁† (A₁ x₁n + A₂ x₂n' - b) = un :=
      calc -A₁† yn' - ρₙ n • A₁† (A₁ x₁n + A₂ x₂n' - b)
         _ = -A₁† (yn' + ρₙ n • (A₁ x₁n + A₂ x₂n' -b)) := by
            rw [← A₁†.map_smul, A₁†.map_add, neg_add']
         _ = -A₁† (yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₁ x₁n + A₂ x₂n' -b)) := by rw [aux]
         _ = -A₁† (yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₁ x₁n + A₂ x₂n + A₂ x₂n' - A₂ x₂n -b)) := by
            congr
            rw [add_assoc, add_comm (A₂ x₂n), ← add_assoc]
            exact Eq.symm (add_sub_cancel_right (A₁ x₁n + A₂ x₂n') (A₂ x₂n))
         _ = -A₁† (yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₂ x₂n' - A₂ x₂n)) := by
            have :  ρₙ n • (A₁ x₁n + A₂ x₂n + A₂ x₂n' - A₂ x₂n - b) = ρₙ n • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₂ x₂n' - A₂ x₂n) := by
               rw [←smul_add]
               refine (smul_right_inj ?hc).mpr ?_
               exact Ne.symm (ne_of_lt (admm.hρₙ_pos n))
               rw[←add_sub]
               exact add_sub_right_comm (A₁ x₁n + A₂ x₂n) (A₂ x₂n' - A₂ x₂n) b
            rw [this, add_assoc]
         _ = -A₁† (yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₁ x₁n + A₂ x₂n -b ) + ρₙ n • A₂ (x₂n' - x₂n)) := by
            have : ρₙ n • (A₂ x₂n' - A₂ x₂n) = ρₙ n • A₂ (x₂n' - x₂n) := by
               refine (smul_right_inj ?hc).mpr ?_
               exact Eq.symm (ContinuousLinearMap.map_sub A₂ x₂n' x₂n)
            rw [this]
         _ = -A₁† (yn + ((1 - τ) * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • A₂ (x₂n' - x₂n)) := by
            have : yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₁ x₁n + A₂ x₂n - b) = yn +
               ((1 - τ) * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) := by
               refine sub_eq_sub_iff_add_eq_add.mp ?_
               rw[sub_sub,←add_smul];simp
               rw[sub_mul,add_sub];simp
            rw [this]
         _ = -A₁† (yn + ((1 - τ) * ρₙ n) • (A₁ x₁n + A₂ x₂n - (A₁ x₁' + A₂ x₂')) + ρₙ n • A₂ (x₂n' - x₂n)) := by
            rw [(admm_kkt.h).eq]
         _ = -A₁† (yn + ((1 - τ) * ρₙ n) • ((A₁ x₁n - A₁ x₁') + (A₂ x₂n - A₂ x₂')) + ρₙ n • A₂ (x₂n' - x₂n)) := by
            have : A₁ x₁n + A₂ x₂n - (A₁ x₁' + A₂ x₂') = (A₁ x₁n - A₁ x₁') + (A₂ x₂n - A₂ x₂') := by
               exact add_sub_add_comm (A₁ x₁n) (A₂ x₂n) (A₁ x₁') (A₂ x₂')
            rw [this]
         _ = -A₁† (yn + ((1 - τ) * ρₙ n) • ((A₁ (e₁ n)) + A₂ (e₂ n)) + ρₙ n • A₂ (x₂n' - x₂n)) := by
            have h1 : A₁ x₁n - A₁ x₁' = A₁ (e₁ n) := by
               have : e₁ n = x₁ n - x₁' := rfl
               rw [this, ← h₄]
               exact Eq.symm (ContinuousLinearMap.map_sub A₁ x₁n x₁')
            have h2 : A₂ x₂n - A₂ x₂' = A₂ (e₂ n) := by
               have : e₂ n = x₂ n - x₂' := rfl
               rw [this, ← h₅]
               exact Eq.symm (ContinuousLinearMap.map_sub A₂ x₂n x₂')
            rw [← h1, ← h2]
         _ = un := rfl
  rw [← h₁, ← this]
  exact ADMM_iter_process₁ n

lemma v_inthesubgradient [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , v n ∈ SubderivAt f₂ (x₂ n) := by
   intro n
   have : (↑n : Nat) - 1 + 1 = (↑n : Nat) := PNat.natPred_add_one n
   -- notation for v n
   let vn := v n
   have h₁ : vn = v n := rfl
   -- notation for y n, y (n-1)
   let yn := y n; let yn' := y (n-1)
   have h₂ : yn = y n := rfl
   have h₃ : yn' = y (n-1) := rfl
   -- notation for x₁ n, x₂ n, x₂ (n-1)
   let x₁n := x₁ n; let x₂n := x₂ n
   have h₄ : x₁n = admm.x₁ n := rfl
   have h₅ : x₂n = admm.x₂ n := rfl

   -- prove : y_n-1 = y_n - (τ * ρ) • (A₁ x₁n + A₂ x₂n - b)
   have aux : yn' = yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) := by
      rw [h₂, ← this, admm.itey (n - 1), ← h₃, this, ← h₄, ← h₅]
      exact eq_sub_of_add_eq rfl
   -- calculate LHS
   have : -A₂† yn' - ρₙ n • A₂† (A₁ x₁n + A₂ x₂n - b) = vn :=
      calc -A₂† yn' - ρₙ n • A₂† (A₁ x₁n + A₂ x₂n - b)
         _ = -A₂† (yn' + ρₙ n • (A₁ x₁n + A₂ x₂n - b)) := by
           rw [← A₂†.map_smul, A₂†.map_add, neg_add']
         _ = -A₂† (yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₁ x₁n + A₂ x₂n - b)) := by rw[aux]
         _ = -A₂† (yn + ((1 - τ) * ρₙ n) • (A₁ x₁n + A₂ x₂n - b)) := by
            have : yn - (τ * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) + ρₙ n • (A₁ x₁n + A₂ x₂n - b) = yn +
              ((1 - τ) * ρₙ n) • (A₁ x₁n + A₂ x₂n - b) := by
               refine sub_eq_sub_iff_add_eq_add.mp ?_
               rw[sub_sub , ←add_smul]
               simp
               rw[sub_mul,add_sub]
               simp
            rw[this]
         -- now substitute for b = (A₁ x₁' + A₂ x₂')
         _ = -A₂† (yn + ((1 - τ) * ρₙ n) • (A₁ x₁n + A₂ x₂n - (A₁ x₁' + A₂ x₂'))) := by
            rw [(admm_kkt.h).eq]
         _ = -A₂† (yn + ((1 - τ) * ρₙ n) • ((A₁ x₁n - A₁ x₁') + (A₂ x₂n  - A₂ x₂'))) := by
            have : A₁ x₁n + A₂ x₂n - (A₁ x₁' + A₂ x₂') = (A₁ x₁n - A₁ x₁') + (A₂ x₂n - A₂ x₂') := by
               exact add_sub_add_comm (A₁ x₁n) (A₂ x₂n) (A₁ x₁') (A₂ x₂')
            rw [this]
         _ = -A₂† (yn + ((1 - τ) * ρₙ n) • ((A₁ (e₁ n)) + A₂ (e₂ n))) := by
            have h1 : A₁ x₁n - A₁ x₁' = A₁ (e₁ n) := by
               have : e₁ n = x₁ n - x₁' := rfl
               rw [this, ← h₄]
               exact Eq.symm (ContinuousLinearMap.map_sub A₁ x₁n x₁')
            have h2 : A₂ x₂n - A₂ x₂' = A₂ (e₂ n) := by
               have : e₂ n = x₂ n - x₂' := rfl
               rw [this, ← h₅]
               exact Eq.symm (ContinuousLinearMap.map_sub A₂ x₂n x₂')
            rw [← h1, ← h2]
         _ = vn := rfl
   rw [← h₁, ← this]
   exact ADMM_iter_process₂ n

lemma Φ_isdescending_eq1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b
      = (1 / (τ * ρₙ (n + 1))) • (y (n + 1) - y n):= by
   intro n
   rw [admm.itey n,add_comm (y n)]
   simp only [one_div, mul_inv_rev, add_sub_cancel_right]
   rw [smul_smul, mul_assoc]
   nth_rw 2 [← mul_assoc]
   have htau1 : τ⁻¹ * τ = 1:= by
      refine inv_mul_cancel₀ ?h
      linarith[admm.htau.1];
   have hrho1 :  (ρₙ (n + 1) : ℝ)⁻¹ * (ρₙ (n + 1) : ℝ) = 1:= by
      refine inv_mul_cancel₀ ?h
      linarith[admm.hρₙ_pos (n + 1)];
   rw [htau1 , one_mul, hrho1, one_smul]

lemma Φ_isdescending_eq2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , (1 / (τ * ρₙ (n + 1))) • (y (n + 1) - y n)
      = (1 / (τ * ρₙ (n + 1))) • (ey (n + 1) - ey n):= by
   intro n
   calc
      _ = (1 / (τ * ρₙ (n + 1))) • (y (n + 1) - y' + y' - y n) := by rw [sub_add, sub_self, sub_zero]
      _ = (1 / (τ * ρₙ (n + 1))) • (y (n + 1) - y' - (y n - y')) := by simp only [one_div,
        mul_inv_rev, sub_add_cancel, sub_sub_sub_cancel_right]

lemma Φ_isdescending_eq3 [Setting E₁ E₂ F admm admm_kkt] : ∀ n , A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b
      = A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)) := by
   intro n
   calc
      _ = A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - (A₁ x₁' + A₂ x₂') := by rw [admm_kkt.h.eq]
      _ = A₁ (x₁ (n + 1)) - A₁ x₁' + (A₂ (x₂ (n + 1)) - A₂ x₂') :=
         add_sub_add_comm (A₁  (x₁ (n + 1))) (A₂ (x₂ (n + 1))) (A₁  x₁') (A₂ x₂')
      _ = A₁ ((x₁ (n + 1)) - x₁') + A₂ ((x₂ (n + 1)) - x₂') := by simp only [map_sub]
      _ = A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)) := by rw [e₁, e₂]

lemma Φ_isdescending_eq3' [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+ , A₁ (x₁ n) + A₂ (x₂ n) - b = A₁ (e₁ n) + A₂ (e₂ n) := by
   intro n
   have := Φ_isdescending_eq3 n.natPred
   have h: n = n.natPred + 1 := by simp only [PNat.natPred_add_one]
   rw[← h] at this
   exact this

lemma subgradientAt_mono_u [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
      (0 : ℝ) ≤ ⟪u n + A₁† y', x₁ n - x₁'⟫ := by
   intro n
   calc
      _ = ⟪u n - (- A₁† y'), x₁ n - x₁'⟫ := by
         simp [sub_eq_add_neg]
      _ ≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply u_inthesubgradient
         exact admm_kkt.h.subgrad₁
lemma subgradientAt_mono_v [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
      (0 : ℝ) ≤ ⟪v n + A₂† y', x₂ n - x₂'⟫ := by
   intro n
   calc
      _ = ⟪v n - (- A₂† y'), x₂ n - x₂'⟫ := by simp [v]
      _ ≥ (0 : ℝ) := by
         apply subgradientAt_mono
         apply v_inthesubgradient
         exact admm_kkt.h.subgrad₂


lemma expended_u_gt_zero [Setting E₁ E₂ F admm admm_kkt]: ∀ n, (0 : ℝ) ≤
      ⟪( -ey (n + 1) - ((1-τ) * ρₙ (n + 1)) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
      - (ρₙ (n + 1) • (A₂ (x₂ (n) - x₂ (n+1))))), (A₁ (e₁ (n + 1)))⟫ := by
   intro n
   let Ae1 := A₁ (e₁ (n + 1))
   let e' := e₁ (n + 1)
   let block := -ey (n + 1) - ((1-τ) * ρₙ (n + 1)) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
   - (ρₙ (n + 1) • (A₂ (x₂ (n) - x₂ (n+1))))
   let u' := - A₁† (y (n + 1) + ((1-τ) * ρₙ (n + 1)) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)))
         + (ρₙ (n + 1) • (A₂ (x₂ (n) - x₂ (n+1)))))
   let x_diff := x₁ (n + 1) - x₁'
   let succ_n := Nat.toPNat' (n + 1)
   calc
      _= ⟪block, Ae1⟫ := by rfl
      _= ⟪A₁† block, e'⟫ := by
         simpa [Ae1, e'] using (ContinuousLinearMap.adjoint_inner_left A₁ e' block).symm
      _= ⟪u' + A₁† y', x_diff⟫ := by
         let block₁ := y (n + 1) + ((1-τ) * ρₙ (n + 1)) • (A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))) + (ρₙ (n + 1) • (A₂ (x₂ (n) - x₂ (n+1))))
         have split_block : -block = block₁ - y' := by
            simp[block, block₁]
            have split_ey :  ey (n + 1) = (y (n + 1)) - y' := by rfl
            rw [split_ey]
            simp
            rw [sub_eq_add_neg,neg_sub (y' - y (n + 1)),add_comm,sub_eq_add_neg, neg_sub]
            rw [add_assoc,← smul_add,smul_sub]
            let A := ((1 - τ) * ρₙ (n + 1)) • ((A₁) (e₁ (n + 1)) + (A₂) (e₂ (n + 1)))
            let C := y (n + 1)
            let D := ρₙ (n + 1) • ((A₂) (x₂ n))
            let E := ρₙ (n + 1) • ((A₂) (x₂ (n + 1)))
            change A + (C - y' + (D - E)) = C + A + (D - E) - y'
            rw [← add_assoc,sub_eq_add_neg,← add_assoc,add_comm A C]
            rw [add_assoc,add_comm (-y') (D - E),← add_assoc,← sub_eq_add_neg]
         rw [← neg_neg block,split_block,neg_sub,A₁†.map_sub]
         have u'_eq : - A₁† block₁ = u' := by
            simp[u']
            rw [← A₁†.map_smul, ← A₁†.map_smul,smul_sub,← A₁†.map_smul, ← A₁†.map_smul]
            rw [← A₁†.map_sub,← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg, ← A₁†.map_neg]
            rw [← A₁†.map_add, ← A₁†.map_add, ← A₁†.map_add]
            simp[block₁]
            rw [← smul_neg, neg_sub,smul_sub]
         have Aty'_eq : A₁† y' = A₁† y' := rfl
         rw [← u'_eq, Aty'_eq, add_comm, sub_eq_add_neg]
         simp[e', x_diff]
         rfl
      _= ⟪(u (succ_n) + A₁† y'), (x₁ (succ_n) - x₁')⟫ := by rfl
      _≥ 0 := by apply subgradientAt_mono_u

lemma expended_v_gt_zero [Setting E₁ E₂ F admm admm_kkt]: ∀ n,
      ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • ((A₁ (e₁ (n + 1))) + (A₂ (e₂ (n + 1)))) , A₂ (e₂ (n + 1)) ⟫ ≥ (0 : ℝ) := by
   intro n
   let succ_n := Nat.toPNat' (n + 1)
   let ey' := ey (succ_n)
   let e₁' := e₁ (succ_n)
   let e₂' := e₂ (succ_n)
   let y_k_1 := y (succ_n)
   let v_k_1 := v (succ_n)
   let x_diff := x₂ (succ_n) - x₂'
   calc
   _ = ⟪ -ey' - ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂') , A₂ e₂' ⟫ := by rfl
   _ = ⟪ A₂† (-ey' - ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂')) , e₂' ⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_left]
   _ = ⟪ -A₂† (ey' + ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂')) , e₂' ⟫ := by
      rw [sub_eq_add_neg, ← neg_add, A₂†.map_neg]
   _ = ⟪ -A₂† (y_k_1 - y' + ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂')) , e₂' ⟫ := by
      have sub : ey' = y_k_1 - y' := by simp [ey', y_k_1] ; rfl
      rw [sub]
   _ = ⟪ -A₂† (y_k_1 + ((1 - τ) * ρₙ (n + 1)) • (A₁ e₁' + A₂ e₂')) + A₂† y' , e₂' ⟫ := by
      rw [sub_eq_add_neg, add_comm y_k_1, add_assoc, A₂†.map_add]
      simp
   _ = ⟪ v_k_1 + A₂† y' , x_diff ⟫ := by rfl
   _ ≥ (0 : ℝ) := by apply subgradientAt_mono_v


lemma starRingEnd_eq_R (x : ℝ) : (starRingEnd ℝ) x = x := rfl

set_option maxHeartbeats 500000 in
lemma expended_u_v_gt_zero [Setting E₁ E₂ F admm admm_kkt]:
∀ n, ⟪ ey (n + 1), -(A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1))) ⟫
      - (1 - τ) * ρₙ (n + 1) * ‖A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2
      + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), A₁ (e₁ (n + 1)) ⟫ ≥ 0 := by
  intro n
  set A_e_sum := A₁ (e₁ (n + 1)) + A₂ (e₂ (n + 1)) with hAes
  set Ae1 := A₁ (e₁ (n + 1)) with hAe1
  set Ae2 := A₂ (e₂ (n + 1)) with hAe2
  have hv : ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum, Ae2 ⟫ ≥ (0 : ℝ) := by
    simpa [A_e_sum, Ae2] using (expended_v_gt_zero (admm:=admm) (admm_kkt:=admm_kkt) n)
  have hu : ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum - ρₙ (n + 1) • A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫ ≥ (0 : ℝ) := by
    simpa [A_e_sum, Ae1, sub_eq_add_neg] using (expended_u_gt_zero (admm:=admm) (admm_kkt:=admm_kkt) n)
  have hsum :
      0 ≤ ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum, Ae2 ⟫
        + ⟪ -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum - ρₙ (n + 1) • A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫ :=
    add_nonneg hv hu
  set U := -ey (n + 1) - ((1 - τ) * ρₙ (n + 1)) • A_e_sum with hU
  set Z := A₂ (x₂ n - x₂ (n + 1)) with hZ
  have hrewrite :
      ⟪ ey (n + 1), -A_e_sum ⟫
      - (1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2
      + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫
      =
      ⟪ U, Ae2 ⟫ + ⟪ U - ρₙ (n + 1) • Z, Ae1 ⟫ := by
    have h1 : ⟪ U - ρₙ (n + 1) • Z, Ae1 ⟫ = ⟪ U, Ae1 ⟫ + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ := by
      simpa [sub_eq_add_neg] using (inner_add_left U (-ρₙ (n + 1) • Z) Ae1)
    have h2 : ⟪ U, Ae2 ⟫ + ⟪ U, Ae1 ⟫ = ⟪ U, Ae1 + Ae2 ⟫ := by
      rw [add_comm]
      simpa using (inner_add_right (𝕜 := ℝ) U Ae1 Ae2).symm
    have h3 : Ae1 + Ae2 = A_e_sum := by simp [hAes]
    have h4 : ⟪ U, A_e_sum ⟫ = ⟪ -ey (n + 1), A_e_sum ⟫ + ⟪ -((1 - τ) * ρₙ (n + 1)) • A_e_sum, A_e_sum ⟫ := by
      have : U = (-ey (n + 1)) + ( -((1 - τ) * ρₙ (n + 1)) • A_e_sum) := by
        simp [U, sub_eq_add_neg]
      simp [this, inner_add_left]
    have h5 : ⟪ -ey (n + 1), A_e_sum ⟫ = ⟪ ey (n + 1), -A_e_sum ⟫ := by
      simp [inner_neg_right]
    have h6 : ⟪ -((1 - τ) * ρₙ (n + 1)) • A_e_sum, A_e_sum ⟫ = -(1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2 := by
      simp [real_inner_smul_left, real_inner_self_eq_norm_sq, mul_comm, mul_assoc]; grind
    have h7 : ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ = ρₙ (n + 1) * ⟪ -Z, Ae1 ⟫ := by
      simp [real_inner_smul_left]
    have h8 : -Z = -A₂ (x₂ n - x₂ (n + 1)) := by simp [Z]
    have h6' :
        -(1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2
        = -⟪((1 - τ) * ρₙ (n + 1)) • A_e_sum, A_e_sum⟫ := by
      simpa [inner_neg_left] using h6.symm
    calc
      ⟪ ey (n + 1), -A_e_sum ⟫ - (1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2 + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫
          = (⟪ ey (n + 1), -A_e_sum ⟫ + (-(1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2)) + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫ := by
            ring
      _ = (⟪ -ey (n + 1), A_e_sum ⟫ + ⟪ -((1 - τ) * ρₙ (n + 1)) • A_e_sum, A_e_sum ⟫) + ρₙ (n + 1) * ⟪ -Z, Ae1 ⟫ := by
            rw [h5, h6', h8]; simp
      _ = ⟪ U, A_e_sum ⟫ + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ := by
            have := congrArg (fun t => t + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫) h4
            simpa [real_inner_smul_left] using this.symm
      _ = ⟪ U, Ae1 + Ae2 ⟫ + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ := by
            simp [h3]
      _ = (⟪ U, Ae2 ⟫ + ⟪ U, Ae1 ⟫) + ⟪ -ρₙ (n + 1) • Z, Ae1 ⟫ := by
            simp [inner_add_right, add_comm]
      _ = ⟪ U, Ae2 ⟫ + ⟪ U - ρₙ (n + 1) • Z, Ae1 ⟫ := by
            simp [sub_eq_add_neg, inner_add_left, real_inner_smul_left, add_comm, add_left_comm, add_assoc]
  have : ⟪ ey (n + 1), -A_e_sum ⟫
          - (1 - τ) * ρₙ (n + 1) * ‖A_e_sum‖^2
          + ρₙ (n + 1) * ⟪ -A₂ (x₂ n - x₂ (n + 1)), Ae1 ⟫ ≥ 0 := by
    have h' : 0 ≤ ⟪ U, Ae2 ⟫ + ⟪ U - ρₙ (n + 1) • Z, Ae1 ⟫ := hsum
    simpa [hrewrite.symm] using h'
  simp [A_e_sum, Ae1] at this
  exact le_of_le_of_eq hsum (id (Eq.symm hrewrite))


lemma substitution1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫ = ρₙ (n + 1) * ⟪(A₂ (x₂ n - x₂ (n+1))),(A₂ (e₂ (n+1)))⟫:= by
   intro n
   rw [neg_mul (ρₙ (n + 1)) ⟪(A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫]
   rw [← mul_neg]
   rw [← inner_neg_left (A₂ (x₂ (n+1) - x₂ n)) (A₂ (e₂ (n+1)))]
   rw [← map_neg A₂ (x₂ (n+1) - x₂ n)]
   rw [neg_sub (x₂ (n+1)) (x₂ n)]

lemma substitution2 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b - A₂ (e₂ (n+1)) = A₁ (e₁ (n+1)) := by
   intro n
   have h := Φ_isdescending_eq3 n
   simp [h]

lemma Φ_isdescending_inequ1 [Setting E₁ E₂ F admm admm_kkt]: ∀ n , 1/(τ * ρₙ (n + 1)) * ⟪(ey (n+1)) ,((ey n)-(ey (n+1)))⟫
      - (1-τ)*ρₙ (n + 1)*‖admm.A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)),(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)⟫
         -ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)),(A₂ (e₂ (n+1))) ⟫ ≥ 0 := by
   intro n
   let pm1 := 1 / (τ * ρₙ (n + 1))
   let pm2 := (1 - τ) * ρₙ (n + 1)
   have h1:  pm1 * ⟪ (ey (n+1)),((ey n)-(ey (n+1)))⟫
      = (⟪ ey (n + 1), -((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))) ⟫) := by
      calc  pm1 * ⟪ ey (n+1), ((ey n)-(ey (n+1))) ⟫
         _ = ⟪ ey (n+1), pm1 • ((ey n)-(ey (n+1))) ⟫ := by
            rw [← real_inner_smul_right (ey (n+1)) ((ey n)-(ey (n+1))) pm1]
         _ = ⟪ ey (n+1), pm1 • -((ey (n+1))-(ey n)) ⟫ := by
            rw [← neg_sub (ey (n+1)) (ey n)]
         _ = ⟪ ey (n+1), -(pm1 • ((ey (n+1))-(ey n))) ⟫ := by
            rw [smul_neg]
         _ = ⟪ ey (n+1), -(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ := by
            rw [← Φ_isdescending_eq2, ← Φ_isdescending_eq1]
         _ = ⟪ ey (n+1), -(A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))) ⟫ := by
            rw [Φ_isdescending_eq3]
   have h2:  pm2*‖admm.A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 = pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 := by
      rw [Φ_isdescending_eq3]
   have h3: ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ -ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₂ (e₂ (n+1))) ⟫
   =  ρₙ (n + 1) * ⟪ -A₂ (x₂ (n) - x₂ (n+1)), (A₁ (e₁ (n+1))) ⟫ := by
      calc ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
         -ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₂ (e₂ (n+1))) ⟫
         _ = ρₙ (n + 1) * ⟪ -A₂ (x₂ (n) - x₂ (n+1)), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
         - ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₂ (e₂ (n+1))) ⟫ := by
            rw [← neg_sub (x₂ n) (x₂ (n+1))]
            rw [map_neg A₂ (x₂ (n) - x₂ (n+1))]
         _ = - ρₙ (n + 1) * ⟪ A₂ (x₂ (n) - x₂ (n+1)), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
         - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1))) ⟫ := by
            rw [inner_neg_left (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)]
            simp
         _ = - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
         + ρₙ (n + 1) * ⟪ (A₂ (x₂ n - x₂ (n+1))), (A₂ (e₂ (n+1))) ⟫ := by
            rw [← substitution1]
            simp only [map_sub, neg_mul];rfl
         _ = ρₙ (n + 1) * ⟪ (A₂ (x₂ n - x₂ (n+1))), (A₂ (e₂ (n+1))) ⟫
         - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ := by
            ring
         _ = ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₂ (e₂ (n+1)) - (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)) ⟫ := by
            rw [← mul_sub]
            rw [← inner_sub_right (A₂ (x₂ (n) - x₂ (n+1))) (A₂ (e₂ (n+1))) ((A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b))]
         _ = - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b - A₂ (e₂ (n+1))) ⟫ := by
            rw [← neg_sub (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) (A₂ (e₂ (n+1)))]
            rw [inner_neg_right]
            simp only [map_sub, mul_neg, neg_mul]
         _ = - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n) - x₂ (n+1))), (A₁ (e₁ (n+1))) ⟫ := by
            rw [substitution2]
         _ = ρₙ (n + 1) * ⟪ -A₂ (x₂ (n) - x₂ (n + 1)), (A₁ (e₁ (n+1))) ⟫ := by
            rw [neg_mul (ρₙ (n + 1)) ⟪ (A₂ (x₂ (n) - x₂ (n + 1))), (A₁ (e₁ (n+1))) ⟫]
            rw [← mul_neg]
            rw [← inner_neg_left (A₂ (x₂ (n) - x₂ (n+1))) (A₁ (e₁ (n+1)))]
   rw [h1,h2]
   have h4: ⟪ ey (n + 1), -((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))) ⟫
   - pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 +
   (ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ -ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1))) ⟫) = ⟪ ey (n + 1), -((A₁ (e₁ (n + 1))) + A₂ (e₂ (n + 1))) ⟫
   - pm2*‖admm.A₁ (e₁ (n+1)) + A₂ (e₂ (n+1))‖^2 +
   ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ -ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1))) ⟫ := by ring
   rw [← h4,h3]
   exact expended_u_v_gt_zero n

lemma A'υ_inthesubgradient [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , - (A₂†) (υ n) ∈ SubderivAt f₂ (x₂ n):= by
   intro n
   rw [υ]
   have : v n = - A₂† (y n + (( 1 - τ) * ρₙ (n))•(A₁ (e₁ n) + A₂ (e₂ n))):= rfl
   rw[Φ_isdescending_eq3' , ← this]
   apply v_inthesubgradient

lemma Φ_isdescending_inequ2 [Setting E₁ E₂ F admm admm_kkt]:∀ n : ℕ+ ,
      ⟪ - ( A₂† ( υ (n+1) - υ n )), (x₂ (n+1)) - (x₂ n) ⟫ ≥ ( 0 : ℝ ) := by
   intro n
   let A₂T := A₂†
   let A₂υn := - (A₂T ((υ) n))
   let A₂υn1 := - (A₂T ((υ) (n+1)))
   have h1 : A₂υn ∈ SubderivAt f₂ (x₂ n) := by apply A'υ_inthesubgradient
   have h2 : A₂υn1 ∈ SubderivAt f₂ (x₂ (n+1)) := by apply A'υ_inthesubgradient (n+1)
   have mono : ⟪ A₂υn1 - A₂υn, (x₂ (n+1) - x₂ n) ⟫ ≥ (0:ℝ):= subgradientAt_mono h2 h1
   have h: -(A₂T ((υ (n+1)) - (υ n))) = A₂υn1 - A₂υn := by
      calc
         -(A₂T ((υ (n+1)) - (υ n))) = - (A₂T (υ (n+1)) - A₂T (υ n)) := by continuity
         _=  (A₂T ((υ) n)) - (A₂T ((υ) (n+1))) := by simp
         _= - (A₂T ((υ) (n+1))) - (-(A₂T ((υ) n))) := by rw [sub_neg_eq_add,add_comm (- (A₂T ((υ) (n+1)))),sub_eq_add_neg]
         _= A₂υn1 - A₂υn := by rfl
   rwa [h]

lemma Φ_isdescending_inequ3 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ ,
      ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫ ≤ M (n+1) := by
   intro n
   let A₂_x_diff := A₂ (x₂ (n+1) - x₂ n)
   let r_n := A₁ (x₁ n) + A₂ (x₂ n) - b
   let r_n_1 := A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b
   let υ_diff := υ (n+1) - υ n
   let y_diff := y (n+1) - y n
   let x_diff := x₂ (n+1) - x₂ n
   let A₂T := A₂†
   have h: ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ =
      M (n+1) + ⟪ υ_diff, A₂_x_diff ⟫ := by
         calc
         ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ =
         (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + (τ * ρₙ (n + 1)) * ⟪ A₂_x_diff, r_n_1 ⟫ := by
            linarith
         _= (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + ⟪ A₂_x_diff, (τ * ρₙ (n + 1)) • r_n_1 ⟫ := by
            rw [inner_smul_right]
         _= (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + ⟪ A₂_x_diff, y_diff ⟫ := by
            have : (τ * ρₙ (n + 1)) • r_n_1 = y_diff := by
               simp [r_n_1, y_diff]
               rw [Φ_isdescending_eq1, ← mul_smul, mul_div, mul_one, div_self, one_smul]
               intro H
               rw [mul_eq_zero] at H
               rcases H with _ | _
               · linarith [admm.htau]
               · linarith [admm.hρₙ_pos (n + 1)]
            rw [this]
         _= (1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫ - (1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫
          + (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + ⟪ A₂_x_diff, y_diff ⟫ := by
            rw [sub_self ((1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫), zero_add]
         _= M (n+1) - (1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫
          + (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ + ⟪ A₂_x_diff, y_diff ⟫ := by
            rw [M];rfl
         _= (1 - τ) * ρₙ (n + 1) * ⟪ A₂_x_diff, r_n_1 ⟫ - (1 - τ) * ρₙ n * ⟪ A₂_x_diff, r_n ⟫ +
            M (n + 1) + ⟪ A₂_x_diff, y_diff ⟫ := by
            ring_nf
         _= ⟪ A₂_x_diff, ((1 - τ) * ρₙ (n + 1)) • r_n_1 - ((1 - τ) * ρₙ n) • r_n ⟫ + M (n+1) + ⟪ A₂_x_diff, y_diff ⟫ := by
            rw [← inner_smul_right,← inner_smul_right,← inner_sub_right]
         _= ⟪ A₂_x_diff, ((1 - τ) * ρₙ (n + 1)) • r_n_1 - ((1 - τ) * ρₙ n) • r_n + y_diff ⟫ + M (n+1) := by
            rw [inner_add_right];ring_nf
         _= ⟪ A₂_x_diff, y (n+1) + ((1 - τ) * ρₙ (n + 1)) • r_n_1 - y n - ((1 - τ) * ρₙ n) • r_n ⟫ + M (n+1) := by
            simp [y_diff]
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
         _= ⟪ A₂_x_diff, υ (n+1) - υ n ⟫ + M (n+1):= by
            rw [υ,υ]
            simp[r_n_1,r_n]
            rw [sub_sub] --神之一手，我真是服了，为什么这个state不能简洁一点，卡了3小时
         _= ⟪ A₂_x_diff, υ_diff ⟫ + M (n+1):= by
            simp [υ_diff]
         _= M (n+1) + ⟪ A₂_x_diff, υ_diff ⟫ := by
            rw [inner_sub_right];ring
         _= M (n+1) + ⟪ υ_diff, A₂_x_diff ⟫ := by
            rw [real_inner_comm]
   have mono: ⟪ υ_diff, A₂_x_diff ⟫ ≤ (0:ℝ) := by
      simp [υ_diff, A₂_x_diff]
      rw [← map_sub A₂]
      have : ⟪ υ_diff, A₂_x_diff ⟫ = ⟪ A₂T υ_diff, x_diff ⟫ := by
         rw [ContinuousLinearMap.adjoint_inner_left]
      rw [this]
      apply neg_nonneg.1
      rw [← inner_neg_left]
      apply Φ_isdescending_inequ2
   linarith

lemma Φ_isdescending_inequ4 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+, 1 / (τ * ρₙ (n + 1)) * ⟪ ey (n + 1), (ey n) - (ey (n + 1)) ⟫
      - (1 - τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + M (n + 1)
      - ρₙ (n + 1) * ⟪ A₂ (x₂ (n + 1) - x₂ n), (A₂ (e₂ (n+1))) ⟫ ≥ 0:= by
   intro n
   let a := 1/(τ*ρₙ (n + 1)) * ⟪ ey (n+1), (ey n)-(ey (n+1)) ⟫
      - (1-τ)*ρₙ (n + 1)*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
   let b0 := M (n+1)
   let c := ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₂ (e₂ (n+1))) ⟫
   let d := ρₙ (n + 1) * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) ⟫
   have dleqb: d ≤ b0 := by apply Φ_isdescending_inequ3
   have h : a + d - c ≥ 0 := by apply Φ_isdescending_inequ1
   have : a + b0 - c ≥ 0 := by linarith
   exact this

lemma inner_eq_norm {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      (a₁ a₂ : X) : ⟪ a₁, a₂ ⟫ = 1/2 * (‖a₁‖^2 + ‖a₂‖^2 - ‖a₁- a₂‖^2) := by
   rw [norm_sub_sq (𝕜 := ℝ) a₁ a₂];ring_nf;
   rfl

lemma Φ_isdescending_eq2' [Setting E₁ E₂ F admm admm_kkt]:
      ∀ n , (τ * ρₙ (n + 1)) • (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b) = ey (n+1) - ey n:=by
   intro n
   rw [Φ_isdescending_eq1, Φ_isdescending_eq2]
   simp only [one_div, mul_inv_rev]
   rw [smul_smul, mul_assoc]
   nth_rw 2 [← mul_assoc]
   rw [mul_inv_cancel₀, one_mul, mul_inv_cancel₀, one_smul]
   rcases admm.htau with ⟨h₁, _⟩
   apply ne_of_gt h₁
   apply ne_of_gt (admm.hρₙ_pos (n + 1))

lemma Φ_isdescending_inequ5' [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
      1 / (τ * ρₙ (n + 1)) * (‖ey n‖^2 - ‖ey (n+1)‖^2) - (2 - τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * (M (n+1)) - ρₙ (n + 1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 - ρₙ (n + 1) * ‖A₂ (e₂ (n+1))‖^2 + ρₙ (n + 1) * ‖A₂ (e₂ n)‖ ^ 2
      = 2 * (1 / (τ * ρₙ (n + 1)) * ⟪ (ey (n+1)),((ey n)-(ey (n+1)))⟫ -
      (1 - τ) * ρₙ  (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + M (n+1) - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫) := by
   intro n
   have h₄'' : ‖A₂ (x₂') - A₂ (x₂ n)‖ = ‖- (A₂ (x₂ n) - A₂ (x₂'))‖ := by simp only [neg_sub]
   have h₄' : ‖A₂ (x₂ (n+1) - x₂ n) - A₂ (e₂ (n+1))‖ = ‖A₂ (e₂ n)‖ := by rw [e₂]; rw[e₂]; simp only [map_sub,sub_sub_sub_cancel_left]; rw [h₄'', norm_neg]
   have h₆ : ‖ey (n+1) - ey n‖ = (τ * ρₙ (n + 1)) * ‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖
      := by rw [←Φ_isdescending_eq2', norm_smul]; simp only [norm_mul, Real.norm_eq_abs,mul_eq_mul_right_iff, norm_eq_zero]
            left
            have h1: τ ≥ 0 := by rcases admm.htau with ⟨h₁, _⟩; apply le_of_lt h₁
            have h2: ρₙ (n + 1) ≥ 0 := by apply le_of_lt (admm.hρₙ_pos (n + 1))
            have h3: |τ| = τ := by apply abs_eq_self.mpr h1
            have h4: |ρₙ (n + 1)| = ρₙ (n + 1) := by apply abs_eq_self.mpr h2
            rw [h3, h4]
   symm
   calc 2 * (1/(τ*ρₙ (n + 1)) * ⟪ (ey (n+1)),((ey n)-(ey (n+1)))⟫ - (1-τ)*ρₙ (n + 1)*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + M (n+1) - ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫)
      _ = 2 / (τ * ρₙ (n + 1)) * ⟪ (ey (n+1)),((ey n)-(ey (n+1)))⟫
      - 2 * (1-τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 2 * ρₙ (n + 1) * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₂ (e₂ (n+1)))⟫ := by ring
      _ = 2 / (τ * ρₙ (n + 1)) * (1 / 2 * (‖ey (n+1)‖^2 + ‖ey n‖^2 - ‖ey (n+1) - ey n‖^2)-‖ey (n+1)‖^2)
      - 2 * (1-τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 2 * ρₙ (n + 1) * ( 1 / 2 * (‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (x₂ (n+1) - x₂ n) - A₂ (e₂ (n+1))‖^2))
      := by nth_rw 2 [inner_eq_norm]; rw [inner_sub_right]; rw [inner_eq_norm, real_inner_self_eq_norm_sq]
      _ = 2 / (τ * ρₙ (n + 1)) * (1 / 2 * (‖ey n‖^2 - ‖ey (n+1) - ey n‖^2-‖ey (n+1)‖^2))
      - 2 * (1-τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 2 * ρₙ (n + 1) * ( 1 / 2 * (‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by rw [h₄']; ring_nf
      _ = 1 / (τ * ρₙ (n + 1)) * ((‖ey n‖^2 - ((τ * ρₙ (n + 1)) * ‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2-‖ey (n+1)‖^2))
      - 2 * (1-τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 1 * ρₙ (n + 1) * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by rw [h₆]; ring_nf
      _ = 1 / (τ * ρₙ (n+1)) * ((‖ey n‖^2 -‖ey (n+1)‖^2)) - 1 / (τ * ρₙ (n+1)) * (τ * ρₙ (n+1)) ^ 2 * (‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2
      - 2 * (1-τ) * ρₙ (n+1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 1 * ρₙ (n+1) * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by ring
      _ = 1 / (τ * ρₙ (n+1)) * ((‖ey n‖^2 -‖ey (n+1)‖^2)) - (τ * ρₙ (n+1)) * (‖(A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b)‖)^2
      - 2 * (1-τ) * ρₙ (n+1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2 * M (n+1)
      - 1 * ρₙ (n+1) * ((‖A₂ (x₂ (n+1) - x₂ n)‖^2 + ‖A₂ (e₂ (n+1))‖^2 - ‖A₂ (e₂ n)‖^2))
      := by nth_rw 2 [div_eq_mul_inv]; rw [one_mul]; nth_rw 3 [pow_two]; simp
            left; rw [mul_assoc]
            nth_rw 2 [← mul_assoc]
            nth_rw 2 [← mul_assoc]
            nth_rw 2 [← mul_assoc]
            rw [inv_mul_cancel₀, one_mul]
            repeat rw [← mul_assoc]
            rw [inv_mul_cancel₀, one_mul]
            apply ne_of_gt (admm.hρₙ_pos (n+1))
            rcases admm.htau with ⟨h₁, _⟩
            apply ne_of_gt h₁
      _ = 1/(τ*ρₙ (n+1)) * (‖ey n‖^2 - ‖ey (n+1)‖^2)
      - (2-τ)*ρₙ (n+1)*‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
      + 2*(M (n+1))
      -ρₙ (n+1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2
      -ρₙ (n+1) * ‖A₂ (e₂ (n+1))‖^2
      +ρₙ (n+1) * ‖A₂ (e₂ n)‖^2
      := by ring_nf

lemma Φ_isdescending_inequ5 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+ , 1 / (τ * ρₙ (n + 1)) * (‖ey n‖ ^ 2 - ‖ey (n+1)‖ ^ 2)
      - (2 - τ) * ρₙ (n + 1) * ‖A₁ (x₁ (n + 1)) + A₂ (x₂ (n + 1)) - b‖ ^ 2 + 2 * M (n+1)
      - ρₙ (n + 1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 - ρₙ (n + 1) * ‖A₂ (e₂ (n+1))‖^2 + ρₙ (n + 1) * ‖A₂ (e₂ n)‖^2 ≥ 0:= by
   intro n
   rw [Φ_isdescending_inequ5']
   apply mul_nonneg
   · norm_num
   apply Φ_isdescending_inequ4 n

lemma basic_inequ₁' (n : ℕ+) : 2 * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫
      ≤ ‖A₂ (x₂ n - x₂ (n+1))‖ ^ 2 + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
   have norm_abs:
      ‖A₂ (x₂ n - x₂ (n+1))‖^2 = ‖A₂ (x₂ (n+1) - x₂ (n))‖^2:= by
      rw[← norm_neg]
      have : -(A₂ (x₂ n - x₂ (n+1))) = A₂ (x₂ (n+1) - x₂ (n)) := by continuity
      rw [this]
   rw [←sub_nonneg];
   have : ‖A₂ (x₂ n - x₂ (n+1))‖^2
      + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 - 2 * ⟪ A₂ (x₂ (n+1) - x₂ (n)), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫
      = ‖A₂ (x₂ n - x₂ (n+1))‖^2 - 2 * ⟪ A₂ (x₂ (n+1) - x₂ (n)), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫ + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      := by ring_nf
   rw [this, norm_abs, ← norm_sub_sq_real]
   apply pow_two_nonneg

lemma M_le [Setting E₁ E₂ F admm admm_kkt](n : ℕ+)(htau : 0 < τ ∧ τ ≤ 1 ): 2 * M (n + 1) ≤ (1 - τ) * ρₙ (n) * ‖A₂ (x₂ n - x₂ (n + 1))‖^2 + (1 - τ) * ρₙ (n) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2 := by
   have : (1 - τ) * ρₙ (n ) * ‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
         + (1 - τ) * ρₙ (n ) * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
         = (1 - τ) * ρₙ (n ) * (‖A₂ (x₂ n - x₂ (n + 1))‖ ^ 2
         + ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 ) := by ring
   rw [this]
   have : 2 * M (n + 1) =  (1 - τ) * ρₙ (n ) * ( 2 * ⟪ A₂ (x₂ (n + 1) - x₂ (n)), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫ ) := by
      dsimp [M]
      ring_nf
   rw [this]
   apply mul_le_mul_of_nonneg_left (basic_inequ₁' n)
   have : 0 ≤ 1 - τ := by linarith [htau.1]
   apply mul_nonneg
   · exact this
   linarith [admm.hρₙ_pos (n)]

lemma τ_segment [Setting E₁ E₂ F admm admm_kkt] : (0 < τ ∧ τ ≤ 1) ∨ τ > 1 := by
   rcases admm.htau with ⟨h1, _⟩
   by_cases h: τ ≤ 1
   ·  left;exact ⟨h1, h⟩
   ·  right;linarith

lemma τ_min1_1 [Setting E₁ E₂ F admm admm_kkt] (h: 0 < τ ∧ τ ≤ 1) : min τ (1 + τ - τ ^ 2) = τ := by
   rcases h with ⟨h1, h2⟩
   apply min_eq_left
   have h3: τ ^ 2 ≤ 1 := by
      apply pow_le_one₀;linarith;linarith
   linarith

lemma τ_min1_2 [Setting E₁ E₂ F admm admm_kkt] (h: τ > 1 ) : min τ (1 + τ - τ ^ 2) = 1 + τ - τ ^ 2 := by
   apply min_eq_right
   have : 1 < τ ^ 2 := by
      apply one_lt_pow₀;exact h;linarith
   linarith

lemma τ_min2_1 [Setting E₁ E₂ F admm admm_kkt] (h: 0 < τ ∧ τ ≤ 1) : min 1 (1 + 1 / τ - τ ) = 1 := by
   rcases h with ⟨h1, h2⟩
   apply min_eq_left
   have h3: τ ≤ 1 / τ :=
   calc
      _ ≤ 1 := h2
      _ ≤ 1 / τ := by
         apply one_le_one_div h1 h2
   linarith

lemma τ_min2_2 [Setting E₁ E₂ F admm admm_kkt] (h: τ > 1 ) : min 1 (1 + 1 / τ - τ ) = 1 + 1 / τ - τ  := by
   apply min_eq_right
   have : τ > 1 / τ :=
   calc
      _ > 1 := h
      _ > 1 / τ := by
         rw [one_div, ← inv_one];apply inv_strictAnti₀;linarith;exact h
   linarith

lemma τ_min3_1 [Setting E₁ E₂ F admm admm_kkt] (h: 0 < τ ∧ τ ≤ 1) : max (1 - τ) (1 - 1 / τ) = 1 - τ := by
   rcases h with ⟨h1, h2⟩
   apply max_eq_left
   have h3: τ ≤ 1 / τ :=
   calc
      _ ≤ 1 := h2
      _ ≤ 1 / τ := by
         apply one_le_one_div h1 h2
   linarith

lemma τ_min3_2 [Setting E₁ E₂ F admm admm_kkt] (h: τ > 1) : max (1 - τ) (1 - 1 / τ) = 1 - 1 / τ  := by
   apply max_eq_right
   have : τ > 1 / τ :=
   calc
      _ > 1 := h
      _ > 1 / τ := by
         rw [one_div, ← inv_one];apply inv_strictAnti₀;linarith;exact h
   linarith

lemma basic_inequ₂ (n : ℕ+) : - 2 * ⟪ A₂ (x₂ (n+1) - x₂ n), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫
      ≤ τ * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 + 1 / τ * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2 := by
   rw [← sub_nonneg]
   have h : τ ≥ 0 := by
      rcases admm.htau with ⟨h₁, _⟩
      linarith
   have h₁ : √τ ^2 = τ := by
      apply Real.sq_sqrt
      assumption
   have h₂ : (τ)⁻¹ = (√τ)⁻¹ ^2 := by
      nth_rw 1[←h₁]; rw [inv_pow]
   rw [div_eq_inv_mul, mul_one, h₂]
   nth_rw 1[←h₁]
   let S1 := A₂ (x₂ (n+1) - x₂ n)
   let S2 := A₁ (x₁ n) + A₂ (x₂ n) - b
   let s1 := √τ
   have h1 : s1 ^2 * ‖S1‖^2 = ‖s1 • S1‖ ^2 := by rw [norm_smul, mul_pow]; simp only [Real.norm_eq_abs,sq_abs]
   have h2 : s1⁻¹ ^2 * ‖S2‖^2 = ‖s1⁻¹ • S2‖ ^2 := by rw [norm_smul, mul_pow]; simp only [inv_pow, norm_inv, Real.norm_eq_abs, sq_abs]
   have : s1 ≠ 0 := by
      have h₃ : s1 = √τ := by rfl
      rw [h₃]
      apply Real.sqrt_ne_zero'.mpr
      rcases admm.htau with ⟨h₁, _⟩
      assumption
   have h3 : inner (𝕜 := ℝ) S1 S2 = inner (𝕜 := ℝ) (s1 • S1) (s1⁻¹ • S2) := by rw [inner_smul_left, inner_smul_right]; rw [← mul_assoc]; simp; rw [mul_inv_cancel₀, one_mul]; exact this
   rw [h1, h2, h3]
   have : ‖s1 • S1‖ ^ 2 + ‖s1⁻¹ • S2‖ ^ 2 - -2 * ⟪s1 • S1, s1⁻¹ • S2⟫_ℝ = ‖s1 • S1‖ ^ 2 + 2 * ⟪s1 • S1, s1⁻¹ • S2⟫_ℝ + ‖s1⁻¹ • S2‖ ^ 2 := by ring_nf
   rw [this, ←norm_add_sq_real]
   apply pow_two_nonneg

set_option maxHeartbeats 200000 in
lemma HWY_eq34 [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
       ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 ≥
       ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n+1) - x₂ n)‖^2
       + 2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ A₁ (x₁ n) + A₂ (x₂ n) - b, (A₂ (x₂ n - x₂ (n+1))) ⟫  := by
   intro n
   have h := Φ_isdescending_inequ5 n
   have hτ_pos : 0 < τ := admm.htau.1
   have hρ_pos : 0 < ρₙ (n+1) := admm.hρₙ_pos (n+1)
   have hτρ_ne : τ * ρₙ (n+1) ≠ 0 := mul_ne_zero (ne_of_gt hτ_pos) (ne_of_gt hρ_pos)
   -- 使用 HWY_Lemma_3_2 改写 M(n+1)
   have hM : M (n+1) = (1 - τ) * ρₙ n * ⟪ (A₂ (x₂ (n+1) - x₂ n)), (A₁ (x₁ n) + A₂ (x₂ n) - b) ⟫ := by
     simp [M]
   -- 改写内积方向
   have hM' : M (n+1) = (1 - τ) * ρₙ n * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ (n+1) - x₂ n)) ⟫ := by
     rw [hM, real_inner_comm]
   -- 再改写减法方向
   have hM'' : 2 * M (n+1) = 2 * (1 - τ) * ρₙ n * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (-(A₂ (x₂ n - x₂ (n+1)))) ⟫ := by
     rw [hM']
     have : A₂ (x₂ (n+1) - x₂ n) = -(A₂ (x₂ n - x₂ (n+1))) := by simp
     rw [← this]
     ring

   have hM''' : 2 * M (n+1) = -2 * (1 - τ) * ρₙ n * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫ := by
     rw [hM'']
     rw [inner_neg_right]
     ring
   -- 两边同乘 τ * ρₙ(n+1) 并展开
   have h_expand : τ * ρₙ (n+1) * (1 / (τ * ρₙ (n+1)) * (‖ey n‖^2 - ‖ey (n+1)‖^2) - (2 - τ) * ρₙ (n+1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + 2 * M (n+1) - ρₙ (n+1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2 - ρₙ (n+1) * ‖A₂ (e₂ (n+1))‖^2 + ρₙ (n+1) * ‖A₂ (e₂ n)‖^2) ≥ 0 := by
     apply mul_nonneg (mul_nonneg (le_of_lt hτ_pos) (le_of_lt hρ_pos)) h
   -- 代入 M 的表达式并化简
   calc ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2
     = ‖ey n‖^2 + τ * ρₙ (n+1) * (ρₙ (n+1) * ‖A₂ (e₂ n)‖^2) := by ring
     _ ≥ ‖ey (n+1)‖^2 + τ * ρₙ (n+1) * (ρₙ (n+1) * ‖A₂ (e₂ (n+1))‖^2)
         + τ * ρₙ (n+1) * ((2 - τ) * ρₙ (n+1) * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2)
         + τ * ρₙ (n+1) * (ρₙ (n+1) * ‖A₂ (x₂ (n+1) - x₂ n)‖^2)
         + τ * ρₙ (n+1) * (-2 * M (n+1)) := by
       field_simp [hτρ_ne] at h_expand
       linarith only [h_expand]
     _ = ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
         + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
         + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n+1) - x₂ n)‖^2
         + 2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫ := by
       simp
       rw [hM''']
       simp
       ring


lemma HWY_Lemma_3_2 [Setting E₁ E₂ F admm admm_kkt] :
   ∀ n : ℕ+,
      ρₙ (n+1) * ⟪ (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫
      ≥ (1 - τ) * ρₙ n * ⟪(A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1)))⟫ := by
   intro n
   have h1 :
         ρₙ (n+1) *
         ⟪ (A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b), (A₂ (x₂ (n+1) - x₂ n)) ⟫
      ≤ (1 - τ) * ρₙ n *
         ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ (n+1) - x₂ n)) ⟫ := by
      simpa [M, real_inner_comm] using Φ_isdescending_inequ3 n
   have key :A₂ (x₂ (n+1) - x₂ n) = - A₂ (x₂ n - x₂ (n+1)) := by
         simp
   rw [key] at h1
   rw [inner_neg_right, inner_neg_right, mul_neg, mul_neg] at h1
   rw [neg_le_neg_iff] at h1
   exact ge_iff_le.1 h1




lemma T_minus_tau_positive [Setting E₁ E₂ F admm admm_kkt]: T_HWY - τ ≥ 3/8 := by
   simp only [T_HWY]
   have h : 2 - 1/2 * (1 + τ - τ^2) - τ = 1/2 * (τ^2 - 3*τ + 3) := by ring
   rw [h]
   have h2 : τ^2 - 3*τ + 3 = (τ - 3/2)^2 + 3/4 := by ring
   rw [h2]
   have h3 : (τ - 3/2)^2 ≥ 0 := sq_nonneg _
   linarith

lemma HWY_eq35 [Setting E₁ E₂ F admm admm_kkt] :
  ∀ n : ℕ+,
    2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫
  ≥ - τ * (T_HWY - τ) * (ρₙ n)^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
    - (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ n - x₂ (n+1))‖^2 := by
  intro n
  -- 记号简化
  set u := A₁ (x₁ n) + A₂ (x₂ n) - b
  set v := A₂ (x₂ n - x₂ (n+1))
  set ε := τ * (T_HWY - τ)
  -- 基本常数正性
  have hτ_pos : 0 < τ := admm.htau.1
  have hT_pos : 0 < T_HWY - τ := by linarith [T_minus_tau_positive]
  have hε_pos : 0 < ε := mul_pos hτ_pos hT_pos
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hsqrtε_ne : (Real.sqrt ε) ≠ 0 := Real.sqrt_ne_zero'.mpr hε_pos

  -- 缩放后的向量
  let xu := (Real.sqrt ε * ρₙ n) • u
  let yv := ((τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1)) • v
  -- set_option diagnostics true 这个怎么用
  -- Cauchy-Schwarz 推出目标不等式
  -- 1. ⟪x, y⟫ ≤ ‖x‖‖y‖
  have hCS : |⟪ xu, yv ⟫| ≤ ‖xu‖ * ‖yv‖ := by
    simpa using abs_real_inner_le_norm xu yv

  -- 2. AM-GM 变形：2‖x‖‖y‖ ≤ ‖x‖² + ‖y‖²
  have hAMGM : 2 * (‖xu‖ * ‖yv‖) ≤ ‖xu‖^2 + ‖yv‖^2 := by
    have := sq_nonneg (‖xu‖ - ‖yv‖)
    ring_nf at this
    linarith

  -- 3. -2⟪x,y⟫ ≤ 2|⟪x,y⟫|
  have hneg : -2 * (⟪ xu, yv ⟫ : ℝ) ≤ 2 * |⟪ xu, yv ⟫| := by
    have : -(⟪ xu, yv ⟫ : ℝ) ≤ |⟪ xu, yv ⟫| := neg_le_abs _
    linarith

  -- 4. 合并链式不等式
  have base : -2 * ⟪ xu, yv ⟫ ≤ ‖xu‖^2 + ‖yv‖^2 := by
    linarith [hneg, hCS, hAMGM]

  -- 左边变换：inner x y → inner u v
  have lhs_eq : 2 * ⟪ xu, yv ⟫ = 2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ u, v ⟫ := by
    simp only [xu, yv, inner_smul_left, inner_smul_right, starRingEnd_apply]
    field_simp [hsqrtε_ne]
    ring_nf
    simp
    ring_nf
  -- 右边展开成范数项
  have hx_sq : ‖xu‖^2 = ε * (ρₙ n)^2 * ‖u‖^2 := by
   --  have : xu = (Real.sqrt ε * ρₙ n) • u := rfl
    simp only [xu]
    simp only [norm_smul]
    -- simp only [sq_abs] 暂时没用
    simp only [Real.norm_eq_abs (Real.sqrt ε * ρₙ n)]
    have h1 : |Real.sqrt ε * ρₙ n| = Real.sqrt ε * ρₙ n := by
      apply abs_of_pos
      exact mul_pos (Real.sqrt_pos.mpr hε_pos) (admm.hρₙ_pos n)
    simp only [h1]
    have h2 : (Real.sqrt ε * ρₙ n * ‖u‖)^2 = (Real.sqrt ε * ρₙ n)^2 * ‖u‖^2 := by ring
    simp only [h2]
    have h3 : (Real.sqrt ε * ρₙ n)^2 = (Real.sqrt ε)^2 * (ρₙ n)^2 := by ring
    rw [h3, Real.sq_sqrt hε_nonneg]

  have hy_sq : ‖yv‖^2 = (τ * (1 - τ))^2 / ε * (ρₙ (n+1))^2 * ‖v‖^2 := by
    simp only [yv, norm_smul]
    simp only [Real.norm_eq_abs ((τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1))]
    have h1 : |(τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1)| ^ 2
        = (τ * (1 - τ))^2 / (Real.sqrt ε)^2 * (ρₙ (n+1))^2 := by
      field_simp [hsqrtε_ne]
      ring_nf
      simp
      ring_nf
      field_simp
    have h2 : (|(τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1)| * ‖v‖)^2 = |(τ * (1 - τ)) / Real.sqrt ε * ρₙ (n+1)|^2 * ‖v‖^2 := by ring_nf
    simp only [h2]
    rw [h1, Real.sq_sqrt hε_nonneg]
  -- 应用 base 不等式，并把左右两边写成题设形式
  have h4 : (τ * (1 - τ))^2 / ε * (ρₙ (n+1))^2 * ‖v‖^2 = (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖v‖^2 := by
    simp only [ε]
    field_simp
  have h5 : ε * (ρₙ n)^2 * ‖u‖^2 = τ * (T_HWY - τ) * (ρₙ n) ^2 * ‖u‖^2 := by
    simp only [ε]
  have h6 : ⟪ xu, yv ⟫ = ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ u, v ⟫ := by
    simp only [xu, yv, inner_smul_left, inner_smul_right, starRingEnd_apply]
    field_simp [hsqrtε_ne]
    ring_nf
    simp
    ring_nf
  have := base
  simp only [hx_sq, hy_sq] at this
  rw [h4] at this
  rw [h5] at this
  rw [h6] at this
  rw [← neg_le_neg_iff] at this
  linarith

lemma eq0 [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
  ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 = ‖A₂ (x₂ (n+1) - x₂ (n))‖^2 := by
    intro n
    have h : A₂ (x₂ (n) - x₂ (n+1)) = A₂ (x₂ n) - A₂ (x₂ (n+1)) := by
      simp
    have h2 : A₂ (x₂ n) - A₂ (x₂ (n+1))=  - A₂ (x₂ (n+1) - x₂ (n)) := by
      simp
    rw [h]
    rw [h2]
    rw [norm_neg]

lemma eq1 [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
 ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2≥
       ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
       + 2 * ρₙ n * ρₙ (n+1) * τ * (1 - τ) * ⟪ (A₁ (x₁ n) + A₂ (x₂ n) - b), (A₂ (x₂ n - x₂ (n+1))) ⟫ + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2:= by
   intro n
   rw [eq0 n]
   linarith [HWY_eq34 n]

lemma eq2 [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
   ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n)^2 * ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2≥
       ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
       - τ * (T_HWY - τ) * (ρₙ n)^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
    - (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
       + τ * (T_HWY - τ) * ρₙ (n)^2 * ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2:= by
      intro n
      linarith [(HWY_eq35 n),(eq1 n)]
-- lemma eq4 [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
--        τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
--        + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
--        - τ * (T_HWY - τ) * (ρₙ n)^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
--     - (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
--        + τ * (T_HWY - τ) * ρₙ (n)^2 * ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2 =
--        τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
--        + τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 )  :=by
--        intro n
--       --  rw[eq0 n]
--        ring_nf

lemma eq3 [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
      ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n)^2* ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2 ≥
       ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (T_HWY - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 )   := by
      intro n
      calc
         _ ≥‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
         + τ * (2 - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
         + τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
         - τ * (T_HWY - τ) * (ρₙ n)^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - (1 - τ)^2 / (T_HWY - τ) * τ * (ρₙ (n+1))^2 * ‖A₂ (x₂ (n) - x₂ (n+1))‖^2
         + τ * (T_HWY - τ) * ρₙ (n)^2 * ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2 :=by exact eq2 n
         _ = ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 ):= by ring_nf
lemma eq3'  [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
      ‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
      + τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
      ≤ ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2
      + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      -  τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 ):= by
         intro n
         have h : ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2
       + τ * (T_HWY - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2
       + τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 ) ≤ ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n)^2* ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2 := by exact eq3 n
         -- set D : ℝ := τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ (n) - x₂ (n+1))‖^2 ) with hD
         -- set L : ℝ := ‖ey (n+1)‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ (n+1))‖^2 + τ * (T_HWY - τ) * (ρₙ (n+1))^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 with hL
         -- set R : ℝ := ‖ey n‖^2 + τ * (ρₙ (n+1))^2 * ‖A₂ (e₂ n)‖^2 + τ * (T_HWY - τ) * ρₙ (n)^2* ‖A₁ (x₁ (n)) + A₂ (x₂ (n)) - b‖ ^ 2 with hR
         linarith  --我服了，表达式打错了，怪不得证不出来
         -- -- have h1 : L + D ≤ R := by exact h
         -- have h2 : L ≤ R - D := by linarith
         -- simp only [hD, hL, hR] at h2
         -- exact h2

lemma eq4'[Setting E₁ E₂ F admm admm_kkt] :T_HWY - τ = 1/2*(τ^2-3*τ+3):= by
      simp only [T_HWY]
      ring_nf


lemma eq4'' [Setting E₁ E₂ F admm admm_kkt] :  1 - (1 - τ)^2 / (1/2*(τ^2-3*τ+3)) = (τ^2 -3*τ +3- 2 *(1 - τ)^2) / (τ^2-3*τ+3):= by
   have hpos : 0 < (τ^2 - 3*τ + 3 : ℝ) := by
      have : (τ^2 - 3*τ + 3 : ℝ) = (τ - (3/2))^2 + (3/4) := by ring
      have hsq : 0 ≤ (τ - (3/2))^2 := by exact sq_nonneg _
      have h34 : 0 < (3/4 : ℝ) := by norm_num
      have h:= add_pos_of_nonneg_of_pos hsq h34
      rw [this]
      exact h
   field_simp [hpos]
   refine one_sub_div ?_
   linarith



lemma eq4 [Setting E₁ E₂ F admm admm_kkt] : 1 - (1 - τ)^2 / (T_HWY - τ) = (1 + τ - τ ^2) / ( 3 - 3 * τ +τ ^2) := by
    rw [eq4']
    rw [eq4'']
    ring_nf

lemma tau_quadratic_bounds [Setting E₁ E₂ F admm admm_kkt] :
  3/4 ≤ τ^2 - 3*τ + 3 ∧ τ^2 - 3*τ + 3 ≤ 3 := by
  constructor
  · -- 证明 3/4 ≤ τ^2 - 3*τ + 3
    have : τ^2 - 3*τ + 3 = (τ - 3/2)^2 + 3/4 := by ring
    rw [this]
    have : 0 ≤ (τ - 3/2)^2 := sq_nonneg _
    linarith
  · have h : τ^2 - 3*τ + 3 = (τ - 3/2)^2 + 3/4 := by ring
    rw [h]
    have : 0 ≤ (τ - 3/2)^2 := sq_nonneg _
    have h1 : 0 < τ := admm.htau.1
    have h2 : τ < (1 + Real.sqrt 5)/2 := admm.htau.2
    -- 先证明 (1 + √5)/2 ≤ 2
    have hsqrt : Real.sqrt (5:ℝ) ≤ 3 := by
      have hb : (0:ℝ) ≤ (3:ℝ) := by norm_num
      have h5le9 : (5:ℝ) ≤ (3:ℝ)^2 := by norm_num
      exact (Real.sqrt_le_left hb).mpr h5le9
   --  have hone_add_sqrt_le4 : 1 + Real.sqrt (5:ℝ) ≤ 4 := by
   --    have := add_le_add_left hsqrt 1
   --    linarith
   --  have hpos2 : (0:ℝ) < 2 := by norm_num
    have hup : (1 + Real.sqrt (5:ℝ)) / 2 ≤ (2:ℝ) := by
      -- (1 + √5)/2 ≤ 2  ↔  1 + √5 ≤ 4
      have : 1 + Real.sqrt (5:ℝ) ≤ 2 * 2 := by linarith
      linarith

    -- 得到 τ ≤ 2
    have hτ_le2 : τ ≤ 2 := le_trans (le_of_lt h2) hup

    -- 于是 |τ - 3/2| ≤ 3/2
    have hleft  : -(3/2 : ℝ) ≤ τ - 3/2 := by
      have : (0:ℝ) ≤ τ := le_of_lt h1
      linarith
    have hright : τ - 3/2 ≤ (3/2 : ℝ) := by
      have : τ ≤ 2 := hτ_le2
      linarith
    -- 平方并加上 3/4，得到 ≤ 3
    have hsq : (τ - 3/2)^2 ≤ (3/2 : ℝ)^2 := by
      exact sq_le_sq' hleft hright
      -- |a| ≤ b ⇒ a^2 ≤ b^2
    have : (τ - 3/2)^2 + 3/4 ≤ (3/2 : ℝ)^2 + 3/4 :=
      add_le_add_right hsq _
    -- (3/2)^2 + 3/4 = 9/4 + 3/4 = 3
    linarith

lemma thm3_1_ineq1 [Setting E₁ E₂ F admm admm_kkt] :
  1 - (1 - τ)^2 / (T_HWY - τ) ≥ (1/3 : ℝ) * (1 + τ - τ^2) := by
  rw [eq4]
  rcases tau_quadratic_bounds with ⟨h1, h2⟩
  -- 设 D = τ^2 - 3τ + 3
  set D : ℝ := τ^2 - 3*τ + 3 with hD

  -- D > 0 且 D ≤ 3
  have hD_pos : 0 < D := by
    have : (0 : ℝ) < 3/4 := by norm_num
    exact lt_of_lt_of_le this (by simpa [hD] using h1)
  have hD_le3 : D ≤ 3 := by simpa [hD] using h2

  -- 得到 1/3 ≤ 1/D
  have inv_ge : (1/3 : ℝ) ≤ 1 / D := by
    -- one_div_le_one_div_of_le : 0 < a → a ≤ b → 1/b ≤ 1/a
    -- 取 a = D, b = 3
    simpa [one_div] using (one_div_le_one_div_of_le hD_pos hD_le3)

  -- 分子非负（把严格不等式放宽）
  have hA_nonneg : 0 ≤ 1 + τ - τ^2 := (admm.htau_range).le

  -- 乘以非负分子
  have hmul := mul_le_mul_of_nonneg_left inv_ge hA_nonneg
  -- 整理成目标样式
  simp only [hD] at hmul
  field_simp at hmul
  field_simp
  have h: 3*(1-τ) + τ^2 = τ*(τ-3) + 3:= by ring
  rw [← h] at hmul
  linarith



lemma thm3_1_eq1 [Setting E₁ E₂ F admm admm_kkt] : 2-T_HWY = 1/2*(1+τ-τ^2):= by
  rw [T_HWY]
  ring_nf

lemma thm3_1_ineq3 [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
   - τ * (ρₙ (n+1))^2 * ((1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) ≤
   - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
         (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := by
   intro n
   have h : τ * (ρₙ (n+1))^2 > 0 := by exact mul_pos (admm.htau.1) (pow_pos (admm.hρₙ_pos (n+1)) 2)
   have hA_nonneg : 0 ≤  1 + τ - τ^2 := (admm.htau_range).le
   -- have h4 :1/2 ≤ 1/3 := by norm_num
   -- set D : ℝ := 1/2*(1+τ-τ^2) with hD
   -- set L : ℝ := ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 with hL
   -- have h3 : 1/2* ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 ≥  1/3 *  ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2:= by
   --    gcongr
   --    norm_num
   have h2 : 1/2*(1+τ-τ^2) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 ≥ 1/3 * (1 + τ - τ^2)* ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2:= by
      gcongr
      norm_num
   have h4 : (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ≥ 1/3 * (1 + τ - τ^2)* ‖A₂ (x₂ n - x₂ (n+1))‖^2:= by
      gcongr
      linarith [thm3_1_ineq1]
   have h1 : (1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ≥ (1/3) * (1 + τ - τ^2)*(‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
      linarith [h2, h4]
   have h5 : - ((1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) ≤  -(1/3) * (1 + τ - τ^2)*(‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
      linarith [h1]
   have h6 := mul_le_mul_of_nonneg_left h5 (le_of_lt h)
   linarith [h6] --神之一手


-- lemma thm3_1_ineq2 [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
--       ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2
--        + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
--        - τ * (ρₙ (n+1))^2 * ((1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) ≥
--        ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2
--         + τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
--        - τ * (ρₙ (n+1))^2 * ((1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + 1/3 * (1 + τ - τ^2)* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) := by
--         intro n
--         linarith [thm3_1_ineq1]

theorem HWY_Theorem_3_1 [Setting E₁ E₂ F admm admm_kkt] : ∀ n : ℕ+,
‖ey (n+1)‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ (n+1))‖^2
+ τ * (T_HWY - τ) * ρₙ (n+1)^2 * ‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2
≤ ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2
+ τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
- (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 * (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2) := by
   intro n
   calc _ ≤ ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2 +
      τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - τ * (ρₙ (n+1))^2 * ((2-T_HWY) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2+(1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) := by exact eq3' n
       _ = ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2 +
      τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
       - τ * (ρₙ (n+1))^2 * ((1/2*(1+τ-τ^2)) *‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖ ^ 2 + (1- (1 - τ)^2 / (T_HWY - τ))* ‖A₂ (x₂ n - x₂ (n+1))‖^2 ) := by simp [thm3_1_eq1]
       _ ≤  ‖ey n‖^2 + τ * ρₙ (n+1)^2 * ‖A₂ (e₂ n)‖^2 +
      τ * (T_HWY - τ) * ρₙ n^2 * ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2
      - (1/3) * (1 + τ - τ^2) * τ * ρₙ (n+1)^2 *
         (‖A₁ (x₁ (n+1)) + A₂ (x₂ (n+1)) - b‖^2 + ‖A₂ (x₂ n - x₂ (n+1))‖^2):= by
        linarith [thm3_1_ineq3 n]

lemma HWY_thm4_1_ineq [Setting E₁ E₂ F admm admm_kkt] :T_HWY - τ >0 := by
   rw[eq4']
   have hpos : 0 < (τ^2 - 3*τ + 3 : ℝ) := by
      have : (τ^2 - 3*τ + 3 : ℝ) = (τ - (3/2))^2 + (3/4) := by ring
      have hsq : 0 ≤ (τ - (3/2))^2 := by exact sq_nonneg _
      have h34 : 0 < (3/4 : ℝ) := by norm_num
      have h:= add_pos_of_nonneg_of_pos hsq h34
      rw [this]
      exact h
   linarith
-- lemma rho_change_term [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
--       ρₙ n * ‖A₂ (e₂ n)‖^2 - ρₙ (n+1) * ‖A₂ (e₂ (n+1))‖^2
--       ≤ ρₙ (n+1) * (‖A₂ (e₂ n)‖^2 - ‖A₂ (e₂ (n+1))‖^2)
--       + (ρₙ n - ρₙ (n+1)) * ‖A₂ (e₂ n)‖^2 := by
--    intro n
--    -- 展开右边：这实际上是一个等式
--    have : ρₙ (n+1) * (‖A₂ (e₂ n)‖^2 - ‖A₂ (e₂ (n+1))‖^2) + (ρₙ n - ρₙ (n+1)) * ‖A₂ (e₂ n)‖^2
--         = ρₙ n * ‖A₂ (e₂ n)‖^2 - ρₙ (n+1) * ‖A₂ (e₂ (n+1))‖^2 := by ring
--    rw [← this]

-- 辅助引理：ey项的变化（考虑ρ变化）
-- lemma ey_change_with_rho [Setting E₁ E₂ F admm admm_kkt]: ∀ n : ℕ+,
--       1 / (τ * ρₙ n) * ‖ey n‖^2 - 1 / (τ * ρₙ (n+1)) * ‖ey (n+1)‖^2
--       = 1 / (τ * ρₙ (n+1)) * (‖ey n‖^2 - ‖ey (n+1)‖^2)
--       + ‖ey n‖^2 * (1/(τ * ρₙ n) - 1/(τ * ρₙ (n+1))) := by
--    intro n
--    ring



end AdaptiveADMM_Convergence_Proof
