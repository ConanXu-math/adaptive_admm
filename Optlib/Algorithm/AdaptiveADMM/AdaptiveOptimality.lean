import Optlib.Algorithm.AdaptiveADMM.AdaptiveDefinitions
import Optlib.Algorithm.AdaptiveADMM.SequenceConvergence

noncomputable section
open Set InnerProductSpace Topology Filter InnerProduct
open scoped Pointwise

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F ]

namespace AdaptiveADMM_Convergence_Proof

variable {admm : ADMM E₁ E₂ F} {admm_kkt : KKTPoint admm}

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

local notation "x₁'" => admm_kkt.x₁
local notation "x₂'" => admm_kkt.x₂
local notation "y'"  => admm_kkt.y

local notation "A₁†" => ContinuousLinearMap.adjoint A₁
local notation "A₂†" => ContinuousLinearMap.adjoint A₂
local notation "⟪" a₁ ", " a₂ "⟫" => @inner ℝ _ _ a₁ a₂

local notation "e₁" => AdaptiveADMM_Convergence_Proof.e₁ admm admm_kkt
local notation "e₂" => AdaptiveADMM_Convergence_Proof.e₂ admm admm_kkt
local notation "ey" => AdaptiveADMM_Convergence_Proof.ey admm admm_kkt
local notation "g1" => AdaptiveADMM_Convergence_Proof.g1 admm admm_kkt
local notation "g2" => AdaptiveADMM_Convergence_Proof.g2 admm admm_kkt
local notation "u" => AdaptiveADMM_Convergence_Proof.u admm admm_kkt
local notation "v" => AdaptiveADMM_Convergence_Proof.v admm admm_kkt
local notation "Ψ" => AdaptiveADMM_Convergence_Proof.Ψ admm admm_kkt
local notation "Φ" => AdaptiveADMM_Convergence_Proof.Φ admm admm_kkt
local notation "T_HWY" => AdaptiveADMM_Convergence_Proof.T_HWY admm
local notation "υ" => AdaptiveADMM_Convergence_Proof.υ admm

lemma f₁_continuous : ContinuousOn f₁ univ :=
   FiniteDimensionalConvexFunctionsContinous convex_univ isOpen_univ OptProblem.cf₁

lemma f₂_continuous : ContinuousOn f₂ univ :=
   FiniteDimensionalConvexFunctionsContinous convex_univ isOpen_univ OptProblem.cf₂

lemma inner_convex1 :∀ n : ℕ+ ,
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

lemma inner_convex2 :∀ n : ℕ+ ,
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
         intro a₀ b₀
         simp only [map_add]
         rw[inner_add_right]
      map_smul' := by
         intro a₀ b₀
         simp only [LinearMapClass.map_smul, RingHom.id_apply, smul_eq_mul]
         apply inner_smul_right
   }
   show ConvexOn ℝ univ f
   apply LinearMap.convexOn
   apply convex_univ

-- ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2
lemma norm_covex1 :∀ n : ℕ+ ,
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
   let quadratic := fun x => ‖x - c‖ ^ 2 / 2
   let g := A₁
   have h2 : quadratic ∘ g = f := by
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

lemma norm_covex2 :∀ n : ℕ+ ,
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
   let quadratic := fun x => ‖x - c‖ ^ 2 / 2
   let g := A₂
   have h2 : quadratic ∘ g = f := by
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

lemma ADMM_iter_process₁'_eq3_1'  : ∀ n : ℕ+ ,
      HasGradientAt (fun _ => f₂ (x₂ n.natPred)) 0 (x₁ n) := by
   intro n
   apply hasGradientAt_const
lemma ADMM_iter_process₁'_eq3_1 : ∀ n : ℕ+ ,
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

lemma ADMM_iter_process₁'_eq3_2'_1 (c : F) :∀ x,
      HasGradientAt ((fun x => ⟪c , (A₁ x)⟫)) (A₁† c) x := by
   apply inner_gradient

lemma ADMM_iter_process₁'_eq3_2' : ∀ n : ℕ+ , ∀ x ,
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

lemma inner_continuous1 :∀ n : ℕ+ ,
      ContinuousOn (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) univ:= by
   intro n
   have :∀ x ∈ univ,HasGradientAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (A₁† (y n.natPred)) x := by
      intro x _
      apply ADMM_iter_process₁'_eq3_2' n
   apply HasGradientAt.continuousOn
   exact this

lemma ADMM_iter_process₁'_eq3_2 : ∀ n : ℕ+ ,
      SubderivAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (x₁ n) = { A₁† (y n.natPred)} := by
   intro n
   apply SubderivAt_eq_gradient (inner_convex1 n)
   apply ADMM_iter_process₁'_eq3_2'

lemma norm_comm {α β: Type*}
      [NormedAddCommGroup α] [InnerProductSpace ℝ α]
      [NormedAddCommGroup β] [InnerProductSpace ℝ β]
      (A : α →L[ℝ] β) (a₁ a₂ : α): ‖A (a₁ - a₂)‖ =‖A (a₂ - a₁)‖ := by
   rw [map_sub, map_sub , ←neg_sub (A a₂) (A a₁)]; apply norm_neg

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

lemma ADMM_iter_process₁'_eq3_3' : ∀ n : ℕ+ ,
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
      : ∀ n : ℕ+ ,
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) (x₁ n) = {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))} := by
   intro n
   apply SubderivAt_eq_gradient (norm_covex1 n)
   apply ADMM_iter_process₁'_eq3_3'

lemma ADMM_iter_process₁'_eq2_1'
       : ∀ n : ℕ+ ,
      (fun x => (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x , x₂ n.natPred , y n.natPred)) =
      (fun x => (f₁ x) + (f₂ (x₂ n.natPred))+ ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫ + ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) := by
   intro n
   rfl


lemma ADMM_iter_process₁'_eq2_1'_1 : ∀ n : ℕ+ ,
      (fun x => (f₁ x) + (f₂ (x₂ n.natPred))+ ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫ + ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2)
      = f₁ + (fun _ => f₂ (x₂ n.natPred)) + (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) + (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2)
      := by
   intro n
   congr


--(@continuousOn_const E₁ ℝ _ _ univ (f₂ (x₂ n.natPred)) )

lemma ADMM_iter_process₁'_eq2_1 : ∀ n : ℕ+ ,
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

lemma ADMM_iter_process₁'_eq2_2 : ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + SubderivAt (fun _ => f₂ (x₂ n.natPred)) (x₁ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ x) + (A₂ (x₂ n.natPred)) - b⟫) (x₁ n) +
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ x) + (A₂ (x₂ n.natPred)) - b‖ ^ 2) (x₁ n) =
      SubderivAt f₁ (x₁ n) + 0 + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}:= by
   intro n
   rw[ADMM_iter_process₁'_eq3_1 n,ADMM_iter_process₁'_eq3_2 n,ADMM_iter_process₁'_eq3_3 n]

lemma ADMM_iter_process₁'_eq2_3 : ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + 0 + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}
      = SubderivAt f₁ (x₁ n) + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}:= by
   intro n
   rw[add_zero]

lemma ADMM_iter_process₁'_eq1 : ∀ n : ℕ+ ,
      SubderivAt f₁ (x₁ n) + { A₁† (y n.natPred)} + {ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ n.natPred) - b))}
      = SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x , x₂ n.natPred , y n.natPred)) (x₁ n):=by
   intro n
   rw[← ADMM_iter_process₁'_eq2_3 n,← ADMM_iter_process₁'_eq2_2 n,← ADMM_iter_process₁'_eq2_1 n]

lemma ADMM_iter_process₁' : ∀ n : ℕ+ ,0 ∈
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


lemma ADMM_iter_process₁ : ∀ n : ℕ+ ,
      ( - A₁† (y (n - 1)) - ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ (n - 1)) - b))) ∈ SubderivAt f₁ (x₁ n) := by
   intro n
   let S := SubderivAt f₁ (x₁ n)
   let p := A₁† (y (n - 1))
   let q := ρₙ n • (A₁† (A₁ (x₁ n) + A₂ (x₂ (n - 1)) - b))
   show - p - q ∈ S
   have := ADMM_iter_process₁' (admm := admm) n
   change 0 ∈ S + {p} + {q} at this
   apply change_item this

lemma ADMM_iter_process₂'_eq3_1'  : ∀ n : ℕ+ ,
      HasGradientAt (fun _ => f₁ (x₁ n)) 0 (x₂ n) := by
   intro n
   apply hasGradientAt_const

lemma ADMM_iter_process₂'_eq3_1 : ∀ n : ℕ+ ,
      SubderivAt (fun _ => f₁ (x₁ n)) (x₂ n) = 0 := by
   intro n
   apply SubderivAt_eq_gradient (convexOn_const (f₁ (x₁ n)) (convex_univ))
   apply ADMM_iter_process₂'_eq3_1'

lemma ADMM_iter_process₂'_eq3_2' : ∀ n : ℕ+ , ∀ x ,
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

lemma inner_continuous2 :∀ n : ℕ+ ,
      ContinuousOn (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) univ:= by
   intro n
   have :∀ x ∈ univ,HasGradientAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (A₂† (y n.natPred)) x := by
      intro x _
      apply ADMM_iter_process₂'_eq3_2' n
   apply HasGradientAt.continuousOn
   exact this

lemma ADMM_iter_process₂'_eq3_2 : ∀ n : ℕ+ ,
      SubderivAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (x₂ n) = { A₂† (y n.natPred)} := by
   intro n
   apply SubderivAt_eq_gradient (inner_convex2 n)
   apply ADMM_iter_process₂'_eq3_2'

lemma ADMM_iter_process₂'_eq3_3'
   : ∀ n : ℕ+ ,
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

lemma ADMM_iter_process₂'_eq3_3 : ∀ n : ℕ+ ,
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) (x₂ n) = {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))} := by
   intro n
   apply SubderivAt_eq_gradient (norm_covex2 n)
   apply ADMM_iter_process₂'_eq3_3'

lemma ADMM_iter_process₂'_eq2_1' : ∀ n : ℕ+ ,
      (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x₁ n , x , y n.natPred)) =
      (fun x => f₁ (x₁ n) + (f₂ x) + ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫ + ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) := by
   intro n
   rfl

lemma ADMM_iter_process₂'_eq2_1'_1 : ∀ n : ℕ+ ,
      (fun x => f₁ (x₁ n) + (f₂ x)+ ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫ + ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2)
      = (fun _ => f₁ (x₁ n)) + f₂ + (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) + (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2):= by
   intro n
   congr

lemma ADMM_iter_process₂'_eq2_1 : ∀ n : ℕ+ ,
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
lemma ADMM_iter_process₂'_eq2_2 : ∀ n : ℕ+ ,
      SubderivAt (fun _ => f₁ (x₁ n)) (x₂ n) + SubderivAt f₂ (x₂ n) +
      SubderivAt (fun x => ⟪y n.natPred , (A₁ (x₁ n)) + (A₂ x) - b⟫) (x₂ n) +
      SubderivAt (fun x => ρₙ n / 2 * ‖(A₁ (x₁ n)) + (A₂ x) - b‖ ^ 2) (x₂ n) =
      0 + SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   rw[ADMM_iter_process₂'_eq3_1 n,ADMM_iter_process₂'_eq3_2 n,ADMM_iter_process₂'_eq3_3 n]

lemma ADMM_iter_process₂'_eq2_3 : ∀ n : ℕ+ ,
      0 + SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}
      = SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   rw[zero_add]

lemma ADMM_iter_process₂'_eq1 : ∀ n : ℕ+ ,
      SubderivAt f₂ (x₂ n) + { A₂† (y n.natPred)} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}
      = SubderivAt (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x₁ n , x , y n.natPred)) (x₂ n):=by
   intro n
   rw[← ADMM_iter_process₂'_eq2_3 n,← ADMM_iter_process₂'_eq2_2 n , ← ADMM_iter_process₂'_eq2_1 n]

lemma ADMM_iter_process₂' : ∀ n : ℕ+ , 0 ∈
      SubderivAt f₂ (x₂ n) + { A₂† (y (n - 1))} + {ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) - b))}:= by
   intro n
   have := first_order_convex_iff_subgradient (f := (fun x ↦ (Augmented_Lagrangian_Function E₁ E₂ F admm.toOptProblem (ρₙ n)) (x₁ n , x , y n.natPred))) (x₂ n)
   have h := admm.itex₂ n.natPred
   have eq : n.natPred + 1 = n := by apply PNat.natPred_add_one
   rw[eq , this , ← ADMM_iter_process₂'_eq1 n] at h
   exact h

lemma ADMM_iter_process₂  : ∀ n : ℕ+ ,
      (- A₂† (y (n - 1))- ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) -b))) ∈ SubderivAt f₂ (x₂ n) := by
   intro n
   let S := SubderivAt f₂ (x₂ n)
   let p := A₂† (y (n - 1))
   let q := ρₙ n • (A₂† (A₁ (x₁ n) + A₂ (x₂ n) -b))
   show - p - q ∈ S
   have := ADMM_iter_process₂' (admm := admm) n
   change 0 ∈ S + {p} + {q} at this
   apply change_item this

lemma u_inthesubgradient : ∀ n : ℕ+ , u n ∈ SubderivAt f₁ (x₁ n) := by
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

lemma v_inthesubgradient : ∀ n : ℕ+ , v n ∈ SubderivAt f₂ (x₂ n) := by
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


end AdaptiveADMM_Convergence_Proof
