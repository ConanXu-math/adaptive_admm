import Optlib.Algorithm.AdaptiveADMM.BoundednessC1
noncomputable section

open Set InnerProductSpace Topology Filter Bornology Metric Real

variable {E₁ E₂ F : Type*}
[NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
[NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
[NormedAddCommGroup F ] [InnerProductSpace ℝ F ] [FiniteDimensional ℝ F]

variable(admm : ADMM E₁ E₂ F)

namespace AdaptiveADMM_Convergence_Proof

variable {admm} (admm_kkt : KKTPoint admm)

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

include admm_kkt

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
local notation "η_k" => AdaptiveADMM_Convergence_Proof.η_k admm
local notation "Q_seq_c1" => AdaptiveADMM_Convergence_Proof.Q_seq_c1 admm
variable (fullrank₁: Function.Injective admm.A₁) (fullrank₂: Function.Injective admm.A₂)
-- Subsequence mapping
local notation "φ" => Converge_Subseq_1.φ (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

-- The limit of the subsequence
local notation "x₁''" => Converge_Subseq_1.x₁'' (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
local notation "x₂''" => Converge_Subseq_1.x₂'' (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
local notation "y''"  => Converge_Subseq_1.y'' (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)

-- The subsequence mapping is strictly increasing
lemma hphi_StrictMono_c1 [Condition_C1 admm] : StrictMono φ := (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂).hphi

--lim_{n → ∞} (uₙ ,vₙ ) = 0 -> lim_{n → ∞} uₙ  = 0
lemma admm_nhds_prod_eq_c1 [Condition_C1 admm] : 𝓝 (x₁'' , x₂'' , y'') = 𝓝 x₁'' ×ˢ 𝓝 x₂'' ×ˢ 𝓝 y'' := by
   rw[nhds_prod_eq,nhds_prod_eq]

lemma hconverge_c1 [Condition_C1 admm]  : Tendsto (fun n => (x₁ (φ n),  x₂ (φ n), y (φ n)))
atTop (𝓝 x₁'' ×ˢ 𝓝 x₂'' ×ˢ 𝓝 y''):=by
   have := (Subseq_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂).hconverge
   rw[admm_nhds_prod_eq_c1 (admm_kkt := admm_kkt)] at this
   exact this

lemma x₁_subseq_converge_c1 [Condition_C1 admm] : Tendsto (fun n => (x₁ (φ n)))  atTop (𝓝 x₁'') :=
   (Filter.tendsto_prod_iff'.1 (hconverge_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)).1

lemma x₂_subseq_converge_c1 [Condition_C1 admm] : Tendsto (fun n => (x₂ (φ n)))  atTop (𝓝 x₂'') :=
   (Filter.tendsto_prod_iff'.1 (Filter.tendsto_prod_iff'.1 (hconverge_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)).2).1

lemma y_subseq_converge_c1  [Condition_C1 admm] : Tendsto (fun n => (y (φ n)))  atTop (𝓝 y'') :=
   (Filter.tendsto_prod_iff'.1 (Filter.tendsto_prod_iff'.1 (hconverge_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)).2).2

def φ₁' [Condition_C1 admm] : ℕ → ℕ+ := by
   intro n
   exact (φ (n + 1)).toPNat'

local notation "φ₁" => φ₁' (admm_kkt := admm_kkt) fullrank₁ fullrank₂

lemma φ₁_equ_c1 [Condition_C1 admm] : ∀ n : ℕ , φ₁ n = φ (n + 1) := by
   intro n
   have : φ (n + 1) > 0 := by
      calc φ (n + 1)
         _ ≥ n + 1  := StrictMono.id_le (hphi_StrictMono_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (n + 1)
         _ > 0      :=by linarith
   exact Nat.sub_one_add_one_eq_of_pos this

-- lim_{ n → ∞} x_n  = x =>  lim_{ n → ∞} x_{n+1}  = x
lemma x₁_subseq_converge'_c1 [Condition_C1 admm] : Tendsto (fun n => (x₁ (φ₁ n)))  atTop (𝓝 x₁'') :=by
   have : (fun n => x₁ (φ₁ n)) = (fun n => (x₁ (φ (n+1)))) :=by
      ext n;rw[φ₁_equ_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ x₁ (φ n)) ) 1]
   apply x₁_subseq_converge_c1 (admm_kkt := admm_kkt)

lemma x₂_subseq_converge'_c1 [Condition_C1 admm]  : Tendsto (fun n => (x₂ (φ₁ n)))  atTop (𝓝 x₂'') :=by
   have : (fun n => x₂ (φ₁ n)) = (fun n => (x₂ (φ (n+1)))) :=by
      ext n;rw[φ₁_equ_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ x₂ (φ n)) ) 1]
   apply x₂_subseq_converge_c1 (admm_kkt := admm_kkt)

lemma y_subseq_converge'_c1 [Condition_C1 admm] : Tendsto (fun n => (y (φ₁ n))) atTop (𝓝 y'') := by
   have : (fun n => y (φ₁ n)) = (fun n => (y (φ (n+1)))) := by
      ext n; rw [φ₁_equ_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ n]
   rw[this , Filter.tendsto_add_atTop_iff_nat (f := (fun n ↦ y (φ n)) ) 1]
   apply y_subseq_converge_c1 (admm_kkt := admm_kkt)
omit admm_kkt in
lemma square_converge_zero₁_c1 [Condition_C1 admm]  (h : Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ ^ 2)  atTop (𝓝 0)) :
   Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₁ (x₁ n) + A₂ (x₂ n) - b‖)^2))  atTop (𝓝 √0) := by apply Filter.Tendsto.sqrt h
   rw [Real.sqrt_zero] at this; simp at this; exact this

-- ‖A₁ (e₁ n) + A₂ (e₂ n)‖ → 0
theorem HWY_Convergence_1_residual_c1 [Condition_C1 admm]:
    Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖^2) atTop (nhds 0) := by
  have h_nplus1 := (HWY_Convergence_1_residual' (admm := admm) (admm_kkt := admm_kkt))
  rw [← tendsto_add_atTop_iff_nat 1]
  exact h_nplus1


lemma converge_zero₁_c1 [Condition_C1 admm]: Tendsto (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖)  atTop (𝓝 0) := by
   have eq : (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖) = (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖) := by
      funext n
      have : A₁ (e₁ n) + A₂ (e₂ n) = A₁ (x₁ n) + A₂ (x₂ n) - b := by
         rw [ AdaptiveADMM_Convergence_Proof.e₁, AdaptiveADMM_Convergence_Proof.e₂]; simp
         calc
            _ = A₁ (x₁ n) + A₂ (x₂ n) - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_sub_comm]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b + b - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_cancel]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b := by
               rw [admm_kkt.h.eq]; simp
      rw [this]
   rw [eq]
   have := HWY_Convergence_1_residual_c1 (admm_kkt := admm_kkt)
   apply square_converge_zero₁_c1 this

-- ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖ → 0
lemma converge_zero₂_c1 [Condition_C1 admm] : Tendsto (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖)  atTop (𝓝 0) := by
   have eq : (fun n => ‖A₁ (e₁ n) + A₂ (e₂ n)‖) = (fun n => ‖A₁ (x₁ n) + A₂ (x₂ n) - b‖) := by
      funext n
      have : A₁ (e₁ n) + A₂ (e₂ n) = A₁ (x₁ n) + A₂ (x₂ n) - b := by
         rw [ AdaptiveADMM_Convergence_Proof.e₁, AdaptiveADMM_Convergence_Proof.e₂]; simp
         calc
            _ = A₁ (x₁ n) + A₂ (x₂ n) - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_sub_comm]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b + b - ((A₁ x₁') + (A₂ x₂')) := by rw [sub_add_cancel]
            _ = A₁ (x₁ n) + A₂ (x₂ n) - b := by
               rw [admm_kkt.h.eq]; simp
      rw [this]
   rw [← eq]
   exact converge_zero₁_c1 (admm_kkt := admm_kkt)

-- with the square norm of A₂ (x₂ (n + 1) - x₂ n) → 0, we can infer that the norm of A₂ (x₂ (n + 1) - x₂ n) also → 0
omit admm_kkt in
lemma square_converge_zero₃_c1 [Condition_C1 admm] (h : Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖ ^ 2)  atTop (𝓝 0)) :
   Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => √((‖A₂ (x₂ (n + 1) - x₂ n)‖)^2))  atTop (𝓝 √0) := by apply Filter.Tendsto.sqrt h
   rw [Real.sqrt_zero] at this; simp [Real.sqrt_sq] at this; simp; exact this

-- the norm of A₂ (x₂ (n + 1) - x₂ n) → 0
theorem converge_zero₃_c1 [Condition_C1 admm]:
    Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖)  atTop (𝓝 0) := by
   have : Tendsto (fun n => ‖A₂ (x₂ (n + 1) - x₂ n)‖ ^ 2)  atTop (𝓝 0) := by
      have := (HWY_Convergence_1_increment (admm := admm) (admm_kkt := admm_kkt))
      exact this
   have h := square_converge_zero₃_c1 this
   exact h

-- A₁ (e₁ n) + A₂ (e₂ n) → 0 (Note that this lemma is without the norm)
lemma Seq_converge_zero₁_c1 [Condition_C1 admm]  : Tendsto (fun n => A₁ (e₁ n) + A₂ (e₂ n))  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 (converge_zero₁_c1 (admm_kkt := admm_kkt))

-- A₁ (x₁ n) + A₂ (x₂ n) - b → 0
lemma Seq_converge_zero₂_c1 [Condition_C1 admm]  : Tendsto (fun n => A₁ (x₁ n) + A₂ (x₂ n) - b)  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 (converge_zero₂_c1 (admm_kkt := admm_kkt))

-- A₂ (x₂ (n + 1) - x₂ n) → 0
lemma Seq_converge_zero₃_c1 [Condition_C1 admm]  : Tendsto (fun n => A₂ (x₂ (n + 1) - x₂ n))  atTop (𝓝 0) := by
   apply tendsto_zero_iff_norm_tendsto_zero.2 (converge_zero₃_c1 (admm_kkt := admm_kkt))

-- A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n)) → 0
lemma sub_Seq_converge_zero₁_c1 [Condition_C1 admm]  : Tendsto (fun n => A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n)))
atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 (Seq_converge_zero₁_c1 (admm_kkt := admm_kkt))
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₁ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₁_equ_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono_c1 (admm_kkt := admm_kkt)
   · simp [StrictMono]

-- A₁ (x₁ (φ₁ n)) + A₂ (x₂ (φ₁ n)) - b → 0
lemma sub_Seq_converge_zero₂_c1 [Condition_C1 admm] : Tendsto (fun n => A₁ (x₁ (φ₁ n)) + A₂ (x₂ (φ₁ n)) - b) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 (Seq_converge_zero₂_c1 (admm_kkt := admm_kkt))
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₁ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₁_equ_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono_c1 (admm_kkt := admm_kkt)
   · simp [StrictMono]

-- A₂ (x₂ ((φ₁ n) + 1) - x₂ (φ₁ n)) → 0
lemma sub_Seq_converge_zero₃_c1 [Condition_C1 admm] : Tendsto (fun n => A₂ (x₂ ((φ₁ n) + 1) - x₂ (φ₁ n))) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 (Seq_converge_zero₃_c1 (admm_kkt := admm_kkt))
   apply StrictMono.tendsto_atTop
   have : (fun n => (Int.toNat (φ₁ n))) = (fun n => (φ (n+1))) := by
      ext n; rw [φ₁_equ_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂ n]; simp
   simp at this; rw [this]
   apply StrictMono.comp
   · apply hphi_StrictMono_c1 (admm_kkt := admm_kkt)
   · simp [StrictMono]

-- The difference between this lemma and the one above is the change of sub-script.
-- A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1)) → 0
lemma sub_Seq_converge_zero₃'_c1 [Condition_C1 admm]  : Tendsto (fun n => A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1))) atTop (𝓝 0) := by
   apply Filter.tendsto_iff_seq_tendsto.1 (Seq_converge_zero₃_c1 (admm_kkt := admm_kkt))
   apply StrictMono.tendsto_atTop
   simp; rw [StrictMono]; intro n₁ n₂ h
   have h₁: φ (n₁ + 1) < φ (n₂ + 1) := by apply hphi_StrictMono_c1 (admm_kkt := admm_kkt); linarith
   have hn₁: φ (n₁ + 1) ≥ 1 := by
      calc
         _ ≥ n₁ + 1 := by apply StrictMono.id_le (hphi_StrictMono_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
         _ ≥ 1 := by linarith
   apply Nat.sub_lt_sub_right hn₁ h₁

-- (( 1 - τ) * ρₙ n ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))) → 0
lemma const_smul_subseq₁_c1 [Condition_C1 admm]  : Tendsto (fun n => (( 1 - τ) * ρₙ (φ₁ n) ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n)))) atTop (𝓝 0) := by
   -- Use ‖c • x‖ = |c| * ‖x‖.
   have h_norm_eq : (fun n => ‖(( 1 - τ) * ρₙ (φ₁ n) ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n)))‖) =
                    (fun n => |(1 - τ) * ρₙ (φ₁ n)| * ‖A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))‖) := by
     ext n
     rw [norm_smul, Real.norm_eq_abs]
   -- The norms of the vector sequence tend to zero.
   have h_vector_norm : Tendsto (fun n => ‖A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))‖) atTop (𝓝 0) := by
     apply tendsto_zero_iff_norm_tendsto_zero.1
     exact sub_Seq_converge_zero₁_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   -- A bounded sequence times a sequence tending to zero also tends to zero.
   have h_bounded : ∃ C, ∀ n, |(1 - τ) * ρₙ n| ≤ C := by
     rcases admm.rho_upper_bound with ⟨BU, hBU_pos, hBU⟩
     use BU
     intro n
     have h_rho_pos : ρₙ n > 0 := admm.hρₙ_pos n
     have h_rho_bound : ρₙ n ≤ BU := hBU n
     rw [abs_mul]
     -- Since ρₙ n > 0, |ρₙ n| = ρₙ n.
     have h_abs_rho : |ρₙ n| = ρₙ n := abs_of_pos h_rho_pos
     rw [h_abs_rho]
     -- It remains to prove |1 - τ| * ρₙ n ≤ BU.
     -- Use ρₙ n ≤ BU and |1 - τ| ≤ 1 to bound their product by BU.
     have h_abs_tau_le : |1 - τ| ≤ 1 := by
       have h_tau_pos : τ > 0 := admm.htau.1
       have h_tau_upper : τ < (1 + Real.sqrt 5) / 2 := admm.htau.2
       by_cases h : τ ≤ 1
       · -- If τ ≤ 1, then |1 - τ| = 1 - τ ≤ 1.
         rw [abs_of_nonneg (sub_nonneg.mpr h)]
         linarith
       · -- If τ > 1, then |1 - τ| = τ - 1.
         push_neg at h
         rw [abs_of_neg (sub_neg.mpr h)]
         -- Prove τ - 1 ≤ 1, equivalently τ ≤ 2.
         -- Use τ < (1+√5)/2 < 2.
         have h_tau_lt_2 : τ < 2 := by
           have : (1 + Real.sqrt 5) / 2 < 2 := by
             have h_sqrt5 : Real.sqrt 5 < 3 := by
               -- From 5 < 9, obtain √5 < √9 = 3.
               have h_sqrt5_lt_sqrt9 : Real.sqrt 5 < Real.sqrt 9 := by
                 apply Real.sqrt_lt_sqrt
                 · norm_num
                 · norm_num
               have h_sqrt9_eq_3 : Real.sqrt 9 = 3 := by norm_num
               linarith [h_sqrt5_lt_sqrt9, h_sqrt9_eq_3]
             linarith
           linarith [h_tau_upper, this]
         linarith
     -- Use |1 - τ| * ρₙ n ≤ ρₙ n ≤ BU.
     calc |1 - τ| * ρₙ n
       ≤ 1 * ρₙ n := mul_le_mul_of_nonneg_right h_abs_tau_le (le_of_lt h_rho_pos)
     _ = ρₙ n := by ring
     _ ≤ BU := h_rho_bound
   rcases h_bounded with ⟨C, hC⟩
   have h_lower : ∀ n, 0 ≤ |(1 - τ) * ρₙ (φ₁ n)| * ‖A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))‖ := by
     intro n
     apply mul_nonneg
     · exact abs_nonneg _
     · exact norm_nonneg _
   have h_upper : ∀ n, |(1 - τ) * ρₙ (φ₁ n)| * ‖A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))‖ ≤ C * ‖A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))‖ := by
     intro n
     apply mul_le_mul_of_nonneg_right (hC (φ₁ n))
     exact norm_nonneg _
   have h_bound_tendsto : Tendsto (fun n => C * ‖A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))‖) atTop (𝓝 0) := by
     convert Tendsto.const_mul C h_vector_norm using 1
     simp [mul_zero]
   have h_norm_tendsto : Tendsto (fun n => |(1 - τ) * ρₙ (φ₁ n)| * ‖A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))‖) atTop (𝓝 0) := by
     apply tendsto_of_tendsto_of_tendsto_of_le_of_le
     · exact tendsto_const_nhds
     · exact h_bound_tendsto
     · exact h_lower
     · exact h_upper
   -- Deduce convergence to zero from convergence of the norms.
   apply tendsto_zero_iff_norm_tendsto_zero.2
   rw [h_norm_eq]
   exact h_norm_tendsto

-- ρₙ (φ₁ n) • A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n))) → 0
lemma const_smul_subseq₂_c1 [Condition_C1 admm]  : Tendsto (fun n => ρₙ (φ₁ n) • A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n))) atTop (𝓝 0) := by
   have : (fun n => ρₙ (φ₁ n) • A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n))) = (fun n => (-ρₙ (φ₁ n)) • A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1))) := by
      ext n
      calc
         _ = ρₙ (φ₁ n) • (-1) • A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1)) := by simp
         _ = (-ρₙ (φ₁ n)) • A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1)) := by
            rw [smul_comm, neg_one_smul]; simp
   rw [this]
   apply tendsto_zero_iff_norm_tendsto_zero.2
   rcases admm.rho_upper_bound with ⟨BU, hBU⟩
   have h_vec : Tendsto (fun n => ‖A₂ (x₂ (φ₁ n) - x₂ ((φ₁ n) - 1))‖) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.1
      exact sub_Seq_converge_zero₃'_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   apply tendsto_of_tendsto_of_tendsto_of_le_of_le
   · exact tendsto_const_nhds
   · rw [← mul_zero BU]
     exact Filter.Tendsto.const_mul BU h_vec
   · intro n
     apply norm_nonneg
   · intro n
     simp
     rw [norm_smul]
     gcongr
     have h_pos : ρₙ (φ₁ n) > 0 := admm.hρₙ_pos (φ₁ n)
     have h_bound : ρₙ (φ₁ n) ≤ BU := hBU.2 (φ₁ n)
     -- Since ρₙ > 0, ‖ρₙ‖ = ρₙ.
     have h_norm_eq : ‖ρₙ (φ₁ n)‖ = ρₙ (φ₁ n) := by
       rw [Real.norm_eq_abs, abs_of_pos h_pos]
     rw [h_norm_eq]
     exact h_bound

-- u (φ₁ n) converges to (- A₁† y'')
lemma u_subseq_converge_c1 [Condition_C1 admm]  : Tendsto (fun n => u (φ₁ n)) atTop (𝓝 (- A₁† y'')) := by
   have : (fun n => u (φ₁ n)) = (fun n => - A₁† ((y (φ₁ n)) + (( 1 - τ) * ρₙ (φ₁ n) ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))) + ρₙ (φ₁ n) • (A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n))))) := by
      funext n
      rw [ AdaptiveADMM_Convergence_Proof.u]
   rw [this]
   have : Tendsto (fun n => (y (φ₁ n)) + (( 1 - τ) * ρₙ (φ₁ n) ) • (A₁ (e₁ (φ₁ n))
         + A₂ (e₂ (φ₁ n)))) atTop (𝓝 y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (y_subseq_converge'_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (const_smul_subseq₁_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
   have h: Tendsto (fun n => (y (φ₁ n)) + (( 1 - τ) * ρₙ (φ₁ n) ) • (A₁ (e₁ (φ₁ n))
         + A₂ (e₂ (φ₁ n))) + ρₙ (φ₁ n) • (A₂ (x₂ ((φ₁ n) - 1) - x₂ (φ₁ n)))) atTop (𝓝 y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (this) (const_smul_subseq₂_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
   have : Tendsto (- A₁†) (𝓝 y'') (𝓝 (- A₁† y'')) := by apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   apply Filter.tendsto_iff_seq_tendsto.1 this; apply h


-- v (φ₁ n) converges to (- A₂† y'')
lemma v_subseq_converge_c1 [Condition_C1 admm]  : Tendsto (fun n => v (φ₁ n)) atTop (𝓝 (- A₂† y'')) := by
   have : (fun n => v (φ₁ n)) = (fun n => - A₂† (y (φ₁ n) + (( 1 - τ) * ρₙ (φ₁ n) ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))))) := by
      funext n; rw [ AdaptiveADMM_Convergence_Proof.v]
   rw [this]
   have h: Tendsto (fun n => (y (φ₁ n) + (( 1 - τ) * ρₙ (φ₁ n) ) • (A₁ (e₁ (φ₁ n)) + A₂ (e₂ (φ₁ n))))) atTop (𝓝  y'') := by
      rw [← add_zero y'']
      apply Filter.Tendsto.add (y_subseq_converge'_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (const_smul_subseq₁_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
   have : Tendsto (- A₂†) (𝓝 y'') (𝓝 (- A₂† y'')) := by apply Continuous.tendsto; apply ContinuousLinearMap.continuous
   apply Filter.tendsto_iff_seq_tendsto.1 this; apply h

-- (nonempty : ∀ (n : ℕ), g n ∈ SubderivAt f (x n)) (lscf : LowerSemicontinuous f)
-- (x_converge : Tendsto x atTop (𝓝 x')) (g_converge : Tendsto g atTop (𝓝 g'))

lemma A₁'y_inthesubgradient_c1 [Condition_C1 admm] : - A₁† y'' ∈ SubderivAt f₁ x₁'':=
   Image_subgradient_closed (fun n ↦ (u_inthesubgradient (admm := admm) (admm_kkt := admm_kkt)) (φ₁ n)) admm.lscf₁
   (x₁_subseq_converge'_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (u_subseq_converge_c1 (admm_kkt := admm_kkt)   fullrank₁ fullrank₂)

lemma A₂'y_inthesubgradient_c1 [Condition_C1 admm]  : - A₂† y'' ∈ SubderivAt f₂ x₂'':=
   Image_subgradient_closed (fun n => (v_inthesubgradient (admm := admm) (admm_kkt := admm_kkt)) (φ₁ n)) admm.lscf₂
   (x₂_subseq_converge'_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (v_subseq_converge_c1 (admm_kkt := admm_kkt)   fullrank₁ fullrank₂)

-- lim ‖ x_n ‖ = ‖ lim x_n ‖
lemma Satisfying_equational_constraint1'_c1 [Condition_C1 admm] : Tendsto A₁ (𝓝 x₁'') (𝓝 (A₁ x₁'')) := by
   apply Continuous.tendsto
   apply ContinuousLinearMap.continuous

lemma Satisfying_equational_constraint1_c1 [Condition_C1 admm] :
Tendsto (fun n => A₁ (x₁ (φ n))) atTop (𝓝 (A₁ x₁'')) := by
   apply tendsto_iff_seq_tendsto.1 (Satisfying_equational_constraint1'_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (x₁ ∘ φ)
   apply tendsto_iff_seq_tendsto.1 (x₁_subseq_converge_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
   apply StrictMono.tendsto_atTop
   apply strictMono_id

lemma Satisfying_equational_constraint2'_c1 [Condition_C1 admm] : Tendsto A₂ (𝓝 x₂'') (𝓝 (A₂ x₂'')) := by
   apply Continuous.tendsto
   apply ContinuousLinearMap.continuous

lemma Satisfying_equational_constraint2_c1 [Condition_C1 admm] :
Tendsto (fun n => A₂ (x₂ (φ n))) atTop (𝓝 (A₂ x₂'')) := by
   apply tendsto_iff_seq_tendsto.1 (Satisfying_equational_constraint2'_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂) (x₂ ∘ φ)
   apply tendsto_iff_seq_tendsto.1 (x₂_subseq_converge_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
   apply StrictMono.tendsto_atTop
   apply strictMono_id

lemma Satisfying_equational_constraint'_c1 [Condition_C1 admm] :
Tendsto (fun n => ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖) atTop (𝓝 ‖(A₁ x₁'') + (A₂ x₂'') - admm.b‖)
:= by
   apply Tendsto.norm
   apply Tendsto.sub_const
   apply Tendsto.add
   apply Satisfying_equational_constraint1_c1 (admm_kkt := admm_kkt)
   apply Satisfying_equational_constraint2_c1 (admm_kkt := admm_kkt)

lemma subconverge_zero₂_c1 [Condition_C1 admm] : Tendsto (fun n =>  ‖A₁ (x₁ (φ n)) + A₂ (x₂ (φ n)) - b‖)  atTop (𝓝 0)
:= by
   apply tendsto_iff_seq_tendsto.1 (converge_zero₂_c1 (admm_kkt := admm_kkt))
   apply StrictMono.tendsto_atTop
   apply hphi_StrictMono_c1 (admm_kkt := admm_kkt)

lemma Satisfying_equational_constraint_norm_c1 [Condition_C1 admm] :
      ‖(A₁ x₁'') + (A₂ x₂'') - admm.b‖ = 0 := by
   apply tendsto_nhds_unique (Satisfying_equational_constraint'_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
   apply subconverge_zero₂_c1 (admm_kkt := admm_kkt)

lemma Satisfying_equational_constraint_c1 [Condition_C1 admm] :
      (A₁ x₁'') + (A₂ x₂'') = admm.b := by
   have h1 := Satisfying_equational_constraint_norm_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   apply norm_eq_zero.1 at h1
   apply eq_of_sub_eq_zero h1

lemma Iskktpair_c1 [Condition_C1 admm] : Convex_KKT x₁'' x₂'' y'' admm.toOptProblem :=
   {
      subgrad₁ :=A₁'y_inthesubgradient_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
      subgrad₂ :=A₂'y_inthesubgradient_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
      eq       :=Satisfying_equational_constraint_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂
   }

def admm_kkt_c1 [Condition_C1 admm] :  KKTPoint admm :=
   KKTPoint.mk x₁''  x₂''  y'' (Iskktpair_c1 (admm_kkt := admm_kkt) fullrank₁ fullrank₂)
end AdaptiveADMM_Convergence_Proof
