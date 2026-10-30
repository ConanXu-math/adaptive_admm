import Optlib.Function.Lsmooth
import Optlib.Function.Proximal
import Optlib.Convex.ConvexFunction
import Optlib.Convex.StronglyConvex
import Optlib.Convex.Subgradient
import Optlib.Differential.Lemmas
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact

/-!
# ISTA with Backtracking

Formalization of ISTA with backtracking stepsize rule from
Beck & Teboulle, "A Fast Iterative Shrinkage-Thresholding Algorithm
for Linear Inverse Problems", SIAM J. Imaging Sci. (2009), §2–3.
-/

noncomputable section ISTABt_section

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

variable {f : E → ℝ} {f' : E → E} {g : E → ℝ}

/-- The quadratic approximation model Q_L(x, y) from equation (2.5). -/
def QModel (f : E → ℝ) (f' : E → E) (g : E → ℝ) (L : ℝ) (x y : E) : ℝ :=
  f y + ⟪x - y, f' y⟫_ℝ + L / 2 * ‖x - y‖ ^ 2 + g x

/-- The objective F = f + g. -/
def FObj (f g : E → ℝ) (x : E) : ℝ := f x + g x

/-- The scaled function (1/L)·g. -/
def gScaled (g : E → ℝ) (L : ℝ) : E → ℝ := fun u => (1/L) * g u

/-- The point z = y - (1/L)·∇f(y). -/
def proxCenter (f' : E → E) (L : ℝ) (y : E) : E := y - (1/L) • f' y

/-- Existence of the proximal point. -/
theorem proxLExists (f' : E → E) (g : E → ℝ) (L : ℝ) (hL : L > 0) (y : E)
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g) :
    ∃ w, prox_prop (gScaled g L) (proxCenter f' L y) w := by
  have hcont : ContinuousOn (gScaled g L) univ := by
    unfold gScaled
    exact ((continuous_const : Continuous (fun _ => (1/L : ℝ))).mul hg_cont).continuousOn
  have hconv : ConvexOn ℝ univ (gScaled g L) := by
    unfold gScaled
    have := @ConvexOn.smul ℝ E ℝ _ _ _ _ _ _ _ _ univ g ((1:ℝ)/L) (by positivity) hg_conv
    convert this using 1
  have hexists := prox_well_define_convex (gScaled g L) hcont hconv (proxCenter f' L y)
  exact hexists

/-- The proximal point p_L(y). -/
def proxL (f' : E → E) (g : E → ℝ) (L : ℝ) (hL : L > 0) (y : E)
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g) : E :=
  Classical.choose (proxLExists f' g L hL y hg_cont hg_conv)

/-- proxL satisfies prox_prop. -/
theorem proxL_spec (f' : E → E) (g : E → ℝ) (L : ℝ) (hL : L > 0) (y : E)
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g) :
    prox_prop (gScaled g L) (proxCenter f' L y)
      (proxL f' g L hL y hg_cont hg_conv) :=
  Classical.choose_spec (proxLExists f' g L hL y hg_cont hg_conv)

/-- proxL minimizes g(u) + (L/2)‖u - z‖² where z = y - (1/L)·f'(y). -/
theorem proxL_min (f' : E → E) (g : E → ℝ) (L : ℝ) (hL : L > 0) (y : E)
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g) :
    IsMinOn (fun u => g u + L / 2 * ‖u - proxCenter f' L y‖ ^ 2) Set.univ
      (proxL f' g L hL y hg_cont hg_conv) := by
  set p := proxL f' g L hL y hg_cont hg_conv
  set z := proxCenter f' L y
  have hspec := proxL_spec f' g L hL y hg_cont hg_conv
  unfold prox_prop at hspec
  rw [isMinOn_univ_iff] at hspec ⊢
  intro v
  have h := hspec v
  unfold gScaled at h
  have key : L * ((1/L) * g p + ‖p - z‖ ^ 2 / 2) ≤ L * ((1/L) * g v + ‖v - z‖ ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left h hL.le
  have hLp : L * ((1/L) * g p + ‖p - z‖ ^ 2 / 2) = g p + L / 2 * ‖p - z‖ ^ 2 := by
    field_simp
  have hLv : L * ((1/L) * g v + ‖v - z‖ ^ 2 / 2) = g v + L / 2 * ‖v - z‖ ^ 2 := by
    field_simp
  rw [hLp, hLv] at key
  exact key

/-- Uniqueness of the proximal point. -/
theorem proxL_unique (f' : E → E) (g : E → ℝ) (L : ℝ) (hL : L > 0) (y : E)
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (p₁ p₂ : E)
    (h₁ : IsMinOn (fun u => g u + L / 2 * ‖u - proxCenter f' L y‖ ^ 2) Set.univ p₁)
    (h₂ : IsMinOn (fun u => g u + L / 2 * ‖u - proxCenter f' L y‖ ^ 2) Set.univ p₂) :
    p₁ = p₂ := by
  set z := proxCenter f' L y
  have h₁' : prox_prop (gScaled g L) z p₁ := by
    unfold prox_prop gScaled
    rw [isMinOn_univ_iff] at h₁ ⊢
    intro v
    have hv := h₁ v
    have hLp : (1:ℝ)/L * g p₁ + ‖p₁ - z‖ ^ 2 / 2 = (g p₁ + L / 2 * ‖p₁ - z‖ ^ 2) / L := by field_simp
    have hLv : (1:ℝ)/L * g v + ‖v - z‖ ^ 2 / 2 = (g v + L / 2 * ‖v - z‖ ^ 2) / L := by field_simp
    rw [hLp, hLv]
    exact div_le_div_of_nonneg_right hv hL.le
  have h₂' : prox_prop (gScaled g L) z p₂ := by
    unfold prox_prop gScaled
    rw [isMinOn_univ_iff] at h₂ ⊢
    intro v
    have hv := h₂ v
    have hLp : (1:ℝ)/L * g p₂ + ‖p₂ - z‖ ^ 2 / 2 = (g p₂ + L / 2 * ‖p₂ - z‖ ^ 2) / L := by field_simp
    have hLv : (1:ℝ)/L * g v + ‖v - z‖ ^ 2 / 2 = (g v + L / 2 * ‖v - z‖ ^ 2) / L := by field_simp
    rw [hLp, hLv]
    exact div_le_div_of_nonneg_right hv hL.le
  have hconv : ConvexOn ℝ univ (gScaled g L) := by
    unfold gScaled
    have := @ConvexOn.smul ℝ E ℝ _ _ _ _ _ _ _ _ univ g ((1:ℝ)/L) (by positivity) hg_conv
    convert this using 1
  exact prox_unique_of_convex (gScaled g L) z hconv h₁' h₂'

/-- Subgradient condition: for all w, g(w) ≥ g(p) + L·⟨z - p, w - p⟩
    where p = proxL, z = y - (1/L)·f'(y). -/
theorem proxL_subgrad (f' : E → E) (g : E → ℝ) (L : ℝ) (hL : L > 0) (y : E)
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g) :
    ∀ w : E,
      g w ≥ g (proxL f' g L hL y hg_cont hg_conv) +
        L * ⟪proxCenter f' L y - proxL f' g L hL y hg_cont hg_conv,
            w - proxL f' g L hL y hg_cont hg_conv⟫_ℝ := by
  set p := proxL f' g L hL y hg_cont hg_conv
  set z := proxCenter f' L y
  have hspec := proxL_spec f' g L hL y hg_cont hg_conv
  have hconv : ConvexOn ℝ univ (gScaled g L) := by
    unfold gScaled
    have := @ConvexOn.smul ℝ E ℝ _ _ _ _ _ _ _ _ univ g ((1:ℝ)/L) (by positivity) hg_conv
    convert this using 1
  have hsubderiv : HasSubgradientAt (gScaled g L) (z - p) p :=
    mem_SubderivAt.mpr ((@prox_iff_subderiv E _ _ _ z (gScaled g L) hconv p).mp hspec)
  intro w
  have h := hsubderiv w
  unfold gScaled at h
  have key : L * ((1/L) * g w) ≥ L * ((1/L) * g p + ⟪z - p, w - p⟫_ℝ) :=
    mul_le_mul_of_nonneg_left h hL.le
  have hLinv : L * (1/L) = 1 := by field_simp
  rw [mul_add, ← mul_assoc, ← mul_assoc] at key
  rw [hLinv, one_mul, one_mul] at key
  exact key

/-- Lemma 2.1 (Descent lemma): If ∇f is L-Lipschitz, then
    f(x) ≤ f(y) + ⟨x - y, ∇f(y)⟩ + (L/2)‖x - y‖². -/
theorem descent_lemma (f : E → ℝ) (f' : E → E)
    (hdiff : ∀ z, HasGradientAt f (f' z) z)
    (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (x y : E) :
    f x ≤ f y + ⟪x - y, f' y⟫_ℝ + L / 2 * ‖x - y‖ ^ 2 := by
  have h := lipschitz_continuos_upper_bound' hdiff hlip y x
  have hcomm : ⟪f' y, x - y⟫_ℝ = ⟪x - y, f' y⟫_ℝ := real_inner_comm _ _
  rw [hcomm] at h
  simp only [NNReal.coe_mk, Nat.cast_two] at h
  exact h

/-- The acceptance condition is satisfied when L̄ ≥ L (Lipschitz constant). -/
theorem acceptance_when_large (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z)
    (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (Lbar : ℝ) (hLbar : Lbar ≥ L) (y : E) :
    FObj f g (proxL f' g Lbar (lt_of_lt_of_le hL hLbar) y hg_cont hg_conv)
      ≤ QModel f f' g Lbar (proxL f' g Lbar (lt_of_lt_of_le hL hLbar) y hg_cont hg_conv) y := by
  set p := proxL f' g Lbar (lt_of_lt_of_le hL hLbar) y hg_cont hg_conv
  have hLbar_pos : Lbar > 0 := lt_of_lt_of_le hL hLbar
  have hdescent := descent_lemma f f' hdiff L hL hlip p y
  unfold FObj QModel
  nlinarith [hdescent, hLbar, sq_nonneg ‖p - y‖]

/-- Lemma 2.3 (Key inequality): If p = p_L(y) and F(p) ≤ Q_L(p, y), then for any x:
    F(x) - F(p) ≥ (L/2)‖p - y‖² + L⟨y - x, p - y⟩. -/
theorem key_inequality (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z)
    (hconv_f : ConvexOn ℝ Set.univ f)
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (L : ℝ) (hL : L > 0) (y : E) (x : E)
    (haccept : FObj f g (proxL f' g L hL y hg_cont hg_conv)
      ≤ QModel f f' g L (proxL f' g L hL y hg_cont hg_conv) y) :
    FObj f g x - FObj f g (proxL f' g L hL y hg_cont hg_conv)
      ≥ L / 2 * ‖proxL f' g L hL y hg_cont hg_conv - y‖ ^ 2
        + L * ⟪y - x, proxL f' g L hL y hg_cont hg_conv - y⟫_ℝ := by
  set p := proxL f' g L hL y hg_cont hg_conv
  set z := proxCenter f' L y
  -- Convexity of f: f y + ⟨f' y, x - y⟩ ≤ f x
  have hconv_f' : f y + ⟪f' y, x - y⟫_ℝ ≤ f x :=
    Convex_first_order_condition' (hdiff y) hconv_f (mem_univ y) x (mem_univ x)
  -- Subgradient of g: g x ≥ g p + L * ⟨z - p, x - p⟩
  have hsubgrad := proxL_subgrad f' g L hL y hg_cont hg_conv x
  -- F(x) ≥ f y + ⟨f' y, x - y⟩ + g p + L * ⟨z - p, x - p⟩
  have hFx_ge : f x + g x ≥ f y + ⟪f' y, x - y⟫_ℝ + g p + L * ⟪z - p, x - p⟫_ℝ := by
    linarith [hconv_f', hsubgrad]
  -- z - p = (y - p) - (1/L) • f' y
  have hz_eq : z - p = (y - p) - (1/L) • f' y := by
    have hz : z = y - (1/L) • f' y := rfl
    rw [hz]; abel
  -- Key identity: ⟨f' y, x - y⟩ - ⟨f' y, p - y⟩ = ⟨f' y, x - p⟩
  have hkey1 : ⟪f' y, x - y⟫_ℝ - ⟪f' y, p - y⟫_ℝ = ⟪f' y, x - p⟫_ℝ := by
    rw [inner_sub_right, inner_sub_right, inner_sub_right]; abel
  -- Key identity: ⟨f' y, x - p⟩ + L * ⟨z - p, x - p⟩ = L * ⟨y - p, x - p⟩
  have hkey2 : ⟪f' y, x - p⟫_ℝ + L * ⟪z - p, x - p⟫_ℝ = L * ⟪y - p, x - p⟫_ℝ := by
    rw [hz_eq]
    rw [show ⟪(y - p) - (1/L) • f' y, x - p⟫_ℝ = ⟪y - p, x - p⟫_ℝ - ⟪(1/L) • f' y, x - p⟫_ℝ from
      inner_sub_left _ _ _]
    rw [real_inner_smul_left]
    have hLne : L ≠ 0 := ne_of_gt hL
    field_simp
    ring
  -- Key identity: L * ⟨y - p, x - p⟩ - (L/2) * ‖p - y‖² = (L/2) * ‖p - y‖² + L * ⟨y - x, p - y⟩
  have hkey3 : L * ⟪y - p, x - p⟫_ℝ - L / 2 * ‖p - y‖ ^ 2
      = L / 2 * ‖p - y‖ ^ 2 + L * ⟪y - x, p - y⟫_ℝ := by
    -- ⟨y - p, x - p⟩ = ⟨y - x, p - y⟩ + ‖p - y‖²
    have hident : ⟪y - p, x - p⟫_ℝ = ⟪y - x, p - y⟫_ℝ + ‖p - y‖ ^ 2 := by
      -- x - p = (x - y) + (y - p)
      have hdecomp : x - p = (x - y) + (y - p) := by abel
      rw [hdecomp, inner_add_right, real_inner_self_eq_norm_sq]
      -- ⟨y - p, x - y⟩ + ‖y - p‖² = ⟨y - x, p - y⟩ + ‖p - y‖²
      have h1 : ⟪y - p, x - y⟫_ℝ = ⟪y - x, p - y⟫_ℝ := by
        have hneg1 : y - p = -(p - y) := by abel
        have hneg2 : x - y = -(y - x) := by abel
        rw [hneg1, hneg2, inner_neg_left, inner_neg_right, neg_neg]
        exact real_inner_comm _ _
      have h2 : ‖y - p‖ ^ 2 = ‖p - y‖ ^ 2 := by
        rw [show y - p = -(p - y) from by abel, norm_neg]
      rw [h1, h2]
    rw [hident]
    ring
  -- Combine: F(x) - F(p) ≥ F(x) - Q(p, y) ≥ (L/2)‖p-y‖² + L⟨y-x, p-y⟩
  unfold FObj at haccept hFx_ge ⊢
  unfold QModel at haccept
  -- F(x) - Q(p, y) = ⟨f' y, x - y⟩ - ⟨f' y, p - y⟩ + L⟨z-p, x-p⟩ - (L/2)‖p-y‖²
  have hge : f x + g x - (f p + g p) ≥
      ⟪f' y, x - y⟫_ℝ + L * ⟪z - p, x - p⟫_ℝ
      - (⟪f' y, p - y⟫_ℝ + L / 2 * ‖p - y‖ ^ 2) := by
    have : f p + g p ≤ f y + ⟪p - y, f' y⟫_ℝ + L / 2 * ‖p - y‖ ^ 2 + g p := haccept
    have : f p + g p ≤ f y + ⟪f' y, p - y⟫_ℝ + L / 2 * ‖p - y‖ ^ 2 + g p := by
      rw [real_inner_comm (f' y) (p - y)] at this
      exact this
    linarith [hFx_ge, this]
  linarith [hge, hkey1, hkey2, hkey3]

/-- Key inequality specialized to x = x* (minimizer):
    F(p) - F(x*) ≤ (L/2)(‖x* - y‖² - ‖x* - p‖²). -/
theorem key_inequality_min (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z)
    (hconv_f : ConvexOn ℝ Set.univ f)
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (L : ℝ) (hL : L > 0) (y : E) (xstar : E)
    (hmin : IsMinOn (FObj f g) Set.univ xstar)
    (haccept : FObj f g (proxL f' g L hL y hg_cont hg_conv)
      ≤ QModel f f' g L (proxL f' g L hL y hg_cont hg_conv) y) :
    FObj f g (proxL f' g L hL y hg_cont hg_conv) - FObj f g xstar
      ≤ L / 2 * (‖xstar - y‖ ^ 2 - ‖xstar - proxL f' g L hL y hg_cont hg_conv‖ ^ 2) := by
  set p := proxL f' g L hL y hg_cont hg_conv
  have hkey := key_inequality f f' g hdiff hconv_f hg_cont hg_conv L hL y xstar haccept
  -- hkey: F(x*) - F(p) ≥ (L/2)‖p - y‖² + L⟨y - x*, p - y⟩
  -- Pythagorean: ‖x* - p‖² - ‖x* - y‖² = ‖p - y‖² + 2⟨y - x*, p - y⟩
  have hpyth : ‖xstar - p‖ ^ 2 - ‖xstar - y‖ ^ 2
      = ‖p - y‖ ^ 2 + 2 * ⟪y - xstar, p - y⟫_ℝ := by
    have hdecomp : xstar - p = (xstar - y) + (y - p) := by abel
    rw [hdecomp, norm_add_sq_real]
    have hcomm : ⟪xstar - y, y - p⟫_ℝ = ⟪y - xstar, p - y⟫_ℝ := by
      have h1 : xstar - y = -(y - xstar) := by abel
      have h2 : y - p = -(p - y) := by abel
      rw [h1, h2, inner_neg_left, inner_neg_right, neg_neg]
    rw [hcomm, show ‖y - p‖ ^ 2 = ‖p - y‖ ^ 2 from by
      rw [show y - p = -(p - y) from by abel, norm_neg]]
    ring
  -- From hkey: F(x*) - F(p) ≥ (L/2)(‖x*-p‖² - ‖x*-y‖²)
  have hkey' : FObj f g xstar - FObj f g p ≥ L / 2 * (‖xstar - p‖ ^ 2 - ‖xstar - y‖ ^ 2) := by
    rw [hpyth]
    linarith [hkey]
  -- F(p) - F(x*) ≤ (L/2)(‖x*-y‖² - ‖x*-p‖²)
  linarith [hkey']

/-! ## The Algorithm Structure --/

/-- The ISTA with backtracking algorithm structure.

    Encodes the algorithm from §3: at each step k ≥ 1, find the smallest
    nonnegative integer i_k such that the acceptance condition (3.2) holds
    with L̄ = η^{i_k} L_{k-1}, then set L_k = η^{i_k} L_{k-1} and
    x_k = p_{L_k}(x_{k-1}). -/
structure ISTABt (f : E → ℝ) (f' : E → E) (g : E → ℝ) where
  /-- Iterates x_k -/
  x : ℕ → E
  /-- Stepsize sequence L_k -/
  Lk : ℕ → ℝ
  /-- Backtracking indices i_k -/
  ik : ℕ → ℕ
  /-- Lipschitz constant of ∇f -/
  L : ℝ
  /-- Initial stepsize estimate -/
  L0 : ℝ
  /-- Backtracking factor -/
  eta : ℝ
  /-- Initial point -/
  x0 : E
  /-- L > 0 -/
  hL : L > 0
  /-- L0 > 0 -/
  hL0 : L0 > 0
  /-- η > 1 -/
  heta : eta > 1
  /-- f differentiable with gradient f' -/
  hf_diff : ∀ z, HasGradientAt f (f' z) z
  /-- f convex -/
  hf_convex : ConvexOn ℝ Set.univ f
  /-- ∇f is L-Lipschitz -/
  hf_lip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f'
  /-- g continuous -/
  hg_continuous : Continuous g
  /-- g convex -/
  hg_convex : ConvexOn ℝ Set.univ g
  /-- F = f + g has a minimizer -/
  hF_min : ∃ xstar, IsMinOn (FObj f g) Set.univ xstar
  /-- x_0 = x0 -/
  x_init : x 0 = x0
  /-- L_0 = L0 -/
  Lk_init : Lk 0 = L0
  /-- L_k > 0 for all k -/
  Lk_pos : ∀ k, 0 < Lk k
  /-- For k ≥ 1: acceptance condition holds at i_k, i.e.,
      F(x_k) ≤ Q_{L_k}(x_k, x_{k-1}) -/
  acceptance : ∀ k ≥ 1,
    FObj f g (x k) ≤ QModel f f' g (Lk k) (x k) (x (k - 1))
  /-- For k ≥ 1: i_k is minimal — for all j < i_k, the acceptance condition
      FAILS with L̄ = η^j L_{k-1}. (When i_k = 0, this is vacuous.) -/
  ik_minimal : ∀ k ≥ 1, ∀ j < ik k,
    ¬ FObj f g (proxL f' g (eta^j * Lk (k-1))
        (mul_pos (pow_pos (by linarith) j) (Lk_pos (k-1))) (x (k-1))
        hg_continuous hg_convex)
      ≤ QModel f f' g (eta^j * Lk (k-1))
        (proxL f' g (eta^j * Lk (k-1))
          (mul_pos (pow_pos (by linarith) j) (Lk_pos (k-1))) (x (k-1))
          hg_continuous hg_convex) (x (k-1))
  /-- For k ≥ 1: L_k = η^{i_k} L_{k-1} -/
  Lk_update : ∀ k ≥ 1, Lk k = eta ^ (ik k) * Lk (k - 1)
  /-- For k ≥ 1: x_k = p_{L_k}(x_{k-1}) -/
  x_update : ∀ k ≥ 1,
    x k = proxL f' g (Lk k) (Lk_pos k) (x (k - 1)) hg_continuous hg_convex

variable {alg : ISTABt f f' g}

/-- The effective upper bound L̄ = max{L₀, ηL}. -/
def Lbar (alg : ISTABt f f' g) : ℝ := max alg.L0 (alg.eta * alg.L)

/-- L̄ > 0. -/
theorem Lbar_pos (alg : ISTABt f f' g) : 0 < Lbar alg := by
  unfold Lbar
  exact lt_max_iff.mpr (Or.inl alg.hL0)

/-! ## L_k bounds --/

/-- `0 < L_k` for all k (from the structure). -/
theorem alg_Lk_pos (alg : ISTABt f f' g) (k : ℕ) : 0 < alg.Lk k := alg.Lk_pos k

/-- `L_k ≤ max{L₀, ηL}` for all k.

    Proof by induction:
    - k = 0: L₀ ≤ max{L₀, ηL} trivially.
    - k ≥ 1: If i_k = 0, then L_k = L_{k-1} ≤ L̄ by IH.
      If i_k ≥ 1, then η^{i_k - 1} L_{k-1} < L (acceptance fails for j = i_k - 1,
      but holds for any L̄' ≥ L). So L_k = η · η^{i_k-1} L_{k-1} < ηL ≤ L̄. -/
theorem alg_Lk_le_bound (alg : ISTABt f f' g) : ∀ k, alg.Lk k ≤ Lbar alg := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · rw [hk, alg.Lk_init]
      unfold Lbar
      exact le_max_left _ _
    have hk1 : k ≥ 1 := by omega
    have hupdate := alg.Lk_update k hk1
    rw [hupdate]
    by_cases hik : alg.ik k = 0
    · -- i_k = 0: L_k = L_{k-1} ≤ L̄ by IH
      rw [hik, pow_zero, one_mul]
      exact ih (k - 1) (by omega)
    · -- i_k ≥ 1: acceptance fails for j = i_k - 1
      have hik_pos : alg.ik k ≥ 1 := by omega
      have hj : alg.ik k - 1 < alg.ik k := by omega
      have hfail := alg.ik_minimal k hk1 (alg.ik k - 1) hj
      -- η^{i_k - 1} L_{k-1} must be < L (otherwise acceptance would hold)
      -- Because acceptance_when_large says: if L' ≥ L then acceptance holds
      have hLkm1_pos : 0 < alg.Lk (k - 1) := alg.Lk_pos (k - 1)
      have hetapow_pos : 0 < alg.eta ^ (alg.ik k - 1) := pow_pos (by linarith [alg.heta]) _
      have hLtrial : 0 < alg.eta ^ (alg.ik k - 1) * alg.Lk (k - 1) :=
        mul_pos hetapow_pos hLkm1_pos
      -- If η^{i_k-1} L_{k-1} ≥ L, acceptance would hold (contradiction with hfail)
      by_contra hcontra
      push_neg at hcontra
      -- hcontra: L̄ < η^{i_k} L_{k-1} = η · η^{i_k-1} L_{k-1}
      unfold Lbar at hcontra
      -- η^{i_k-1} L_{k-1} ≥ L (otherwise η · η^{i_k-1} L_{k-1} < ηL ≤ max{L0, ηL})
      by_cases hcase : alg.eta ^ (alg.ik k - 1) * alg.Lk (k - 1) ≥ alg.L
      · -- Acceptance should hold, contradiction with hfail
        have haccept := acceptance_when_large f f' g alg.hf_diff alg.L alg.hL alg.hf_lip
          alg.hg_continuous alg.hg_convex
          (alg.eta ^ (alg.ik k - 1) * alg.Lk (k - 1)) hcase (alg.x (k - 1))
        exact hfail haccept
      · -- η^{i_k-1} L_{k-1} < L, so η^{i_k} L_{k-1} = η · η^{i_k-1} L_{k-1} < ηL ≤ max{L0, ηL}
        have : alg.eta ^ (alg.ik k) * alg.Lk (k - 1)
            = alg.eta * (alg.eta ^ (alg.ik k - 1) * alg.Lk (k - 1)) := by
          conv_lhs =>
            rw [show alg.ik k = alg.ik k - 1 + 1 from by omega, pow_succ,
                mul_comm (alg.eta ^ (alg.ik k - 1)) alg.eta, mul_assoc]
        rw [this] at hcontra
        have h1 : alg.eta * (alg.eta ^ (alg.ik k - 1) * alg.Lk (k - 1))
            < alg.eta * alg.L := by
          exact mul_lt_mul_of_pos_left (lt_of_not_ge hcase) (by linarith [alg.heta])
        have hetaL_le : alg.eta * alg.L ≤ max alg.L0 (alg.eta * alg.L) := le_max_right _ _
        linarith

/-! ## Monotonicity --/

/-- F(x_k) is monotonically non-increasing: F(x_k) ≤ F(x_{k-1}) for k ≥ 1.

    From the acceptance condition and the fact that p_{L_k}(x_{k-1})
    minimizes Q_{L_k}(·, x_{k-1}), so Q_{L_k}(x_k, x_{k-1}) ≤ Q_{L_k}(x_{k-1}, x_{k-1}) = F(x_{k-1}). -/
theorem alg_Fx_monotone (alg : ISTABt f f' g) :
    ∀ k ≥ 1, FObj f g (alg.x k) ≤ FObj f g (alg.x (k - 1)) := by
  intro k hk
  have haccept := alg.acceptance k hk
  have hupdate := alg.x_update k hk
  have hLk_pos := alg.Lk_pos k
  have hLk_ne : alg.Lk k ≠ 0 := ne_of_gt hLk_pos
  rw [hupdate] at haccept ⊢
  set y := alg.x (k - 1)
  set Lk := alg.Lk k
  set p := proxL f' g Lk hLk_pos y alg.hg_continuous alg.hg_convex
  have hmin := proxL_min f' g Lk hLk_pos y alg.hg_continuous alg.hg_convex
  rw [isMinOn_univ_iff] at hmin
  have hmin_y := hmin y
  have hQ_yy : QModel f f' g Lk y y = FObj f g y := by
    unfold QModel FObj
    simp only [sub_self, inner_zero_left, norm_zero, pow_two, mul_zero, add_zero]
  have hkey : Lk / 2 * (‖p - proxCenter f' Lk y‖ ^ 2 - ‖y - proxCenter f' Lk y‖ ^ 2)
      = Lk / 2 * ‖p - y‖ ^ 2 + ⟪p - y, f' y⟫_ℝ := by
    have hz : proxCenter f' Lk y = y - (1/Lk) • f' y := rfl
    rw [hz]
    have h1 : p - (y - (1/Lk) • f' y) = (p - y) + (1/Lk) • f' y := by abel
    have h2 : y - (y - (1/Lk) • f' y) = (1/Lk) • f' y := by abel
    rw [h1, h2, norm_add_sq_real, real_inner_smul_right]
    field_simp
    ring
  have hQ_le : QModel f f' g Lk p y ≤ QModel f f' g Lk y y := by
    unfold QModel
    simp only [sub_self, inner_zero_left, norm_zero, pow_two, mul_zero, add_zero]
    linarith [hmin_y, hkey]
  unfold FObj at haccept ⊢
  unfold QModel at haccept
  linarith [haccept, hQ_yy, hQ_le]

/-! ## Rate Theorem --/

/-- **Rate theorem**: For any minimizer x* and k ≥ 1:
    F(x_k) - F(x*) ≤ max{L₀, ηL} · ‖x₀ - x*‖² / (2k). -/
theorem alg_rate (alg : ISTABt f f' g) :
    ∀ xstar : E, IsMinOn (FObj f g) Set.univ xstar →
      ∀ k ≥ 1, FObj f g (alg.x k) - FObj f g xstar
        ≤ Lbar alg * ‖alg.x0 - xstar‖ ^ 2 / (2 * (k : ℝ)) := by
  intro xstar hmin k hk
  have hLbar_pos : 0 < Lbar alg := Lbar_pos alg
  have hx0 : alg.x 0 = alg.x0 := alg.x_init
  have hkey : ∀ n : ℕ, FObj f g (alg.x (n + 1)) - FObj f g xstar
      ≤ Lbar alg / 2 * (‖xstar - alg.x n‖ ^ 2 - ‖xstar - alg.x (n + 1)‖ ^ 2) := by
    intro n
    have hn1 : n + 1 ≥ 1 := by omega
    have haccept := alg.acceptance (n + 1) hn1
    have hupdate := alg.x_update (n + 1) hn1
    have hLk_pos := alg.Lk_pos (n + 1)
    have hsub : n + 1 - 1 = n := by omega
    rw [hupdate, hsub] at haccept
    have hki := key_inequality_min f f' g alg.hf_diff alg.hf_convex
      alg.hg_continuous alg.hg_convex (alg.Lk (n + 1)) hLk_pos (alg.x n) xstar hmin haccept
    have hxeq : alg.x (n + 1) = proxL f' g (alg.Lk (n + 1)) hLk_pos (alg.x n)
        alg.hg_continuous alg.hg_convex := by rw [hupdate, hsub]
    rw [← hxeq] at hki
    have hLk_le := alg_Lk_le_bound alg (n + 1)
    have hFA : 0 ≤ ‖xstar - alg.x n‖ ^ 2 - ‖xstar - alg.x (n + 1)‖ ^ 2 := by
      have hF1 : FObj f g xstar ≤ FObj f g (alg.x (n + 1)) := hmin (mem_univ (alg.x (n + 1)))
      nlinarith [hki, hF1, hLk_pos]
    calc FObj f g (alg.x (n + 1)) - FObj f g xstar
        ≤ alg.Lk (n + 1) / 2 * (‖xstar - alg.x n‖ ^ 2 - ‖xstar - alg.x (n + 1)‖ ^ 2) := hki
      _ ≤ Lbar alg / 2 * (‖xstar - alg.x n‖ ^ 2 - ‖xstar - alg.x (n + 1)‖ ^ 2) := by
        have hLk_div : alg.Lk (n + 1) / 2 ≤ Lbar alg / 2 := by linarith [hLk_le]
        exact mul_le_mul_of_nonneg_right hLk_div hFA
  have hmain : ∀ (j : ℕ), j ≥ 1 → (↑j : ℝ) * (FObj f g (alg.x j) - FObj f g xstar)
      ≤ Lbar alg / 2 * (‖xstar - alg.x 0‖ ^ 2 - ‖xstar - alg.x j‖ ^ 2) := by
    intro j hj
    induction j using Nat.strong_induction_on with
    | h j ih =>
      by_cases hj0 : j = 0
      · omega
      have hj1 : j ≥ 1 := by omega
      by_cases hj1_eq : j = 1
      · subst hj1_eq
        rw [Nat.cast_one, one_mul]
        exact hkey 0
      have hj2 : j ≥ 2 := by omega
      have hjm1 : j - 1 ≥ 1 := by omega
      have hih := ih (j - 1) (by omega) hjm1
      have hkey_j := hkey (j - 1)
      rw [Nat.sub_add_cancel hj1] at hkey_j
      have hmono_j : FObj f g (alg.x j) ≤ FObj f g (alg.x (j - 1)) :=
        alg_Fx_monotone alg j hj1
      have hj_cast : (↑j : ℝ) = ↑(j - 1) + 1 := by
        rw [Nat.cast_sub hj1, Nat.cast_one]; ring
      rw [hj_cast, add_mul, one_mul]
      have hjm1_pos : (0 : ℝ) < ↑(j - 1) := by exact_mod_cast (show 0 < j - 1 from by omega)
      have hstep1 : ↑(j - 1) * (FObj f g (alg.x j) - FObj f g xstar)
          ≤ ↑(j - 1) * (FObj f g (alg.x (j - 1)) - FObj f g xstar) := by
        exact mul_le_mul_of_nonneg_left (by linarith [hmono_j]) (le_of_lt hjm1_pos)
      have hstep2 : ↑(j - 1) * (FObj f g (alg.x (j - 1)) - FObj f g xstar)
          + (FObj f g (alg.x j) - FObj f g xstar)
          ≤ Lbar alg / 2 * (‖xstar - alg.x 0‖ ^ 2 - ‖xstar - alg.x (j - 1)‖ ^ 2)
            + (FObj f g (alg.x j) - FObj f g xstar) := by
        linarith [hih, hstep1]
      have hstep3 : Lbar alg / 2 * (‖xstar - alg.x 0‖ ^ 2 - ‖xstar - alg.x (j - 1)‖ ^ 2)
          + (FObj f g (alg.x j) - FObj f g xstar)
          ≤ Lbar alg / 2 * (‖xstar - alg.x 0‖ ^ 2 - ‖xstar - alg.x j‖ ^ 2) := by
        linarith [hkey_j]
      linarith [hstep1, hstep2, hstep3]
  have hmain_k := hmain k hk
  have hnorm_nn : 0 ≤ ‖xstar - alg.x k‖ ^ 2 := sq_nonneg _
  have hLbar_nn : 0 ≤ Lbar alg / 2 := by linarith
  have hbound : (↑k : ℝ) * (FObj f g (alg.x k) - FObj f g xstar)
      ≤ Lbar alg / 2 * ‖xstar - alg.x 0‖ ^ 2 := by
    have h1 : Lbar alg / 2 * (‖xstar - alg.x 0‖ ^ 2 - ‖xstar - alg.x k‖ ^ 2)
        ≤ Lbar alg / 2 * ‖xstar - alg.x 0‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith [hnorm_nn]) hLbar_nn
    linarith [hmain_k, h1]
  rw [hx0] at hbound
  have hk_pos : (0 : ℝ) < ↑k := by exact_mod_cast (show 0 < k from hk)
  have h2k_pos : (0 : ℝ) < 2 * ↑k := by linarith
  have hnorm_eq : ‖xstar - alg.x0‖ ^ 2 = ‖alg.x0 - xstar‖ ^ 2 := by
    rw [show xstar - alg.x0 = -(alg.x0 - xstar) from by abel, norm_neg]
  rw [hnorm_eq] at hbound
  rw [le_div_iff₀ h2k_pos]
  have h2final : 2 * (↑k * (FObj f g (alg.x k) - FObj f g xstar))
      ≤ Lbar alg * ‖alg.x0 - xstar‖ ^ 2 := by
    have : 2 * (Lbar alg / 2 * ‖alg.x0 - xstar‖ ^ 2) = Lbar alg * ‖alg.x0 - xstar‖ ^ 2 := by ring
    linarith [hbound, this]
  rw [show (FObj f g (alg.x k) - FObj f g xstar) * (2 * ↑k)
      = 2 * (↑k * (FObj f g (alg.x k) - FObj f g xstar)) from by ring]
  exact h2final

/-! ## Backtracking termination and minimal accepting index --/

/-- Predicate: the backtracking index `i` is *accepted* at point `y` with base
    stepsize `ℓ`, i.e. `F(p_{η^i·ℓ}(y)) ≤ Q_{η^i·ℓ}(p_{η^i·ℓ}(y), y)`.

    The Lipschitz constant `L` is **not** part of this predicate; it is used
    only to prove that some accepting index exists (`acceptAt_exists`). -/
def acceptAt (f : E → ℝ) (f' : E → E) (g : E → ℝ) (eta ell : ℝ) (heta : eta > 1)
    (hell : ell > 0) (y : E) (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (i : ℕ) : Prop :=
  have h0 : 0 < eta := lt_trans zero_lt_one heta
  FObj f g (proxL f' g (eta ^ i * ell)
    (mul_pos (pow_pos h0 i) hell) y hg_cont hg_conv) ≤
    QModel f f' g (eta ^ i * ell)
      (proxL f' g (eta ^ i * ell) (mul_pos (pow_pos h0 i) hell) y hg_cont hg_conv) y

instance instAcceptAtDecidable (f : E → ℝ) (f' : E → E) (g : E → ℝ) (eta ell : ℝ)
    (heta : eta > 1) (hell : ell > 0) (y : E) (hg_cont : Continuous g)
    (hg_conv : ConvexOn ℝ Set.univ g) (i : ℕ) :
    Decidable (acceptAt f f' g eta ell heta hell y hg_cont hg_conv i) :=
  Classical.propDecidable _

/-- For any point `y` and base stepsize `ℓ > 0`, there exists a backtracking
    index `i` such that `η^i·ℓ` satisfies the acceptance condition.

    The Lipschitz constant `L` is used **only** here, to find `i` with
    `η^i·ℓ ≥ L`; then `acceptance_when_large` gives the condition. -/
theorem acceptAt_exists (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (ell : ℝ) (hell : ell > 0) (y : E) :
    ∃ i : ℕ, acceptAt f f' g eta ell heta hell y hg_cont hg_conv i := by
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (L / ell) heta
  have h1 : L < eta ^ i * ell := (div_lt_iff₀ hell).mp hi
  have hge : L ≤ eta ^ i * ell := le_of_lt h1
  refine ⟨i, ?_⟩
  exact acceptance_when_large f f' g hdiff L hL hlip hg_cont hg_conv (eta ^ i * ell) hge y

/-- The minimal accepting (backtracking) index, defined via `Nat.find`. -/
noncomputable def btIndex (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (ell : ℝ) (hell : ell > 0) (y : E) : ℕ :=
  Nat.find (acceptAt_exists f f' g hdiff L hL hlip hg_cont hg_conv eta heta ell hell y)

/-- `btIndex` satisfies the acceptance condition. -/
theorem btIndex_accept (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (ell : ℝ) (hell : ell > 0) (y : E) :
    acceptAt f f' g eta ell heta hell y hg_cont hg_conv
      (btIndex f f' g hdiff L hL hlip hg_cont hg_conv eta heta ell hell y) :=
  Nat.find_spec (acceptAt_exists f f' g hdiff L hL hlip hg_cont hg_conv eta heta ell hell y)

/-- Minimality of `btIndex`: no smaller index is accepted. -/
theorem btIndex_minimal (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (ell : ℝ) (hell : ell > 0) (y : E) (j : ℕ)
    (hj : j < btIndex f f' g hdiff L hL hlip hg_cont hg_conv eta heta ell hell y) :
    ¬ acceptAt f f' g eta ell heta hell y hg_cont hg_conv j :=
  Nat.find_min (acceptAt_exists f f' g hdiff L hL hlip hg_cont hg_conv eta heta ell hell y) hj

/-! ## Recursive construction of the ISTABt iterates --/

/-- State carried through the recursion: current iterate `y`, current
    stepsize `ell` together with the proof `hell : 0 < ell`, and the
    backtracking index `ik` used to reach this state (set to `0` initially). -/
structure StepState (E : Type*) where
  y : E
  ell : ℝ
  hell : 0 < ell
  ik : ℕ

/-- One backtracking step: from a state `(y, ℓ)` compute the next state by
    finding the minimal accepting index, updating the stepsize and the iterate. -/
noncomputable def nextStep (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (st : StepState E) : StepState E :=
  have h0 : 0 < eta := lt_trans zero_lt_one heta
  let j := btIndex f f' g hdiff L hL hlip hg_cont hg_conv eta heta st.ell st.hell st.y
  let Lnew := eta ^ j * st.ell
  let hLnew : 0 < Lnew := mul_pos (pow_pos h0 j) st.hell
  let p := proxL f' g Lnew hLnew st.y hg_cont hg_conv
  ⟨p, Lnew, hLnew, j⟩

/-- The full state sequence, defined by structural recursion on `ℕ`.

    `stepStates ... 0 = ⟨x₀, L₀, L₀>0, 0⟩` and
    `stepStates ... (k+1) = nextStep ... (stepStates ... k)`. -/
noncomputable def stepStates (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) : ℕ → StepState E
  | 0 => ⟨x0, L0, hL0, 0⟩
  | k + 1 => nextStep f f' g hdiff L hL hlip hg_cont hg_conv eta heta
      (stepStates f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k)

/-- The iterate sequence `x_k`. -/
noncomputable def xSeq (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) : E :=
  (stepStates f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k).y

/-- The stepsize sequence `L_k`. -/
noncomputable def LkSeq (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) : ℝ :=
  (stepStates f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k).ell

/-- The backtracking-index sequence `i_k`. -/
noncomputable def ikSeq (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) : ℕ :=
  (stepStates f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k).ik

/-- `L_k > 0` for all `k` (carried structurally by the state). -/
noncomputable def LkSeq_pos (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) :
    0 < LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k :=
  (stepStates f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k).hell

/-! ### Initial conditions --/

theorem xSeq_init (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) :
    xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 0 = x0 := rfl

theorem LkSeq_init (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) :
    LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 0 = L0 := rfl

theorem ikSeq_init (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) :
    ikSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 0 = 0 := rfl

/-! ### Successor equations --/

theorem ikSeq_succ (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) :
    ikSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k + 1) =
      btIndex f f' g hdiff L hL hlip hg_cont hg_conv eta heta
        (LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k)
        (LkSeq_pos f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k)
        (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k) := rfl

theorem LkSeq_succ (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) :
    LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k + 1) =
      eta ^ (ikSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k + 1)) *
        LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k := rfl

theorem xSeq_succ (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) :
    xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k + 1) =
      proxL f' g
        (LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k + 1))
        (LkSeq_pos f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k + 1))
        (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k)
        hg_cont hg_conv := rfl

/-! ### Dynamic properties: acceptance, minimality, updates --/

/-- Acceptance condition holds for every `k ≥ 1`. -/
theorem seq_acceptance (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) (hk : k ≥ 1) :
    FObj f g (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k) ≤
      QModel f f' g (LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k)
        (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k)
        (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)) := by
  have hn : k = (k - 1) + 1 := by omega
  rw [hn, Nat.add_sub_cancel]
  have hik := ikSeq_succ f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)
  have hacc := btIndex_accept f f' g hdiff L hL hlip hg_cont hg_conv eta heta
    (LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
    (LkSeq_pos f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
    (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
  rw [← hik] at hacc
  exact hacc

/-- Minimality of `i_k` for every `k ≥ 1`: every `j < i_k` fails acceptance. -/
theorem seq_ik_minimal (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) (hk : k ≥ 1)
    (j : ℕ) (hj : j < ikSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k) :
    ¬ FObj f g (proxL f' g
        (eta ^ j * LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
        (mul_pos (pow_pos (lt_trans zero_lt_one heta) j)
          (LkSeq_pos f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)))
        (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
        hg_cont hg_conv) ≤
      QModel f f' g
        (eta ^ j * LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
        (proxL f' g
          (eta ^ j * LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
          (mul_pos (pow_pos (lt_trans zero_lt_one heta) j)
            (LkSeq_pos f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)))
          (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
          hg_cont hg_conv)
        (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)) := by
  have hn : k = (k - 1) + 1 := by omega
  rw [hn] at hj
  have hik := ikSeq_succ f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)
  rw [hik] at hj
  exact btIndex_minimal f f' g hdiff L hL hlip hg_cont hg_conv eta heta
    (LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
    (LkSeq_pos f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
    (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)) j hj

/-- Step-size update `L_k = η^{i_k}·L_{k-1}` for `k ≥ 1`. -/
theorem seq_Lk_update (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) (hk : k ≥ 1) :
    LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k =
      eta ^ (ikSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k) *
        LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1) := by
  have hn : k = (k - 1) + 1 := by omega
  rw [hn, Nat.add_sub_cancel]
  exact LkSeq_succ f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)

/-- Iterate update `x_k = p_{L_k}(x_{k-1})` for `k ≥ 1`. -/
theorem seq_x_update (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (L : ℝ) (hL : L > 0)
    (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E) (k : ℕ) (hk : k ≥ 1) :
    xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k =
      proxL f' g
        (LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k)
        (LkSeq_pos f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k)
        (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1))
        hg_cont hg_conv := by
  have hn : k = (k - 1) + 1 := by omega
  rw [hn, Nat.add_sub_cancel]
  exact xSeq_succ f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 (k - 1)

/-! ## Construction of an `ISTABt` instance and the final rate theorem --/

/-- The `ISTABt` instance generated by the backtracking recursion from the
    original data `x₀`, `L₀ > 0`, `η > 1` and the function assumptions.
    All dynamic properties (termination, acceptance, minimality, updates) are
    **proven**, not assumed. -/
noncomputable def mkISTABt (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (hf_convex : ConvexOn ℝ Set.univ f)
    (L : ℝ) (hL : L > 0) (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E)
    (hF_min : ∃ xstar, IsMinOn (FObj f g) Set.univ xstar) : ISTABt f f' g where
  x := xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  Lk := LkSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  ik := ikSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  L := L
  L0 := L0
  eta := eta
  x0 := x0
  hL := hL
  hL0 := hL0
  heta := heta
  hf_diff := hdiff
  hf_convex := hf_convex
  hf_lip := hlip
  hg_continuous := hg_cont
  hg_convex := hg_conv
  hF_min := hF_min
  x_init := xSeq_init f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  Lk_init := LkSeq_init f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  Lk_pos := LkSeq_pos f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  acceptance := seq_acceptance f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  ik_minimal := seq_ik_minimal f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  Lk_update := seq_Lk_update f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0
  x_update := seq_x_update f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0

/-- **Final rate theorem** — stated directly in terms of the original data and
    assumptions (no `ISTABt` instance needed): for any minimizer `x*` and
    `k ≥ 1`,
    `F(x_k) - F(x*) ≤ max{L₀, ηL}·‖x₀ - x*‖² / (2k)`. -/
theorem istabt_rate (f : E → ℝ) (f' : E → E) (g : E → ℝ)
    (hdiff : ∀ z, HasGradientAt f (f' z) z) (hf_convex : ConvexOn ℝ Set.univ f)
    (L : ℝ) (hL : L > 0) (hlip : LipschitzWith (⟨L, hL.le⟩ : NNReal) f')
    (hg_cont : Continuous g) (hg_conv : ConvexOn ℝ Set.univ g)
    (eta : ℝ) (heta : eta > 1) (L0 : ℝ) (hL0 : L0 > 0) (x0 : E)
    (hF_min : ∃ xstar, IsMinOn (FObj f g) Set.univ xstar)
    (xstar : E) (hmin : IsMinOn (FObj f g) Set.univ xstar) (k : ℕ) (hk : k ≥ 1) :
    FObj f g (xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k) -
        FObj f g xstar ≤
      max L0 (eta * L) * ‖x0 - xstar‖ ^ 2 / (2 * (k : ℝ)) := by
  set alg := mkISTABt f f' g hdiff hf_convex L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 hF_min
  have hrate := alg_rate alg xstar hmin k hk
  have hx : alg.x k =
      xSeq f f' g hdiff L hL hlip hg_cont hg_conv eta heta L0 hL0 x0 k := rfl
  have hx0 : alg.x0 = x0 := rfl
  have hLbar : Lbar alg = max L0 (eta * L) := by
    unfold Lbar
    rw [show alg.L0 = L0 from rfl, show alg.eta = eta from rfl, show alg.L = L from rfl]
  rw [hx, hx0, hLbar] at hrate
  exact hrate

end ISTABt_section
