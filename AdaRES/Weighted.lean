import AdaRES.Transform
import AdaRES.PaperCount

open scoped BigOperators InnerProduct

namespace AdaRES

noncomputable section

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ ι
variable {L : ι → ℝ}

def weightedObjective (data : WeightedSmooth L) (ψ : ProperConvex V) (x : V) : ℝ :=
  data.f x + ψ.f x

structure WeightedMinimum (data : WeightedSmooth L) (ψ : ProperConvex V) where
  xstar : V
  dom : xstar ∈ ψ.dom
  minimal : ∀ x ∈ ψ.dom, weightedObjective data ψ xstar ≤ weightedObjective data ψ x

def weightedSolutions {data : WeightedSmooth L} {ψ : ProperConvex V}
    (opt : WeightedMinimum data ψ) : Set V :=
  {x | x ∈ ψ.dom ∧ weightedObjective data ψ x = weightedObjective data ψ opt.xstar}

def weightedGap {data : WeightedSmooth L} {ψ : ProperConvex V} (opt : WeightedMinimum data ψ) (x : V) : ℝ :=
  weightedObjective data ψ x - weightedObjective data ψ opt.xstar

def weightedResidual (hL : ∀ i, 0 < L i) (data : WeightedSmooth L) (ψ : ProperConvex V) (x : V) : ℝ :=
  weightedSq L (weightedStep hL data ψ x - x)

def WeightedLocalGrowth (hL : ∀ i, 0 < L i) {data : WeightedSmooth L} {ψ : ProperConvex V}
    (opt : WeightedMinimum data ψ) (x0 : V) (μ : ℝ) : Prop :=
  let B := diagonalEquiv L hL
  ∀ x ∈ ψ.dom, weightedObjective data ψ x ≤ weightedObjective data ψ x0 →
    μ / 2 * (Metric.infDist (B x) (B '' weightedSolutions opt))^2 ≤ weightedGap opt x

theorem normalized_domain (hL : ∀ i, 0 < L i) (ψ : ProperConvex V) (x : V) :
    diagonalEquiv L hL x ∈ (normalizeRegularizer L hL ψ).dom ↔ x ∈ ψ.dom := by
  let B := diagonalEquiv L hL
  change B.symm (B x) ∈ ψ.dom ↔ x ∈ ψ.dom
  rw [B.symm_apply_apply]

theorem normalized_objective (hL : ∀ i, 0 < L i) (data : WeightedSmooth L) (ψ : ProperConvex V) (x : V) :
    objective (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) (diagonalEquiv L hL x)
      = weightedObjective data ψ x := by
  let B := diagonalEquiv L hL
  change data.f (B.symm (B x)) + ψ.f (B.symm (B x)) = data.f x + ψ.f x
  rw [B.symm_apply_apply]

def normalizeMinimum (hL : ∀ i, 0 < L i) {data : WeightedSmooth L} {ψ : ProperConvex V}
    (opt : WeightedMinimum data ψ) : Minimum (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) := by
  let B := diagonalEquiv L hL
  refine { xstar := B opt.xstar
           dom := (normalized_domain hL ψ _).2 opt.dom
           minimal := ?_ }
  intro y hy
  obtain ⟨x, rfl⟩ := B.surjective y
  rw [normalized_objective, normalized_objective]
  exact opt.minimal x ((normalized_domain hL ψ x).1 hy)

theorem normalized_solutions (hL : ∀ i, 0 < L i) {data : WeightedSmooth L} {ψ : ProperConvex V}
    (opt : WeightedMinimum data ψ) : solutions (normalizeMinimum hL opt) = diagonalEquiv L hL '' weightedSolutions opt := by
  let B := diagonalEquiv L hL
  have H (x : V) : B x ∈ solutions (normalizeMinimum hL opt) ↔ x ∈ weightedSolutions opt := by
    change (B x ∈ (normalizeRegularizer L hL ψ).dom ∧
      objective (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) (B x) =
        objective (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) (B opt.xstar)) ↔
      (x ∈ ψ.dom ∧ weightedObjective data ψ x = weightedObjective data ψ opt.xstar)
    rw [normalized_domain, normalized_objective, normalized_objective]
  ext y
  obtain ⟨x, rfl⟩ := B.surjective y
  constructor
  · intro hx
    exact ⟨x, (H x).1 hx, rfl⟩
  · rintro ⟨z, hz, he⟩
    have hz' : z = x := B.injective he
    subst z
    exact (H x).2 hz

theorem normalized_gap (hL : ∀ i, 0 < L i) {data : WeightedSmooth L} {ψ : ProperConvex V}
    (opt : WeightedMinimum data ψ) (x : V) :
    gap (normalizeMinimum hL opt) (diagonalEquiv L hL x) = weightedGap opt x := by
  let B := diagonalEquiv L hL
  change objective (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) (B x) -
    objective (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) (B opt.xstar) = _
  rw [normalized_objective, normalized_objective]
  rfl

theorem normalized_growth (hL : ∀ i, 0 < L i) {data : WeightedSmooth L} {ψ : ProperConvex V}
    (opt : WeightedMinimum data ψ) (x0 : V) {μ : ℝ} (hq : WeightedLocalGrowth hL opt x0 μ) :
    LocalGrowth (normalizeMinimum hL opt) (diagonalEquiv L hL x0) μ := by
  let B := diagonalEquiv L hL
  intro y hy hlevel
  obtain ⟨x, rfl⟩ := B.surjective y
  rw [normalized_objective, normalized_objective] at hlevel
  have H := hq x ((normalized_domain hL ψ x).1 hy) hlevel
  rw [normalized_solutions, normalized_gap]
  exact H

theorem normalized_residual (hL : ∀ i, 0 < L i) (data : WeightedSmooth L) (ψ : ProperConvex V) (x : V) :
    residual (normalizeSmooth hL data) (normalizeRegularizer L hL ψ) (diagonalEquiv L hL x)
      = weightedResidual hL data ψ x := by
  unfold weightedResidual residual
  rw [← diagonal_norm_sq L hL, map_sub, weightedStep_map]

def normalizeParams (hL : ∀ i, 0 < L i) (p : RestartParams V) : RestartParams V :=
  { p with x0 := diagonalEquiv L hL p.x0 }

variable (hL : ∀ i, 0 < L i)

def dataB (data : WeightedSmooth L) : Smooth V := normalizeSmooth hL data

def ψB (ψ : ProperConvex V) : ProperConvex V := normalizeRegularizer L hL ψ

def weightedFistaState (data : WeightedSmooth L) (ψ : ProperConvex V) (x0 : V) (n : ℕ) : FState V :=
  let B := diagonalEquiv L hL
  let s := fistaState (dataB hL data) (ψB hL ψ) (B x0) n
  ⟨B.symm s.x, B.symm s.z⟩

theorem weightedFistaState_zero (data : WeightedSmooth L) (ψ : ProperConvex V) (x0 : V) :
    let s := weightedFistaState hL data ψ x0 0
    s.x = x0 ∧ s.z = x0 := by simp [weightedFistaState, fistaState]

theorem weightedFistaState_next (data : WeightedSmooth L) (ψ : ProperConvex V) (x0 : V) (n : ℕ) :
    let s := weightedFistaState hL data ψ x0 n
    let q := weightedFistaState hL data ψ x0 (n + 1)
    let t := theta n
    q.x = weightedStep hL data ψ ((1 - t) • s.x + t • s.z) ∧
      q.z = s.z + t⁻¹ • (q.x - ((1 - t) • s.x + t • s.z)) := by
  let B := diagonalEquiv L hL
  let N := fistaState (dataB hL data) (ψB hL ψ) (B x0)
  let t := theta n
  let y := (1 - t) • (N n).x + t • (N n).z
  have hx : (N (n + 1)).x = step (dataB hL data) (ψB hL ψ) y := rfl
  have hz : (N (n + 1)).z = (N n).z + t⁻¹ • ((N (n + 1)).x - y) := rfl
  constructor
  · change B.symm (N (n + 1)).x = B.symm (step (dataB hL data) (ψB hL ψ)
      (B ((1 - t) • B.symm (N n).x + t • B.symm (N n).z)))
    rw [map_add, map_smul, map_smul, B.apply_symm_apply, B.apply_symm_apply, hx]
  · change B.symm (N (n + 1)).z = B.symm (N n).z + t⁻¹ •
      (B.symm (N (n + 1)).x - ((1 - t) • B.symm (N n).x + t • B.symm (N n).z))
    rw [hz, map_add, map_smul, map_sub]
    dsimp only [y]
    rw [map_add, map_smul, map_smul]

def weightedPhasePoint (data : WeightedSmooth L) (ψ : ProperConvex V) (prev : V) (μ : ℝ) (t : ℕ) : V :=
  let B := diagonalEquiv L hL
  B.symm (phasePoint (dataB hL data) (ψB hL ψ) (B prev) μ t)

theorem weightedPhasePoint_zero (data : WeightedSmooth L) (ψ : ProperConvex V) (prev : V) (μ : ℝ) :
    weightedPhasePoint hL data ψ prev μ 0 = weightedStep hL data ψ prev := rfl

theorem weightedPhasePoint_succ (data : WeightedSmooth L) (ψ : ProperConvex V)
    (prev : V) (μ : ℝ) (t : ℕ) :
    weightedPhasePoint hL data ψ prev μ (t + 1) =
      (weightedFistaState hL data ψ (weightedPhasePoint hL data ψ prev μ t) (period μ)).x := by
  let B := diagonalEquiv L hL
  let x := phasePoint (dataB hL data) (ψB hL ψ) (B prev) μ t
  change B.symm (fista (dataB hL data) (ψB hL ψ) x (period μ)) =
    B.symm (fista (dataB hL data) (ψB hL ψ) (B (B.symm x)) (period μ))
  rw [B.apply_symm_apply]

def weightedPrevious (data : WeightedSmooth L) (ψ : ProperConvex V) (p : RestartParams V) (s : ℕ) : V :=
  (diagonalEquiv L hL).symm (previous (dataB hL data) (ψB hL ψ) (normalizeParams hL p) s)

theorem weightedPrevious_map (data : WeightedSmooth L) (ψ : ProperConvex V) (p : RestartParams V) (s : ℕ) :
    diagonalEquiv L hL (weightedPrevious hL data ψ p s) =
      previous (dataB hL data) (ψB hL ψ) (normalizeParams hL p) s :=
  (diagonalEquiv L hL).apply_symm_apply _

theorem weightedPrevious_zero (data : WeightedSmooth L) (ψ : ProperConvex V) (p : RestartParams V) :
    weightedPrevious hL data ψ p 0 = p.x0 := by simp [weightedPrevious, previous, normalizeParams]

def weightedBlocks (data : WeightedSmooth L) (ψ : ProperConvex V) (prev : V)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) : ℕ :=
  firstBlocks (dataB hL data) (ψB hL ψ) (diagonalEquiv L hL prev) hμ hε

theorem weighted_stageBlocks_eq (data : WeightedSmooth L) (ψ : ProperConvex V) (p : RestartParams V) (s : ℕ) :
    stageBlocks (dataB hL data) (ψB hL ψ) (normalizeParams hL p) s =
      weightedBlocks hL data ψ (weightedPrevious hL data ψ p s) (estimate_pos p.μ0_pos s) p.ε_pos := by
  unfold weightedBlocks
  rw [weightedPrevious_map]
  rfl

theorem weightedPrevious_succ (data : WeightedSmooth L) (ψ : ProperConvex V)
    (p : RestartParams V) (s : ℕ) :
    weightedPrevious hL data ψ p (s + 1) = weightedPhasePoint hL data ψ
      (weightedPrevious hL data ψ p s) (estimate p.μ0 s)
      (weightedBlocks hL data ψ (weightedPrevious hL data ψ p s) (estimate_pos p.μ0_pos s) p.ε_pos) := by
  rw [← weighted_stageBlocks_eq hL data ψ p s]
  show weightedPrevious hL data ψ p (s + 1) =
    (diagonalEquiv L hL).symm (phasePoint (dataB hL data) (ψB hL ψ)
      (diagonalEquiv L hL (weightedPrevious hL data ψ p s)) (estimate p.μ0 s)
      (stageBlocks (dataB hL data) (ψB hL ψ) (normalizeParams hL p) s))
  rw [weightedPrevious_map]
  rfl

def weightedBlockStop (data : WeightedSmooth L) (ψ : ProperConvex V) (prev : V) (μ ε : ℝ) (t : ℕ) : Prop :=
  (16 * weightedResidual hL data ψ prev / μ) * (phaseFactor μ)^t <
      weightedResidual hL data ψ (weightedPhasePoint hL data ψ prev μ t) ∨
    weightedResidual hL data ψ (weightedPhasePoint hL data ψ prev μ t) ≤ ε

theorem weighted_blockStop_eq (data : WeightedSmooth L) (ψ : ProperConvex V) (prev : V) (μ ε : ℝ) (t : ℕ) :
    blockStop (dataB hL data) (ψB hL ψ) (diagonalEquiv L hL prev) μ ε t ↔
      weightedBlockStop hL data ψ prev μ ε t := by
  let B := diagonalEquiv L hL
  let x := phasePoint (dataB hL data) (ψB hL ψ) (B prev) μ t
  have hx : B (weightedPhasePoint hL data ψ prev μ t) = x := B.apply_symm_apply _
  have hr := normalized_residual hL data ψ (weightedPhasePoint hL data ψ prev μ t)
  change residual (dataB hL data) (ψB hL ψ) (B (weightedPhasePoint hL data ψ prev μ t)) = _ at hr
  rw [hx] at hr
  unfold blockStop phaseConstant weightedBlockStop
  change (16 * residual (dataB hL data) (ψB hL ψ) (B prev) / μ * (phaseFactor μ)^t <
    residual (dataB hL data) (ψB hL ψ) x ∨ residual (dataB hL data) (ψB hL ψ) x ≤ ε) ↔ _
  have hprev : residual (dataB hL data) (ψB hL ψ) (B prev) =
      weightedResidual hL data ψ prev := normalized_residual hL data ψ prev
  rw [hprev, hr]

theorem weighted_blocks_spec (data : WeightedSmooth L) (ψ : ProperConvex V) (prev : V)
    {μ ε : ℝ} (hμ : 0 < μ) (hε : 0 < ε) :
    let t := weightedBlocks hL data ψ prev hμ hε
    0 < t ∧ weightedBlockStop hL data ψ prev μ ε t ∧
      ∀ j, 0 < j → j < t → ¬weightedBlockStop hL data ψ prev μ ε j := by
  let B := diagonalEquiv L hL
  refine ⟨firstBlocks_pos _ _ (B prev) hμ hε, ?_, ?_⟩
  · exact (weighted_blockStop_eq hL data ψ prev μ ε _).1 (firstBlocks_spec _ _ (B prev) hμ hε)
  · intro j hj hjt hs
    exact firstBlocks_minimal _ _ (B prev) hμ hε hj hjt ((weighted_blockStop_eq hL data ψ prev μ ε j).2 hs)

theorem weighted_stageSuccess_eq (data : WeightedSmooth L) (ψ : ProperConvex V) (p : RestartParams V) (s : ℕ) :
    stageSuccess (dataB hL data) (ψB hL ψ) (normalizeParams hL p) s ↔
      weightedResidual hL data ψ (weightedPrevious hL data ψ p (s + 1)) ≤ p.ε := by
  show residual (dataB hL data) (ψB hL ψ)
    (previous (dataB hL data) (ψB hL ψ) (normalizeParams hL p) (s + 1)) ≤ p.ε ↔ _
  have hr : residual (dataB hL data) (ψB hL ψ)
      (diagonalEquiv L hL (weightedPrevious hL data ψ p (s + 1))) =
        weightedResidual hL data ψ (weightedPrevious hL data ψ p (s + 1)) :=
    normalized_residual hL data ψ (weightedPrevious hL data ψ p (s + 1))
  rw [weightedPrevious_map] at hr
  rw [hr]

theorem weighted_stage_exists {data : WeightedSmooth L} {ψ : ProperConvex V}
    (p : RestartParams V) (h0 : p.x0 ∈ ψ.dom)
    (opt : WeightedMinimum data ψ) {μF : ℝ} (hF : 0 < μF)
    (hq : WeightedLocalGrowth hL opt p.x0 μF) :
    ∃ s, stageSuccess (dataB hL data) (ψB hL ψ) (normalizeParams hL p) s :=
  stage_exists (normalizeMinimum hL opt) (normalizeParams hL p)
    ((normalized_domain hL ψ p.x0).2 h0) hF (normalized_growth hL opt p.x0 hq)

theorem weighted_main {data : WeightedSmooth L} {ψ : ProperConvex V}
    (opt : WeightedMinimum data ψ) (p : RestartParams V)
    (h0 : p.x0 ∈ ψ.dom) {μF : ℝ} (hF : 0 < μF)
    (hq : WeightedLocalGrowth hL opt p.x0 μF) :
    let B := diagonalEquiv L hL
    let pB := normalizeParams hL p
    let hterm := weighted_stage_exists hL p h0 opt hF hq
    let s := firstStage pB hterm
    let y := B.symm (resultPoint pB hterm)
    let S := goodStage p.μ0 μF
    let U := earlyRounds (weightedGap opt p.x0) μF p.ε
    let W := goodRounds (weightedGap opt p.x0) p.ε
    y = weightedStep hL data ψ (weightedPrevious hL data ψ p (s + 1)) ∧
    s ≤ S ∧
    (∀ j < s, ¬(weightedResidual hL data ψ (weightedPrevious hL data ψ p (j + 1)) ≤ p.ε)) ∧
    weightedResidual hL data ψ (weightedPrevious hL data ψ p (s + 1)) ≤ p.ε ∧
    y ∈ ψ.dom ∧ weightedResidual hL data ψ y ≤ p.ε ∧ weightedGap opt y ≤ 8 * p.ε / μF ∧
    callCount pB hterm = (1 + ∑ j ∈ Finset.range (s + 1),
      (weightedBlocks hL data ψ (weightedPrevious hL data ψ p j)
        (estimate_pos p.μ0_pos j) p.ε_pos * period (estimate p.μ0 j) + 1)) ∧
    callCount pB hterm ≤ 1 + (∑ j ∈ Finset.range S, (U * period (estimate p.μ0 j) + 1))
      + (W * period (estimate p.μ0 S) + 1) := by
  intro B pB hterm s y S U W
  let optB := normalizeMinimum hL opt
  have hx0 : pB.x0 ∈ (ψB hL ψ).dom := (normalized_domain hL ψ p.x0).2 h0
  have hqB : LocalGrowth optB pB.x0 μF := normalized_growth hL opt p.x0 hq
  have H := result_spec optB pB hx0 hF hqB hterm
  have hy : B y = resultPoint pB hterm := B.apply_symm_apply _
  have hstep : y = weightedStep hL data ψ (weightedPrevious hL data ψ p (s + 1)) := by
    change B.symm (step (dataB hL data) (ψB hL ψ) (previous (dataB hL data) (ψB hL ψ) pB (s + 1))) =
      B.symm (step (dataB hL data) (ψB hL ψ)
        (B (weightedPrevious hL data ψ p (s + 1))))
    have he : B (weightedPrevious hL data ψ p (s + 1)) =
        previous (dataB hL data) (ψB hL ψ) pB (s + 1) := weightedPrevious_map hL data ψ p _
    rw [he]
  refine ⟨hstep, H.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj hr
    exact (H.2.1 j hj) ((weighted_stageSuccess_eq hL data ψ p j).2 hr)
  · exact (weighted_stageSuccess_eq hL data ψ p s).1 H.2.2.1
  · apply (normalized_domain hL ψ y).1
    change B y ∈ (ψB hL ψ).dom
    rw [hy]
    exact H.2.2.2.1
  · have hr := normalized_residual hL data ψ y
    change residual (dataB hL data) (ψB hL ψ) (B y) = weightedResidual hL data ψ y at hr
    rw [hy] at hr
    rw [← hr]
    exact H.2.2.2.2.1
  · have hg := normalized_gap hL opt y
    change gap optB (B y) = weightedGap opt y at hg
    rw [hy] at hg
    rw [← hg]
    exact H.2.2.2.2.2
  · change 1 + (∑ j ∈ Finset.range (s + 1),
        (stageBlocks (dataB hL data) (ψB hL ψ) pB j * period (estimate p.μ0 j) + 1)) = _
    apply congrArg (fun n : ℕ => 1 + n)
    apply Finset.sum_congr rfl
    intro j hj
    have he : stageBlocks (dataB hL data) (ψB hL ψ) pB j =
        weightedBlocks hL data ψ (weightedPrevious hL data ψ p j) (estimate_pos p.μ0_pos j) p.ε_pos :=
      weighted_stageBlocks_eq hL data ψ p j
    rw [he]
  · have Hc := callCount_bound optB pB hx0 hF hqB hterm
    have hgap : gap optB pB.x0 = weightedGap opt p.x0 := normalized_gap hL opt p.x0
    rw [hgap] at Hc
    exact Hc

end
end AdaRES
