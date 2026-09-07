module

/-
  Coarse Incidence Geometric Bridge

  Constructs the geometric data (point set, tube family, incidence, regularity)
  needed to apply `coarse_config_regular_incidence` from a CTNiceConfiguration.

  Main lemma: `coarse_incidence_geometric_bridge`

  ## Recipe

  1. Translate `coarseConfig.pointSet` by (-1/2,-1/2) so it fits in the unit ball.
  2. For each translated point p', recover p = p' - centerTranslation.
  3. Find a coarse square Q ∈ coarseConfig.P₀ containing p.
  4. Assign `coarseConfig.tubeFamily Q` as the tube family for p'.
  5. Prove incidence via the wide carrier trick: p ∈ Q, T intersects Q,
     |T.slope| ≤ 1 ⇒ p ∈ wideCarrier T ⇒ p' ∈ cthickening δ (canonicalWideCarrier T).
  6. Wire everything into `coarse_config_regular_incidence`.

  The caller supplies square-root regularity of the point set and the
  unpacked regular incidence estimate body.

  Whiteprint: combining_theorem_genuine / coarse_incidence_geometric_bridge
  Dependencies: IncidenceHelpers, CoarseRegularIncidenceBridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseRegularIncidenceBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.IncidenceHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence

/-! ========================================================================
   Translated point set and coarse square lookup
   ======================================================================== -/

/-- The coarse configuration's point set translated by (-1/2,-1/2). -/
def translatedCoarsePointSet {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ) : Set EuclideanPlane :=
  translationEquiv centerTranslation '' coarseConfig.pointSet

/-- Given a translated point p' in the translated coarse point set, recover
    the original point p = p' - centerTranslation. -/
def originalPoint (p' : EuclideanPlane) : EuclideanPlane :=
  p' - centerTranslation

/-- The original point of a translated point is in the coarse point set. -/
lemma originalPoint_in_coarsePointSet
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {p' : EuclideanPlane}
    (hp' : p' ∈ translatedCoarsePointSet coarseConfig) :
    originalPoint p' ∈ coarseConfig.pointSet := by
  rcases hp' with ⟨p, hp, h_eq⟩
  have h1 : p + centerTranslation = p' := h_eq
  have h2 : originalPoint p' = p := by
    dsimp only [originalPoint]
    have h : p' - centerTranslation = p := by
      calc p' - centerTranslation
        = (p + centerTranslation) - centerTranslation := by rw [h1]
      _ = p := by simp
    exact h
  rw [h2]
  exact hp

/-- Given a translated point p', find a coarse square Q ∈ coarseConfig.P₀
    containing the original point p. -/
noncomputable def coarseSquareOfPoint
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (p' : EuclideanPlane)
    (hp' : p' ∈ translatedCoarsePointSet coarseConfig) :
    DyadicSquare m :=
  let p := originalPoint p'
  let hp : p ∈ coarseConfig.pointSet := originalPoint_in_coarsePointSet hp'
  Classical.choose (show ∃ (Q : DyadicSquare m), Q ∈ coarseConfig.P₀ ∧ p ∈ Q.toSet from by
    simpa [NiceConfiguration.pointSet, Finset.mem_biUnion] using hp)

/-- The chosen coarse square is in coarseConfig.P₀. -/
lemma coarseSquareOfPoint_in_P₀
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {p' : EuclideanPlane}
    {hp' : p' ∈ translatedCoarsePointSet coarseConfig} :
    coarseSquareOfPoint coarseConfig p' hp' ∈ coarseConfig.P₀ :=
  (Classical.choose_spec (show ∃ (Q : DyadicSquare m), Q ∈ coarseConfig.P₀ ∧
      originalPoint p' ∈ Q.toSet from by
    simpa [NiceConfiguration.pointSet, Finset.mem_biUnion] using
      originalPoint_in_coarsePointSet hp')).1

/-- The original point is in the chosen coarse square. -/
lemma coarseSquareOfPoint_contains
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {p' : EuclideanPlane}
    {hp' : p' ∈ translatedCoarsePointSet coarseConfig} :
    originalPoint p' ∈ (coarseSquareOfPoint coarseConfig p' hp').toSet :=
  (Classical.choose_spec (show ∃ (Q : DyadicSquare m), Q ∈ coarseConfig.P₀ ∧
      originalPoint p' ∈ Q.toSet from by
    simpa [NiceConfiguration.pointSet, Finset.mem_biUnion] using
      originalPoint_in_coarsePointSet hp')).2

/-! ========================================================================
   Tube family construction
   ======================================================================== -/

/-- Tube family for a translated point: the coarse tubes associated to the
    coarse square containing the original point. -/
noncomputable def coarseTubeFamilyOfPoint
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (p' : EuclideanPlane)
    (hp' : p' ∈ translatedCoarsePointSet coarseConfig) :
    Finset (DyadicTube m) :=
  coarseConfig.tubeFamily (coarseSquareOfPoint coarseConfig p' hp')
    coarseSquareOfPoint_in_P₀

/-- The tube family is a subset of coarseConfig.T₀. -/
lemma coarseTubeFamilyOfPoint_sub_T₀
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {p' : EuclideanPlane}
    {hp' : p' ∈ translatedCoarsePointSet coarseConfig} :
    (coarseTubeFamilyOfPoint coarseConfig p' hp' : Set (DyadicTube m)) ⊆
      (coarseConfig.T₀ : Set (DyadicTube m)) :=
  coarseConfig.h_subset (coarseSquareOfPoint coarseConfig p' hp')
    coarseSquareOfPoint_in_P₀

/-- Each tube family is an S-set at coarse scale with constant CΔ. -/
lemma coarseTubeFamilyOfPoint_sset
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {p' : EuclideanPlane}
    {hp' : p' ∈ translatedCoarsePointSet coarseConfig} :
    IsDeltaSSet (dyadicDelta m) s CΔ
      (coarseTubeFamilyOfPoint coarseConfig p' hp' : Set (DyadicTube m)) :=
  coarseConfig.h_delta_s_set (coarseSquareOfPoint coarseConfig p' hp')
    coarseSquareOfPoint_in_P₀

/-! ========================================================================
   Incidence proof

   For p' in translated point set and T in its tube family:
   1. p = originalPoint p' is in coarse square Q
   2. T intersects Q (from coarseConfig.h_intersect)
   3. p ∈ wideCarrier T (wide carrier trick, |T.slope| ≤ 1)
   4. p + centerTranslation = p' ∈ translatedWideCarrier centerTranslation T
   5. translatedWideCarrier centerTranslation T = canonicalWideCarrier m T
   6. Hence p' ∈ cthickening δ (canonicalWideCarrier m T)
   ======================================================================== -/

/-- Incidence: every translated point is in the δ-thickening of the
    canonical wide carrier of every tube in its tube family. -/
lemma coarseTubeFamilyOfPoint_incidence
    {m : ℕ} {s CΔ : ℝ} {MΔ : ℕ}
    {coarseConfig : CTNiceConfiguration m s CΔ MΔ}
    {p' : EuclideanPlane}
    {hp' : p' ∈ translatedCoarsePointSet coarseConfig}
    {h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1}
    {T : DyadicTube m}
    (hT_in : T ∈ coarseTubeFamilyOfPoint coarseConfig p' hp') :
    p' ∈ Metric.cthickening (dyadicDelta m) (canonicalWideCarrier m T) := by
  let p := originalPoint p'
  let Q := coarseSquareOfPoint coarseConfig p' hp'
  have hQ_in_P0 : Q ∈ coarseConfig.P₀ := coarseSquareOfPoint_in_P₀
  have hp_in_Q : p ∈ Q.toSet := coarseSquareOfPoint_contains
  have h_intersect : (T.toSet ∩ Q.toSet).Nonempty :=
    coarseConfig.h_intersect Q hQ_in_P0 T hT_in
  have hT_in_T0 : T ∈ coarseConfig.T₀ :=
    coarseConfig.h_subset Q hQ_in_P0 hT_in
  have h_slope : |T.slope| ≤ 1 := h_slope_coarse T hT_in_T0
  have h_p_in_carrier : p ∈ wideCarrier T :=
    wideCarrier_contains_square_point h_intersect hp_in_Q h_slope
  have h_p'_eq : p + centerTranslation = p' := by
    simp [p, originalPoint] <;> abel
  have h_main : p + centerTranslation ∈
      Metric.cthickening (dyadicDelta m) (translatedWideCarrier centerTranslation T) :=
    translatedWideCarrier_incidence h_p_in_carrier
  have h_carrier_eq : translatedWideCarrier centerTranslation T = canonicalWideCarrier m T := by
    rfl
  rw [h_carrier_eq] at h_main
  rw [h_p'_eq] at h_main
  exact h_main

/-! ========================================================================
   Full bridge: apply the regular incidence estimate
   ======================================================================== -/

/-- Full geometric bridge: from coarse configuration + square-root regularity
    to the coarse tube cardinality lower bound.

    The caller supplies:
    - The unpacked regular incidence estimate body (`h_est_body`)
    - A point set `P_orig` contained in the translated coarse point set
    - Square-root regularity of `P_orig`
    - Slope bound for coarse tubes
    - Constant weakening `CΔ ≤ δ^{-εReg}`

    This lemma constructs the tube family, proves incidence and S-set
    properties, and wires everything into `coarse_config_regular_incidence`. -/
lemma coarse_incidence_geometric_bridge
    {m : ℕ} {s t u εReg η CΔ : ℝ} {MΔ : ℕ}
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (h_slope_coarse : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1)
    -- Estimate body at exact scale δ
    (hεReg_pos : 0 < εReg) (hη_pos : 0 < η)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (h_est_body : RegularIncidenceAtScale (canonicalWideCarrier m) s t εReg η δ)
    (hu_t : t ≤ u) (hu_two : u ≤ 2)
    (hδ_eq : δ = dyadicDelta m)
    -- Point set and regularity
    (P_orig : Set EuclideanPlane)
    (hP_sub : P_orig ⊆ translatedCoarsePointSet coarseConfig)
    (hP_ball : P_orig ⊆ Metric.closedBall 0 1)
    (hP_regular : IsSquareRootRegular δ u
        (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P_orig)
    -- Tube S-set constant condition
    (hCΔ_weaken : CΔ ≤ Real.rpow δ (-εReg)) :
    (coarseConfig.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) := by
  let tubeFamily' : (p' : EuclideanPlane) → p' ∈ P_orig → Set (DyadicTube m) :=
    fun p' hp' =>
      have h_sub : p' ∈ translatedCoarsePointSet coarseConfig := hP_sub hp'
      (coarseTubeFamilyOfPoint coarseConfig p' h_sub : Set (DyadicTube m))
  have h_tube_sset : ∀ (p' : EuclideanPlane) (hp' : p' ∈ P_orig),
      IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily' p' hp') := by
    intro p' hp'
    let h_sub : p' ∈ translatedCoarsePointSet coarseConfig := hP_sub hp'
    have h1 : IsDeltaSSet (dyadicDelta m) s CΔ (tubeFamily' p' hp') := by
      exact coarseTubeFamilyOfPoint_sset (coarseConfig := coarseConfig) (hp' := h_sub)
    have hδ_eq' : δ = dyadicDelta m := hδ_eq
    have h2 : IsDeltaSSet δ s CΔ (tubeFamily' p' hp') := by
      simpa [hδ_eq'] using h1
    exact IsDeltaSSet.weaken_C h2 hCΔ_weaken
  have h_incidence : ∀ (p' : EuclideanPlane) (hp' : p' ∈ P_orig) (T : DyadicTube m),
      T ∈ tubeFamily' p' hp' →
        p' ∈ Metric.cthickening δ (canonicalWideCarrier m T) := by
    intro p' hp' T hT_in
    let h_sub : p' ∈ translatedCoarsePointSet coarseConfig := hP_sub hp'
    have h3 : p' ∈ Metric.cthickening (dyadicDelta m) (canonicalWideCarrier m T) :=
      coarseTubeFamilyOfPoint_incidence
        (h_slope_coarse := h_slope_coarse) (hT_in := hT_in)
    simpa [hδ_eq] using h3
  have h_union_sub : (⋃ (p' : EuclideanPlane), ⋃ (hp' : p' ∈ P_orig),
        tubeFamily' p' hp') ⊆ (coarseConfig.T₀ : Set (DyadicTube m)) := by
    apply Set.iUnion_subset
    intro p'
    apply Set.iUnion_subset
    intro hp'
    exact coarseTubeFamilyOfPoint_sub_T₀
      (coarseConfig := coarseConfig)
      (p' := p')
      (hp' := hP_sub hp')
  have hChart' : ∀ (p' : EuclideanPlane) (hp' : p' ∈ P_orig) (T : DyadicTube m),
      T ∈ tubeFamily' p' hp' → InStandardChart.inChart T := by
    intro p' hp' T hT_in
    have hT_in_T0 : T ∈ coarseConfig.T₀ := by
      exact h_union_sub (Set.mem_iUnion₂.mpr ⟨p', hp', hT_in⟩)
    exact DyadicTube.inChart_of_slope_bound (h_slope_coarse T hT_in_T0)
  exact coarse_config_regular_incidence_at_delta
    (coarseConfig := coarseConfig)
    (carrier := canonicalWideCarrier m)
    (hεReg_pos := hεReg_pos)
    (hη_pos := hη_pos)
    (h_est_body := h_est_body)
    (hu_t := hu_t)
    (hu_two := hu_two)
    (hδ_pos := hδ_pos)
    (P := P_orig)
    (hP_ball := hP_ball)
    (hP_regular := hP_regular)
    (tubeFamily := tubeFamily')
    (h_tube_sset := h_tube_sset)
    (h_incidence := h_incidence)
    (hChart := hChart')
    (h_union_sub := h_union_sub)

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
