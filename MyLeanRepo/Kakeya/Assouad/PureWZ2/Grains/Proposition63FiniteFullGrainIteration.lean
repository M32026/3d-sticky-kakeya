import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootSequentialReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63UniformLineHitBudget

/-!
# Finite Proposition 6.3 iteration with genuine line-hit grains

This module packages the exact per-scale data still produced by the analytic
Lemma 4.11/4.12 argument and feeds the resulting line-hit grain candidate
directly into the existing positive-mass finite iterator.  Every numerical
factor in the iterator is fixed before the iteration starts.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- The complete analytic certificate for one finite-grid full-grain step.
It keeps the one-scale shading, its genuine constant-multiplicity refinement,
and the fresh balanced square-root cover in one dependent package. -/
structure Proposition63UniformFullGrainStepData
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss secondLoss queryScale sqrtScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (planeMap : Point3 → Point3)
    (sourceLeftFactor sourceRightFactor : ENNReal)
    (coefficient : NNReal) (uniformPreparationLoss : ENNReal)
    (uniformCoverBudget : ℕ) where
  original : PureWZ2OneScaleLocalGrainData
    (sigma := sigma) (outputLoss := firstLoss)
    (rho := queryScale) (Y := reentry.normalization.croppedRefined)
    (fun point => planeMap point)
  incoming_mass : sourceLeftFactor * current.mass ≤
    sourceRightFactor * original.shading.mass
  prepared : Proposition63OneScaleConstantMultiplicityData
    (secondLoss := secondLoss) planeMap original
  cells : Proposition63BalancedCellData (scale := sqrtScale)
    prepared.refined.shading
  preparation_budget : prepared.preparationLoss ≤ uniformPreparationLoss
  plane_unit : ∀ point ∈ original.shading.union, ‖planeMap point‖ = 1
  cover_budget :
    (512 : ENNReal) *
        ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
          (9 * Kakeya.realRpowENN delta (-secondLoss) *
            Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
      (uniformCoverBudget : ENNReal)

/-- Source-generic version of one full-grain preparation.  Unlike the
historical iterator record, this does not force the analytic source to be the
fresh re-entry shading.  It is used when Phase 1 has already pulled its
selected-family output back to a restored dyadic shading on the ambient
family. -/
structure Proposition63UniformAmbientFullGrainStepData
    {delta sigma firstLoss secondLoss queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (planeMap : Point3 → Point3)
    (sourceLeftFactor sourceRightFactor : ENNReal)
    (coefficient : NNReal) (uniformPreparationLoss : ENNReal)
    (uniformCoverBudget : ℕ) (sqrtScale : ℝ) where
  original : PureWZ2OneScaleLocalGrainData
    (sigma := sigma) (outputLoss := firstLoss)
    (rho := queryScale) (Y := source) (fun point => planeMap point)
  incoming_mass : sourceLeftFactor * source.mass ≤
    sourceRightFactor * original.shading.mass
  prepared : Proposition63OneScaleConstantMultiplicityData
    (secondLoss := secondLoss) planeMap original
  cells : Proposition63BalancedCellData (scale := sqrtScale)
    prepared.refined.shading
  preparation_budget : prepared.preparationLoss ≤ uniformPreparationLoss
  plane_unit : ∀ point ∈ original.shading.union, ‖planeMap point‖ = 1
  cover_budget :
    (512 : ENNReal) *
        ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
          (9 * Kakeya.realRpowENN delta (-secondLoss) *
            Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
      (uniformCoverBudget : ENNReal)

/-- A full-grain step whose preparation loss fits one budget also fits any
larger budget.  All analytic and geometric witnesses remain unchanged. -/
def Proposition63UniformFullGrainStepData.monoPreparationLoss
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss secondLoss queryScale sqrtScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current}
    {planeMap : Point3 → Point3}
    {sourceLeftFactor sourceRightFactor : ENNReal}
    {coefficient : NNReal} {firstBudget secondBudget : ENNReal}
    {uniformCoverBudget : ℕ}
    (data : Proposition63UniformFullGrainStepData
      (firstLoss := firstLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) (sqrtScale := sqrtScale) reentry planeMap
      sourceLeftFactor sourceRightFactor coefficient firstBudget
      uniformCoverBudget)
    (hbudget : firstBudget ≤ secondBudget) :
    Proposition63UniformFullGrainStepData
      (firstLoss := firstLoss) (secondLoss := secondLoss)
      (queryScale := queryScale) (sqrtScale := sqrtScale) reentry planeMap
      sourceLeftFactor sourceRightFactor coefficient secondBudget
      uniformCoverBudget where
  original := data.original
  incoming_mass := data.incoming_mass
  prepared := data.prepared
  cells := data.cells
  preparation_budget := data.preparation_budget.trans hbudget
  plane_unit := data.plane_unit
  cover_budget := data.cover_budget

/-- Root-driven finite Lemma 4.11/4.12 iteration whose step is the genuine
line-hit full-grain construction.  `leftFactor` and `rightFactor` are fixed
before the iteration; `hleftBudget` and `hrightBudget` are exactly the scalar
absorptions relating them to the analytic and geometric losses at each
scheduled scale. -/
theorem proposition63_finite_fullGrain_iteration_from_root
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss stickyLoss firstLoss secondLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent logExponent N : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (queryScale sqrtScale spatialScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (sourceLeftFactor sourceRightFactor leftFactor rightFactor :
      ℕ → ENNReal)
    (uniformPreparationLoss : ℕ → ENNReal)
    (uniformCoverBudget : ℕ → ℕ)
    (parameters : Proposition63RootFiniteReentryParameters
      (currentLoss := currentLoss) (weightLoss := weightLoss)
      (reentryLoss := reentryLoss) (N := N) root leftFactor rightFactor)
    (coefficient : NNReal)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (planeLipschitz : LipschitzWith coefficient planeMap)
    (variationBudget : ∀ index, index < N →
      (coefficient : ℝ) * spatialScale index ≤ variationScale index)
    (hSticky : ∀ reentrySource :
        PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := parameters.reentryNormalizationLoss) reentrySource
          normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          reentryNormalized.croppedRefined rho logExponent))
    (requested_lower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (requested_upper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (query_pos : ∀ index, index < N → 0 < queryScale index)
    (query_small : ∀ index, index < N → queryScale index ≤ 1 / 4)
    (sqrt_eq : ∀ index, index < N →
      sqrtScale index = Real.sqrt (queryScale index))
    (sqrt_pos : ∀ index, index < N → 0 < sqrtScale index)
    (coverBudget_pos : ∀ index, index < N →
      0 < uniformCoverBudget index)
    (target_constant :
      Kakeya.realRpowENN delta (-secondLoss) ≤ constant)
    (hleftBudget : ∀ index (index_lt : index < N),
      leftFactor index ≤
        proposition63UniformLineFactor
            (Kakeya.realRpowENN delta (secondLoss + 2))
            (sqrtScale index) (sqrt_pos index index_lt) *
          (((1 : ENNReal) / 2) /
            (2 * (uniformCoverBudget index : ENNReal))) *
          sourceLeftFactor index)
    (hrightBudget : ∀ index, index < N →
      sourceRightFactor index *
          (uniformPreparationLoss index * 2) ≤
        rightFactor index)
    (stepData : ∀ index : ℕ, ∀ index_lt : index < N,
      ∀ current : WZ1PaperTubeShading root.normalization.croppedFamily,
        ∀ _current_sub : PaperIsSubshading current
          root.normalization.croppedRefined,
        ∀ _current_cubical : WZ1PaperIsCubicalShading current,
        ∀ _current_multiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            root.normalization.croppedRefined.pointMultiplicity point,
        ∀ _current_mass_ledger :
          (∏ prior ∈ Finset.range index, leftFactor prior) *
              root.normalization.croppedRefined.mass ≤
            (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass,
        ∀ _current_mass_pos : 0 < current.mass,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) root.normalization current,
        data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss →
        ∀ _sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, index_lt⟩) logExponent,
          Nonempty (Proposition63UniformFullGrainStepData
            (firstLoss := firstLoss) (secondLoss := secondLoss)
            (queryScale := queryScale index)
            (sqrtScale := sqrtScale index) data planeMap
            (sourceLeftFactor index) (sourceRightFactor index) coefficient
            (uniformPreparationLoss index) (uniformCoverBudget index))) :
    ∃ final : WZ1PaperTubeShading root.normalization.croppedFamily,
      PaperIsSubshading final root.normalization.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point =
          root.normalization.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (queryScale index))))
          (queryScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          root.normalization.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  apply joint_finite_variation_local_ad_iteration_of_mass_pos
    root.normalization.croppedRefined root.normalization.cropped_cubical
      (cropped_extremal_shading_mass_pos
        root.normalization.final_extremal root.normalization.line_class
        parameters.delta_small)
      planeMap N spatialScale queryScale variationScale constant
      leftFactor rightFactor parameters.leftFactor_pos
  intro index index_lt current current_sub current_cubical
    current_multiplicity current_mass_ledger current_mass_pos
  rcases parameters.prepareWithCanonicalWeight index index_lt current
      current_sub current_cubical current_multiplicity current_mass_ledger
      current_mass_pos with
    ⟨data, normalization_weight, _levelCount_eq, hnormalizationLoss⟩
  have hStickyData :
      ∀ reentrySource : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
        ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := data.reentryNormalizationLoss) reentrySource
            normalizationExponent,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta stickyLoss →
              Nonempty (PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := stickyLoss)
                reentryNormalized.croppedRefined rho logExponent) := by
    rw [hnormalizationLoss]
    exact hSticky
  rcases proposition63CurrentShadingReentry_sticky data hStickyData
      (requested ⟨index, index_lt⟩)
      (requested_lower ⟨index, index_lt⟩)
      (requested_upper ⟨index, index_lt⟩) with ⟨sticky⟩
  let step := Classical.choice <|
    stepData index index_lt current current_sub current_cubical
      current_multiplicity current_mass_ledger current_mass_pos data
      normalization_weight sticky
  rcases data.lineHitCandidate_joint_one_scale_of_extremal_budget
      planeMap step.original step.prepared step.cells
      (query_pos index index_lt) (query_small index index_lt)
      (sqrt_eq index index_lt) (sqrt_pos index index_lt) step.plane_unit
      coefficient hcoefficientOne planeLipschitz
      (uniformCoverBudget index) (coverBudget_pos index index_lt)
      step.cover_budget (spatialScale index) (variationScale index)
      (variationBudget index index_lt) constant target_constant
      (sourceLeftFactor index) (sourceRightFactor index)
      (uniformPreparationLoss index) step.preparation_budget step.incoming_mass
      (parameters.delta_small.trans (by norm_num)) with
    ⟨next, hnextSub, hnextCubical, hnextMultiplicity, hnextVariation,
      hnextAD, hnextMass⟩
  have hnextMassRoot :
      (proposition63UniformLineFactor
            (Kakeya.realRpowENN delta (secondLoss + 2))
            (sqrtScale index) (sqrt_pos index index_lt) *
          (((1 : ENNReal) / 2) /
            (2 * (uniformCoverBudget index : ENNReal))) *
          sourceLeftFactor index) * current.mass ≤
        (sourceRightFactor index *
          (uniformPreparationLoss index * 2)) * next.mass :=
    hnextMass
  refine ⟨next, hnextSub, hnextCubical, hnextMultiplicity, hnextVariation,
    hnextAD, ?_⟩
  calc
    leftFactor index * current.mass ≤
        (proposition63UniformLineFactor
              (Kakeya.realRpowENN delta (secondLoss + 2))
              (sqrtScale index) (sqrt_pos index index_lt) *
            (((1 : ENNReal) / 2) /
              (2 * (uniformCoverBudget index : ENNReal))) *
            sourceLeftFactor index) * current.mass :=
      mul_le_mul_left (hleftBudget index index_lt) _
    _ ≤ (sourceRightFactor index *
          (uniformPreparationLoss index * 2)) * next.mass := hnextMassRoot
    _ ≤ rightFactor index * next.mass :=
      mul_le_mul_left (hrightBudget index index_lt) _

end Kakeya.Assouad.PureWZ2

end
