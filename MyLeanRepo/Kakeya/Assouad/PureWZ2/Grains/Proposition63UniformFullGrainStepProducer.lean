import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FiniteFullGrainIteration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FreshBalancedCells

/-!
# Concrete producer for a finite Proposition 6.3 full-grain step

This module closes the structural gap in the finite iterator.  Starting from
one analytic local-AD output, it performs the dyadic multiplicity preparation,
fresh non-aligned whole-cell balancing at exactly `sqrt queryScale`, transfers
the one-scale package through that same refinement, and returns the dependent
step record consumed by the line-hit iterator.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

/-- Assemble one iterator step from a one-scale analytic output and the two
explicit loss absorptions needed for multiplicity selection and fresh
square-root cell balancing. -/
theorem proposition63_uniformFullGrainStep_of_freshBalancing
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss middleLoss finalLoss queryScale sqrtScale : ℝ}
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
    (uniformCoverBudget : ℕ)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := reentry.normalization.croppedRefined)
      (fun point => planeMap point))
    (incoming_mass : sourceLeftFactor * current.mass ≤
      sourceRightFactor * original.shading.mass)
    (hfirstMiddle : firstLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 reentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta firstLoss)
    (hdeltaSqrt : delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hboundary : ∀ prepared : Proposition63OneScaleConstantMultiplicityData
      (secondLoss := middleLoss) planeMap original,
      2 * ((2 * (2 ^ prepared.level : ENNReal)) *
          ENNReal.ofReal (1000 * delta / sqrtScale)) <
        prepared.refined.shading.mass)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : ∀ prepared :
      Proposition63OneScaleConstantMultiplicityData
        (secondLoss := middleLoss) planeMap original,
      ∀ fresh : Proposition63FreshBalancedCellsData
        (sqrtScale := sqrtScale) planeMap original prepared
          original.extremal.delta_pos,
        fresh.freshLoss * Kakeya.realRpowENN delta finalLoss ≤
          Kakeya.realRpowENN delta middleLoss)
    (hpreparationBudget : ∀ prepared :
      Proposition63OneScaleConstantMultiplicityData
        (secondLoss := middleLoss) planeMap original,
      ∀ fresh : Proposition63FreshBalancedCellsData
        (sqrtScale := sqrtScale) planeMap original prepared
          original.extremal.delta_pos,
        fresh.preparedLoss ≤ uniformPreparationLoss)
    (plane_unit : ∀ point ∈ original.shading.union, ‖planeMap point‖ = 1)
    (cover_budget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-finalLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal)) :
    Nonempty (Proposition63UniformFullGrainStepData
      (firstLoss := firstLoss) (secondLoss := finalLoss)
      (queryScale := queryScale) (sqrtScale := sqrtScale) reentry planeMap
      sourceLeftFactor sourceRightFactor coefficient uniformPreparationLoss
      uniformCoverBudget) := by
  let prepared := Classical.choice <|
    proposition63_prepare_oneScale_constantMultiplicity planeMap original
      hfirstMiddle hmiddleLoss hmultiplicitySlack
  let fresh := Classical.choice <|
    proposition63_fresh_balancedCells planeMap original prepared
      hdeltaSqrt hsqrtPos hsqrtOne (hboundary prepared)
  let finalPrepared := fresh.toConstantMultiplicity hmiddleFinal hfinalLoss
    (hbalancingSlack prepared fresh)
  have hcells : Proposition63BalancedCellData (scale := sqrtScale)
      finalPrepared.refined.shading := by
    simpa only [finalPrepared,
      Proposition63FreshBalancedCellsData.toConstantMultiplicity] using
        fresh.cells
  have hbudget : finalPrepared.preparationLoss ≤
      uniformPreparationLoss := by
    simpa only [finalPrepared,
      Proposition63FreshBalancedCellsData.toConstantMultiplicity] using
        hpreparationBudget prepared fresh
  exact ⟨{
    original := original
    incoming_mass := incoming_mass
    prepared := finalPrepared
    cells := hcells
    preparation_budget := hbudget
    plane_unit := plane_unit
    cover_budget := cover_budget
  }⟩

/-- Paper-faithful variant using the top-level Convex-Wolff boundary-layer
estimate for the fresh square-root balancing step. -/
theorem proposition63_uniformFullGrainStep_of_freshBalancingCWA
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss middleLoss finalLoss queryScale sqrtScale : ℝ}
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
    (uniformCoverBudget : ℕ)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := reentry.normalization.croppedRefined)
      (fun point => planeMap point))
    (incoming_mass : sourceLeftFactor * current.mass ≤
      sourceRightFactor * original.shading.mass)
    (hfirstMiddle : firstLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 reentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta firstLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : ∀ prepared :
      Proposition63OneScaleConstantMultiplicityData
        (secondLoss := middleLoss) planeMap original,
      ∀ fresh : Proposition63FreshBalancedCellsData
        (sqrtScale := sqrtScale) planeMap original prepared
          original.extremal.delta_pos,
        fresh.freshLoss * Kakeya.realRpowENN delta finalLoss ≤
          Kakeya.realRpowENN delta middleLoss)
    (hpreparationBudget : ∀ prepared :
      Proposition63OneScaleConstantMultiplicityData
        (secondLoss := middleLoss) planeMap original,
      ∀ fresh : Proposition63FreshBalancedCellsData
        (sqrtScale := sqrtScale) planeMap original prepared
          original.extremal.delta_pos,
        fresh.preparedLoss ≤ uniformPreparationLoss)
    (plane_unit : ∀ point ∈ original.shading.union, ‖planeMap point‖ = 1)
    (cover_budget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-finalLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal)) :
    Nonempty (Proposition63UniformFullGrainStepData
      (firstLoss := firstLoss) (secondLoss := finalLoss)
      (queryScale := queryScale) (sqrtScale := sqrtScale) reentry planeMap
      sourceLeftFactor sourceRightFactor coefficient uniformPreparationLoss
      uniformCoverBudget) := by
  let prepared := Classical.choice <|
    proposition63_prepare_oneScale_constantMultiplicity planeMap original
      hfirstMiddle hmiddleLoss hmultiplicitySlack
  let fresh := Classical.choice <|
    proposition63_fresh_balancedCells_of_cwa_scalar planeMap original prepared
      reentry.normalization.line_class hdeltaSmall hperiodicScale hsqrtPos
      hsqrtOne hboundaryScalar
  let finalPrepared := fresh.toConstantMultiplicity hmiddleFinal hfinalLoss
    (hbalancingSlack prepared fresh)
  have hcells : Proposition63BalancedCellData (scale := sqrtScale)
      finalPrepared.refined.shading := by
    simpa only [finalPrepared,
      Proposition63FreshBalancedCellsData.toConstantMultiplicity] using
        fresh.cells
  have hbudget : finalPrepared.preparationLoss ≤
      uniformPreparationLoss := by
    simpa only [finalPrepared,
      Proposition63FreshBalancedCellsData.toConstantMultiplicity] using
        hpreparationBudget prepared fresh
  exact ⟨{
    original := original
    incoming_mass := incoming_mass
    prepared := finalPrepared
    cells := hcells
    preparation_budget := hbudget
    plane_unit := plane_unit
    cover_budget := cover_budget
  }⟩

/-- Canonical preparation-budget specialization.  Both finite pigeonhole
losses are bounded before the step by one explicit physical logarithmic
envelope. -/
theorem proposition63_uniformFullGrainStep_of_freshBalancingCWA_uniform
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      firstLoss middleLoss finalLoss queryScale sqrtScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (planeMap : Point3 → Point3)
    (sourceLeftFactor sourceRightFactor : ENNReal)
    (coefficient : NNReal) (uniformCoverBudget : ℕ)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := reentry.normalization.croppedRefined)
      (fun point => planeMap point))
    (incoming_mass : sourceLeftFactor * current.mass ≤
      sourceRightFactor * original.shading.mass)
    (hfirstMiddle : firstLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 reentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta firstLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope delta *
        Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss)
    (plane_unit : ∀ point ∈ original.shading.union, ‖planeMap point‖ = 1)
    (cover_budget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-finalLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal)) :
    Nonempty (Proposition63UniformFullGrainStepData
      (firstLoss := firstLoss) (secondLoss := finalLoss)
      (queryScale := queryScale) (sqrtScale := sqrtScale) reentry planeMap
      sourceLeftFactor sourceRightFactor coefficient
      (proposition63UniformPreparationLoss
        reentry.normalization.croppedFamily)
      uniformCoverBudget) := by
  rcases proposition63_prepare_oneScale_constantMultiplicity_with_loss
      planeMap original hfirstMiddle hmiddleLoss hmultiplicitySlack with
    ⟨prepared, hpreparedLoss⟩
  let fresh := Classical.choice <|
    proposition63_fresh_balancedCells_of_cwa_scalar planeMap original prepared
      reentry.normalization.line_class hdeltaSmall hperiodicScale hsqrtPos
      hsqrtOne hboundaryScalar
  have hfreshSlack : fresh.freshLoss *
      Kakeya.realRpowENN delta finalLoss ≤
        Kakeya.realRpowENN delta middleLoss :=
    (mul_le_mul_left fresh.freshLoss_le_envelope
      (Kakeya.realRpowENN delta finalLoss)).trans hbalancingSlack
  let finalPrepared := fresh.toConstantMultiplicity hmiddleFinal hfinalLoss
    hfreshSlack
  have hcells : Proposition63BalancedCellData (scale := sqrtScale)
      finalPrepared.refined.shading := by
    simpa only [finalPrepared,
      Proposition63FreshBalancedCellsData.toConstantMultiplicity] using
        fresh.cells
  have hbudget : finalPrepared.preparationLoss ≤
      proposition63UniformPreparationLoss
        reentry.normalization.croppedFamily := by
    have hfresh := fresh.freshLoss_le_envelope
    dsimp only [finalPrepared,
      Proposition63FreshBalancedCellsData.toConstantMultiplicity,
      proposition63UniformPreparationLoss]
    rw [fresh.preparedLoss_eq, hpreparedLoss]
    gcongr
  exact ⟨{
    original := original
    incoming_mass := incoming_mass
    prepared := finalPrepared
    cells := hcells
    preparation_budget := hbudget
    plane_unit := plane_unit
    cover_budget := cover_budget
  }⟩

/-- Source-generic canonical producer used after the dyadic Phase-1 output
has been pulled back to the ambient family.  Its proof is the same fresh
multiplicity/balancing construction, but the source is no longer tied to the
ordinary re-entry shading by a dependent index. -/
theorem proposition63_uniformAmbientFullGrainStep_of_freshBalancingCWA_uniform
    {delta sigma firstLoss middleLoss finalLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (sourceLeftFactor sourceRightFactor : ENNReal)
    (coefficient : NNReal) (uniformCoverBudget : ℕ)
    (original : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := firstLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (incoming_mass : sourceLeftFactor * source.mass ≤
      sourceRightFactor * original.shading.mass)
    (hfirstMiddle : firstLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 family.card + 1 : ℕ) : ENNReal) *
          Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta firstLoss)
    (hline : WZ1PaperIsLineClass family)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hperiodicScale : 50 * delta ≤ sqrtScale)
    (hsqrtPos : 0 < sqrtScale)
    (hsqrtOne : sqrtScale ≤ 1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtScale)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope delta *
        Kakeya.realRpowENN delta finalLoss ≤
      Kakeya.realRpowENN delta middleLoss)
    (plane_unit : ∀ point ∈ original.shading.union, ‖planeMap point‖ = 1)
    (cover_budget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-finalLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal)) :
    Nonempty (Proposition63UniformAmbientFullGrainStepData
      (sigma := sigma) (firstLoss := firstLoss) (secondLoss := finalLoss)
      (queryScale := queryScale) source planeMap sourceLeftFactor
      sourceRightFactor coefficient
      (proposition63UniformPreparationLoss family) uniformCoverBudget
      sqrtScale) := by
  rcases proposition63_prepare_oneScale_constantMultiplicity_with_loss
      planeMap original hfirstMiddle hmiddleLoss hmultiplicitySlack with
    ⟨prepared, hpreparedLoss⟩
  let fresh := Classical.choice <|
    proposition63_fresh_balancedCells_of_cwa_scalar planeMap original prepared
      hline hdeltaSmall hperiodicScale hsqrtPos hsqrtOne hboundaryScalar
  have hfreshSlack : fresh.freshLoss *
      Kakeya.realRpowENN delta finalLoss ≤
        Kakeya.realRpowENN delta middleLoss :=
    (mul_le_mul_left fresh.freshLoss_le_envelope
      (Kakeya.realRpowENN delta finalLoss)).trans hbalancingSlack
  let finalPrepared := fresh.toConstantMultiplicity hmiddleFinal hfinalLoss
    hfreshSlack
  have hcells : Proposition63BalancedCellData (scale := sqrtScale)
      finalPrepared.refined.shading := by
    simpa only [finalPrepared,
      Proposition63FreshBalancedCellsData.toConstantMultiplicity] using
        fresh.cells
  have hbudget : finalPrepared.preparationLoss ≤
      proposition63UniformPreparationLoss family := by
    have hfresh := fresh.freshLoss_le_envelope
    dsimp only [finalPrepared,
      Proposition63FreshBalancedCellsData.toConstantMultiplicity,
      proposition63UniformPreparationLoss]
    rw [fresh.preparedLoss_eq, hpreparedLoss]
    gcongr
  exact ⟨{
    original := original
    incoming_mass := incoming_mass
    prepared := finalPrepared
    cells := hcells
    preparation_budget := hbudget
    plane_unit := plane_unit
    cover_budget := cover_budget
  }⟩

end Kakeya.Assouad.PureWZ2

end
