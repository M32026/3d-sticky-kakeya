import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityPublicRepackaging
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityExtremality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ExactMultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorLocalReduction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05RescaledFiberRefresh
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledShading
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageCarrier
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralAggregateDensity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Section6CoverAdapter

/-!
# Construction-private deterministic Node 5 owner call

This is the owner-call core shared by legacy and selected-caller inputs.  Its
indices are only the deterministic prop-sticky datum and its exact re-entry;
no historical quotient, all-positive caller family, or universal-input record
appears in the ABI.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private noncomputable def identityPaperRefinement
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    WZ1PaperRefinement shading 0 where
  selected :=
    { family := family
      embedding := Equiv.toEmbedding (Equiv.refl (Fin family.card))
      tube_eq := fun _ => rfl }
  refined := shading
  subshading := fun _ => Set.Subset.rfl
  retained_mass := by simp [wz1PaperRefinementFraction]

/-- Exact-multiplicity input tied to one deterministic re-entry seed. -/
structure PureWZ2Node05DeterministicExactInput
    {delta sigma seedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {callerRequested : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent)
    (hdelta : 0 < delta) where
  m : ℕ
  m_pos : 0 < m
  truncation :
    PureWZ2Node05ExactMultiplicityTruncationData
      seed.data.refined hdelta m
  fineCellNested :
    ∀ source point, point ∈ seed.data.refined.carrier source →
      ∃ cell ∈ seed.data.balanced.activeCells,
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
          wz1PaperGridCube callerRequested.1 cell

namespace PureWZ2Node05DeterministicExactInput

noncomputable def truncatedBalanced
    {delta sigma seedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {callerRequested : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    {seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent}
    {hdelta : 0 < delta}
    (exact : PureWZ2Node05DeterministicExactInput seed hdelta) :
    PureWZ2BalancedCoverData seed.data.cover exact.truncation.truncated
      seed.data.croppedCoarseShading :=
  exact.truncation.toBalancedBase seed.data.balanced

noncomputable def node5Balanced
    {delta sigma seedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {callerRequested : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    {seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent}
    {hdelta : 0 < delta}
    (exact : PureWZ2Node05DeterministicExactInput seed hdelta) :
    PureWZ2Node5BalancedCoverData exact.truncatedBalanced :=
  exact.truncation.toNode5Balanced seed.data.balanced exact.m_pos
    exact.fineCellNested

end PureWZ2Node05DeterministicExactInput

/-- Density-refresh output consumed by the deterministic concrete call. -/
def PureWZ2Node05DeterministicDensityReceipt
    {delta sigma seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {callerRequested : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent)
    {hdelta : 0 < delta}
    (exact : PureWZ2Node05DeterministicExactInput seed hdelta) : Prop :=
  ∀ parent : Fin seed.data.coarse.card,
    Nonempty
      (WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := outputLoss)
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            seed.data.selected.family
            (wz2PaperFullFiberIndices seed.data.selected.family
              seed.data.coarse parent))
          exact.truncation.truncated)
        (seed.data.coarse.tube parent)
        seed.data.coarse_extremal.delta_pos)

private theorem publicDense_of_literalDense
    {delta rho lambda : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {parentTube : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {familyData :
      WZ2PaperLiteralUnitRescaledFamilyData fine parentTube hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho (WZ2PaperAssouadUnitRescalingData.ofTube parentTube hrho)
        familyData jacobianConstant)
    (literal :
      WZ2PaperLiteralUnitRescaledShadingData familyData sourceShading)
    (dense : literal.targetShading.IsLambdaDense
      (Kakeya.realRpowENN (delta / rho) lambda)) :
    (certificate.publicShading literal.targetShading).IsLambdaDense
      (Kakeya.realRpowENN (delta / rho) lambda) := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  rw [certificate.publicBody_mass_eq, certificate.publicShading_mass_eq]
  exact dense

/-- Refresh every exact-truncated deterministic fiber.  All geometry is
constructed internally; the remaining premise is the explicit parentwise
density inequality. -/
noncomputable def pureWZ2Node05Deterministic_density
    {delta sigma seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {callerRequested : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent)
    {hdelta : 0 < delta}
    (exact : PureWZ2Node05DeterministicExactInput seed hdelta)
    (seed_le_output : seedLoss ≤ outputLoss)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24)
    (fiberMassRetention :
      ∀ parent : Fin seed.data.coarse.card,
        (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset
              seed.data.selected.family
              (wz2PaperFullFiberIndices seed.data.selected.family
                seed.data.coarse parent))
            seed.data.refined).mass ≤
          2 *
            (restrictPaperShading
              (Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices seed.data.selected.family
                  seed.data.coarse parent))
              exact.truncation.truncated).mass)
    (densityAbsorption :
      ∀ parent : Fin seed.data.coarse.card,
        Kakeya.realRpowENN (delta / callerRequested.1) outputLoss *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
          ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            (((restrictPaperShading
                  (Kakeya.Streamlined.TubeSubfamily.fromFinset
                    seed.data.selected.family
                    (wz2PaperFullFiberIndices seed.data.selected.family
                      seed.data.coarse parent))
                  seed.data.refined).mass / 2) /
              ((Kakeya.Streamlined.TubeSubfamily.fromFinset
                seed.data.selected.family
                (wz2PaperFullFiberIndices seed.data.selected.family
                  seed.data.coarse parent)).family.enncard *
                Kakeya.realRpowENN delta 2))) :
    PureWZ2Node05DeterministicDensityReceipt
      (outputLoss := outputLoss) seed exact := by
  intro parent
  let fiber :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      seed.data.selected.family
      (wz2PaperFullFiberIndices seed.data.selected.family
        seed.data.coarse parent)
  let oldFiber := restrictPaperShading fiber seed.data.refined
  let newFiber := restrictPaperShading fiber exact.truncation.truncated
  let oldOutput :=
    (Classical.choice (seed.data.rescaledFiber parent)).mono_loss seed_le_output
  have fiberCovered :
      ∀ index : Fin fiber.family.card,
        WZ1PaperTubeCovers
          (fiber.family.tube index) (seed.data.coarse.tube parent) := by
    intro index
    rw [fiber.tube_eq index]
    exact
      (mem_wz2PaperFullFiberIndices_iff parent
        (fiber.embedding index)).mp
        (Finset.orderEmbOfFin_mem
          (wz2PaperFullFiberIndices seed.data.selected.family
            seed.data.coarse parent) rfl index)
  have fiberNonempty : fiber.family.Nonempty := by
    change 0 <
      (wz2PaperFullFiberIndices seed.data.selected.family
        seed.data.coarse parent).card
    rcases seed.data.cover.parent_hit parent with ⟨source, hsource⟩
    exact Finset.card_pos.mpr
      ⟨source, (mem_wz2PaperFullFiberIndices_iff parent source).mpr hsource⟩
  let sourceDensity : ENNReal :=
    (oldFiber.mass / 2) /
      (fiber.family.enncard * Kakeya.realRpowENN delta 2)
  let newLiteral : WZ2PaperLiteralUnitRescaledShadingData
      oldOutput.familyData newFiber :=
    Classical.choice <|
      wz2_paper_literal_unit_rescaled_shading
        wz2_paper_literal_image_carrier hdelta
        seed.data.coarse_extremal.delta_pos callerRequested.2.2 ratioSmall
        (seed.data.cover.fine_line_class.subfamily fiber)
        (seed.data.cover.coarse_line_class parent)
        fiberCovered
        oldOutput.familyData newFiber
  let imageMeasure := Classical.choice <|
    wz2_paper_literal_image_measure
      wz2_paper_literal_unit_rescaling_volume
      oldOutput.familyData newFiber newLiteral
  have sourceCardPos : 0 < fiber.family.card :=
    fiberNonempty
  have sourceCardZero : fiber.family.enncard ≠ 0 := by
    change (fiber.family.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt sourceCardPos)
  have sourceCardTop : fiber.family.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have deltaPowerZero : Kakeya.realRpowENN delta 2 ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta 2)).ne'
  have deltaPowerTop : Kakeya.realRpowENN delta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have denominatorZero :
      fiber.family.enncard * Kakeya.realRpowENN delta 2 ≠ 0 :=
    mul_ne_zero sourceCardZero deltaPowerZero
  have denominatorTop :
      fiber.family.enncard * Kakeya.realRpowENN delta 2 ≠ ⊤ :=
    ENNReal.mul_ne_top sourceCardTop deltaPowerTop
  have sourceMass :
      sourceDensity * fiber.family.enncard *
            Kakeya.realRpowENN delta 2 ≤ newFiber.mass := by
    have retained := fiberMassRetention parent
    change oldFiber.mass ≤ 2 * newFiber.mass at retained
    have halfRetained : oldFiber.mass / 2 ≤ newFiber.mass := by
      apply (ENNReal.div_le_iff_le_mul
        (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
      simpa [mul_comm] using retained
    calc
      sourceDensity * fiber.family.enncard *
            Kakeya.realRpowENN delta 2 =
          sourceDensity *
            (fiber.family.enncard * Kakeya.realRpowENN delta 2) := by ring
      _ = oldFiber.mass / 2 :=
        ENNReal.div_mul_cancel denominatorZero denominatorTop
      _ ≤ newFiber.mass := halfRetained
  have literalDense :
      newLiteral.targetShading.IsLambdaDense
        (Kakeya.realRpowENN
          (delta / callerRequested.1) outputLoss) :=
    wz2_paper_literal_aggregate_density
      wz2_paper_shading_mass_upper hdelta
      seed.data.coarse_extremal.delta_pos ratioSmall oldOutput.familyData
      newFiber newLiteral imageMeasure sourceDensity
      (Kakeya.realRpowENN (delta / callerRequested.1) outputLoss)
      sourceMass
      (by
        simpa [sourceDensity, oldFiber, fiber] using
          densityAbsorption parent)
  have publicDense := publicDense_of_literalDense
    oldOutput.rescalingCertificate newLiteral literalDense
  exact
    ⟨oldOutput.refreshSameFamily newLiteral
      (fun index point hpoint =>
        exact.truncation.subshading (fiber.embedding index) hpoint)
      publicDense⟩

/-- Full-fiber comparison after the identity-family exact refinement. -/
def PureWZ2Node05DeterministicUniformity
    {delta sigma seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {callerRequested : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent fineExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent)
    {hdelta : 0 < delta}
    (exact : PureWZ2Node05DeterministicExactInput seed hdelta)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1) : Prop :=
  ∀ first second : Fin seed.data.coarse.card,
    ((wz2PaperFullFiberIndices
        (seed.data.selected.comp
          (exact.truncation.toPaperRefinement
            fineExponent refinementScalar).selected).family
        seed.data.coarse first).card : ENNReal) ≤
      Kakeya.realRpowENN callerRequested.1 (-outputLoss) *
        ((wz2PaperFullFiberIndices
          (seed.data.selected.comp
            (exact.truncation.toPaperRefinement
              fineExponent refinementScalar).selected).family
          seed.data.coarse second).card : ENNReal)

/-- The exact truncation refinement retains the deterministic fine family
definitionally, so a pre-refinement owner-cardinality comparison transports
without any legacy universal-input cast. -/
theorem pureWZ2Node05Deterministic_uniformity
    {delta sigma seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {callerRequested : WZ2PaperRequestedScale delta}
    {normalizationExponent seedLogExponent fineExponent : ℕ}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent)
    {hdelta : 0 < delta}
    (exact : PureWZ2Node05DeterministicExactInput seed hdelta)
    (refinementScalar :
      2 * wz1PaperRefinementFraction delta fineExponent ≤ 1)
    (ownerUniform :
      ∀ first second : Fin seed.data.coarse.card,
        ((wz2PaperFullFiberIndices seed.data.selected.family
            seed.data.coarse first).card : ENNReal) ≤
          Kakeya.realRpowENN callerRequested.1 (-outputLoss) *
            ((wz2PaperFullFiberIndices seed.data.selected.family
              seed.data.coarse second).card : ENNReal)) :
    PureWZ2Node05DeterministicUniformity
      (outputLoss := outputLoss) seed exact refinementScalar := by
  exact ownerUniform

/-- Generic receipt for a concrete Node 5 owner call. -/
structure PureWZ2Node05DeterministicOwnerCallReceipt
    {delta sigma seedLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {normalizationExponent seedLogExponent : ℕ}
    {callerRequested : WZ2PaperRequestedScale delta}
    (seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent)
    (outputLoss : ℝ) (outputLogExponent : ℕ) where
  delta_pos : 0 < delta
  sourceFineLoss : ℝ
  structuralBudget : ℝ
  fineExponent : ℕ
  logExponent_eq : seedLogExponent + fineExponent = outputLogExponent
  refinementScalar :
    2 * wz1PaperRefinementFraction delta fineExponent ≤ 1
  exact : PureWZ2Node05DeterministicExactInput
    seed delta_pos
  sourceFineExtremal :
    WZ2PaperCroppedIsExtremal sigma sourceFineLoss
      seed.data.selected.family seed.data.refined
  criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
    sigma outputLoss structuralBudget
  seed_le_structural : seedLoss ≤ criticalFloor.structuralLoss
  source_le_structural : sourceFineLoss ≤ criticalFloor.structuralLoss
  structural_le_output : criticalFloor.structuralLoss ≤ outputLoss
  absorption :
    2 * Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
      Kakeya.realRpowENN delta sourceFineLoss
  delta_cutoff : delta ≤ criticalFloor.delta₀
  rho_cutoff : callerRequested.1 ≤ criticalFloor.delta₀
  density :
    PureWZ2Node05DeterministicDensityReceipt
      (outputLoss := outputLoss) seed exact
  uniform :
    PureWZ2Node05DeterministicUniformity
      (outputLoss := outputLoss) seed exact refinementScalar

namespace PureWZ2Node05DeterministicOwnerCallReceipt

noncomputable def rawOutput
    {delta sigma seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {normalizationExponent seedLogExponent : ℕ}
    {callerRequested : WZ2PaperRequestedScale delta}
    {seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent}
    {outputLogExponent : ℕ}
    (receipt : PureWZ2Node05DeterministicOwnerCallReceipt
      seed outputLoss outputLogExponent) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading callerRequested normalizationExponent
      seedLogExponent (seedLogExponent + receipt.fineExponent) := by
  let data := seed.repackageExactMultiplicity
    receipt.delta_pos receipt.exact.truncation
    receipt.fineExponent receipt.refinementScalar
    (receipt.seed_le_structural.trans receipt.structural_le_output)
    receipt.exact.truncatedBalanced receipt.density
  let coarseRefinement :=
    identityPaperRefinement seed.data.croppedCoarseShading
  have fineConclusion :=
    receipt.exact.truncation.extremal_and_volume_lower_of_critical_floor
      receipt.sourceFineExtremal receipt.criticalFloor
      receipt.source_le_structural receipt.structural_le_output
      receipt.absorption receipt.delta_cutoff
  have coarseStructural : WZ2PaperCroppedIsExtremal
      sigma receipt.criticalFloor.structuralLoss seed.data.coarse
        seed.data.croppedCoarseShading :=
    seed.data.coarse_extremal.mono_loss receipt.seed_le_structural
  have coarseVolumeLower :
      Kakeya.realRpowENN callerRequested.1 (sigma + outputLoss) ≤
        volume seed.data.croppedCoarseShading.union :=
    receipt.criticalFloor.volume_floor callerRequested.1
      coarseStructural.delta_pos receipt.rho_cutoff seed.data.coarse
      coarseStructural.nonempty seed.data.croppedCoarseShading
      coarseStructural.cwa_nearby_scales coarseStructural.cubical
      coarseStructural.dense
  exact
    { seed := seed
      post :=
        { fineRefinementExponent := receipt.fineExponent
          coarseRefinementExponent := 0
          coarseRefinement := coarseRefinement
          data := data
          refined_extremal := fineConclusion.1
          exactMultiplicity := receipt.exact.m
          exactMultiplicity_pos := receipt.exact.m_pos
          delta_pos := receipt.delta_pos
          truncation := receipt.exact.truncation
          refinementScalar := receipt.refinementScalar
          logExponent_eq := rfl
          selected_eq := rfl
          refined_eq := HEq.rfl
          coarse_eq := rfl
          croppedCoarseShading_eq := HEq.rfl
          fineCellNested := receipt.exact.node5Balanced.fine_cell_nested
          refined_volume_lower := fineConclusion.2
          full_fiber_uniform := receipt.uniform
          coarse_volume_lower := coarseVolumeLower } }

noncomputable def output
    {delta sigma seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {normalizationExponent seedLogExponent : ℕ}
    {callerRequested : WZ2PaperRequestedScale delta}
    {seed : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := seedLoss)
      sourceShading callerRequested normalizationExponent seedLogExponent}
    {outputLogExponent : ℕ}
    (receipt : PureWZ2Node05DeterministicOwnerCallReceipt
      seed outputLoss outputLogExponent) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading callerRequested normalizationExponent
      seedLogExponent outputLogExponent :=
  Eq.mp (congrArg (fun exponent =>
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading callerRequested normalizationExponent
      seedLogExponent exponent) receipt.logExponent_eq) receipt.rawOutput

end PureWZ2Node05DeterministicOwnerCallReceipt

end Kakeya.Assouad

end
