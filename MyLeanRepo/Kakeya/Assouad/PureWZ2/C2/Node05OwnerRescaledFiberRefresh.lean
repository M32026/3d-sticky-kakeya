import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerFiberRetention
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05RescaledFiberRefresh
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentRescaledFiber
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledShading
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralAggregateDensity

/-!
# Refresh the exact-truncated owner fibers

This module specializes the same-family rescaling refresh to the deterministic
owner output.  The old and new source shadings are restricted along the same
complete owner fiber, and the parent tube is the corresponding selected owner
tube.  Thus no family, parent, or shading can be reselected at this boundary.

The refreshed literal density remains an explicit geometric input.  The
parentwise factor-two mass retention is supplied by the owner exact truncation.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace WZ2PaperOwnerParentSelectedData

variable
    {delta sigma outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales : Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer}
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant)

/-- Refresh one deterministic owner fiber after exact truncation.  Both source
shadings use the identical complete owner subfamily, and the new literal
shading is indexed by the old output's literal family. -/
noncomputable def refreshExactFiber
    (parent : Fin data.selectedPacked.family.card)
    (oldOutput :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading)
      (data.selectedPacked.family.tube parent)
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1))
    (newLiteral :
    WZ2PaperLiteralUnitRescaledShadingData
      oldOutput.familyData
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.toExactMultiplicityData.truncation.truncated))
    (newDense :
    (oldOutput.rescalingCertificate.publicShading
        newLiteral.targetShading).IsLambdaDense
      (Kakeya.realRpowENN
        (delta / callerRequested.1) outputLoss)) :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.toExactMultiplicityData.truncation.truncated)
      (data.selectedPacked.family.tube parent)
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) :=
  oldOutput.refreshSameFamily
    newLiteral
    (fun index point hpoint =>
      data.toExactMultiplicityData.truncation.subshading
        ((data.internalCover.fullFiberSubfamily parent).embedding index)
        hpoint)
    newDense

/-- The source-fiber mass receipt accompanying `refreshExactFiber`. -/
theorem refreshExactFiber_mass_retention
    (parent : Fin data.selectedPacked.family.card) :
    (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).mass ≤
      2 *
        (restrictPaperShading
          (data.internalCover.fullFiberSubfamily parent)
          data.toExactMultiplicityData.truncation.truncated).mass :=
  data.toExactMultiplicityData_restrict_fullFiber_mass_retention parent

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

/-- Canonically rebuild the literal shading on the exact-truncated owner fiber
and refresh its public output.  The scalar premise spends exactly the
factor-two loss supplied by `refreshExactFiber_mass_retention`: the density
fed to the aggregate image theorem is one half of the old fiber density. -/
noncomputable def refreshExactFiberOfOldDensity
    (parent : Fin data.selectedPacked.family.card)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24)
    (oldOutput :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := outputLoss)
        (restrictPaperShading
          (data.internalCover.fullFiberSubfamily parent)
          data.finalFineShading)
        (data.selectedPacked.family.tube parent)
        (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1))
    (densityAbsorption :
      Kakeya.realRpowENN (delta / callerRequested.1) outputLoss *
            (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (((restrictPaperShading
                (data.internalCover.fullFiberSubfamily parent)
                data.finalFineShading).mass / 2) /
            ((data.internalCover.fullFiberSubfamily parent).family.enncard *
              Kakeya.realRpowENN delta 2))) :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.toExactMultiplicityData.truncation.truncated)
      (data.selectedPacked.family.tube parent)
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) := by
  let sourceFamily :=
    (data.internalCover.fullFiberSubfamily parent).family
  let oldFiber := restrictPaperShading
    (data.internalCover.fullFiberSubfamily parent) data.finalFineShading
  let newFiber := restrictPaperShading
    (data.internalCover.fullFiberSubfamily parent)
      data.toExactMultiplicityData.truncation.truncated
  let sourceDensity : ENNReal :=
    (oldFiber.mass / 2) /
      (sourceFamily.enncard * Kakeya.realRpowENN delta 2)
  let newLiteral : WZ2PaperLiteralUnitRescaledShadingData
      oldOutput.familyData newFiber :=
    Classical.choice <|
      wz2_paper_literal_unit_rescaled_shading
        wz2_paper_literal_image_carrier
        actualNearby.scaleData.delta_pos
        (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
        callerRequested.2.2 ratioSmall
        (data.section6Cover.fine_line_class.subfamily
          (data.internalCover.fullFiberSubfamily parent))
        (data.section6Cover.coarse_line_class parent)
        (data.internalCover.fullFiberSubfamily_covered parent)
        oldOutput.familyData newFiber
  let imageMeasure := Classical.choice <|
    wz2_paper_literal_image_measure
      wz2_paper_literal_unit_rescaling_volume
      oldOutput.familyData newFiber newLiteral
  have sourceCardPos : 0 < sourceFamily.card :=
    data.internalCover.fullFiberSubfamily_nonempty parent
  have sourceCardZero : sourceFamily.enncard ≠ 0 := by
    change (sourceFamily.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt sourceCardPos)
  have sourceCardTop : sourceFamily.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have deltaPowerZero : Kakeya.realRpowENN delta 2 ≠ 0 := by
    exact
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos actualNearby.scaleData.delta_pos 2)).ne'
  have deltaPowerTop : Kakeya.realRpowENN delta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have denominatorZero :
      sourceFamily.enncard * Kakeya.realRpowENN delta 2 ≠ 0 :=
    mul_ne_zero sourceCardZero deltaPowerZero
  have denominatorTop :
      sourceFamily.enncard * Kakeya.realRpowENN delta 2 ≠ ⊤ :=
    ENNReal.mul_ne_top sourceCardTop deltaPowerTop
  have sourceMass :
      sourceDensity * sourceFamily.enncard *
            Kakeya.realRpowENN delta 2 ≤
        newFiber.mass := by
    have retained := data.refreshExactFiber_mass_retention parent
    change oldFiber.mass ≤ 2 * newFiber.mass at retained
    have halfRetained : oldFiber.mass / 2 ≤ newFiber.mass := by
      apply (ENNReal.div_le_iff_le_mul
        (Or.inl (by norm_num)) (Or.inl (by norm_num))).mpr
      simpa [mul_comm] using retained
    calc
      sourceDensity * sourceFamily.enncard *
            Kakeya.realRpowENN delta 2 =
          sourceDensity *
            (sourceFamily.enncard * Kakeya.realRpowENN delta 2) := by ring
      _ = oldFiber.mass / 2 := by
        exact ENNReal.div_mul_cancel denominatorZero denominatorTop
      _ ≤ newFiber.mass := halfRetained
  have literalDense :
      newLiteral.targetShading.IsLambdaDense
        (Kakeya.realRpowENN
          (delta / callerRequested.1) outputLoss) :=
    wz2_paper_literal_aggregate_density
      wz2_paper_shading_mass_upper
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      ratioSmall oldOutput.familyData newFiber newLiteral imageMeasure
      sourceDensity
      (Kakeya.realRpowENN
        (delta / callerRequested.1) outputLoss)
      sourceMass (by simpa [sourceDensity, oldFiber, sourceFamily] using
        densityAbsorption)
  have publicDense := publicDense_of_literalDense
    oldOutput.rescalingCertificate newLiteral literalDense
  exact data.refreshExactFiber parent oldOutput newLiteral publicDense

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
