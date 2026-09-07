import MyLeanRepo.Kakeya.Assouad.PureWZ2.CriticalRescaledFiberWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentRescalingGeometry

/-!
# Critical rescaled witnesses on final same-family owner fibers

The public rescaled output and the pure critical witness use the same complete
final owner fiber and the same final cropped shading.  The ordinary witness is
the exact literal affine image of that cropped shading; its density follows
from the same source-mass absorption used by the public cubical output.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace WZ2PaperOwnerParentSelectedData

variable
    {delta sigma loss : ℝ}
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
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
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
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    {parent : Fin data.selectedPacked.family.card}
    {ratioSmall : delta / callerRequested.1 ≤ 1 / 24}

/--
Produce the pure critical witness on the exact final owner fiber.

No ordinary normalization trace is used.  The ordinary shading is the exact
literal image of `data.finalFiberShading parent`.
-/
noncomputable def FinalFiberRescalingLeaves.criticalRescaledWitness
    (leaves :
      FinalFiberRescalingLeaves
        (sigma := sigma) (outputLoss := loss)
        data parent ratioSmall)
    (imageDistance :
      ∀ (publicIndex :
            Fin leaves.output.rescalingCertificate.publicFamily.card)
          (sourcePoint : Point3),
        sourcePoint ∈
            (data.finalFiberShading parent).carrier
              (leaves.output.familyData.sourceIndex
                (leaves.output.rescalingCertificate.section6Index.symm
                  publicIndex)) →
          Metric.infEDist
              (wz2PaperLiteralUnitRescalingMap
                (data.selectedPacked.family.tube parent)
                (actualNearby.scaleData.delta_pos.trans_le
                  callerRequested.2.1)
                sourcePoint)
              (Kakeya.unitSegment
                (leaves.output.rescalingCertificate.publicFamily.tube
                  publicIndex).base
                (leaves.output.rescalingCertificate.publicFamily.tube
                  publicIndex).direction) ≤
            ENNReal.ofReal (delta / callerRequested.1)) :
    PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss)
      (data.finalFiberShading parent)
      (data.selectedPacked.family.tube parent)
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) := by
  let sourceFamily := (data.finalFiber parent).family
  let sourceShading := data.finalFiberShading parent
  let output := leaves.output
  let certificate := output.rescalingCertificate
  let literal := output.familyData
  let ratio := delta / callerRequested.1
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / callerRequested.1 : ℝ) ^ 2)
  let sourceDenominator : ENNReal :=
    sourceFamily.enncard * Kakeya.realRpowENN delta 2
  let sourceDensity : ENNReal :=
    sourceShading.mass / sourceDenominator
  have imageSubsetPublic :
      ∀ publicIndex,
        wz2PaperLiteralUnitRescalingMap
              (data.selectedPacked.family.tube parent)
              (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) ''
            sourceShading.carrier
              (literal.sourceIndex
                (certificate.section6Index.symm publicIndex)) ⊆
          (certificate.publicFamily.tube publicIndex).carrier := by
    intro publicIndex
    rintro imagePoint ⟨sourcePoint, sourcePointMem, rfl⟩
    change
      wz2PaperLiteralUnitRescalingMap
          (data.selectedPacked.family.tube parent)
          (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
          sourcePoint ∈
        Metric.cthickening ratio
          (Kakeya.unitSegment
            (certificate.publicFamily.tube publicIndex).base
            (certificate.publicFamily.tube publicIndex).direction)
    rw [Metric.mem_cthickening_iff]
    simpa [output, certificate, literal, sourceShading, ratio] using
      imageDistance publicIndex sourcePoint sourcePointMem
  have sourceCardZero : sourceFamily.enncard ≠ 0 := by
    change (sourceFamily.card : ENNReal) ≠ 0
    exact_mod_cast
      (Nat.ne_of_gt
        (data.internalCover.fullFiberSubfamily_nonempty parent))
  have sourceCardTop : sourceFamily.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have deltaPowerZero : Kakeya.realRpowENN delta 2 ≠ 0 := by
    exact
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos actualNearby.scaleData.delta_pos 2)).ne'
  have deltaPowerTop : Kakeya.realRpowENN delta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have denominatorZero : sourceDenominator ≠ 0 :=
    mul_ne_zero sourceCardZero deltaPowerZero
  have denominatorTop : sourceDenominator ≠ ⊤ :=
    ENNReal.mul_ne_top sourceCardTop deltaPowerTop
  have sourceMass :
      sourceDensity * sourceDenominator = sourceShading.mass := by
    exact ENNReal.div_mul_cancel denominatorZero denominatorTop
  have publicBodyUpper :
      certificate.publicFamily.toBodyFamily.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN ratio 2 *
            sourceFamily.enncard := by
    have ratioPos : 0 < ratio :=
      div_pos actualNearby.scaleData.delta_pos
        (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
    have ratioOne : ratio ≤ 1 :=
      (div_le_one
        (actualNearby.scaleData.delta_pos.trans_le
          callerRequested.2.1)).mpr callerRequested.2.1
    have tubeVolumeUpper :
        Kakeya.deltaTubeVolume ratio ≤
          24 * Kakeya.realRpowENN ratio 2 *
            Kakeya.deltaTubeVolume 1 := by
      let publicIndex : Fin certificate.publicFamily.card :=
        ⟨0, output.extremal.nonempty⟩
      have upper :=
        tube_volume_scaling.2.2 ratio ratioPos ratioOne
          (certificate.publicFamily.tube publicIndex)
      rwa [tube_volume_scaling.1 ratio
        (certificate.publicFamily.tube publicIndex)] at upper
    rw [tubeFamily_mass_eq_nominal]
    change
      certificate.publicFamily.enncard *
          Kakeya.deltaTubeVolume ratio ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN ratio 2 *
            sourceFamily.enncard
    rw [output.source_cardinality_eq]
    calc
      sourceFamily.enncard * Kakeya.deltaTubeVolume ratio ≤
          sourceFamily.enncard *
            (24 * Kakeya.realRpowENN ratio 2 *
              Kakeya.deltaTubeVolume 1) := by
        gcongr
      _ ≤
          sourceFamily.enncard *
            (55296 * Kakeya.realRpowENN ratio 2 *
              Kakeya.deltaTubeVolume 1) := by
        gcongr
        norm_num
      _ =
          (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN ratio 2 *
              sourceFamily.enncard := by
        ring
  have scaleIdentity :
      ENNReal.ofReal ((1 / callerRequested.1 : ℝ) ^ 2) *
          Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN ratio 2 := by
    simp only [ratio, Kakeya.realRpowENN]
    have deltaTwo : Real.rpow delta 2 = delta ^ 2 :=
      Real.rpow_two delta
    have ratioTwo :
        Real.rpow (delta / callerRequested.1) 2 =
          (delta / callerRequested.1) ^ 2 :=
      Real.rpow_two (delta / callerRequested.1)
    rw [deltaTwo, ratioTwo]
    rw [← ENNReal.ofReal_mul (sq_nonneg (1 / callerRequested.1))]
    congr 1
    field_simp
      [(actualNearby.scaleData.delta_pos.trans_le
        callerRequested.2.1).ne']
  have massLower :
      Kakeya.realRpowENN ratio loss *
            certificate.publicFamily.toBodyFamily.mass ≤
        jacobian * sourceShading.mass := by
    calc
      Kakeya.realRpowENN ratio loss *
            certificate.publicFamily.toBodyFamily.mass ≤
          Kakeya.realRpowENN ratio loss *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN ratio 2 *
                sourceFamily.enncard) := by
        gcongr
      _ =
          (Kakeya.realRpowENN ratio loss *
              (55296 * Kakeya.deltaTubeVolume 1)) *
            (Kakeya.realRpowENN ratio 2 *
              sourceFamily.enncard) := by
        ring
      _ ≤
          (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sourceDensity) *
            (Kakeya.realRpowENN ratio 2 *
              sourceFamily.enncard) := by
        exact
          mul_le_mul_right'
            (by simpa [ratio, sourceDensity, sourceDenominator] using
              leaves.density_absorption)
            _
      _ =
          jacobian * (sourceDensity * sourceDenominator) := by
        simp only [jacobian, sourceDenominator]
        rw [← scaleIdentity]
        ring
      _ = jacobian * sourceShading.mass := by
        rw [sourceMass]
  have ordinaryDense :
      (certificate.literalExactCroppedImageShading
        sourceShading imageSubsetPublic).IsLambdaDense
          (Kakeya.realRpowENN ratio loss) :=
    certificate.literalExactCroppedImageShading_dense_of_mass
      sourceShading imageSubsetPublic massLower
  exact output.withCroppedExactImage imageSubsetPublic ordinaryDense

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
