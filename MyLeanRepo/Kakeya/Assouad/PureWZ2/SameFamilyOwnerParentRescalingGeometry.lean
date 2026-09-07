import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentRescaledFiber
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CWARescaling
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedScaleProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralPackedImageStatements

/-!
# Geometry for rescaling one final owner-parent fiber

The same-family owner route already supplies the source line class, anchor
line class, complete source-to-anchor cover, and pure nearby-scale CWA on the
unrescaled final fiber.  This record contains only the extra tree geometry
needed to transport that CWA to the ordinary public rescaled family.

Target locality is recorded directly.  Requiring the cropped source family
to satisfy the repository's full-carrier `IsInUnitBall` convention would be
strictly stronger than the frozen Node 3 input.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace WZ2PaperOwnerParentSelectedData

variable
    {delta : ℝ}
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
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant)

structure FinalFiberRescalingGeometry
    (parent : Fin data.selectedPacked.family.card) where
  scale_separation : 100 * delta ≤ callerRequested.1
  source_strongly_separated :
    ∀ first second, first ≠ second →
      wz2PaperLiteralSourceSeparationFactor * delta <
        wz1PaperLineDistance
          ((data.finalFiber parent).family.tube first)
          ((data.finalFiber parent).family.tube second)
  target_locality :
    ∀ index,
      ‖wz2PaperTubeMidpoint
        ((wz2PaperLiteralOrdinaryRescaledFamily
          (data.finalFiber parent).family
          (data.selectedPacked.family.tube parent)
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1)).tube index)‖ ≤ 3
  nested_geometry :
    ∀ (t : ℝ) (ht : delta ≤ t) (ht' : t ≤ callerRequested.1)
      (scaleData :
        WZ2PaperPureScaleCoverData
          (data.finalFiber parent).family t fiberConstant),
      WZ1PaperIsLineClass scaleData.coarse ∧
        (∀ source,
          WZ1PaperTubeCovers
            ((data.finalFiber parent).family.tube source)
            (scaleData.coarse.tube
              (scaleData.cover.parent source))) ∧
        (∀ middle,
          WZ2PaperDilatedTubeCovers 2
            (scaleData.coarse.tube middle)
            (data.selectedPacked.family.tube parent)) ∧
        (∀ first second, first ≠ second →
          wz2PaperLiteralSourceSeparationFactor * t <
            wz1PaperLineDistance
              (scaleData.coarse.tube first)
              (scaleData.coarse.tube second)) ∧
        WZ2PaperOrdinaryNestedTargetLocalization
          (data.finalFiber parent).family scaleData.coarse
          (data.selectedPacked.family.tube parent)
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1)
  bounded_witness :
    ∀ (s : ℝ), delta ≤ s → s ≤ callerRequested.1 →
      ∃ (t : ℝ)
        (scaleData :
          WZ2PaperPureScaleCoverData
            (data.finalFiber parent).family t fiberConstant),
        s ≤ t ∧ t ≤ callerRequested.1

structure FinalFiberRescalingScalarAbsorptions
    {sigma outputLoss : ℝ}
    (parent : Fin data.selectedPacked.family.card)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24) where
  cwa_absorption :
    (81000000 : ENNReal) * fiberConstant ≤
      Kakeya.realRpowENN
        (delta / callerRequested.1) (-outputLoss)
  density_absorption :
    Kakeya.realRpowENN (delta / callerRequested.1) outputLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        ((data.finalFiberShading parent).mass /
          ((data.finalFiber parent).family.enncard *
            Kakeya.realRpowENN delta 2))
  volume_absorption :
    (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / callerRequested.1) 2 *
          (data.finalFiber parent).family.enncard ≤
      (2 ^
          balancing.balanced.finalData.producer.fiberBand.level :
        ENNReal) *
        Kakeya.realRpowENN
          (delta / callerRequested.1) (sigma - outputLoss)

theorem FinalFiberRescalingGeometry.publicPureCWA
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    {parent : Fin data.selectedPacked.family.card}
    (geometry : FinalFiberRescalingGeometry data parent)
    {targetConstant : ENNReal}
    (constant_absorption :
      (81000000 : ENNReal) * fiberConstant ≤ targetConstant)
    (targetConstant_finite : targetConstant ≠ ⊤) :
    WZ2PaperPureCWAAtNearbyScales
      (data.finalFiberCertificate parent).publicFamily
      targetConstant := by
  let sourceFamily := (data.finalFiber parent).family
  let anchor := data.selectedPacked.family.tube parent
  have sourceLine : WZ1PaperIsLineClass sourceFamily :=
    data.section6Cover.fine_line_class.subfamily (data.finalFiber parent)
  have anchorLine : WZ1PaperTubeInLineClass anchor :=
    data.section6Cover.coarse_line_class parent
  have sourceCovered :
      ∀ index, WZ1PaperTubeCovers (sourceFamily.tube index) anchor :=
    data.internalCover.fullFiberSubfamily_covered parent
  have sourceCWA :
      WZ2PaperPureCWAAtNearbyScales sourceFamily fiberConstant :=
    pureWZ2_same_family_owner_final_fiber_pure_cwa
      owner data.selectedPacked data.balancedPullback parent
  have canonicalCWA :
      WZ2PaperPureCWAAtNearbyScales
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceFamily anchor
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1))
        ((81000000 : ENNReal) * fiberConstant) :=
    wz2PaperPureCWAAtNearbyScales_rescale_of_locality
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      callerRequested.2.2 actualNearby.scaleData.delta_pos
      geometry.scale_separation sourceLine anchorLine sourceCovered
      geometry.source_strongly_separated geometry.target_locality
      sourceCWA sourceCWA.2.1.2 sourceCWA.2.1.1
      geometry.nested_geometry geometry.bounded_witness
  have weakened :
      WZ2PaperPureCWAAtNearbyScales
        (wz2PaperLiteralOrdinaryRescaledFamily
          sourceFamily anchor
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1))
        targetConstant :=
    canonicalCWA.mono constant_absorption targetConstant_finite
  let literal := data.finalFiberLiteral parent
  let canonicalLiteral :=
    wz2PaperLiteralOrdinaryRescaledFamilyLiteralData
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      callerRequested.2.2 sourceFamily anchor
      sourceLine anchorLine sourceCovered
  let certificate := data.finalFiberCertificate parent
  let indexEquiv :
      Fin certificate.publicFamily.card ≃
        Fin
          (wz2PaperLiteralOrdinaryRescaledFamily
            sourceFamily anchor
            (actualNearby.scaleData.delta_pos.trans_le
              callerRequested.2.1)).card :=
    literal.sourceEquiv.trans canonicalLiteral.sourceEquiv.symm
  have tube_eq :
      ∀ index : Fin certificate.publicFamily.card,
        certificate.publicFamily.tube index =
          (wz2PaperLiteralOrdinaryRescaledFamily
            sourceFamily anchor
            (actualNearby.scaleData.delta_pos.trans_le
              callerRequested.2.1)).tube (indexEquiv index) := by
    intro index
    change
      wz2PaperLiteralOrdinaryRescaledTube
          (sourceFamily.tube (literal.sourceIndex index))
          anchor
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1) =
        wz2PaperLiteralOrdinaryRescaledTube
          (sourceFamily.tube
            (canonicalLiteral.sourceIndex (indexEquiv index)))
          anchor
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1)
    congr 2
    change
      literal.sourceIndex index =
        canonicalLiteral.sourceIndex
          (canonicalLiteral.sourceEquiv.symm
            (literal.sourceIndex index))
    exact
      (canonicalLiteral.sourceEquiv.apply_symm_apply
        (literal.sourceIndex index)).symm
  exact weakened.reindex indexEquiv tube_eq

noncomputable def FinalFiberRescalingGeometry.toLeaves
    {sigma outputLoss : ℝ}
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    {parent : Fin data.selectedPacked.family.card}
    {ratioSmall : delta / callerRequested.1 ≤ 1 / 24}
    (geometry : FinalFiberRescalingGeometry data parent)
    (absorptions :
      FinalFiberRescalingScalarAbsorptions
        (sigma := sigma) (outputLoss := outputLoss)
        data parent ratioSmall) :
    FinalFiberRescalingLeaves
      (sigma := sigma) (outputLoss := outputLoss)
      data parent ratioSmall where
  public_pure_cwa :=
    geometry.publicPureCWA
      absorptions.cwa_absorption
      (by simp [Kakeya.realRpowENN])
  density_absorption := absorptions.density_absorption
  volume_absorption := absorptions.volume_absorption

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
