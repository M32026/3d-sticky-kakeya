import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentCoarseBounds
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Output
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledFamily
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledShading
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageCarrier
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMultiplicityFloor
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralAggregateDensity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageVolumeUpper

/-!
# Public rescaled output on a final owner-parent fiber

The final owner-parent fiber is complete.  The literal target family,
cubical image shading, and fixed Assouad-to-literal certificate are therefore
canonical.  The only geometric leaf is pure nearby-scale CWA on the resulting
ordinary public family.  Density and volume reduce to two scalar absorption
inequalities.
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

noncomputable def finalFiber
    (parent : Fin data.selectedPacked.family.card) :
    Kakeya.Streamlined.TubeSubfamily data.selectedFine.family :=
  data.internalCover.fullFiberSubfamily parent

noncomputable def finalFiberShading
    (parent : Fin data.selectedPacked.family.card) :
    WZ1PaperTubeShading (data.finalFiber parent).family :=
  restrictPaperShading (data.finalFiber parent) data.finalFineShading

noncomputable def finalFiberLiteral
    (parent : Fin data.selectedPacked.family.card) :
    WZ2PaperLiteralUnitRescaledFamilyData
      (data.finalFiber parent).family
      (data.selectedPacked.family.tube parent)
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) :=
  Classical.choice <|
    wz2_paper_literal_unit_rescaled_family
      wz2_paper_literal_canonical_unit_rescaled_tube
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      callerRequested.2.2
      (data.finalFiber parent).family
      (data.section6Cover.fine_line_class.subfamily
        (data.finalFiber parent))
      (data.selectedPacked.family.tube parent)
      (data.section6Cover.coarse_line_class parent)
      (data.internalCover.fullFiberSubfamily_covered parent)

noncomputable def finalFiberLiteralShading
    (parent : Fin data.selectedPacked.family.card)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24) :
    WZ2PaperLiteralUnitRescaledShadingData
      (data.finalFiberLiteral parent)
      (data.finalFiberShading parent) :=
  Classical.choice <|
    wz2_paper_literal_unit_rescaled_shading
      wz2_paper_literal_image_carrier
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      callerRequested.2.2 ratioSmall
      (data.section6Cover.fine_line_class.subfamily
        (data.finalFiber parent))
      (data.section6Cover.coarse_line_class parent)
      (data.internalCover.fullFiberSubfamily_covered parent)
      (data.finalFiberLiteral parent)
      (data.finalFiberShading parent)

noncomputable def finalFiberCertificate
    (parent : Fin data.selectedPacked.family.card) :
    WZ2PaperAssouadToLiteralRescalingCertificate
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      (WZ2PaperAssouadUnitRescalingData.ofTube
        (data.selectedPacked.family.tube parent)
        (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1))
      (data.finalFiberLiteral parent) 4000000 :=
  wz2PaperAssouadToLiteralRescalingFixed
    actualNearby.scaleData.delta_pos
    (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
    callerRequested.2.2
    (data.finalFiber parent).family
    (data.selectedPacked.family.tube parent)
    (data.internalCover.fullFiberSubfamily_covered parent)
    (data.finalFiberLiteral parent)

structure FinalFiberRescalingLeaves
    (parent : Fin data.selectedPacked.family.card)
    (ratioSmall : delta / callerRequested.1 ≤ 1 / 24) where
  public_pure_cwa :
    WZ2PaperPureCWAAtNearbyScales
      (data.finalFiberCertificate parent).publicFamily
      (Kakeya.realRpowENN
        (delta / callerRequested.1) (-outputLoss))
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

noncomputable def FinalFiberRescalingLeaves.output
    {data : WZ2PaperOwnerParentSelectedData owner outputConstant}
    {parent : Fin data.selectedPacked.family.card}
    {ratioSmall : delta / callerRequested.1 ≤ 1 / 24}
    (leaves :
      FinalFiberRescalingLeaves
        (sigma := sigma) (outputLoss := outputLoss)
        data parent ratioSmall) :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      (data.finalFiberShading parent)
      (data.selectedPacked.family.tube parent)
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) := by
  let sourceFamily := (data.finalFiber parent).family
  let sourceShading := data.finalFiberShading parent
  let literal := data.finalFiberLiteral parent
  let literalShading := data.finalFiberLiteralShading parent ratioSmall
  let certificate := data.finalFiberCertificate parent
  let sourceDensity : ENNReal :=
    sourceShading.mass /
      (sourceFamily.enncard * Kakeya.realRpowENN delta 2)
  let multiplicityFloor : ENNReal :=
    (2 ^
      balancing.balanced.finalData.producer.fiberBand.level : ENNReal)
  have sourceCardPos : 0 < sourceFamily.card :=
    data.internalCover.fullFiberSubfamily_nonempty parent
  have sourceCardZero : sourceFamily.enncard ≠ 0 := by
    change (sourceFamily.card : ENNReal) ≠ 0
    exact_mod_cast (Nat.ne_of_gt sourceCardPos)
  have sourceCardTop : sourceFamily.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have deltaPowerZero :
      Kakeya.realRpowENN delta 2 ≠ 0 := by
    exact
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos actualNearby.scaleData.delta_pos 2)).ne'
  have deltaPowerTop :
      Kakeya.realRpowENN delta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have denominatorZero :
      sourceFamily.enncard *
          Kakeya.realRpowENN delta 2 ≠
        0 :=
    mul_ne_zero sourceCardZero deltaPowerZero
  have denominatorTop :
      sourceFamily.enncard *
          Kakeya.realRpowENN delta 2 ≠
        ⊤ :=
    ENNReal.mul_ne_top sourceCardTop deltaPowerTop
  have sourceMass :
      sourceDensity * sourceFamily.enncard *
            Kakeya.realRpowENN delta 2 ≤
        sourceShading.mass := by
    calc
      sourceDensity * sourceFamily.enncard *
            Kakeya.realRpowENN delta 2 =
          sourceDensity *
            (sourceFamily.enncard *
              Kakeya.realRpowENN delta 2) := by ring
      _ = sourceShading.mass := by
        exact
          ENNReal.div_mul_cancel denominatorZero denominatorTop
      _ ≤ sourceShading.mass := le_rfl
  have multiplicityFloorBound :
      ∀ point ∈ sourceShading.union,
        multiplicityFloor ≤
          (sourceShading.pointMultiplicity point : ENNReal) := by
    intro point hpoint
    let ownerFiber :=
      owner.exactified.restrictedCover.fullFiberSubfamily
        (data.selectedPacked.embedding parent)
    let ownerShading :=
      restrictPaperShading ownerFiber owner.exactified.refined
    have pointEq :
        sourceShading.pointMultiplicity point =
          ownerShading.pointMultiplicity point :=
      data.balancedPullback.pullback.full_fiber_pointMultiplicity_eq
        parent point
    have sourceMultiplicityPos :
        0 < sourceShading.pointMultiplicity point := by
      rcases hpoint with ⟨index, hindex⟩
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      exact
        Finset.card_pos.mpr
          ⟨index,
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ index, hindex⟩⟩
    have ownerMultiplicityPos :
        0 < ownerShading.pointMultiplicity point := by
      rwa [← pointEq]
    have ownerPoint : point ∈ ownerShading.union := by
      rcases Finset.card_pos.mp ownerMultiplicityPos with
        ⟨index, hindex⟩
      exact
        ⟨index, (Finset.mem_filter.mp hindex).2⟩
    rw [pointEq]
    exact
      (owner.fiber_multiplicity_band
        (data.selectedPacked.embedding parent)
        point ownerPoint).1
  have targetCardinality :
      literal.targetFamily.enncard = sourceFamily.enncard := by
    have hcard :
        literal.targetFamily.card = sourceFamily.card := by
      simpa using
        Fintype.card_congr
          (Equiv.ofBijective
            literal.sourceIndex literal.sourceIndex_bijective)
    exact
      congrArg (fun cardinality : ℕ => (cardinality : ENNReal)) hcard
  have literalNonempty : literal.targetFamily.Nonempty := by
    change 0 < literal.targetFamily.card
    have hsource : 0 < sourceFamily.card :=
      data.internalCover.fullFiberSubfamily_nonempty parent
    have hcard :
        literal.targetFamily.card = sourceFamily.card := by
      simpa using
        Fintype.card_congr
          (Equiv.ofBijective
            literal.sourceIndex literal.sourceIndex_bijective)
    rwa [hcard]
  let imageMeasure :=
    Classical.choice <|
      wz2_paper_literal_image_measure
        wz2_paper_literal_unit_rescaling_volume
        literal sourceShading literalShading
  have literalDense :
      literalShading.targetShading.IsLambdaDense
        (Kakeya.realRpowENN
          (delta / callerRequested.1) outputLoss) :=
    wz2_paper_literal_aggregate_density
      wz2_paper_shading_mass_upper
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      ratioSmall literal sourceShading literalShading imageMeasure
      sourceDensity
      (Kakeya.realRpowENN
        (delta / callerRequested.1) outputLoss)
      sourceMass (by simpa [sourceDensity] using leaves.density_absorption)
  have literalVolume :
      volume literalShading.targetShading.union ≤
        Kakeya.realRpowENN
          (delta / callerRequested.1) (sigma - outputLoss) :=
    wz2_paper_literal_image_volume_upper
      wz2_paper_literal_image_multiplicity_floor
      wz2_paper_shading_mass_upper
      wz2_paper_multiplicity_floor_volume
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      ratioSmall literal sourceShading literalShading
      multiplicityFloor
      (Kakeya.realRpowENN
        (delta / callerRequested.1) (sigma - outputLoss))
      multiplicityFloorBound
      (by
        rw [targetCardinality]
        simpa [multiplicityFloor] using leaves.volume_absorption)
  let publicShading :=
    certificate.publicShading literalShading.targetShading
  have publicDense :
      publicShading.IsLambdaDense
        (Kakeya.realRpowENN
          (delta / callerRequested.1) outputLoss) := by
    rw [Kakeya.Streamlined.Shading.IsLambdaDense]
    rw [certificate.publicBody_mass_eq,
      certificate.publicShading_mass_eq]
    exact literalDense
  have publicVolume :
      volume publicShading.union ≤
        Kakeya.realRpowENN
          (delta / callerRequested.1) (sigma - outputLoss) := by
    rw [certificate.publicShading_union_eq]
    exact literalVolume
  let publicExtremal :
      WZ2PaperCroppedIsExtremal
        sigma outputLoss certificate.publicFamily publicShading :=
    {
      delta_pos :=
        div_pos actualNearby.scaleData.delta_pos
          (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      delta_le_one :=
        (div_le_one
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1)).mpr callerRequested.2.1
      nonempty :=
        certificate.publicFamily_nonempty literalNonempty
      cwa_nearby_scales := leaves.public_pure_cwa
      cubical :=
        certificate.publicShading_cubical
          literalShading.target_cubical
      dense := publicDense
      volume_upper := publicVolume
    }
  exact
    {
      familyData := literal
      literalShading := literalShading
      jacobianConstant := 4000000
      jacobianConstant_one := by norm_num
      jacobianConstant_finite := by norm_num
      rescalingCertificate := certificate
      extremal := publicExtremal
      source_cardinality_eq := by
        calc
          certificate.publicFamily.enncard =
              literal.targetFamily.enncard :=
            certificate.publicFamily_enncard_eq
          _ = sourceFamily.enncard := targetCardinality
    }

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
