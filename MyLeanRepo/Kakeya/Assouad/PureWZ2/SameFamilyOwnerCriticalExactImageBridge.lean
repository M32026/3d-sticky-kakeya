import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalImageContainment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedPaperCarrierImageContainment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerCriticalRescaledProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentRefinement

/-!
# Exact-image bridge on final same-family owner fibers

The frozen dense cubicalization becomes an ordinary exact-image source once
the normalization ordinary carrier has positive volume at every exact final
owner index.  This is the thinnest non-circular condition needed to eliminate
the pointwise distance input of the critical rescaled-fiber producer.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace WZ2PaperOwnerParentSelectedData

variable
    {delta sigma inputLoss normalizationLoss loss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        normalized.croppedFamily actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested normalized.croppedRefined}
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
          normalized.croppedFamily
          (scales coordinate) ambientConstant}
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
    (leaves :
      FinalFiberRescalingLeaves
        (sigma := sigma) (outputLoss := loss)
        data parent ratioSmall)

/--
Positive ordinary source volume at each exact final owner index supplies the
pointwise distance input consumed by `criticalRescaledWitness`.
-/
theorem FinalFiberRescalingLeaves.imageDistance_of_ordinary_volume_pos
    (ordinaryVolumePos :
      ∀ index : Fin (data.finalFiber parent).family.card,
        0 <
          volume
            (normalized.ordinaryRefined.carrier
              (normalized.indexEquiv.symm
                (data.selectedSource.embedding
                  ((data.finalFiber parent).embedding index))))) :
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
          ENNReal.ofReal (delta / callerRequested.1) := by
  intro publicIndex sourcePoint sourcePointMem
  let finalIndex :=
    leaves.output.familyData.sourceIndex
      (leaves.output.rescalingCertificate.section6Index.symm publicIndex)
  let selectedFineIndex :=
    (data.finalFiber parent).embedding finalIndex
  let croppedIndex :=
    data.selectedSource.embedding selectedFineIndex
  let ordinaryIndex :=
    normalized.indexEquiv.symm croppedIndex
  let sourceTube :=
    (data.finalFiber parent).family.tube finalIndex
  let anchor := data.selectedPacked.family.tube parent
  let ordinarySource :=
    normalized.frame ''
      normalized.ordinaryRefined.carrier ordinaryIndex
  let finalCarrier :=
    (data.finalFiberShading parent).carrier finalIndex
  have ordinaryIndexEq :
      normalized.indexEquiv ordinaryIndex = croppedIndex :=
    normalized.indexEquiv.apply_symm_apply croppedIndex
  have sourceTubeEq :
      sourceTube = normalized.croppedFamily.tube croppedIndex := by
    calc
      sourceTube =
          data.selectedFine.family.tube selectedFineIndex :=
        (data.finalFiber parent).tube_eq finalIndex
      _ = normalized.croppedFamily.tube croppedIndex :=
        data.selectedSource.tube_eq selectedFineIndex
  have ordinarySourceSubset :
      ordinarySource ⊆ sourceTube.carrier := by
    rintro point ⟨ordinaryPoint, ordinaryPointMem, rfl⟩
    rw [sourceTubeEq, ← ordinaryIndexEq,
      normalized.ordinary_carrier_image_eq ordinaryIndex]
    exact
      ⟨ordinaryPoint,
        normalized.ordinaryRefined.subset_body
          ordinaryIndex ordinaryPointMem,
        rfl⟩
  have ordinarySourceVolumePos :
      0 < volume ordinarySource := by
    rw [Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      normalized.frame
      (normalized.ordinaryRefined.carrier ordinaryIndex)
      (normalized.ordinaryRefined.measurable_carrier ordinaryIndex)]
    exact ordinaryVolumePos finalIndex
  have finalSubset :
      finalCarrier ⊆
        pureWZ2DenseCubicalization sourceTube ordinarySource := by
    intro point pointMem
    change
      point ∈
        pureWZ2DenseCubicalization sourceTube ordinarySource
    rw [sourceTubeEq, ← ordinaryIndexEq,
      ← normalized.cropped_carrier_eq_dense_cubicalization ordinaryIndex]
    rw [ordinaryIndexEq]
    exact data.finalFine_subshading selectedFineIndex pointMem
  have canonicalContainment :
      wz2PaperLiteralUnitRescalingMap
          anchor
          (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) ''
          finalCarrier ⊆
        (wz2PaperLiteralOrdinaryRescaledTube
          sourceTube anchor
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1)).carrier :=
    wz2PaperLiteral_denseCubicalization_image_subset_ordinary
      actualNearby.scaleData.delta_pos
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      callerRequested.2.2
      sourceTube anchor
      (data.internalCover.fullFiberSubfamily_covered parent finalIndex)
      ordinarySource finalCarrier
      ordinarySourceSubset ordinarySourceVolumePos finalSubset
  have imageMem :=
    canonicalContainment
      ⟨sourcePoint, sourcePointMem, rfl⟩
  have publicTubeEq :
      leaves.output.rescalingCertificate.publicFamily.tube publicIndex =
        wz2PaperLiteralOrdinaryRescaledTube
          sourceTube anchor
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1) := by
    rfl
  change
    Metric.infEDist
        (wz2PaperLiteralUnitRescalingMap
          anchor
          (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
          sourcePoint)
        (Kakeya.unitSegment
          (leaves.output.rescalingCertificate.publicFamily.tube
            publicIndex).base
          (leaves.output.rescalingCertificate.publicFamily.tube
            publicIndex).direction) ≤
      ENNReal.ofReal (delta / callerRequested.1)
  rw [publicTubeEq]
  exact Metric.mem_cthickening_iff.mp imageMem

/--
The exact same final owner fiber admits the critical rescaled witness whenever
its corresponding frozen ordinary carriers have positive volume.
-/
noncomputable def FinalFiberRescalingLeaves.criticalRescaledWitness_of_ordinary_volume_pos
    (ordinaryVolumePos :
      ∀ index : Fin (data.finalFiber parent).family.card,
        0 <
          volume
            (normalized.ordinaryRefined.carrier
              (normalized.indexEquiv.symm
                (data.selectedSource.embedding
                  ((data.finalFiber parent).embedding index))))) :
    PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss)
      (data.finalFiberShading parent)
      (data.selectedPacked.family.tube parent)
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) :=
  leaves.criticalRescaledWitness
    (leaves.imageDistance_of_ordinary_volume_pos
      normalized ordinaryVolumePos)

/--
The bounded-base field of the frozen normalization makes the entire cropped
paper carrier legal in the public ordinary rescaling.  Hence the critical
exact-image witness does not require positive ordinary source volume.
-/
theorem FinalFiberRescalingLeaves.imageDistance_of_bounded_normalization :
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
          ENNReal.ofReal (delta / callerRequested.1) := by
  intro publicIndex sourcePoint sourcePointMem
  let finalIndex :=
    leaves.output.familyData.sourceIndex
      (leaves.output.rescalingCertificate.section6Index.symm publicIndex)
  let selectedFineIndex :=
    (data.finalFiber parent).embedding finalIndex
  let croppedIndex :=
    data.selectedSource.embedding selectedFineIndex
  let sourceTube :=
    (data.finalFiber parent).family.tube finalIndex
  let anchor := data.selectedPacked.family.tube parent
  have sourceTubeEq :
      sourceTube = normalized.croppedFamily.tube croppedIndex := by
    calc
      sourceTube =
          data.selectedFine.family.tube selectedFineIndex :=
        (data.finalFiber parent).tube_eq finalIndex
      _ = normalized.croppedFamily.tube croppedIndex :=
        data.selectedSource.tube_eq selectedFineIndex
  have sourceLine : WZ1PaperTubeInLineClass sourceTube := by
    rw [sourceTubeEq]
    exact normalized.line_class croppedIndex
  have sourceBase : ‖sourceTube.base‖ ≤ 4 := by
    rw [sourceTubeEq]
    exact normalized.ordinary_bounded_base croppedIndex
  have sourcePointPaper :
      sourcePoint ∈ wz1PaperTubeCarrier sourceTube := by
    have croppedMem :
        sourcePoint ∈ normalized.croppedRefined.carrier croppedIndex :=
      data.finalFine_subshading selectedFineIndex sourcePointMem
    rw [sourceTubeEq]
    exact
      normalized.croppedRefined.subset_body
        croppedIndex croppedMem
  have canonicalContainment :
      wz2PaperLiteralUnitRescalingMap
          anchor
          (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) ''
          wz1PaperTubeCarrier sourceTube ⊆
        (wz2PaperLiteralOrdinaryRescaledTube
          sourceTube anchor
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1)).carrier :=
    wz2PaperLiteral_image_paperCarrier_subset_ordinary_of_boundedBase
      actualNearby.scaleData.delta_pos
      sourceTube anchor
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      callerRequested.2.2 ratioSmall sourceLine sourceBase
      (data.internalCover.fullFiberSubfamily_covered parent finalIndex)
  have imageMem :=
    canonicalContainment
      ⟨sourcePoint, sourcePointPaper, rfl⟩
  have publicTubeEq :
      leaves.output.rescalingCertificate.publicFamily.tube publicIndex =
        wz2PaperLiteralOrdinaryRescaledTube
          sourceTube anchor
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1) := by
    rfl
  change
    Metric.infEDist
        (wz2PaperLiteralUnitRescalingMap
          anchor
          (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
          sourcePoint)
        (Kakeya.unitSegment
          (leaves.output.rescalingCertificate.publicFamily.tube
            publicIndex).base
          (leaves.output.rescalingCertificate.publicFamily.tube
            publicIndex).direction) ≤
      ENNReal.ofReal (delta / callerRequested.1)
  rw [publicTubeEq]
  exact Metric.mem_cthickening_iff.mp imageMem

/--
Critical exact-image witness from the frozen bounded-base normalization.
-/
noncomputable def
    FinalFiberRescalingLeaves.criticalRescaledWitness_of_bounded_normalization :
    PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss)
      (data.finalFiberShading parent)
      (data.selectedPacked.family.tube parent)
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1) :=
  leaves.criticalRescaledWitness
    (leaves.imageDistance_of_bounded_normalization normalized)

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
