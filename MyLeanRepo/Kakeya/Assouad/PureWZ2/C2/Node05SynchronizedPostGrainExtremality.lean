import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedPostGrainReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRigidBodyMassRatio
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorLocalReduction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection

/-!
# Extremality of the synchronized post-grain restriction

The synchronized pruning supplies a genuine per-tube lower bound measured
against ordinary unit-tube volume.  This file converts that bound to the
cropped paper-density convention using the fixed `13824` body-volume ratio.
It then packages the selected extremality once its non-hereditary nearby-CWA
certificate is supplied.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- The dense-cubicalization defining the ancestor re-entry retains a fixed
fraction of the actual post-grain carrier inside the framed ordinary trace. -/
theorem pureWZ2Node05PostGrainOverlap_per_tube
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (index : Fin coarseRefinement.selected.family.card) :
    (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          volume (coarseGrains.shading.carrier index) ≤
      volume ((pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains).carrier index) := by
  let ordinaryIndex := ancestor.geometry.indexEquiv.symm index
  let ordinary := ancestor.geometry.frame ''
    ancestor.geometry.ordinaryRefined.carrier ordinaryIndex
  let cropped := coarseGrains.shading.carrier index
  let tube := coarseRefinement.selected.family.tube index
  have hcropped : cropped ⊆ pureWZ2DenseCubicalization tube ordinary := by
    intro point pointMem
    have ancestorMem := coarseGrains.subshading index pointMem
    have hdense := ancestor.geometry.cropped_carrier_eq_dense_cubicalization
      ordinaryIndex
    rw [ancestor.geometry.indexEquiv.apply_symm_apply index] at hdense
    rw [hdense] at ancestorMem
    exact ancestorMem
  have hordinaryMeasurable : MeasurableSet ordinary :=
    ancestor.geometry.frame.toHomeomorph.measurableEmbedding
      |>.measurableSet_image'
        (ancestor.geometry.ordinaryRefined.measurable_carrier ordinaryIndex)
  have htrace := pureWZ2_dense_cubical_trace
    ancestor.cropped_extremal.delta_pos tube ordinary cropped
    hordinaryMeasurable (coarseGrains.shading.measurable_carrier index)
    (coarseGrains.cubical index) hcropped
  have hordinaryVolume :
      volume ordinary =
        volume (ancestor.geometry.ordinaryRefined.carrier ordinaryIndex) :=
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      ancestor.geometry.frame _
      (ancestor.geometry.ordinaryRefined.measurable_carrier ordinaryIndex)
  have hsourceTubeVolume :
      volume
          (ancestor.geometry.selected.family.tube ordinaryIndex).carrier =
        volume tube.carrier := by
    have hframeVolume :=
      Kakeya.Streamlined.AffineIsometryEquiv.volume_image
        ancestor.geometry.frame
        (ancestor.geometry.selected.family.tube ordinaryIndex).carrier
        (wz2_paper_ordinary_tube_carrier_measurable
          (ancestor.geometry.selected.family.tube ordinaryIndex)
          ancestor.cropped_extremal.delta_pos)
    have hcarrier := ancestor.geometry.ordinary_carrier_image_eq ordinaryIndex
    rw [ancestor.geometry.indexEquiv.apply_symm_apply index] at hcarrier
    calc
      volume
          (ancestor.geometry.selected.family.tube ordinaryIndex).carrier =
        volume
          (ancestor.geometry.frame ''
            (ancestor.geometry.selected.family.tube ordinaryIndex).carrier) :=
              hframeVolume.symm
      _ = volume tube.carrier := by rw [← hcarrier]
  have hordinaryDensity :
      ancestor.geometry.ordinaryDensity * volume tube.carrier ≤
        volume ordinary := by
    rw [← hsourceTubeVolume, hordinaryVolume]
    exact ancestor.geometry.ordinary_per_tube ordinaryIndex
  have htubePositive : 0 < volume tube.carrier :=
    wz2_paper_ordinary_tube_volume_pos tube
      ancestor.cropped_extremal.delta_pos
  have htubeTop : volume tube.carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top tube
      ancestor.cropped_extremal.delta_pos
  have hdensityRatio : ancestor.geometry.ordinaryDensity ≤
      volume ordinary * (volume tube.carrier)⁻¹ := by
    calc
      ancestor.geometry.ordinaryDensity =
          (ancestor.geometry.ordinaryDensity * volume tube.carrier) *
            (volume tube.carrier)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel htubePositive.ne' htubeTop,
          mul_one]
      _ ≤ volume ordinary * (volume tube.carrier)⁻¹ := by
        gcongr
  calc
    (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          volume cropped ≤
        (100 : ENNReal)⁻¹ *
          (volume ordinary * (volume tube.carrier)⁻¹) *
            volume cropped := by gcongr
    _ = (100 : ENNReal)⁻¹ * volume ordinary *
          (volume tube.carrier)⁻¹ * volume cropped := by ring
    _ ≤ volume (ordinary ∩ cropped) := htrace
    _ = volume ((pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains).carrier index) := rfl

/-- The same pointwise trace estimate controls the whole actual post-grain
indexed mass, independently of the later pruning threshold. -/
theorem pureWZ2Node05PostGrainOverlap_cropped_mass_lower
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss) :
    (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          coarseGrains.shading.mass ≤
      (pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains).mass := by
  change
    ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity) *
          (∑ index : Fin coarseRefinement.selected.family.card,
            volume (coarseGrains.shading.carrier index)) ≤
      ∑ index : Fin coarseRefinement.selected.family.card,
        volume ((pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains).carrier index)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun index _ =>
    pureWZ2Node05PostGrainOverlap_per_tube
      coarseRefinement ancestor coarseGrains index

/-- The ancestor ordinary trace cannot have more indexed mass than the
ordinary tube bodies of the corresponding cropped family. -/
theorem pureWZ2Node05PostGrainAncestorTrace_mass_le_body_mass
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss) :
    ancestor.geometry.ordinaryRefined.mass ≤
      coarseRefinement.selected.family.toBodyFamily.mass := by
  have hsource : ancestor.geometry.ordinaryRefined.mass ≤
      ancestor.geometry.selected.family.toBodyFamily.mass := by
    change
      (∑ index : Fin ancestor.geometry.selected.family.card,
        volume (ancestor.geometry.ordinaryRefined.carrier index)) ≤
      ∑ index : Fin ancestor.geometry.selected.family.card,
        volume (ancestor.geometry.selected.family.tube index).carrier
    exact Finset.sum_le_sum fun index _ =>
      measure_mono (ancestor.geometry.ordinaryRefined.subset_body index)
  refine hsource.trans_eq ?_
  apply Fintype.sum_equiv ancestor.geometry.indexEquiv
  intro index
  have hframeVolume :=
    Kakeya.Streamlined.AffineIsometryEquiv.volume_image
      ancestor.geometry.frame
      (ancestor.geometry.selected.family.tube index).carrier
      (wz2_paper_ordinary_tube_carrier_measurable
        (ancestor.geometry.selected.family.tube index)
        ancestor.cropped_extremal.delta_pos)
  have hcarrier := ancestor.geometry.ordinary_carrier_image_eq index
  calc
    volume (ancestor.geometry.selected.family.tube index).carrier =
        volume (ancestor.geometry.frame ''
          (ancestor.geometry.selected.family.tube index).carrier) :=
      hframeVolume.symm
    _ = volume (coarseRefinement.selected.family.tube
        (ancestor.geometry.indexEquiv index)).carrier := by rw [hcarrier]

/-- The exact dense-cubical trace and actual grain density give an aggregate
lower bound in terms of the ancestor ordinary trace mass. -/
theorem pureWZ2Node05PostGrainOverlap_ancestor_mass_lower
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (hdeltaSmall : delta ≤ 1 / 12) :
    ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
        Kakeya.realRpowENN delta grainLoss) *
          ancestor.geometry.ordinaryRefined.mass ≤
      (pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains).mass := by
  have hordinaryBody :=
    pureWZ2Node05PostGrainAncestorTrace_mass_le_body_mass
      coarseRefinement ancestor
  have hordinaryPaper :
      coarseRefinement.selected.family.toBodyFamily.mass ≤
        (wz1PaperBodyFamily coarseRefinement.selected.family).mass := by
    change
      (∑ index : Fin coarseRefinement.selected.family.card,
        volume (coarseRefinement.selected.family.tube index).carrier) ≤
      ∑ index : Fin coarseRefinement.selected.family.card,
        volume (wz1PaperTubeCarrier
          (coarseRefinement.selected.family.tube index))
    exact Finset.sum_le_sum fun index _ => by
      calc
        volume (coarseRefinement.selected.family.tube index).carrier =
            Kakeya.deltaTubeVolume delta :=
          tube_volume_scaling.1 delta
            (coarseRefinement.selected.family.tube index)
        _ ≤ volume (wz1PaperTubeCarrier
            (coarseRefinement.selected.family.tube index)) :=
          wz2PaperTubeCarrier_volume_lower
            ancestor.cropped_extremal.delta_pos hdeltaSmall
            (coarseRefinement.selected.family.tube index)
            (coarseGrains.line_class index)
  have hgrain :
      Kakeya.realRpowENN delta grainLoss *
          ancestor.geometry.ordinaryRefined.mass ≤
        coarseGrains.shading.mass := by
    calc
      Kakeya.realRpowENN delta grainLoss *
          ancestor.geometry.ordinaryRefined.mass ≤
        Kakeya.realRpowENN delta grainLoss *
          coarseRefinement.selected.family.toBodyFamily.mass := by gcongr
      _ ≤ Kakeya.realRpowENN delta grainLoss *
          (wz1PaperBodyFamily coarseRefinement.selected.family).mass := by gcongr
      _ ≤ coarseGrains.shading.mass := coarseGrains.extremal.dense
  calc
    ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
        Kakeya.realRpowENN delta grainLoss) *
          ancestor.geometry.ordinaryRefined.mass =
      ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity) *
        (Kakeya.realRpowENN delta grainLoss *
          ancestor.geometry.ordinaryRefined.mass) := by ring
    _ ≤ ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity) *
        coarseGrains.shading.mass := by gcongr
    _ ≤ (pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains).mass :=
      pureWZ2Node05PostGrainOverlap_cropped_mass_lower
        coarseRefinement ancestor coarseGrains

/-- The literal post-grain overlap is dense after combining the ancestor
ordinary density, the actual grain density, and the paper/ordinary body-volume
comparison. -/
theorem pureWZ2Node05PostGrainOverlap_dense
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (hdeltaSmall : delta ≤ 1 / 12) :
    (pureWZ2Node05PostGrainOverlapShading
      coarseRefinement ancestor coarseGrains).IsLambdaDense
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss) := by
  let family := coarseRefinement.selected.family
  have hordinaryPaper : family.toBodyFamily.mass ≤
      (wz1PaperBodyFamily family).mass := by
    change
      (∑ index : Fin family.card, volume (family.tube index).carrier) ≤
        ∑ index : Fin family.card,
          volume (wz1PaperTubeCarrier (family.tube index))
    exact Finset.sum_le_sum fun index _ => by
      calc
        volume (family.tube index).carrier =
            Kakeya.deltaTubeVolume delta :=
          tube_volume_scaling.1 delta (family.tube index)
        _ ≤ volume (wz1PaperTubeCarrier (family.tube index)) :=
          wz2PaperTubeCarrier_volume_lower
            ancestor.cropped_extremal.delta_pos hdeltaSmall
            (family.tube index) (coarseGrains.line_class index)
  calc
    ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss) * family.toBodyFamily.mass ≤
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss) *
            (wz1PaperBodyFamily family).mass := by gcongr
    _ = ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity) *
          (Kakeya.realRpowENN delta grainLoss *
            (wz1PaperBodyFamily family).mass) := by ring
    _ ≤ ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity) *
          coarseGrains.shading.mass := by
      exact mul_le_mul_right coarseGrains.extremal.dense _
    _ ≤ (pureWZ2Node05PostGrainOverlapShading
        coarseRefinement ancestor coarseGrains).mass :=
      pureWZ2Node05PostGrainOverlap_cropped_mass_lower
        coarseRefinement ancestor coarseGrains

/-- Construct the synchronized core from scalar absorptions only.  The
ordinary/cropped aggregate overlap is derived from the exact re-entry
geometry and the actual whole-cell grain shading. -/
theorem exists_pureWZ2Node05SynchronizedPostGrainCore_of_scalars_with_loss_two
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (inputEta outputEta : ℝ)
    (croppedMassFraction : ENNReal)
    (hdeltaSmall : delta ≤ 1 / 12)
    (densitySeparation :
      Kakeya.realRpowENN delta outputEta ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta inputEta)
    (inputDensityAbsorption :
      Kakeya.realRpowENN delta inputEta ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss)
    (croppedMassAbsorption :
      croppedMassFraction ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity) :
    ∃ core : PureWZ2Node05SynchronizedPostGrainCore
        coarseRefinement ancestor coarseGrains outputEta croppedMassFraction,
      core.retentionLoss = 2 := by
  apply exists_pureWZ2Node05SynchronizedPostGrainCore_with_loss_two
    coarseRefinement ancestor coarseGrains inputEta outputEta
      croppedMassFraction densitySeparation
  apply max_le
  · exact (mul_le_mul_left inputDensityAbsorption _).trans
      (pureWZ2Node05PostGrainOverlap_dense
        coarseRefinement ancestor coarseGrains hdeltaSmall)
  · exact (mul_le_mul_left croppedMassAbsorption _).trans
      (pureWZ2Node05PostGrainOverlap_cropped_mass_lower
        coarseRefinement ancestor coarseGrains)

/-- Compatibility wrapper retaining the original scalar-only core API. -/
theorem exists_pureWZ2Node05SynchronizedPostGrainCore_of_scalars
    {delta sigma sourceLoss normalizationLoss grainLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    (coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent)
    (ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss)
    (coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss)
    (inputEta outputEta : ℝ)
    (croppedMassFraction : ENNReal)
    (hdeltaSmall : delta ≤ 1 / 12)
    (densitySeparation :
      Kakeya.realRpowENN delta outputEta ≤
        (1 / 2 : ENNReal) * Kakeya.realRpowENN delta inputEta)
    (inputDensityAbsorption :
      Kakeya.realRpowENN delta inputEta ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss)
    (croppedMassAbsorption :
      croppedMassFraction ≤
        (100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity) :
    Nonempty (PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction) := by
  rcases exists_pureWZ2Node05SynchronizedPostGrainCore_of_scalars_with_loss_two
      coarseRefinement ancestor coarseGrains inputEta outputEta
      croppedMassFraction hdeltaSmall densitySeparation
      inputDensityAbsorption croppedMassAbsorption with ⟨core, _⟩
  exact ⟨core⟩

namespace PureWZ2Node05SynchronizedPostGrainCore

variable
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta selectedLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    {coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent}
    {ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss}
    {coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss}
    {croppedMassFraction : ENNReal}
    (core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction)

/-- The synchronized cropped union is a literal subset of the actual
post-grain union. -/
theorem selected_cropped_union_subset :
    (restrictPaperShading
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained)
      coarseGrains.shading).union ⊆
        coarseGrains.shading.union := by
  rintro point ⟨index, pointMem⟩
  exact
    ⟨(pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).embedding index,
      pointMem⟩

/-- Summing the synchronized pointwise overlap estimates gives aggregate
density relative to ordinary unit-tube mass. -/
theorem selected_cropped_ordinary_dense :
    Kakeya.realRpowENN delta outputEta *
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained).family.toBodyFamily.mass ≤
      (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading).mass := by
  change
    Kakeya.realRpowENN delta outputEta *
        (∑ index : Fin core.retained.card,
          volume
            ((pureWZ2Node05PostGrainSelectedSubfamily
              coarseRefinement.selected.family core.retained).family.tube
                index).carrier) ≤
      ∑ index : Fin core.retained.card,
        volume
          ((restrictPaperShading
            (pureWZ2Node05PostGrainSelectedSubfamily
              coarseRefinement.selected.family core.retained)
            coarseGrains.shading).carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  exact (core.ordinary_overlap_per_tube index).trans
    (measure_mono Set.inter_subset_right)

/-- The synchronized ordinary trace retains the requested source fraction
once the fixed dense-cubical and factor-two pruning losses are absorbed. -/
theorem retained_ordinary_mass_of_scalar
    (selectedNormalizationExponent : ℕ)
    (hdeltaSmall : delta ≤ 1 / 12)
    (absorption :
      core.retentionLoss *
          wz2PaperPureRefinementFraction delta selectedNormalizationExponent ≤
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss) *
            wz2PaperPureRefinementFraction delta normalizationExponent) :
    wz2PaperPureRefinementFraction delta selectedNormalizationExponent *
          ancestor.ordinarySource.shading.mass ≤
      (pureWZ2Node05PostGrainSelectedOrdinaryTrace
        coarseRefinement ancestor coarseGrains core.retained).mass := by
  have hscaled :
      core.retentionLoss *
          (wz2PaperPureRefinementFraction delta selectedNormalizationExponent *
            ancestor.ordinarySource.shading.mass) ≤
        core.retentionLoss *
          (pureWZ2Node05PostGrainSelectedOrdinaryTrace
            coarseRefinement ancestor coarseGrains core.retained).mass := by
    calc
      core.retentionLoss *
          (wz2PaperPureRefinementFraction delta selectedNormalizationExponent *
            ancestor.ordinarySource.shading.mass) =
        (core.retentionLoss * wz2PaperPureRefinementFraction delta
          selectedNormalizationExponent) *
            ancestor.ordinarySource.shading.mass := by ring
      _ ≤ (((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
            Kakeya.realRpowENN delta grainLoss) *
          wz2PaperPureRefinementFraction delta normalizationExponent) *
            ancestor.ordinarySource.shading.mass := by gcongr
      _ ≤ ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
            Kakeya.realRpowENN delta grainLoss) *
          ancestor.geometry.ordinaryRefined.mass := by
        rw [mul_assoc]
        exact mul_le_mul_right ancestor.geometry.retained_mass _
      _ ≤ (pureWZ2Node05PostGrainOverlapShading
          coarseRefinement ancestor coarseGrains).mass :=
        pureWZ2Node05PostGrainOverlap_ancestor_mass_lower
          coarseRefinement ancestor coarseGrains hdeltaSmall
      _ ≤ core.retentionLoss * (selectedTubeShading
          (pureWZ2Node05PostGrainOverlapShading
            coarseRefinement ancestor coarseGrains) core.retained).mass :=
        core.overlap_mass_retention
      _ = core.retentionLoss *
          (pureWZ2Node05PostGrainSelectedOrdinaryTrace
            coarseRefinement ancestor coarseGrains core.retained).mass := by
        rw [core.ordinary_mass_eq]
  exact (ENNReal.mul_le_mul_iff_right
    core.retentionLoss_ne_zero core.retentionLoss_ne_top).mp hscaled

/-- Convert the ordinary-volume density furnished by synchronized pruning to
the literal cropped-paper density used by Section 6. -/
theorem selected_cropped_dense
    {selectedLoss : ℝ}
    (densityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN delta selectedLoss ≤
        Kakeya.realRpowENN delta outputEta) :
    (restrictPaperShading
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained)
      coarseGrains.shading).IsLambdaDense
        (Kakeya.realRpowENN delta selectedLoss) := by
  let selected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  have hpaper :
      (wz1PaperBodyFamily selected.family).mass ≤
        (13824 : ENNReal) * selected.family.toBodyFamily.mass :=
    wz2PaperBodyFamily_mass_le_ordinary
      ancestor.cropped_extremal.delta_pos
      ancestor.cropped_extremal.delta_le_one selected.family
      (coarseGrains.line_class.subfamily selected)
  calc
    Kakeya.realRpowENN delta selectedLoss *
          (wz1PaperBodyFamily selected.family).mass ≤
        Kakeya.realRpowENN delta selectedLoss *
          ((13824 : ENNReal) * selected.family.toBodyFamily.mass) := by
            gcongr
    _ = ((13824 : ENNReal) *
          Kakeya.realRpowENN delta selectedLoss) *
            selected.family.toBodyFamily.mass := by ring
    _ ≤ Kakeya.realRpowENN delta outputEta *
          selected.family.toBodyFamily.mass := by gcongr
    _ ≤ (restrictPaperShading selected coarseGrains.shading).mass := by
      exact core.selected_cropped_ordinary_dense

/-- The cardinality retained by synchronized pruning transports the ambient
top-level paper CWA after one explicit scalar absorption. -/
theorem selected_cropped_top_level_cwa
    {selectedLoss : ℝ}
    (constantAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-selectedLoss)) :
    WZ2PaperConvexWolffBound
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-selectedLoss)) := by
  let selected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  have hweightZero : Kakeya.realRpowENN delta outputEta ≠ 0 :=
    (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos ancestor.cropped_extremal.delta_pos outputEta)).ne'
  have hweightTop : Kakeya.realRpowENN delta outputEta ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hcardinality :
      Kakeya.realRpowENN delta outputEta *
          coarseRefinement.selected.family.enncard ≤
        1 * selected.family.enncard := by
    simpa [selected] using core.cardinality_retention
  have raw := coarseGrains.top_level_cwa.subfamily_of_weighted_cardinality
    selected hweightZero hweightTop hcardinality
  intro convexSet hconvex
  exact (raw convexSet hconvex).trans (by gcongr)

/-- All hereditary extremality fields are reconstructed on the exact selected
post-grain shading.  Nearby CWA and its density absorption remain explicit. -/
theorem selected_cropped_extremal
    {selectedLoss : ℝ}
    (grainLoss_le : grainLoss ≤ selectedLoss)
    (nearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-selectedLoss)))
    (densityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN delta selectedLoss ≤
        Kakeya.realRpowENN delta outputEta) :
    WZ2PaperCroppedIsExtremal sigma selectedLoss
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading) := by
  let selected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  let ambient := coarseGrains.extremal.mono_loss grainLoss_le
  exact
    { delta_pos := ambient.delta_pos
      delta_le_one := ambient.delta_le_one
      nonempty := Finset.card_pos.mpr core.retained_nonempty
      cwa_nearby_scales := nearby
      cubical := restrictPaperShading_cubical selected coarseGrains.cubical
      dense := core.selected_cropped_dense densityAbsorption
      volume_upper := (measure_mono core.selected_cropped_union_subset).trans
        ambient.volume_upper }

end PureWZ2Node05SynchronizedPostGrainCore

namespace PureWZ2Node05SelectedGrainReceipt

variable
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta selectedLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent : ℕ}
    {coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent}
    {ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss}
    {coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss}
    {croppedMassFraction : ENNReal}
    {core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction}

/-- Build the selected grain receipt after proving only the two genuinely
non-hereditary CWA fields, the scalar density absorption, and the critical
volume floor. -/
theorem ofNearbyAndDensity
    (nearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-selectedLoss)))
    (densityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN delta selectedLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (grainLoss_le : grainLoss ≤ selectedLoss)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-selectedLoss))
    (volumeLower : Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
      volume (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading).union) :
    PureWZ2Node05SelectedGrainReceipt core selectedLoss where
  grainLoss_le := grainLoss_le
  extremal := core.selected_cropped_extremal grainLoss_le nearby densityAbsorption
  top_level_cwa := core.selected_cropped_top_level_cwa topLevelAbsorption
  volume_lower := volumeLower

/-- Use one quantifier-ordered cropped critical-floor selection to discharge
the selected union-volume lower bound.  The same structural-loss CWA and
density witnesses are used in that invocation; the final loss is obtained by
monotonicity without changing the selected family or shading. -/
theorem ofCriticalFloor
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma selectedLoss selectedLoss)
    (grainLoss_le : grainLoss ≤ selectedLoss)
    (hdeltaCutoff : delta ≤ criticalFloor.delta₀)
    (nearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-criticalFloor.structuralLoss)))
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-selectedLoss)) :
    PureWZ2Node05SelectedGrainReceipt core selectedLoss := by
  let selected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  let shading := restrictPaperShading selected coarseGrains.shading
  have hstructuralDense : shading.IsLambdaDense
      (Kakeya.realRpowENN delta criticalFloor.structuralLoss) :=
    core.selected_cropped_dense densityAbsorption
  have htargetNearby : WZ2PaperPureCWAAtNearbyScales selected.family
      (Kakeya.realRpowENN delta (-selectedLoss)) :=
    nearby.mono_loss ancestor.cropped_extremal.delta_pos
      ancestor.cropped_extremal.delta_le_one criticalFloor.structuralLoss_le
  have htargetDensityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN delta selectedLoss ≤
        Kakeya.realRpowENN delta outputEta := by
    calc
      (13824 : ENNReal) * Kakeya.realRpowENN delta selectedLoss ≤
          (13824 : ENNReal) *
            Kakeya.realRpowENN delta criticalFloor.structuralLoss := by
        gcongr
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_exponent_ge
          ancestor.cropped_extremal.delta_pos
          ancestor.cropped_extremal.delta_le_one
          criticalFloor.structuralLoss_le
      _ ≤ Kakeya.realRpowENN delta outputEta := densityAbsorption
  have hvolumeLower : Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
      volume shading.union :=
    criticalFloor.volume_floor delta ancestor.cropped_extremal.delta_pos
      hdeltaCutoff selected.family
      (Finset.card_pos.mpr core.retained_nonempty) shading nearby
      (restrictPaperShading_cubical selected coarseGrains.cubical)
      hstructuralDense
  exact ofNearbyAndDensity htargetNearby htargetDensityAbsorption
    grainLoss_le topLevelAbsorption hvolumeLower

/-- Derive the selected volume floor from Node 2's ordinary critical floor
using the exact ancestor trace on this synchronized family.  This is a local,
source-indexed conversion and does not assume the global cropped-floor
reduction statement. -/
theorem ofReentryTraceAndPureCriticalFloor
    {densityLoss structuralBudget : ℝ}
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma selectedLoss structuralBudget)
    (lossConstant : ENNReal)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (grainLoss_le_density : grainLoss ≤ densityLoss)
    (densityLoss_le : densityLoss ≤ selectedLoss)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hdeltaCutoff : delta ≤ criticalFloor.delta₀)
    (nearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-densityLoss)))
    (densityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-selectedLoss))
    (traceAbsorption : lossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta outputEta)
    (cwaAbsorption :
      lossConstant * Kakeya.realRpowENN delta (-densityLoss) ≤
        Kakeya.realRpowENN delta (-criticalFloor.structuralLoss))
    (criticalDensityAbsorption :
      Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        lossConstant⁻¹ * Kakeya.realRpowENN delta densityLoss) :
    PureWZ2Node05SelectedGrainReceipt core selectedLoss := by
  let selected := pureWZ2Node05PostGrainSelectedSubfamily
    coarseRefinement.selected.family core.retained
  let shading := restrictPaperShading selected coarseGrains.shading
  let normalized := ancestor.toNormalizationData
  have hselectedNonempty : selected.family.Nonempty :=
    Finset.card_pos.mpr core.retained_nonempty
  have hfinalSubset : ∀ index, shading.carrier index ⊆
      normalized.croppedRefined.carrier (selected.embedding index) := by
    intro index point hpoint
    exact coarseGrains.subshading (selected.embedding index) hpoint
  have hordinaryPerTube : ∀ index : Fin selected.family.card,
      Kakeya.realRpowENN delta outputEta *
          volume (normalized.croppedFamily.tube
            (selected.embedding index)).carrier ≤
        volume (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (normalized.ordinaryIndex selected index)) := by
    intro index
    have hoverlap := core.ordinary_overlap_per_tube index
    calc
      Kakeya.realRpowENN delta outputEta *
            volume (normalized.croppedFamily.tube
              (selected.embedding index)).carrier ≤
          volume ((selectedTubeShading
            (pureWZ2Node05PostGrainOverlapShading
              coarseRefinement ancestor coarseGrains)
            core.retained).carrier index) := by
        change Kakeya.realRpowENN delta outputEta *
            volume (selected.family.tube index).carrier ≤ _
        simpa [selected, Kakeya.DeltaTube.volume] using hoverlap
      _ ≤ volume (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (normalized.ordinaryIndex selected index)) := by
        apply measure_mono
        intro point hpoint
        exact hpoint.1
  have hfamilyDensity := core.selected_cropped_extremal
    grainLoss_le_density nearby densityAbsorption
  rcases normalized.croppedFloorReduction_of_trace selected shading
      hselectedNonempty (restrictPaperShading_cubical selected
        coarseGrains.cubical) hfinalSubset
      (Kakeya.realRpowENN delta outputEta) hordinaryPerTube
      lossConstant (Kakeya.realRpowENN delta (-densityLoss))
      (Kakeya.realRpowENN delta densityLoss)
      lossConstantOne lossConstantTop traceAbsorption nearby
      hfamilyDensity.dense hdeltaSmall with ⟨reduced⟩
  have hordinaryCWA : WZ2PaperPureCWAAtNearbyScales
      reduced.ordinaryFamily
      (Kakeya.realRpowENN delta (-criticalFloor.structuralLoss)) :=
    reduced.ordinary_cwa.mono cwaAbsorption
      (by simp [Kakeya.realRpowENN])
  have hordinaryDense : reduced.ordinaryShading.IsLambdaDense
      (Kakeya.realRpowENN delta criticalFloor.structuralLoss) := by
    exact
      (mul_le_mul_left criticalDensityAbsorption
        reduced.ordinaryFamily.toBodyFamily.mass).trans
        reduced.ordinary_dense
  have hvolumeLower : Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
      volume shading.union :=
    (criticalFloor.volume_floor delta
      ancestor.cropped_extremal.delta_pos hdeltaCutoff
      reduced.ordinaryFamily reduced.ordinary_nonempty
      reduced.ordinaryShading hordinaryCWA hordinaryDense).trans
        reduced.ordinary_union_volume_le
  have htargetNearby : WZ2PaperPureCWAAtNearbyScales selected.family
      (Kakeya.realRpowENN delta (-selectedLoss)) :=
    nearby.mono_loss ancestor.cropped_extremal.delta_pos
      ancestor.cropped_extremal.delta_le_one densityLoss_le
  have htargetDensityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN delta selectedLoss ≤
        Kakeya.realRpowENN delta outputEta := by
    calc
      (13824 : ENNReal) * Kakeya.realRpowENN delta selectedLoss ≤
          (13824 : ENNReal) * Kakeya.realRpowENN delta densityLoss := by
        gcongr
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_exponent_ge
          ancestor.cropped_extremal.delta_pos
          ancestor.cropped_extremal.delta_le_one densityLoss_le
      _ ≤ Kakeya.realRpowENN delta outputEta := densityAbsorption
  exact ofNearbyAndDensity htargetNearby htargetDensityAbsorption
    (grainLoss_le_density.trans densityLoss_le) topLevelAbsorption hvolumeLower

/-- Regard the selected configuration as an identity refinement of its own
exact cropped shading.  This is the source expected by the next sticky call. -/
noncomputable def toIdentityGrainRefinementData
    (receipt : PureWZ2Node05SelectedGrainReceipt core selectedLoss) :
    PureWZ2GrainRefinementData
      (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading)
      sigma selectedLoss := by
  let configuration := receipt.toGrainConfiguration
  exact
    { shading := configuration.shading
      subshading := fun _ => Set.Subset.rfl
      line_class := configuration.line_class
      cubical := configuration.cubical
      extremal := configuration.extremal
      top_level_cwa := configuration.top_level_cwa
      volume_lower := receipt.volume_lower
      globalGrains := configuration.globalGrains
      localGrains := configuration.localGrains
      planeMap_vertical_bound := by
        intro point
        exact coarseGrains.planeMap_vertical_bound
          ⟨point, by
            rcases point.property with ⟨index, pointMem⟩
            exact ⟨(pureWZ2Node05PostGrainSelectedSubfamily
              coarseRefinement.selected.family core.retained).embedding index,
              pointMem⟩⟩ }

@[simp] theorem toIdentityGrainRefinementData_shading
    (receipt : PureWZ2Node05SelectedGrainReceipt core selectedLoss) :
    receipt.toIdentityGrainRefinementData.shading =
      restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading := rfl

end PureWZ2Node05SelectedGrainReceipt

namespace PureWZ2Node05SelectedReentryReceipt

variable
    {delta sigma sourceLoss normalizationLoss grainLoss outputEta selectedLoss : ℝ}
    {coarseFamily : Kakeya.Streamlined.TubeFamily delta}
    {baseShading : WZ1PaperTubeShading coarseFamily}
    {coarseRefinementExponent normalizationExponent
      selectedNormalizationExponent : ℕ}
    {coarseRefinement :
      WZ1PaperRefinement baseShading coarseRefinementExponent}
    {ancestor :
      PureWZ2PropStickyReentryData
        (sigma := sigma) coarseRefinement.refined normalizationExponent
        sourceLoss normalizationLoss}
    {coarseGrains :
      PureWZ2GrainRefinementData
        coarseRefinement.refined sigma grainLoss}
    {croppedMassFraction : ENNReal}
    {core : PureWZ2Node05SynchronizedPostGrainCore
      coarseRefinement ancestor coarseGrains outputEta croppedMassFraction}

/-- Assemble the exact selected re-entry after deriving its selected
extremality and top-level CWA from the synchronized core. -/
theorem ofNearbyAndScalars
    (nearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-selectedLoss)))
    (grainLoss_le : grainLoss ≤ selectedLoss)
    (densityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN delta selectedLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-selectedLoss))
    (volumeLower : Kakeya.realRpowENN delta (sigma + selectedLoss) ≤
      volume (restrictPaperShading
        (pureWZ2Node05PostGrainSelectedSubfamily
          coarseRefinement.selected.family core.retained)
        coarseGrains.shading).union)
    (normalizationLoss_le : normalizationLoss ≤ selectedLoss)
    (retainedOrdinaryMass :
      wz2PaperPureRefinementFraction delta selectedNormalizationExponent *
          ancestor.ordinarySource.shading.mass ≤
        (pureWZ2Node05PostGrainSelectedOrdinaryTrace
          coarseRefinement ancestor coarseGrains core.retained).mass)
    (densityBudget : Kakeya.realRpowENN delta sourceLoss / 2 ≤
      Kakeya.realRpowENN delta outputEta) :
    PureWZ2Node05SelectedReentryReceipt core selectedLoss
      selectedNormalizationExponent := by
  let grainReceipt : PureWZ2Node05SelectedGrainReceipt core selectedLoss :=
    PureWZ2Node05SelectedGrainReceipt.ofNearbyAndDensity
      nearby densityAbsorption grainLoss_le topLevelAbsorption volumeLower
  exact
    { grainReceipt with
      normalizationLoss_le := normalizationLoss_le
      retained_ordinary_mass := retainedOrdinaryMass
      density_budget := densityBudget }

/-- Construct the complete selected re-entry receipt from one cropped
critical floor and scalar absorptions.  Both the selected volume floor and
ordinary mass retention are discharged internally. -/
theorem ofCriticalFloorAndScalars
    (criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
      sigma selectedLoss selectedLoss)
    (grainLoss_le : grainLoss ≤ selectedLoss)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hdeltaCutoff : delta ≤ criticalFloor.delta₀)
    (nearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-criticalFloor.structuralLoss)))
    (densityAbsorption :
      (13824 : ENNReal) *
          Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-selectedLoss))
    (normalizationLoss_le : normalizationLoss ≤ selectedLoss)
    (retainedMassAbsorption :
      core.retentionLoss * wz2PaperPureRefinementFraction delta
          selectedNormalizationExponent ≤
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss) *
            wz2PaperPureRefinementFraction delta normalizationExponent)
    (densityBudget : Kakeya.realRpowENN delta sourceLoss / 2 ≤
      Kakeya.realRpowENN delta outputEta) :
    PureWZ2Node05SelectedReentryReceipt core selectedLoss
      selectedNormalizationExponent := by
  let grainReceipt : PureWZ2Node05SelectedGrainReceipt core selectedLoss :=
    PureWZ2Node05SelectedGrainReceipt.ofCriticalFloor criticalFloor
      grainLoss_le hdeltaCutoff nearby densityAbsorption topLevelAbsorption
  exact
    { grainReceipt with
      normalizationLoss_le := normalizationLoss_le
      retained_ordinary_mass := core.retained_ordinary_mass_of_scalar
        selectedNormalizationExponent hdeltaSmall retainedMassAbsorption
      density_budget := densityBudget }

/-- Complete selected re-entry from the same synchronized overlap, using the
ancestor normalization trace and Node 2's ordinary critical floor instead of
a global cropped-floor reduction. -/
theorem ofReentryTraceAndPureCriticalFloorAndScalars
    {densityLoss structuralBudget : ℝ}
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma selectedLoss structuralBudget)
    (lossConstant : ENNReal)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (grainLoss_le_density : grainLoss ≤ densityLoss)
    (densityLoss_le : densityLoss ≤ selectedLoss)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hdeltaCutoff : delta ≤ criticalFloor.delta₀)
    (nearby : WZ2PaperPureCWAAtNearbyScales
      (pureWZ2Node05PostGrainSelectedSubfamily
        coarseRefinement.selected.family core.retained).family
      (Kakeya.realRpowENN delta (-densityLoss)))
    (densityAbsorption :
      (13824 : ENNReal) * Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta outputEta)
    (topLevelAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-selectedLoss))
    (traceAbsorption : lossConstant⁻¹ ≤
      (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta outputEta)
    (cwaAbsorption :
      lossConstant * Kakeya.realRpowENN delta (-densityLoss) ≤
        Kakeya.realRpowENN delta (-criticalFloor.structuralLoss))
    (criticalDensityAbsorption :
      Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        lossConstant⁻¹ * Kakeya.realRpowENN delta densityLoss)
    (normalizationLoss_le : normalizationLoss ≤ selectedLoss)
    (retainedMassAbsorption :
      core.retentionLoss * wz2PaperPureRefinementFraction delta
          selectedNormalizationExponent ≤
        ((100 : ENNReal)⁻¹ * ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN delta grainLoss) *
            wz2PaperPureRefinementFraction delta normalizationExponent)
    (densityBudget : Kakeya.realRpowENN delta sourceLoss / 2 ≤
      Kakeya.realRpowENN delta outputEta) :
    PureWZ2Node05SelectedReentryReceipt core selectedLoss
      selectedNormalizationExponent := by
  let grainReceipt : PureWZ2Node05SelectedGrainReceipt core selectedLoss :=
    PureWZ2Node05SelectedGrainReceipt.ofReentryTraceAndPureCriticalFloor
      criticalFloor lossConstant lossConstantOne lossConstantTop
      grainLoss_le_density densityLoss_le hdeltaSmall hdeltaCutoff nearby
      densityAbsorption topLevelAbsorption traceAbsorption cwaAbsorption
      criticalDensityAbsorption
  exact
    { grainReceipt with
      normalizationLoss_le := normalizationLoss_le
      retained_ordinary_mass := core.retained_ordinary_mass_of_scalar
        selectedNormalizationExponent hdeltaSmall retainedMassAbsorption
      density_budget := densityBudget }

end PureWZ2Node05SelectedReentryReceipt

end Kakeya.Assouad

end
