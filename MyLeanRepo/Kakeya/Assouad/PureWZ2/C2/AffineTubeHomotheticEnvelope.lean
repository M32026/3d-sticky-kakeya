import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DirectionConstraint
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ActiveParentGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CombinedAffineEquiv
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# A localized affine tube-carrier envelope

An affine image of an ordinary unit tube can be much longer than an ordinary
target tube.  If the source and target supporting axes agree after the affine
map and one source-carrier anchor lands in the target carrier, the axial
length and transverse Lipschitz costs give an explicit homothetic envelope.
This is the packet-local geometric input needed by Proposition 6.4.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- A localized affine image of one ordinary tube lies in an explicit
homothety of a target ordinary tube with the same image supporting axis. -/
theorem pureWZ2_affine_tube_carrier_subset_homothety
    {sourceDelta targetDelta lipschitzFactor factor : ℝ}
    (hsourceDelta : 0 ≤ sourceDelta)
    (htargetDelta : 0 ≤ targetDelta)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (targetTube : Kakeya.DeltaTube targetDelta)
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    (hlipschitzFactor : 0 ≤ lipschitzFactor)
    (hlipschitz : ∀ first second,
      dist (equivalence first) (equivalence second) ≤
        lipschitzFactor * dist first second)
    (haxis : equivalence '' tubeAxisLine sourceTube =
      tubeAxisLine targetTube)
    (anchor : Point3)
    (hanchorSource : anchor ∈ sourceTube.carrier)
    (hanchorTarget : equivalence anchor ∈ targetTube.carrier)
    (hfactor :
      1 + 2 *
          (lipschitzFactor * (1 + sourceDelta) + targetDelta) ≤
        factor)
    (htransverse :
      lipschitzFactor * sourceDelta ≤ factor * targetDelta) :
    equivalence '' sourceTube.carrier ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint targetTube) factor ''
        targetTube.carrier := by
  have hbudgetNonneg :
      0 ≤ lipschitzFactor * (1 + sourceDelta) + targetDelta := by
    positivity
  have hfactorOne : 1 ≤ factor :=
    le_trans (by linarith : 1 ≤ 1 + 2 *
      (lipschitzFactor * (1 + sourceDelta) + targetDelta)) hfactor
  have hfactorPos : 0 < factor := zero_lt_one.trans_le hfactorOne
  intro imagePoint himagePoint
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  rcases exists_closest_on_axis hsourceDelta sourceTube sourcePoint
      hsourcePoint with
    ⟨sourceParameter, hsourceParameter, hsourceDistance⟩
  rcases exists_closest_on_axis hsourceDelta sourceTube anchor
      hanchorSource with
    ⟨anchorParameter, hanchorParameter, hanchorDistance⟩
  rcases exists_closest_on_axis htargetDelta targetTube
      (equivalence anchor) hanchorTarget with
    ⟨targetParameter, htargetParameter, htargetDistance⟩
  let sourceAxisPoint :=
    sourceTube.base + sourceParameter • sourceTube.direction
  let anchorAxisPoint :=
    sourceTube.base + anchorParameter • sourceTube.direction
  let targetAxisPoint :=
    targetTube.base + targetParameter • targetTube.direction
  have hsourceAxis : sourceAxisPoint ∈ tubeAxisLine sourceTube :=
    ⟨sourceParameter, rfl⟩
  have hanchorAxis : anchorAxisPoint ∈ tubeAxisLine sourceTube :=
    ⟨anchorParameter, rfl⟩
  have hsourceImageAxis :
      equivalence sourceAxisPoint ∈ tubeAxisLine targetTube := by
    rw [← haxis]
    exact ⟨sourceAxisPoint, hsourceAxis, rfl⟩
  have hanchorImageAxis :
      equivalence anchorAxisPoint ∈ tubeAxisLine targetTube := by
    rw [← haxis]
    exact ⟨anchorAxisPoint, hanchorAxis, rfl⟩
  rcases hsourceImageAxis with ⟨imageParameter, himageParameter⟩
  have hsourceAxisDistance : dist sourceAxisPoint anchorAxisPoint ≤ 1 := by
    have hparameter : |sourceParameter - anchorParameter| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hsourceParameter.1, hsourceParameter.2,
        hanchorParameter.1, hanchorParameter.2]
    rw [dist_eq_norm]
    have hdifference :
        sourceAxisPoint - anchorAxisPoint =
          (sourceParameter - anchorParameter) • sourceTube.direction := by
      dsimp only [sourceAxisPoint, anchorAxisPoint]
      module
    rw [hdifference, norm_smul, sourceTube.direction_unit, mul_one,
      Real.norm_eq_abs]
    exact hparameter
  have himageAxisDistance :
      dist (equivalence sourceAxisPoint)
          (equivalence anchorAxisPoint) ≤ lipschitzFactor := by
    calc
      dist (equivalence sourceAxisPoint)
          (equivalence anchorAxisPoint) ≤
          lipschitzFactor * dist sourceAxisPoint anchorAxisPoint :=
        hlipschitz _ _
      _ ≤ lipschitzFactor * 1 := by gcongr
      _ = lipschitzFactor := mul_one _
  have hanchorImageDistance :
      dist (equivalence anchorAxisPoint) (equivalence anchor) ≤
        lipschitzFactor * sourceDelta := by
    exact (hlipschitz anchorAxisPoint anchor).trans <| by
      gcongr
      simpa [anchorAxisPoint, dist_comm] using hanchorDistance
  have himageToTargetAxis :
      dist (equivalence sourceAxisPoint) targetAxisPoint ≤
        lipschitzFactor * (1 + sourceDelta) + targetDelta := by
    calc
      dist (equivalence sourceAxisPoint) targetAxisPoint ≤
          dist (equivalence sourceAxisPoint)
              (equivalence anchorAxisPoint) +
            dist (equivalence anchorAxisPoint) (equivalence anchor) +
            dist (equivalence anchor) targetAxisPoint := by
        exact dist_triangle4 _ _ _ _
      _ ≤ lipschitzFactor + lipschitzFactor * sourceDelta +
          targetDelta := by gcongr
      _ = lipschitzFactor * (1 + sourceDelta) + targetDelta := by ring
  have hparameterDistance :
      |imageParameter - targetParameter| ≤
        lipschitzFactor * (1 + sourceDelta) + targetDelta := by
    have hdistanceIdentity :
        dist (equivalence sourceAxisPoint) targetAxisPoint =
          |imageParameter - targetParameter| := by
      rw [himageParameter]
      dsimp only [targetAxisPoint]
      rw [dist_eq_norm]
      have hdifference :
          (targetTube.base + imageParameter • targetTube.direction) -
              (targetTube.base +
                targetParameter • targetTube.direction) =
            (imageParameter - targetParameter) •
              targetTube.direction := by
        module
      rw [hdifference, norm_smul, targetTube.direction_unit, mul_one,
        Real.norm_eq_abs]
    rw [← hdistanceIdentity]
    exact himageToTargetAxis
  let contractedParameter :=
    1 / 2 + (imageParameter - 1 / 2) / factor
  have hcontractedParameter : contractedParameter ∈ Set.Icc (0 : ℝ) 1 := by
    have himageLower :
        -(lipschitzFactor * (1 + sourceDelta) + targetDelta) ≤
          imageParameter := by
      have hbounds := abs_le.mp hparameterDistance
      linarith [htargetParameter.1]
    have himageUpper :
        imageParameter ≤
          1 + (lipschitzFactor * (1 + sourceDelta) + targetDelta) := by
      have hbounds := abs_le.mp hparameterDistance
      linarith [htargetParameter.2]
    dsimp only [contractedParameter]
    rw [Set.mem_Icc]
    constructor
    · rw [show
        1 / 2 + (imageParameter - 1 / 2) / factor =
          (imageParameter + (factor - 1) / 2) / factor by
            field_simp [hfactorPos.ne']
            ring]
      have hbudget :
          lipschitzFactor * (1 + sourceDelta) + targetDelta ≤
            (factor - 1) / 2 := by
        linarith
      exact div_nonneg (by linarith) hfactorPos.le
    · rw [show
        1 / 2 + (imageParameter - 1 / 2) / factor =
          (imageParameter + (factor - 1) / 2) / factor by
            field_simp [hfactorPos.ne']
            ring]
      apply (div_le_one hfactorPos).2
      have hbudget :
          lipschitzFactor * (1 + sourceDelta) + targetDelta ≤
            (factor - 1) / 2 := by
        linarith
      linarith
  let contractedAxisPoint :=
    targetTube.base + contractedParameter • targetTube.direction
  have hcontractedAxis : contractedAxisPoint ∈
      Kakeya.unitSegment targetTube.base targetTube.direction :=
    ⟨contractedParameter, hcontractedParameter, rfl⟩
  let midpoint := wz2PaperTubeMidpoint targetTube
  let contractedPoint :=
    AffineMap.homothety midpoint factor⁻¹ (equivalence sourcePoint)
  have hcontractedAxisIdentity :
      contractedAxisPoint =
        AffineMap.homothety midpoint factor⁻¹
          (equivalence sourceAxisPoint) := by
    rw [himageParameter, AffineMap.homothety_apply]
    dsimp only [contractedAxisPoint, contractedParameter, midpoint,
      wz2PaperTubeMidpoint]
    simp only [vsub_eq_sub, vadd_eq_add]
    apply PiLp.ext
    intro coordinate
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hfactorPos.ne']
    ring
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ targetDelta := by
    rw [hcontractedAxisIdentity]
    have hscale :
        dist
            (AffineMap.homothety midpoint factor⁻¹
              (equivalence sourcePoint))
            (AffineMap.homothety midpoint factor⁻¹
              (equivalence sourceAxisPoint)) =
          factor⁻¹ *
            dist (equivalence sourcePoint)
              (equivalence sourceAxisPoint) := by
      exact homothety_dist (inv_pos.mpr hfactorPos) _ _
    rw [hscale]
    calc
      factor⁻¹ *
          dist (equivalence sourcePoint)
            (equivalence sourceAxisPoint) ≤
          factor⁻¹ * (lipschitzFactor * sourceDelta) := by
        gcongr
        exact (hlipschitz sourcePoint sourceAxisPoint).trans <|
          mul_le_mul_of_nonneg_left
            (by simpa [sourceAxisPoint] using hsourceDistance)
            hlipschitzFactor
      _ ≤ factor⁻¹ * (factor * targetDelta) := by gcongr
      _ = targetDelta := by
        field_simp [hfactorPos.ne']
  have hcontractedCarrier : contractedPoint ∈ targetTube.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      targetDelta (Kakeya.unitSegment targetTube.base targetTube.direction)
      hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  dsimp only [contractedPoint, midpoint]
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hfactorPos.ne']
  ring

/-- The preceding envelope specialized to the translated Proposition-6.4
map followed by a positive isotropic dilation. -/
theorem pureWZ2Proposition64_combined_tube_carrier_subset_homothety
    {sourceDelta targetDelta halfHeight normalization scale factor : ℝ}
    (hsourceDelta : 0 ≤ sourceDelta)
    (htargetDelta : 0 ≤ targetDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation isotropicCenter : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hscale : 0 < scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (targetTube : Kakeya.DeltaTube targetDelta)
    (haxis :
      pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation ''
              tubeAxisLine sourceTube) =
        tubeAxisLine targetTube)
    (anchor : Point3)
    (hanchorSource : anchor ∈ sourceTube.carrier)
    (hanchorTarget :
      pureWZ2Proposition64IsotropicMap isotropicCenter scale
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation anchor) ∈
        targetTube.carrier)
    (hfactor :
      1 + 2 *
          ((scale * (11 / halfHeight)) * (1 + sourceDelta) +
            targetDelta) ≤ factor)
    (htransverse :
      (scale * (11 / halfHeight)) * sourceDelta ≤
        factor * targetDelta) :
    pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation '' sourceTube.carrier) ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint targetTube) factor ''
        targetTube.carrier := by
  let translated := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight
      (lt_of_lt_of_le zero_lt_one hnormalization)
  let isotropic := pureWZ2Proposition64IsotropicAffineEquiv
    isotropicCenter scale hscale
  let combined := translated.trans isotropic
  have hcombinedApply : ∀ point, combined point =
      pureWZ2Proposition64IsotropicMap isotropicCenter scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation point) := by
    intro point
    simp [combined, translated, isotropic, AffineEquiv.trans_apply]
  have hlipschitzNonneg :
      0 ≤ scale * (11 / halfHeight) := by positivity
  have hlipschitz : ∀ first second,
      dist (combined first) (combined second) ≤
        (scale * (11 / halfHeight)) * dist first second := by
    intro first second
    rw [hcombinedApply, hcombinedApply,
      pureWZ2Proposition64IsotropicMap_dist isotropicCenter hscale]
    have htranslated :
        dist
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation first)
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation second) ≤
          (11 / halfHeight) * dist first second := by
      rw [dist_eq_norm, pureWZ2Proposition64TranslatedMap_sub]
      rw [← dist_eq_norm]
      have hmapIdentity :
          pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
              normalization =
            pureWZ2Proposition64Map (fun _ => g anchorHeight) slabCenter 0
              halfHeight normalization := by
        funext point
        ext coordinate
        fin_cases coordinate <;>
          simp [pureWZ2Proposition64Map, point3]
      rw [hmapIdentity]
      exact pureWZ2Proposition64Map_dist_le hhalfHeight hhalfHeightOne
        hnormalization hanchorSlope slabCenter first second
    calc
      scale * dist
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation first)
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation second) ≤
        scale * ((11 / halfHeight) * dist first second) := by gcongr
      _ = (scale * (11 / halfHeight)) * dist first second := by ring
  have hcombinedAxis : combined '' tubeAxisLine sourceTube =
      tubeAxisLine targetTube := by
    rw [← haxis]
    ext point
    constructor
    · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
      refine ⟨pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint,
        ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
      exact (hcombinedApply sourcePoint).symm
    · rintro ⟨translatedPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
      exact ⟨sourcePoint, hsourcePoint, hcombinedApply sourcePoint⟩
  have hcombinedAnchor : combined anchor ∈ targetTube.carrier := by
    simpa only [hcombinedApply] using hanchorTarget
  have hcarrier := pureWZ2_affine_tube_carrier_subset_homothety
    hsourceDelta htargetDelta sourceTube targetTube combined
    hlipschitzNonneg hlipschitz hcombinedAxis anchor hanchorSource
    hcombinedAnchor hfactor htransverse
  rintro point ⟨translatedPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  exact hcarrier ⟨sourcePoint, hsourcePoint, hcombinedApply sourcePoint⟩

/-- A common post-translation centers an affine image of a complete source
parent on a target parent.  Every source child in the first parent then lies
in an explicit homothety of every target child in the second parent.  No
alignment of the two child axes is required. -/
theorem pureWZ2_affine_parent_packet_subset_child_homothety
    {sourceDelta sourceRho targetDelta targetRho lipschitzFactor factor : ℝ}
    (hsourceRho : 0 ≤ sourceRho)
    (htargetDelta : 0 < targetDelta)
    (htargetRho : 0 ≤ targetRho)
    (sourceChild : Kakeya.DeltaTube sourceDelta)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetChild : Kakeya.DeltaTube targetDelta)
    (targetParent : Kakeya.DeltaTube targetRho)
    (hsourceChild : sourceChild.carrier ⊆ sourceParent.carrier)
    (htargetChild : targetChild.carrier ⊆ targetParent.carrier)
    (equivalence : Point3 ≃ᵃ[ℝ] Point3)
    (hlipschitzFactor : 0 ≤ lipschitzFactor)
    (hlipschitz : ∀ first second,
      dist (equivalence first) (equivalence second) ≤
        lipschitzFactor * dist first second)
    (hfactorOne : 1 ≤ factor)
    (hfactorRadius :
      lipschitzFactor * (sourceRho + 1 / 2) +
          (targetRho + 1 / 2) ≤
        factor * targetDelta) :
    let shift := wz2PaperTubeMidpoint targetParent -
      equivalence (wz2PaperTubeMidpoint sourceParent)
    (fun point => equivalence point + shift) '' sourceChild.carrier ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint targetChild) factor ''
        targetChild.carrier := by
  dsimp only
  let sourceMidpoint := wz2PaperTubeMidpoint sourceParent
  let targetMidpoint := wz2PaperTubeMidpoint targetParent
  let childMidpoint := wz2PaperTubeMidpoint targetChild
  let shift := targetMidpoint - equivalence sourceMidpoint
  let shifted : Point3 → Point3 := fun point => equivalence point + shift
  have hfactorPos : 0 < factor := zero_lt_one.trans_le hfactorOne
  intro imagePoint himagePoint
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsourcePointParent : sourcePoint ∈ sourceParent.carrier :=
    hsourceChild hsourcePoint
  have hsourceRadius : dist sourcePoint sourceMidpoint ≤ sourceRho + 1 / 2 := by
    exact pureWZ2_tube_carrier_subset_midpoint_ball hsourceRho sourceParent
      hsourcePointParent
  have hshiftedCenter : shifted sourceMidpoint = targetMidpoint := by
    dsimp only [shifted, shift]
    abel
  have hshiftedRadius :
      dist (shifted sourcePoint) targetMidpoint ≤
        lipschitzFactor * (sourceRho + 1 / 2) := by
    rw [← hshiftedCenter]
    have htranslationDistance :
        dist (shifted sourcePoint) (shifted sourceMidpoint) =
          dist (equivalence sourcePoint) (equivalence sourceMidpoint) := by
      dsimp only [shifted]
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [htranslationDistance]
    exact (hlipschitz sourcePoint sourceMidpoint).trans <| by gcongr
  have hchildMidpointChild : childMidpoint ∈ targetChild.carrier :=
    wz2_paper_tubeMidpoint_mem_carrier targetChild htargetDelta.le
  have hchildMidpointParent : childMidpoint ∈ targetParent.carrier :=
    htargetChild hchildMidpointChild
  have hchildRadius :
      dist childMidpoint targetMidpoint ≤ targetRho + 1 / 2 := by
    exact pureWZ2_tube_carrier_subset_midpoint_ball htargetRho targetParent
      hchildMidpointParent
  have himageRadius :
      dist (shifted sourcePoint) childMidpoint ≤
        lipschitzFactor * (sourceRho + 1 / 2) +
          (targetRho + 1 / 2) := by
    calc
      dist (shifted sourcePoint) childMidpoint ≤
          dist (shifted sourcePoint) targetMidpoint +
            dist targetMidpoint childMidpoint :=
        dist_triangle _ _ _
      _ ≤ lipschitzFactor * (sourceRho + 1 / 2) +
          (targetRho + 1 / 2) := by
        gcongr
        simpa [dist_comm] using hchildRadius
  let contractedPoint :=
    AffineMap.homothety childMidpoint factor⁻¹ (shifted sourcePoint)
  have hcontractedDistance :
      dist contractedPoint childMidpoint ≤ targetDelta := by
    have hdistance :
        dist contractedPoint childMidpoint =
          factor⁻¹ * dist (shifted sourcePoint) childMidpoint := by
      simpa [contractedPoint, AffineMap.homothety_apply] using
        (homothety_dist (m := childMidpoint)
          (inv_pos.mpr hfactorPos) (shifted sourcePoint) childMidpoint)
    rw [hdistance]
    calc
      factor⁻¹ * dist (shifted sourcePoint) childMidpoint ≤
          factor⁻¹ *
            (lipschitzFactor * (sourceRho + 1 / 2) +
              (targetRho + 1 / 2)) := by gcongr
      _ ≤ factor⁻¹ * (factor * targetDelta) := by gcongr
      _ = targetDelta := by field_simp [hfactorPos.ne']
  have hchildMidpointSegment : childMidpoint ∈
      Kakeya.unitSegment targetChild.base targetChild.direction := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    rfl
  have hcontractedCarrier : contractedPoint ∈ targetChild.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint childMidpoint
      targetDelta (Kakeya.unitSegment targetChild.base targetChild.direction)
      hchildMidpointSegment hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  dsimp only [contractedPoint, shifted, shift, sourceMidpoint,
    targetMidpoint, childMidpoint]
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hfactorPos.ne']
  ring

/-- The combined Proposition-6.4 image of a cropped full-line carrier lies in
an explicit homothety of its centered target ordinary carrier. -/
theorem pureWZ2Proposition64_combined_paperCarrier_subset_homothety
    {sourceDelta targetDelta halfHeight normalization scale factor : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation isotropicCenter : Point3)
    (htranslationHeight : translation 2 = 0)
    (hslabCenter : |slabCenter| ≤ 1)
    (hisotropicCenter : |isotropicCenter 2| ≤ 1)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hscale : 0 < scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (targetTube : Kakeya.DeltaTube targetDelta)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    (htargetLine : WZ1PaperTubeInLineClass targetTube)
    (htargetCentered :
      wz2PaperTubeMidpoint targetTube = wz1TubeAxisZeroPoint targetTube)
    (haxis : tubeAxisLine targetTube =
      pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation '' tubeAxisLine sourceTube))
    (hfactorOne : 1 ≤ factor)
    (hfactorAxial : 12 * scale / halfHeight ≤ factor)
    (hfactorTransverse :
      180 * scale * sourceDelta ≤ factor * targetDelta) :
    pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation ''
            wz1PaperTubeCarrier sourceTube) ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint targetTube) factor ''
        targetTube.carrier := by
  have hfactorPos : 0 < factor := zero_lt_one.trans_le hfactorOne
  rintro imagePoint ⟨translatedPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  let sourceAxisPoint :=
    wz1PaperAxisPointAtHeight sourceTube (sourcePoint 2)
  let translatedAxisPoint :=
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation sourceAxisPoint
  let targetAxisPoint :=
    pureWZ2Proposition64IsotropicMap isotropicCenter scale translatedAxisPoint
  have hsourceAxis : sourceAxisPoint ∈ tubeAxisLine sourceTube :=
    wz1PaperAxisPointAtHeight_mem_axis sourceTube (sourcePoint 2)
  have htargetAxis : targetAxisPoint ∈ tubeAxisLine targetTube := by
    rw [haxis]
    exact ⟨translatedAxisPoint,
      ⟨sourceAxisPoint, hsourceAxis, rfl⟩, rfl⟩
  have htransverse :
      dist
          (pureWZ2Proposition64IsotropicMap isotropicCenter scale
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation sourcePoint))
          targetAxisPoint ≤
        180 * scale * sourceDelta := by
    rw [pureWZ2Proposition64IsotropicMap_dist isotropicCenter hscale]
    have hraw := pureWZ2Proposition64TranslatedMap_sameHeightAxis_dist_le
      hsourceDelta g slabCenter anchorHeight halfHeight normalization
      translation hnormalization hanchorSlope sourceTube hsourceLine
      hsourcePoint
    dsimp only [targetAxisPoint, translatedAxisPoint, sourceAxisPoint]
    calc
      scale * dist
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation sourcePoint)
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation
              (wz1PaperAxisPointAtHeight sourceTube (sourcePoint 2))) ≤
          scale * (180 * sourceDelta) := by gcongr
      _ = 180 * scale * sourceDelta := by ring
  have hsourceHeight : |sourcePoint 2| ≤ 1 := by
    simpa [wz1PaperTubeCarrier, Kakeya.Streamlined.axisBox] using
      hsourcePoint.2.2.2
  have htranslatedHeight :
      translatedAxisPoint 2 =
        (sourcePoint 2 - slabCenter) / halfHeight := by
    dsimp only [translatedAxisPoint]
    rw [pureWZ2Proposition64TranslatedMap_apply_two,
      wz1PaperAxisPointAtHeight_coord_two hsourceLine,
      htranslationHeight, add_zero]
  have htargetHeight :
      targetAxisPoint 2 =
        scale *
          ((sourcePoint 2 - slabCenter) / halfHeight -
            isotropicCenter 2) := by
    dsimp only [targetAxisPoint]
    simp only [pureWZ2Proposition64IsotropicMap, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul, htranslatedHeight]
  have htargetHeightAbs : |targetAxisPoint 2| ≤ 3 * scale / halfHeight := by
    have hheightDiff : |sourcePoint 2 - slabCenter| ≤ 2 := by
      exact (abs_sub _ _).trans (by linarith)
    rw [htargetHeight, abs_mul, abs_of_pos hscale]
    have hinner :
        |(sourcePoint 2 - slabCenter) / halfHeight - isotropicCenter 2| ≤
          3 / halfHeight := by
      calc
        _ ≤ |(sourcePoint 2 - slabCenter) / halfHeight| +
            |isotropicCenter 2| := abs_sub _ _
        _ ≤ 2 / halfHeight + 1 := by
          rw [abs_div, abs_of_pos hhalfHeight]
          gcongr
        _ ≤ 3 / halfHeight := by
          apply (le_div_iff₀ hhalfHeight).2
          rw [add_mul, div_mul_cancel₀ _ hhalfHeight.ne']
          nlinarith
    calc
      scale *
          |(sourcePoint 2 - slabCenter) / halfHeight -
            isotropicCenter 2| ≤ scale * (3 / halfHeight) := by gcongr
      _ = 3 * scale / halfHeight := by ring
  rcases wz1Paper_axis_exists_parameter htargetLine htargetAxis with
    ⟨axisParameter, haxisParameter⟩
  have htargetZeroTwo : wz1TubeAxisZeroPoint targetTube 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two targetTube htargetLine.vertical
  have hpaperVertical : 1 / 2 ≤ wz1PaperDirection targetTube 2 :=
    htargetLine.1
  have hpaperVerticalPos : 0 < wz1PaperDirection targetTube 2 := by linarith
  have hparameterIdentity :
      targetAxisPoint 2 =
        axisParameter * wz1PaperDirection targetTube 2 := by
    have hcoordinate := congrArg (fun point : Point3 => point 2) haxisParameter
    simpa [htargetZeroTwo, smul_eq_mul] using hcoordinate
  have hparameterAbs : |axisParameter| ≤ 6 * scale / halfHeight := by
    have hmul :
        |axisParameter| * wz1PaperDirection targetTube 2 ≤
          3 * scale / halfHeight := by
      rw [← abs_of_pos hpaperVerticalPos, ← abs_mul,
        ← hparameterIdentity]
      exact htargetHeightAbs
    apply (le_div_iff₀ hhalfHeight).2
    have hscaled :
        |axisParameter| * halfHeight *
            wz1PaperDirection targetTube 2 ≤ 3 * scale := by
      calc
        _ = halfHeight *
            (|axisParameter| * wz1PaperDirection targetTube 2) := by ring
        _ ≤ halfHeight * (3 * scale / halfHeight) := by gcongr
        _ = 3 * scale := by field_simp [hhalfHeight.ne']
    nlinarith
  let contractedAxisParameter := axisParameter / factor
  have hcontractedAxisParameter : |contractedAxisParameter| ≤ 1 / 2 := by
    dsimp only [contractedAxisParameter]
    rw [abs_div, abs_of_pos hfactorPos]
    apply (div_le_iff₀ hfactorPos).2
    calc
      |axisParameter| ≤ 6 * scale / halfHeight := hparameterAbs
      _ = (12 * scale / halfHeight) / 2 := by ring
      _ ≤ factor / 2 := by gcongr
      _ = (1 / 2) * factor := by ring
  let contractedAxisPoint :=
    wz2PaperTubeMidpoint targetTube +
      contractedAxisParameter • wz1PaperDirection targetTube
  have hcontractedAxis : contractedAxisPoint ∈
      Kakeya.unitSegment targetTube.base targetTube.direction := by
    dsimp only [contractedAxisPoint]
    unfold wz1PaperDirection
    split_ifs with horientation
    · refine ⟨1 / 2 + contractedAxisParameter, ?_, ?_⟩
      · rw [abs_le] at hcontractedAxisParameter
        constructor <;> linarith
      · dsimp only [wz2PaperTubeMidpoint]
        change targetTube.base +
            (1 / 2 + contractedAxisParameter) • targetTube.direction =
          targetTube.base + (1 / 2 : ℝ) • targetTube.direction +
            contractedAxisParameter • targetTube.direction
        module
    · refine ⟨1 / 2 - contractedAxisParameter, ?_, ?_⟩
      · rw [abs_le] at hcontractedAxisParameter
        constructor <;> linarith
      · dsimp only [wz2PaperTubeMidpoint]
        change targetTube.base +
            (1 / 2 - contractedAxisParameter) • targetTube.direction =
          targetTube.base + (1 / 2 : ℝ) • targetTube.direction +
            contractedAxisParameter • (-targetTube.direction)
        module
  let targetMidpoint := wz2PaperTubeMidpoint targetTube
  let contractedPoint :=
    AffineMap.homothety targetMidpoint factor⁻¹
      (pureWZ2Proposition64IsotropicMap isotropicCenter scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint))
  have hcontractedAxisIdentity : contractedAxisPoint =
      AffineMap.homothety targetMidpoint factor⁻¹ targetAxisPoint := by
    dsimp only [contractedAxisPoint, contractedAxisParameter, targetMidpoint]
    rw [haxisParameter, ← htargetCentered]
    rw [AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    apply PiLp.ext
    intro coordinate
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hfactorPos.ne']
    ring
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ targetDelta := by
    rw [hcontractedAxisIdentity]
    have hscaled := homothety_dist (m := targetMidpoint)
      (inv_pos.mpr hfactorPos)
      (pureWZ2Proposition64IsotropicMap isotropicCenter scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint))
      targetAxisPoint
    dsimp only [contractedPoint]
    rw [hscaled]
    calc
      factor⁻¹ * dist
          (pureWZ2Proposition64IsotropicMap isotropicCenter scale
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation sourcePoint))
          targetAxisPoint ≤ factor⁻¹ * (180 * scale * sourceDelta) := by
        gcongr
      _ ≤ factor⁻¹ * (factor * targetDelta) := by gcongr
      _ = targetDelta := by field_simp [hfactorPos.ne']
  have hcontractedCarrier : contractedPoint ∈ targetTube.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      targetDelta (Kakeya.unitSegment targetTube.base targetTube.direction)
      hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  dsimp only [contractedPoint, targetMidpoint]
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hfactorPos.ne']
  ring

/-- The exact Proposition-6.4 image of a genuine ordinary source tube lies in
a homothety of its exact centered target child.  Axial length is paid by the
true affine factor `scale / halfHeight`; no source-parent or target-parent
half-length enters the estimate. -/
theorem pureWZ2Proposition64_combined_ordinaryCarrier_subset_homothety
    {sourceDelta targetDelta halfHeight normalization scale factor : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceDeltaOne : sourceDelta ≤ 1)
    (htargetDelta : 0 < targetDelta)
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation isotropicCenter : Point3)
    (htranslationHeight : translation 2 = 0)
    (hslabCenter : |slabCenter| ≤ 1)
    (hisotropicCenter : |isotropicCenter 2| ≤ 1)
    (hhalfHeight : 0 < halfHeight)
    (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 1 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hscale : 0 < scale)
    (sourceTube : Kakeya.DeltaTube sourceDelta)
    (targetTube : Kakeya.DeltaTube targetDelta)
    (hsourceBase : ‖sourceTube.base‖ ≤ 4)
    (hsourceLine : WZ1PaperTubeInLineClass sourceTube)
    (htargetLine : WZ1PaperTubeInLineClass targetTube)
    (htargetCentered :
      wz2PaperTubeMidpoint targetTube = wz1TubeAxisZeroPoint targetTube)
    (haxis : tubeAxisLine targetTube =
      pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation '' tubeAxisLine sourceTube))
    (hfactorOne : 1 ≤ factor)
    (hfactorAxial : 40 * scale / halfHeight ≤ factor)
    (hfactorTransverse :
      20 * scale * sourceDelta ≤ factor * targetDelta) :
    pureWZ2Proposition64IsotropicMap isotropicCenter scale ''
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation '' sourceTube.carrier) ⊆
      AffineMap.homothety (wz2PaperTubeMidpoint targetTube) factor ''
        targetTube.carrier := by
  have hfactorPos : 0 < factor := zero_lt_one.trans_le hfactorOne
  rintro imagePoint ⟨translatedPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  let sourceAxisPoint :=
    wz1PaperAxisPointAtHeight sourceTube (sourcePoint 2)
  let translatedAxisPoint :=
    pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation sourceAxisPoint
  let targetAxisPoint :=
    pureWZ2Proposition64IsotropicMap isotropicCenter scale translatedAxisPoint
  have hsourceAxis : sourceAxisPoint ∈ tubeAxisLine sourceTube :=
    wz1PaperAxisPointAtHeight_mem_axis sourceTube (sourcePoint 2)
  have htargetAxis : targetAxisPoint ∈ tubeAxisLine targetTube := by
    rw [haxis]
    exact ⟨translatedAxisPoint,
      ⟨sourceAxisPoint, hsourceAxis, rfl⟩, rfl⟩
  have htransverse :
      dist
          (pureWZ2Proposition64IsotropicMap isotropicCenter scale
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation sourcePoint))
          targetAxisPoint ≤
        20 * scale * sourceDelta := by
    rw [pureWZ2Proposition64IsotropicMap_dist isotropicCenter hscale]
    have hraw :=
      pureWZ2Proposition64TranslatedMap_ordinary_sameHeightAxis_dist_le
        hsourceDelta g slabCenter anchorHeight halfHeight normalization
        translation hnormalization hanchorSlope sourceTube hsourceLine
        hsourcePoint
    dsimp only [targetAxisPoint, translatedAxisPoint, sourceAxisPoint]
    calc
      scale * dist
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation sourcePoint)
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation
              (wz1PaperAxisPointAtHeight sourceTube (sourcePoint 2))) ≤
          scale * (20 * sourceDelta) := by gcongr
      _ = 20 * scale * sourceDelta := by ring
  have hsourceRadius :
      dist sourcePoint (wz2PaperTubeMidpoint sourceTube) ≤
        sourceDelta + 1 / 2 :=
    pureWZ2_tube_carrier_subset_midpoint_ball hsourceDelta.le sourceTube
      hsourcePoint
  have hmidpointNorm :
      ‖wz2PaperTubeMidpoint sourceTube‖ ≤ 4 + 1 / 2 := by
    unfold wz2PaperTubeMidpoint
    calc
      ‖sourceTube.base + (1 / 2 : ℝ) • sourceTube.direction‖ ≤
          ‖sourceTube.base‖ +
            ‖(1 / 2 : ℝ) • sourceTube.direction‖ :=
        norm_add_le _ _
      _ = ‖sourceTube.base‖ + 1 / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
          sourceTube.direction_unit, mul_one]
      _ ≤ 4 + 1 / 2 := by gcongr
  have hsourceNorm : ‖sourcePoint‖ ≤ 6 := by
    calc
      ‖sourcePoint‖ =
          ‖(sourcePoint - wz2PaperTubeMidpoint sourceTube) +
            wz2PaperTubeMidpoint sourceTube‖ := by
              congr 1
              abel
      _ ≤ ‖sourcePoint - wz2PaperTubeMidpoint sourceTube‖ +
          ‖wz2PaperTubeMidpoint sourceTube‖ := norm_add_le _ _
      _ = dist sourcePoint (wz2PaperTubeMidpoint sourceTube) +
          ‖wz2PaperTubeMidpoint sourceTube‖ := by rw [dist_eq_norm]
      _ ≤ (sourceDelta + 1 / 2) + (4 + 1 / 2) := by gcongr
      _ ≤ 6 := by linarith
  have hsourceHeight : |sourcePoint 2| ≤ 6 := by
    have hcoordinate : |sourcePoint 2| ≤ ‖sourcePoint‖ := by
      simpa [Real.norm_eq_abs] using
        PiLp.norm_apply_le sourcePoint (2 : Fin 3)
    exact hcoordinate.trans hsourceNorm
  have htranslatedHeight :
      translatedAxisPoint 2 =
        (sourcePoint 2 - slabCenter) / halfHeight := by
    dsimp only [translatedAxisPoint]
    rw [pureWZ2Proposition64TranslatedMap_apply_two,
      wz1PaperAxisPointAtHeight_coord_two hsourceLine,
      htranslationHeight, add_zero]
  have htargetHeight :
      targetAxisPoint 2 =
        scale *
          ((sourcePoint 2 - slabCenter) / halfHeight -
            isotropicCenter 2) := by
    dsimp only [targetAxisPoint]
    simp only [pureWZ2Proposition64IsotropicMap, PiLp.smul_apply,
      PiLp.sub_apply, smul_eq_mul, htranslatedHeight]
  have htargetHeightAbs : |targetAxisPoint 2| ≤ 8 * scale / halfHeight := by
    have hheightDiff : |sourcePoint 2 - slabCenter| ≤ 7 := by
      exact (abs_sub _ _).trans (by linarith)
    rw [htargetHeight, abs_mul, abs_of_pos hscale]
    have hinner :
        |(sourcePoint 2 - slabCenter) / halfHeight - isotropicCenter 2| ≤
          8 / halfHeight := by
      calc
        _ ≤ |(sourcePoint 2 - slabCenter) / halfHeight| +
            |isotropicCenter 2| := abs_sub _ _
        _ ≤ 7 / halfHeight + 1 := by
          rw [abs_div, abs_of_pos hhalfHeight]
          gcongr
        _ ≤ 8 / halfHeight := by
          apply (le_div_iff₀ hhalfHeight).2
          rw [add_mul, div_mul_cancel₀ _ hhalfHeight.ne']
          linarith
    calc
      scale *
          |(sourcePoint 2 - slabCenter) / halfHeight -
            isotropicCenter 2| ≤ scale * (8 / halfHeight) := by gcongr
      _ = 8 * scale / halfHeight := by ring
  rcases wz1Paper_axis_exists_parameter htargetLine htargetAxis with
    ⟨axisParameter, haxisParameter⟩
  have htargetZeroTwo : wz1TubeAxisZeroPoint targetTube 2 = 0 :=
    wz1TubeAxisZeroPoint_coord_two targetTube htargetLine.vertical
  have hpaperVertical : 1 / 2 ≤ wz1PaperDirection targetTube 2 :=
    htargetLine.1
  have hpaperVerticalPos : 0 < wz1PaperDirection targetTube 2 := by linarith
  have hparameterIdentity :
      targetAxisPoint 2 =
        axisParameter * wz1PaperDirection targetTube 2 := by
    have hcoordinate := congrArg (fun point : Point3 => point 2) haxisParameter
    simpa [htargetZeroTwo, smul_eq_mul] using hcoordinate
  have hparameterAbs : |axisParameter| ≤ 16 * scale / halfHeight := by
    have hmul :
        |axisParameter| * wz1PaperDirection targetTube 2 ≤
          8 * scale / halfHeight := by
      rw [← abs_of_pos hpaperVerticalPos, ← abs_mul,
        ← hparameterIdentity]
      exact htargetHeightAbs
    apply (le_div_iff₀ hhalfHeight).2
    have hscaled :
        |axisParameter| * halfHeight *
            wz1PaperDirection targetTube 2 ≤ 8 * scale := by
      calc
        _ = halfHeight *
            (|axisParameter| * wz1PaperDirection targetTube 2) := by ring
        _ ≤ halfHeight * (8 * scale / halfHeight) := by gcongr
        _ = 8 * scale := by field_simp [hhalfHeight.ne']
    nlinarith
  let contractedAxisParameter := axisParameter / factor
  have hcontractedAxisParameter : |contractedAxisParameter| ≤ 1 / 2 := by
    dsimp only [contractedAxisParameter]
    rw [abs_div, abs_of_pos hfactorPos]
    apply (div_le_iff₀ hfactorPos).2
    calc
      |axisParameter| ≤ 16 * scale / halfHeight := hparameterAbs
      _ ≤ (40 * scale / halfHeight) / 2 := by
        have hratio : 0 < scale / halfHeight := div_pos hscale hhalfHeight
        rw [show 16 * scale / halfHeight = 16 * (scale / halfHeight) by ring,
          show (40 * scale / halfHeight) / 2 =
            20 * (scale / halfHeight) by ring]
        nlinarith
      _ ≤ factor / 2 := by gcongr
      _ = (1 / 2) * factor := by ring
  let contractedAxisPoint :=
    wz2PaperTubeMidpoint targetTube +
      contractedAxisParameter • wz1PaperDirection targetTube
  have hcontractedAxis : contractedAxisPoint ∈
      Kakeya.unitSegment targetTube.base targetTube.direction := by
    dsimp only [contractedAxisPoint]
    unfold wz1PaperDirection
    split_ifs with horientation
    · refine ⟨1 / 2 + contractedAxisParameter, ?_, ?_⟩
      · rw [abs_le] at hcontractedAxisParameter
        constructor <;> linarith
      · dsimp only [wz2PaperTubeMidpoint]
        change targetTube.base +
            (1 / 2 + contractedAxisParameter) • targetTube.direction =
          targetTube.base + (1 / 2 : ℝ) • targetTube.direction +
            contractedAxisParameter • targetTube.direction
        module
    · refine ⟨1 / 2 - contractedAxisParameter, ?_, ?_⟩
      · rw [abs_le] at hcontractedAxisParameter
        constructor <;> linarith
      · dsimp only [wz2PaperTubeMidpoint]
        change targetTube.base +
            (1 / 2 - contractedAxisParameter) • targetTube.direction =
          targetTube.base + (1 / 2 : ℝ) • targetTube.direction +
            contractedAxisParameter • (-targetTube.direction)
        module
  let targetMidpoint := wz2PaperTubeMidpoint targetTube
  let contractedPoint :=
    AffineMap.homothety targetMidpoint factor⁻¹
      (pureWZ2Proposition64IsotropicMap isotropicCenter scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint))
  have hcontractedAxisIdentity : contractedAxisPoint =
      AffineMap.homothety targetMidpoint factor⁻¹ targetAxisPoint := by
    dsimp only [contractedAxisPoint, contractedAxisParameter, targetMidpoint]
    rw [haxisParameter, ← htargetCentered]
    rw [AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    apply PiLp.ext
    intro coordinate
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [hfactorPos.ne']
    ring
  have hcontractedDistance :
      dist contractedPoint contractedAxisPoint ≤ targetDelta := by
    rw [hcontractedAxisIdentity]
    have hscaled := homothety_dist (m := targetMidpoint)
      (inv_pos.mpr hfactorPos)
      (pureWZ2Proposition64IsotropicMap isotropicCenter scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation sourcePoint))
      targetAxisPoint
    dsimp only [contractedPoint]
    rw [hscaled]
    calc
      factor⁻¹ * dist
          (pureWZ2Proposition64IsotropicMap isotropicCenter scale
            (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
              halfHeight normalization translation sourcePoint))
          targetAxisPoint ≤ factor⁻¹ * (20 * scale * sourceDelta) := by
        gcongr
      _ ≤ factor⁻¹ * (factor * targetDelta) := by gcongr
      _ = targetDelta := by field_simp [hfactorPos.ne']
  have hcontractedCarrier : contractedPoint ∈ targetTube.carrier :=
    Metric.mem_cthickening_of_dist_le contractedPoint contractedAxisPoint
      targetDelta (Kakeya.unitSegment targetTube.base targetTube.direction)
      hcontractedAxis hcontractedDistance
  refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
  dsimp only [contractedPoint, targetMidpoint]
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  field_simp [hfactorPos.ne']
  ring

end Kakeya.Assouad

end
