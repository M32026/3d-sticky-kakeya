import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.VerticalFinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64FinalProvenance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64FinalSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64FullSlabAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureNearbyTopLevel

/-!
# Final Proposition 6.4 vertical assembly

This module packages the closed geometric part of the final mild rescaling.
The remaining nearby CWA, density, and union-volume upper bound stay explicit:
they are quantitative Lemma-3.5 cleanup data and are not inferred from
containment alone.  Nonemptiness is supplied by the same selected ED witness.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Increasing only the AD constant preserves a local-grain package on the
same shading. -/
noncomputable def PureWZ2LocalGrainData.mono_constant
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C C' : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C)
    (hconstant : C ≤ C') (hC'top : C' ≠ ⊤) :
    PureWZ2LocalGrainData shading sigma C' where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := data.planeMap_incidence
  local_ad rho hdeltaRho hrhoOne point :=
    (data.local_ad rho hdeltaRho hrhoOne point).mono_constant
      hconstant hC'top

/-- Assemble cropped extremality from the quantitative conclusions of the
Lemma-3.5 cleanup.  The lower volume bound is also the non-vacuity witness:
it rules out an empty final indexed family. -/
theorem pureWZ2Proposition64_croppedExtremal_of_quantitative
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hnearby : WZ2PaperPureCWAAtNearbyScales family
      (Kakeya.realRpowENN delta (-loss)))
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdense : shading.IsLambdaDense
      (Kakeya.realRpowENN delta loss))
    (hupper : MeasureTheory.volume shading.union ≤
      Kakeya.realRpowENN delta (sigma - loss))
    (hfamily : family.Nonempty) :
    WZ2PaperCroppedIsExtremal sigma loss family shading := by
  exact {
    delta_pos := hdelta
    delta_le_one := hdeltaOne
    nonempty := hfamily
    cwa_nearby_scales := hnearby
    cubical := hcubical
    dense := hdense
    volume_upper := hupper }

/-- The ordinary-carrier top-level bound supplied by pure nearby-CWA, after
the fixed factor four is absorbed into the final loss budget. -/
theorem pureWZ2Proposition64_topLevelOrdinary_of_extremal
    {delta sigma structuralLoss outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma structuralLoss family shading)
    (habsorb : 4 * Kakeya.realRpowENN delta (-structuralLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss)) :
    WZ2PaperBodyConvexWolffBound family.toBodyFamily
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  have hraw := pureWZ2Proposition64_pureNearby_topLevelOrdinary
    extremal.delta_le_one extremal.cwa_nearby_scales
  intro convexSet hconvex
  exact (hraw convexSet hconvex).trans (by gcongr)

/-- The isotropic image of the popular exact restriction is contained in the
isotropic image of the full translated source shading. -/
theorem pureWZ2Proposition64_popularIsotropicImage_subset
    {sourceDelta imageDelta finalDelta sigma rawLoss extensionConstant
      slabCenter anchorHeight halfHeight normalization width scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    {raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma C rawLoss extensionConstant}
    {translation : Point3}
    {normalized : PureWZ2Proposition64NormalizedData
      raw slabCenter anchorHeight halfHeight normalization}
    {image : PureWZ2Proposition64ActualImageRediscretizationData
      (targetDelta := imageDelta) raw.slope slabCenter anchorHeight
        halfHeight normalization translation normalized.halfHeight_pos
        normalized.normalization_pos sourceFamily sourceShading}
    {exactShading : WZ1PaperTubeShading image.family}
    (hexactCarrier : ∀ target, exactShading.carrier target ⊆
      pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
        halfHeight normalization translation ''
          sourceShading.carrier (image.sourceParent target))
    {rawNormal : {point : Point3 // point ∈ exactShading.union} → Point3}
    {targetK : NNReal}
    {himageDelta : 0 < imageDelta} {hfinalDelta : 0 < finalDelta}
    {hfinalDeltaSmall : finalDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hradius : scale * (6 * imageDelta) +
      2 * finalDelta ≤ 6 * finalDelta}
    (cleanup : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale) exactShading rawNormal targetK
        himageDelta hfinalDelta hfinalDeltaSmall hscale hradius) :
    pureWZ2Proposition64IsotropicMap cleanup.popular.center scale ''
        cleanup.popular.restricted.union ⊆
      pureWZ2Proposition64IsotropicMap cleanup.popular.center scale ''
        (pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
          halfHeight normalization translation '' sourceShading.union) := by
  rintro point ⟨exactPoint, hexactPoint, rfl⟩
  rcases hexactPoint with ⟨index, hpoint⟩
  have hexact : exactPoint ∈ exactShading.carrier index :=
    cleanup.popular.restricted_subshading index hpoint
  rcases hexactCarrier index hexact with
    ⟨sourcePoint, hsourcePoint, hexactEq⟩
  refine ⟨pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
      halfHeight normalization translation sourcePoint, ?_, ?_⟩
  · exact ⟨sourcePoint, ⟨image.sourceParent index, hsourcePoint⟩, rfl⟩
  · exact congrArg
      (pureWZ2Proposition64IsotropicMap cleanup.popular.center scale)
      hexactEq

/-- Assemble all closed geometric outputs of the Proposition 6.4 mild
rescaling.  Only the genuinely quantitative final cleanup certificates are
supplied by the caller. -/
theorem pureWZ2Proposition64_assembleVerticalRediscretization
    {sourceDelta imageDelta finalDelta sigma rawLoss extensionConstant
      slabCenter anchorHeight halfHeight normalization width scale
      nearbyLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {localConstant slabConstant : ENNReal}
    {raw : PureWZ2RawC2GlobalGrainData
      sourceShading sigma localConstant rawLoss extensionConstant}
    {translation : Point3}
    {normalized : PureWZ2Proposition64NormalizedData
      raw slabCenter anchorHeight halfHeight normalization}
    {image : PureWZ2Proposition64ActualImageRediscretizationData
      (targetDelta := imageDelta) raw.slope slabCenter anchorHeight
        halfHeight normalization translation normalized.halfHeight_pos
        normalized.normalization_pos sourceFamily sourceShading}
    {exactShading : WZ1PaperTubeShading image.family}
    (hexactCarrier : ∀ target, exactShading.carrier target ⊆
      pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
        halfHeight normalization translation ''
          sourceShading.carrier (image.sourceParent target))
    {rawNormal : {point : Point3 // point ∈ exactShading.union} → Point3}
    {targetK : NNReal}
    {himageDelta : 0 < imageDelta} {hfinalDelta : 0 < finalDelta}
    {hfinalDeltaSmall : finalDelta ≤ 1 / 4}
    {hscale : 1 ≤ scale}
    {hradius : scale * (6 * imageDelta) +
      2 * finalDelta ≤ 6 * finalDelta}
    {cleanup : PureWZ2Proposition64Lemma35LocalCleanupData
      (width := width) (scale := scale) exactShading rawNormal targetK
        himageDelta hfinalDelta hfinalDeltaSmall hscale hradius}
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData cleanup.finalShading K)
    (provenance : PureWZ2Proposition64FinalProvenanceData
      (normalized := normalized) (image := image)
      (exactCarrier_provenance := hexactCarrier) (cleanup := cleanup) ed)
    (globalBounds : PureWZ2RawC2GlobalBoundData raw)
    (hvalueBudget :
      3 * halfHeight * extensionConstant *
        Real.rpow sourceDelta (-rawLoss) ≤ normalization)
    (hfirstBudget :
      halfHeight * extensionConstant * Real.rpow sourceDelta (-rawLoss) ≤
        normalization)
    (hsecondBudget :
      halfHeight ^ 2 * extensionConstant * Real.rpow sourceDelta (-rawLoss) ≤
        normalization)
    (hsourceSlab : ∀ point ∈ sourceShading.union,
      point 2 ∈ Set.Icc
        (slabCenter - halfHeight) (slabCenter + halfHeight))
    (hsourceSlabAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection raw.slope
          (globalGrainSlab sourceShading.union z sourceDelta))
        sourceDelta (1 - sigma) slabConstant)
    (htranslationOne : |translation 1| ≤ 2)
    (hfinalLine : WZ1PaperIsLineClass ed.subfamily.family)
    (hfinalDeltaOne : finalDelta ≤ 1)
    (hfinalDeltaPaper : finalDelta ≤ 1 / 96)
    (hfinalNearby : WZ2PaperPureCWAAtNearbyScales ed.subfamily.family
      (Kakeya.realRpowENN finalDelta (-nearbyLoss)))
    (hnearbyLoss : nearbyLoss ≤ outputLoss)
    (hfinalCWAAbsorb :
      4 * Kakeya.realRpowENN finalDelta (-nearbyLoss) ≤
        Kakeya.realRpowENN finalDelta (-outputLoss))
    (hfinalDense : ed.finalShading.IsLambdaDense
      (Kakeya.realRpowENN finalDelta outputLoss))
    (hvolumeUpper : MeasureTheory.volume ed.finalShading.union ≤
      Kakeya.realRpowENN finalDelta (sigma - outputLoss))
    (hfinalNonempty : ed.subfamily.family.Nonempty)
    (cleanupLocal : PureWZ2LocalGrainData cleanup.finalShading sigma
      (192 * localConstant))
    (hvertical : ∀ point, |cleanupLocal.planeMap point 2| ≤ 1 / 2)
    (hheightBudget : halfHeight * (2 * finalDelta / scale) ≤ sourceDelta)
    (hanalyticScale : scale * (sourceDelta / normalization) ≤ finalDelta)
    (hlocalConstant : 192 * localConstant ≤
      Kakeya.realRpowENN finalDelta (-outputLoss))
    (hglobalConstant : 7077888 * slabConstant ≤
      Kakeya.realRpowENN finalDelta (-outputLoss)) :
    Nonempty (PureWZ2VerticalRediscretizationData
      normalized finalDelta outputLoss) := by
  let finalSlope := pureWZ2Proposition64FinalSlope
    normalized.slope cleanup.popular.center scale
  let f := pureWZ2Proposition64FinalIntervalSlope
    normalized.slope cleanup.popular.center scale
  have hfinalSlopeNormalized : finalSlope.IsNormalized :=
    pureWZ2Proposition64FinalSlope_normalized_of_raw raw globalBounds normalized
      cleanup.popular.center hscale (cleanup.popular.center_mem 2)
      hvalueBudget hfirstBudget hsecondBudget
  have hfinalSlopeImage : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      horizontalSlice
        (pureWZ2Proposition64IsotropicMap cleanup.popular.center scale ''
          (pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
            halfHeight normalization translation '' sourceShading.union)) z ≠ ∅ →
      finalSlope z = normalized.slope
        (cleanup.popular.center 2 + z / scale) := by
    intros
    rfl
  have hfinalExtremal : WZ2PaperCroppedIsExtremal
      sigma outputLoss ed.subfamily.family ed.finalShading :=
    pureWZ2Proposition64_croppedExtremal_of_quantitative
      hfinalDelta hfinalDeltaOne
      (hfinalNearby.mono_loss hfinalDelta hfinalDeltaOne hnearbyLoss)
      (ed.cubical cleanup.cubical) hfinalDense hvolumeUpper hfinalNonempty
  have hfinalCentered : ∀ index,
      wz2PaperTubeMidpoint (ed.subfamily.family.tube index) =
        wz1TubeAxisZeroPoint (ed.subfamily.family.tube index) := by
    intro index
    have hfinalVertical := (hfinalLine index).vertical
    rw [ed.tube_provenance index] at hfinalVertical
    rw [ed.tube_provenance index]
    apply pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
    simpa [pureWZ2Proposition64IsotropicPaperFamily,
      pureWZ2Proposition64IsotropicRebasedPaperTube,
      pureWZ2Proposition64IsotropicPaperTube] using hfinalVertical
  have hfinalCWARaw : WZ2PaperConvexWolffBound ed.subfamily.family
      (4 * Kakeya.realRpowENN finalDelta (-nearbyLoss)) :=
    pureWZ2Proposition64_pureNearby_topLevel hfinalDelta
      (hfinalDeltaPaper.trans (by norm_num)) hfinalLine
      hfinalCentered hfinalNearby
  have hfinalCWA : WZ2PaperConvexWolffBound ed.subfamily.family
      (Kakeya.realRpowENN finalDelta (-outputLoss)) := by
    intro convexSet hconvex
    exact (hfinalCWARaw convexSet hconvex).trans (by gcongr)
  let selectedLocal := ed.restrictLocalGrains cleanupLocal
  let finalLocal := selectedLocal.mono_constant hlocalConstant
    (by simp [Kakeya.realRpowENN])
  have hexactUnion : cleanup.popular.restricted.union ⊆
      pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
        halfHeight normalization translation '' sourceShading.union := by
    rintro point ⟨index, hpoint⟩
    have hexact := cleanup.popular.restricted_subshading index hpoint
    rcases hexactCarrier index hexact with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, ⟨image.sourceParent index, hsourcePoint⟩, rfl⟩
  have hcenterOne : |cleanup.popular.center 1| ≤ 1 := by
    exact cleanup.popular.center_mem 1
  have hcleanupGlobal :=
    pureWZ2Proposition64FullIsotropicPaperShading_globalAD
      normalized hsourceSlabAD translation image.translation_height
        htranslationOne image.family cleanup.popular.restricted hexactUnion
        cleanup.popular.center scale hcenterOne himageDelta hfinalDelta
        hfinalDeltaSmall hscale hradius cleanup.sourceWindow
        hsourceSlab hheightBudget hanalyticScale hfinalSlopeNormalized
  have hfinalGlobalAD : ∀ z : PureWZ2UnitInterval,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (f z))
          (horizontalSlice ed.finalShading.union z.1))
        finalDelta (1 - sigma)
          (Kakeya.realRpowENN finalDelta (-outputLoss)) := by
    intro z
    have hrestricted : PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (f z))
          (horizontalSlice ed.finalShading.union z.1))
        finalDelta (1 - sigma) (7077888 * slabConstant) :=
      (hcleanupGlobal z.1 z.2).mono (by
      apply Set.image_mono
      intro point (hpoint : point ∈
        horizontalSlice ed.finalShading.union z.1)
      exact ⟨ed.union_subset hpoint.1, hpoint.2⟩)
    apply hrestricted.mono_constant hglobalConstant
    simp [Kakeya.realRpowENN]
  refine ⟨{
    translation := translation
    translation_height := image.translation_height
    isotropicCenter := cleanup.popular.center
    isotropicScale := scale
    isotropicScale_pos := lt_of_lt_of_le zero_lt_one hscale
    family := ed.subfamily.family
    shading := ed.finalShading
    sourceParent := provenance.sourceParent
    axis_provenance := provenance.axis_provenance
    shading_near_source_image := provenance.carrier_provenance
    line_class := hfinalLine
    bounded_base := by
      intro index
      let tube := ed.subfamily.family.tube index
      have hbase : tube.base =
          wz2PaperTubeMidpoint tube - (1 / 2 : ℝ) • tube.direction := by
        unfold wz2PaperTubeMidpoint
        module
      rw [hbase]
      have hmidpoint : ‖wz2PaperTubeMidpoint tube‖ ≤ 3 := by
        rw [hfinalCentered index]
        let point := wz1TubeAxisZeroPoint tube
        have hzero : point 2 = 0 :=
          wz1TubeAxisZeroPoint_coord_two tube (hfinalLine index).vertical
        have hnorm : ‖point‖ ^ 2 =
            point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [Fin.sum_univ_succ]
          ring
        have hzeroBounds := abs_le.mp (hfinalLine index).2.1
        have honeBounds := abs_le.mp (hfinalLine index).2.2
        have hzeroSq : point 0 ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by nlinarith
        have honeSq : point 1 ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by nlinarith
        have hnormNonnegative : 0 ≤ ‖point‖ := norm_nonneg _
        nlinarith
      calc
        ‖wz2PaperTubeMidpoint tube - (1 / 2 : ℝ) • tube.direction‖ ≤
            ‖wz2PaperTubeMidpoint tube‖ +
              ‖(1 / 2 : ℝ) • tube.direction‖ := norm_sub_le _ _
        _ = ‖wz2PaperTubeMidpoint tube‖ + 1 / 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
            tube.direction_unit, mul_one]
        _ ≤ 3 + 1 / 2 := by gcongr
        _ ≤ 4 := by norm_num
    extremal := hfinalExtremal
    top_level_cwa := hfinalCWA
    localGrains := finalLocal
    planeMap_vertical_bound := ?_
    f := f
    f_normalized :=
      pureWZ2Proposition64FinalIntervalSlope_normalized_of_raw
        raw globalBounds normalized cleanup.popular.center hscale
        (cleanup.popular.center_mem 2) hvalueBudget hfirstBudget hsecondBudget
    f_eq_on_active := by
      intro z _hslice
      rfl
    final_global_ad := hfinalGlobalAD }⟩
  · intro point
    exact ed.restrictLocalGrains_vertical_bound cleanupLocal hvertical point

end Kakeya.Assouad

end
