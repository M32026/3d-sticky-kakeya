import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PaperEDCleanup

/-!
# Final Proposition 6.4 source provenance

The final paper family is obtained by restricting an exact translated-`Phi`
image to a popular box, applying one isotropic similarity, saturating in the
final grid, deleting zero-mass carriers, and selecting an essentially-
distinct subfamily.  This module composes the corresponding parent maps and
keeps both the axis and carrier provenance all the way back to the original
source family.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

structure PureWZ2Proposition64FinalProvenanceData
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
    {exactCarrier_provenance : ∀ target,
      exactShading.carrier target ⊆
        pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
          halfHeight normalization translation ''
          sourceShading.carrier (image.sourceParent target)}
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
    (ed : PureWZ2Proposition64PaperEDCleanupData cleanup.finalShading K) where
  sourceParent : Fin ed.subfamily.family.card → Fin sourceFamily.card
  sourceParent_eq : sourceParent = fun target =>
    image.sourceParent (cleanup.sourceParent (ed.sourceParent target))
  axis_provenance : ∀ target,
    tubeAxisLine (ed.subfamily.family.tube target) =
      pureWZ2Proposition64IsotropicMap cleanup.popular.center scale ''
        (pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
          halfHeight normalization translation ''
          tubeAxisLine (sourceFamily.tube (sourceParent target)))
  carrier_provenance : ∀ target,
    ed.finalShading.carrier target ⊆
      Metric.cthickening (6 * finalDelta)
        (pureWZ2Proposition64IsotropicMap cleanup.popular.center scale ''
          (pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
            halfHeight normalization translation ''
            sourceShading.carrier (sourceParent target)))

/-- Compose the ED, positive-mass, isotropic, exact-image, and original-source
indices.  The carrier estimate uses genuine same-grid witnesses at both
rediscretization stages. -/
theorem pureWZ2Proposition64_finalProvenance
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
    {exactCarrier_provenance : ∀ target,
      exactShading.carrier target ⊆
        pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
          halfHeight normalization translation ''
          sourceShading.carrier (image.sourceParent target)}
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
    (ed : PureWZ2Proposition64PaperEDCleanupData cleanup.finalShading K) :
    Nonempty (PureWZ2Proposition64FinalProvenanceData
      (normalized := normalized) (image := image)
      (exactCarrier_provenance := exactCarrier_provenance)
      (cleanup := cleanup) ed) := by
  let parent : Fin ed.subfamily.family.card → Fin sourceFamily.card :=
    fun target => image.sourceParent (cleanup.sourceParent (ed.sourceParent target))
  refine ⟨{
    sourceParent := parent
    sourceParent_eq := rfl
    axis_provenance := ?_
    carrier_provenance := ?_ }⟩
  · intro target
    rw [ed.tube_provenance target, cleanup.axis_provenance]
    apply congrArg (fun line : Set Point3 =>
      pureWZ2Proposition64IsotropicMap cleanup.popular.center scale '' line)
    rw [image.axis_provenance]
  · intro target point hpoint
    have hlocalPoint : point ∈
        cleanup.finalShading.carrier (ed.sourceParent target) := by
      rw [ed.sourceParent_eq]
      simpa [ed.shading_eq, restrictPaperShading] using hpoint
    change point ∈ wz1PaperCubicalSaturation finalDelta
        (pureWZ2Proposition64IsotropicMap cleanup.popular.center scale ''
          cleanup.popular.restricted.carrier (ed.sourceParent target)) at hlocalPoint
    rcases hlocalPoint with
      ⟨isotropicPoint, hisotropicPoint, hfinalCell⟩
    rcases hisotropicPoint with ⟨exactPoint, hexactPoint, rfl⟩
    have hfinalDistance : dist point
        (pureWZ2Proposition64IsotropicMap cleanup.popular.center scale exactPoint) ≤
          2 * finalDelta := by
      exact le_of_lt <|
        wz1_paper_grid_cube_diameter_lt_two_rho hfinalDelta
          (cell := wz1PaperGridIndex finalDelta point)
          ((mem_wz1PaperGridCube _ _ _).mpr rfl)
          ((mem_wz1PaperGridCube _ _ _).mpr hfinalCell.symm)
    have hexactInImage : exactPoint ∈
        exactShading.carrier (cleanup.sourceParent (ed.sourceParent target)) := by
      rw [cleanup.sourceParent_eq]
      exact cleanup.popular.restricted_subshading _ hexactPoint
    rcases exactCarrier_provenance _ hexactInImage with
      ⟨sourcePoint, hsourcePoint, hexactEq⟩
    apply Metric.mem_cthickening_of_dist_le point
      (pureWZ2Proposition64IsotropicMap cleanup.popular.center scale exactPoint)
      (6 * finalDelta) _
    · refine ⟨exactPoint, ?_, rfl⟩
      refine ⟨sourcePoint, ?_, hexactEq⟩
      simpa [parent] using hsourcePoint
    · exact hfinalDistance.trans (by linarith [hfinalDelta])

end Kakeya.Assouad

end
