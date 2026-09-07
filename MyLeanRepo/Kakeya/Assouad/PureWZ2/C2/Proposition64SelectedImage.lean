import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TubeTransport
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Selected exact images in Proposition 6.4

Lemma 3.5 first restricts the source tubes to one common horizontal window.
This module reindexes that selected source subfamily through the exact
Proposition 6.4 affine map while retaining provenance in the original source
family.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

/-- Exact-image rediscretization of a selected source subfamily.  The returned
`sourceParent` lands in the original source family, rather than merely in the
intermediate selected family. -/
noncomputable def pureWZ2Proposition64SelectedActualImageRediscretization
    {sourceDelta targetDelta : ℝ}
    (g : SlopeFunction)
    (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation : Point3)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (htranslationHeight : translation 2 = 0)
    (htargetDelta : 0 < targetDelta)
    (hnormalized :
      (pureWZ2Proposition64Slope g slabCenter anchorHeight halfHeight
        normalization).IsNormalized)
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (selected : Finset (Fin sourceFamily.card)) :
    PureWZ2Proposition64ActualImageRediscretizationData
      (targetDelta := targetDelta) g slabCenter anchorHeight halfHeight
        normalization translation hhalfHeight hnormalization
        sourceFamily sourceShading := by
  let selectedSource :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset sourceFamily selected
  let selectedShading : WZ1PaperTubeShading selectedSource.family :=
    restrictPaperShading selectedSource sourceShading
  let selectedImage :=
    pureWZ2Proposition64ActualImageRediscretization g slabCenter anchorHeight
      halfHeight normalization translation hhalfHeight hnormalization
      htranslationHeight htargetDelta hnormalized selectedSource.family
      selectedShading
  exact
    { translation_height := htranslationHeight
      family := selectedImage.family
      shading := selectedImage.shading
      sourceParent := fun target =>
        selectedSource.embedding (selectedImage.sourceParent target)
      axis_provenance := by
        intro target
        rw [selectedImage.axis_provenance target]
        apply congrArg (fun sourceLine : Set Point3 =>
          pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation '' sourceLine)
        rw [selectedSource.tube_eq]
      shading_near_source_image := by
        intro target
        simpa [selectedShading, restrictPaperShading] using
          selectedImage.shading_near_source_image target
      cubical := selectedImage.cubical
      cell_meets_source_image := by
        intro target point hpoint
        simpa [selectedShading, restrictPaperShading] using
          selectedImage.cell_meets_source_image target point hpoint
      projection_close := by
        intro z hz value hvalue
        rcases selectedImage.projection_close z hz value hvalue with
          ⟨sourceValue, hsourceValue, hclose⟩
        refine ⟨sourceValue, ?_, hclose⟩
        rcases hsourceValue with
          ⟨imagePoint, ⟨⟨sourcePoint, hsourcePoint, rfl⟩, hheight⟩, rfl⟩
        rcases hsourcePoint with ⟨sourceIndex, hsourcePoint⟩
        refine ⟨pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation sourcePoint, ?_, rfl⟩
        exact ⟨⟨sourcePoint,
          ⟨selectedSource.embedding sourceIndex,
            hsourcePoint⟩, rfl⟩, hheight⟩ }

end Kakeya.Assouad

end
