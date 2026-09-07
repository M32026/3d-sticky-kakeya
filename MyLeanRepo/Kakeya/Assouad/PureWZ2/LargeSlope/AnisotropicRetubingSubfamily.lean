import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactImage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GrainSubfamilyRestriction

/-!
# Restrict an exact triangular retubing to a source subfamily

The final simultaneous CWA regularization selects source indices.  Exact
affine-image geometry must be restricted by those same indices rather than
reconstructed on an unrelated target family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The canonical triangular target family of a source subfamily is the
corresponding subfamily of the original triangular target family. -/
@[simp] theorem anisotropicPaperTargetFamily_subfamily_tube
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (selected : Kakeya.Streamlined.TubeSubfamily sourceFamily)
    (g : SlopeFunction) (center : Point3) (hcd : c < d) (hm : 0 < m)
    (index : Fin selected.family.card) :
    (anisotropicPaperTargetFamily selected.family g c d m center
        targetDelta hcd hm).tube index =
      (anisotropicPaperTargetFamily sourceFamily g c d m center
        targetDelta hcd hm).tube (selected.embedding index) := by
  change anisotropicPaperTargetTube g c d m center targetDelta hcd hm
      (selected.family.tube index) =
    anisotropicPaperTargetTube g c d m center targetDelta hcd hm
      (sourceFamily.tube (selected.embedding index))
  rw [selected.tube_eq]

/-- Restrict all fields of an exact triangular retubing along one genuine
source tube subfamily.  The Jacobian mass estimate is reproved indexwise, so
no global mass claim is inherited across the restriction. -/
def PureWZ2AnisotropicPaperRetubingData.subfamily
    {sourceDelta targetDelta c d m : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    (raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm)
    (selected : Kakeya.Streamlined.TubeSubfamily sourceFamily) :
    PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) selected.family
      (restrictPaperShading selected sourceShading) g center hcd hm := by
  let targetFamily := anisotropicPaperTargetFamily selected.family
    g c d m center targetDelta hcd hm
  let targetShading : WZ1PaperTubeShading targetFamily :=
    { carrier := fun index => raw.shading.carrier (selected.embedding index)
      measurable_carrier := fun index =>
        raw.shading.measurable_carrier (selected.embedding index)
      subset_body := fun index point hpoint => by
        have h := raw.shading.subset_body (selected.embedding index) hpoint
        change point ∈ wz1PaperTubeCarrier (targetFamily.tube index)
        rw [anisotropicPaperTargetFamily_subfamily_tube
          selected g center hcd hm index]
        exact h }
  refine
    { center_height := raw.center_height
      shading := targetShading
      line_class := ?_
      midpoint_local := ?_
      midpoint_height_zero := ?_
      direction_two_pos := ?_
      cubical := ?_
      axis := ?_
      shading_carrier := ?_
      exact_image_subset := ?_
      union_image_subset := ?_
      mass_lower := ?_ }
  · intro index
    simpa only [targetFamily,
      anisotropicPaperTargetFamily_subfamily_tube selected g center hcd hm
        index] using raw.line_class (selected.embedding index)
  · intro index
    simpa only [targetFamily,
      anisotropicPaperTargetFamily_subfamily_tube selected g center hcd hm
        index] using raw.midpoint_local (selected.embedding index)
  · intro index
    simpa only [targetFamily,
      anisotropicPaperTargetFamily_subfamily_tube selected g center hcd hm
        index] using raw.midpoint_height_zero (selected.embedding index)
  · intro index
    simpa only [targetFamily,
      anisotropicPaperTargetFamily_subfamily_tube selected g center hcd hm
        index] using raw.direction_two_pos (selected.embedding index)
  · intro index point hpoint
    exact raw.cubical (selected.embedding index) point hpoint
  · intro index
    rw [show (targetFamily.tube index) =
        (anisotropicPaperTargetFamily sourceFamily g c d m center
          targetDelta hcd hm).tube (selected.embedding index) by
      exact anisotropicPaperTargetFamily_subfamily_tube
        selected g center hcd hm index]
    rw [raw.axis]
    rw [selected.tube_eq]
  · intro index
    change raw.shading.carrier (selected.embedding index) = _
    rw [raw.shading_carrier]
    rfl
  · intro index point hpoint
    change point ∈ raw.shading.carrier (selected.embedding index)
    apply raw.exact_image_subset (selected.embedding index)
    exact hpoint
  · rintro target ⟨source, ⟨index, hsource⟩, rfl⟩
    exact ⟨index, raw.exact_image_subset (selected.embedding index)
      ⟨source, hsource, rfl⟩⟩
  · change ENNReal.ofReal m *
        (∑ index : Fin selected.family.card,
          volume (sourceShading.carrier (selected.embedding index))) ≤
      ∑ index : Fin selected.family.card,
        volume (raw.shading.carrier (selected.embedding index))
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    have himage :
        volume
            (anisotropicCenteredRescalingMap g c d m center ''
              sourceShading.carrier (selected.embedding index)) ≤
          volume (raw.shading.carrier (selected.embedding index)) :=
      measure_mono (raw.exact_image_subset (selected.embedding index))
    rw [volume_image_anisotropicCenteredRescalingMap
      g hcd hm center _
        (sourceShading.measurable_carrier (selected.embedding index))]
      at himage
    exact himage

end Kakeya.Assouad

end
