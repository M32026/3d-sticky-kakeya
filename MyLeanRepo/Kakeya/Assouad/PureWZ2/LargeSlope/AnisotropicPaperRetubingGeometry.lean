import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicPaperTargetTube
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicAlignedScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Paper-carrier retubing for the exact Proposition 6.5 map

This is the carrier-level step hidden in the phrase "containing tubes" and
"induced cube shadings" in the paper.  The source is a cropped full-line
paper carrier, not the ordinary unit-segment carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

theorem anisotropicCenteredRescalingMap_image_paperPoint_dist_axis
    (g : SlopeFunction) {c d m sourceDelta S : ℝ}
    (hg : g.IsNormalized) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (center : Point3)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceDelta : 0 < sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    {point : Point3} (hpoint : point ∈ wz1PaperTubeCarrier source) :
    dist (anisotropicCenteredRescalingMap g c d m center point)
        (anisotropicCenteredRescalingMap g c d m center
          (wz1PaperAxisPointAtHeight source (point 2))) ≤
      S * (18 * sourceDelta) := by
  calc
    dist (anisotropicCenteredRescalingMap g c d m center point)
        (anisotropicCenteredRescalingMap g c d m center
          (wz1PaperAxisPointAtHeight source (point 2))) ≤
      S * dist point (wz1PaperAxisPointAtHeight source (point 2)) :=
        anisotropicCenteredRescalingMap_dist_le_height
          g hg hcd hdc hm hmOne hsub hS center point _
    _ ≤ S * (18 * sourceDelta) := by
      apply mul_le_mul_of_nonneg_left
      · exact wz2_paper_carrier_same_height_dist_18delta
          hsourceDelta source hsource hpoint
      · rw [hS]
        positivity

/-- Cubical saturation of the exact image stays inside one target paper tube
provided the target radius pays for the transported source thickness and one
target grid-cube diameter. -/
theorem anisotropicPaperCubicalSaturation_subset_targetCarrier
    (g : SlopeFunction) {c d m sourceDelta targetDelta S : ℝ}
    (hg : g.IsNormalized) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (hradius : S * (18 * sourceDelta) + 2 * targetDelta ≤
      6 * targetDelta)
    (center : Point3)
    (source : Kakeya.DeltaTube sourceDelta)
    (hsource : WZ1PaperTubeInLineClass source)
    (sourceSet : Set Point3)
    (hsourceSet : sourceSet ⊆ wz1PaperTubeCarrier source) :
    wz1PaperCubicalSaturation targetDelta
        (anisotropicCenteredRescalingMap g c d m center '' sourceSet) ⊆
      Metric.cthickening (6 * targetDelta)
        (tubeAxisLine
          (anisotropicPaperTargetTube
            g c d m center targetDelta hcd hm source)) := by
  intro targetPoint htargetPoint
  rcases htargetPoint with
    ⟨imagePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, hgrid⟩
  have hsameCell : dist targetPoint
      (anisotropicCenteredRescalingMap g c d m center sourcePoint) <
        2 * targetDelta := by
    apply wz1_paper_grid_cube_diameter_lt_two_rho htargetDelta
      (cell := wz1PaperGridIndex targetDelta targetPoint)
    · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
    · exact (mem_wz1PaperGridCube _ _ _).mpr hgrid.symm
  let sourceAxisPoint := wz1PaperAxisPointAtHeight source (sourcePoint 2)
  let targetAxisPoint :=
    anisotropicCenteredRescalingMap g c d m center sourceAxisPoint
  have htargetAxis : targetAxisPoint ∈ tubeAxisLine
      (anisotropicPaperTargetTube
        g c d m center targetDelta hcd hm source) := by
    rw [anisotropicPaperTargetTube_axis g center hcd hm source hsource]
    exact ⟨sourceAxisPoint,
      wz1PaperAxisPointAtHeight_mem_axis source _, rfl⟩
  have himageAxis : dist
      (anisotropicCenteredRescalingMap g c d m center sourcePoint)
      targetAxisPoint ≤ S * (18 * sourceDelta) := by
    exact anisotropicCenteredRescalingMap_image_paperPoint_dist_axis
      g hg hcd hdc hm hmOne hsub hS center source hsourceDelta hsource
        (hsourceSet hsourcePoint)
  have htargetDistance : dist targetPoint targetAxisPoint ≤
      6 * targetDelta := by
    calc
      dist targetPoint targetAxisPoint ≤
          dist targetPoint
              (anisotropicCenteredRescalingMap g c d m center sourcePoint) +
            dist (anisotropicCenteredRescalingMap g c d m center sourcePoint)
              targetAxisPoint := dist_triangle _ _ _
      _ ≤ 2 * targetDelta + S * (18 * sourceDelta) := by
        exact add_le_add hsameCell.le himageAxis
      _ ≤ 6 * targetDelta := by
        linarith
  exact Metric.mem_cthickening_of_dist_le targetPoint targetAxisPoint
    (6 * targetDelta) _ htargetAxis htargetDistance

/-- For a reciprocal-grid target scale, cubical saturation of an image set
contained in the half-open unit coordinate box remains in the paper crop. -/
theorem anisotropicPaperCubicalSaturation_subset_axisBox
    {targetDelta : ℝ} {count : ℕ}
    (htargetDelta : 0 < targetDelta) (hcount : 0 < count)
    (halign : targetDelta * (count : ℝ) = 1)
    (sourceSet : Set Point3)
    (hsourceWindow : ∀ point ∈ sourceSet,
      ∀ coordinate : Fin 3, -1 ≤ point coordinate ∧ point coordinate < 1) :
    wz1PaperCubicalSaturation targetDelta sourceSet ⊆
      Kakeya.Streamlined.axisBox 2 2 2 := by
  intro targetPoint htargetPoint
  rcases htargetPoint with
    ⟨sourcePoint, hsourcePoint, hgrid⟩
  have hsourceCell : sourcePoint ∈
      wz1PaperGridCube targetDelta
        (wz1PaperGridIndex targetDelta targetPoint) :=
    (mem_wz1PaperGridCube _ _ _).mpr hgrid.symm
  have htargetCell : targetPoint ∈
      wz1PaperGridCube targetDelta
        (wz1PaperGridIndex targetDelta targetPoint) :=
    (mem_wz1PaperGridCube _ _ _).mpr rfl
  simp only [Kakeya.Streamlined.axisBox]
  norm_num
  exact ⟨aligned_gridCube_coordinate_mem_unit htargetDelta hcount halign 0
      hsourceCell htargetCell (hsourceWindow sourcePoint hsourcePoint 0),
    aligned_gridCube_coordinate_mem_unit htargetDelta hcount halign 1
      hsourceCell htargetCell (hsourceWindow sourcePoint hsourcePoint 1),
    aligned_gridCube_coordinate_mem_unit htargetDelta hcount halign 2
      hsourceCell htargetCell (hsourceWindow sourcePoint hsourcePoint 2)⟩

end Kakeya.Assouad

end
