import MyLeanRepo.Kakeya.Assouad.WZ1.DistinguishedTubeSlopeExtension
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPartition
import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling
import Mathlib.Tactic

/-!
# Height control for a Property-(P) source witness

The formal Property-(P) witness lies in the same three-dimensional source
grid cell as the source point attached to a target shaded point.  This module
turns that literal statement into the approximate anchored-height control
used by the global normal-ratio slope.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The third coordinate of the anchored image is exactly the distinguished
tube height used by the slope construction. -/
lemma anchored_rescaling_coord_two_eq_distinguished_height
    {sourceDelta rho : ℝ} (hrho : 0 < rho)
    (anchor : Kakeya.DeltaTube sourceDelta) (point : Point3) :
    (wz1AnchoredUnitRescalingMap anchor rho hrho point) (2 : Fin 3) =
      distinguishedTubeHeight anchor point := by
  exact unitRescalingMap_coord2
    (anchor.base + (1 / 2 : ℝ) • anchor.direction)
    anchor.direction anchor.direction_unit
    (100 * rho) (by positivity) point

/-- Distinguished-tube height is a norm-one linear coordinate. -/
lemma distinguishedTubeHeight_sub_le_dist
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (first second : Point3) :
    |distinguishedTubeHeight tube first -
        distinguishedTubeHeight tube second| ≤
      dist first second := by
  have halgebra :
      distinguishedTubeHeight tube first -
          distinguishedTubeHeight tube second =
        inner ℝ (first - second) tube.direction := by
    simp only [distinguishedTubeHeight]
    rw [← inner_sub_left]
    congr 1
    abel
  rw [halgebra]
  calc
    |inner ℝ (first - second) tube.direction|
        ≤ ‖first - second‖ * ‖tube.direction‖ :=
      abs_real_inner_le_norm (first - second) tube.direction
    _ = ‖first - second‖ := by
      rw [tube.direction_unit, mul_one]
    _ = dist first second := by rw [dist_eq_norm]

/-- Points in one Property-(P) source cell have anchored heights differing by
at most the cell diameter. -/
lemma same_rho_grid_cell_distinguished_height
    {delta rho : ℝ} (hrho : 0 < rho)
    (tube : Kakeya.DeltaTube delta)
    {first second : Point3}
    (hcell : rhoGridIndex rho first = rhoGridIndex rho second) :
    |distinguishedTubeHeight tube first -
        distinguishedTubeHeight tube second| ≤
      2 * rho := by
  exact (distinguishedTubeHeight_sub_le_dist tube first second).trans
    (grid_cell_diameter hrho hcell)

/--
If a target point is within `distanceError` of the anchored image of a source
point, and Property (P) supplies a distinguished-tube point in the same source
grid cell, then their target/source anchored heights differ by at most
`distanceError + 2 * rho`.
-/
lemma property_p_witness_height_error
    {sourceDelta rho distanceError : ℝ}
    (hrho : 0 < rho)
    (anchor : Kakeya.DeltaTube sourceDelta)
    {targetPoint sourcePoint distinguishedPoint : Point3}
    (hdistance :
      dist targetPoint
        (wz1AnchoredUnitRescalingMap
          anchor rho hrho sourcePoint) ≤ distanceError)
    (hcell :
      rhoGridIndex rho sourcePoint =
        rhoGridIndex rho distinguishedPoint) :
    |targetPoint (2 : Fin 3) -
        distinguishedTubeHeight anchor distinguishedPoint| ≤
      distanceError + 2 * rho := by
  let imagePoint :=
    wz1AnchoredUnitRescalingMap anchor rho hrho sourcePoint
  have htargetImage :
      |targetPoint (2 : Fin 3) - imagePoint (2 : Fin 3)| ≤
        distanceError := by
    exact (PiLp.dist_apply_le targetPoint imagePoint (2 : Fin 3)).trans
      hdistance
  have himageHeight :
      imagePoint (2 : Fin 3) =
        distinguishedTubeHeight anchor sourcePoint := by
    exact anchored_rescaling_coord_two_eq_distinguished_height
      hrho anchor sourcePoint
  have hsourceDistinguished :
      |distinguishedTubeHeight anchor sourcePoint -
          distinguishedTubeHeight anchor distinguishedPoint| ≤
        2 * rho :=
    same_rho_grid_cell_distinguished_height hrho anchor hcell
  calc
    |targetPoint (2 : Fin 3) -
        distinguishedTubeHeight anchor distinguishedPoint|
        = |(targetPoint (2 : Fin 3) - imagePoint (2 : Fin 3)) +
            (distinguishedTubeHeight anchor sourcePoint -
              distinguishedTubeHeight anchor distinguishedPoint)| := by
          rw [himageHeight]
          congr 1
          ring
    _ ≤ |targetPoint (2 : Fin 3) - imagePoint (2 : Fin 3)| +
          |distinguishedTubeHeight anchor sourcePoint -
            distinguishedTubeHeight anchor distinguishedPoint| :=
      abs_add_le _ _
    _ ≤ distanceError + 2 * rho :=
      add_le_add htargetImage hsourceDistinguished

end Kakeya.Assouad

end
