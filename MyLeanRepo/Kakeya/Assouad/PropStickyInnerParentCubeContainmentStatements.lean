import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Coarse-cell containment from the actual paper parent

This is the literal geometry used while constructing the coarse shading in
the proof of WZ Proposition 3.2 and its WZ2 analogue:

> “if `Q` intersects `(1 / (2 n)) T_tilde`, then `Q` is contained in
> `T_tilde`.”

The current partitioning-cover API stores the equivalent quantitative
ingredients rather than an explicit same-axis inner tube.  A point in the
fine paper carrier lies within `18 * delta` of the fine axis at the same
height; the paper line-cover relation places that axis within `3 * rho` of
the coarse axis; and a side-`rho` cube has diameter less than `2 * rho`.
Thus `18 * delta ≤ rho` places the whole cube in the `6 * rho` neighborhood
of the coarse axis.  Crop-box containment is supplied separately because it
comes from the fact that the cube is an active paper cell.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PropStickyCoarseCellContainmentStatement : Prop :=
  ∀ {delta rho : ℝ},
    0 < delta →
    0 < rho →
    18 * delta ≤ rho →
    ∀ (fineTube : Kakeya.DeltaTube delta)
      (coarseTube : Kakeya.DeltaTube rho),
      WZ1PaperTubeInLineClass fineTube →
      WZ1PaperTubeInLineClass coarseTube →
      WZ1PaperTubeCovers fineTube coarseTube →
      ∀ coarseCell : ℤ × ℤ × ℤ,
        (wz1PaperGridCube rho coarseCell ∩
          wz1PaperTubeCarrier fineTube).Nonempty →
        wz1PaperGridCube rho coarseCell ⊆
          Kakeya.Streamlined.axisBox 2 2 2 →
        wz1PaperGridCube rho coarseCell ⊆
          wz1PaperTubeCarrier coarseTube

end Kakeya.Assouad

end
