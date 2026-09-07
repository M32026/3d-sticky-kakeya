import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCellAreaUniformityStatement
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Thickening one occupied projected-fiber grid cell

At a selected grid level, all retained terminal centers in one occupied cell
are within the coarse mesh of one another.  Every point in a terminal atom is
within the terminal mesh of its center.  If both meshes are controlled by
`rho`, the entire retained cell band and its `rho`-thickening lie in one
explicit planar ball.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
One occupied retained cell has an explicit `O(base^2 * rho^2)` thickening
area.

The terminal atom mesh is allowed to be one factor `base` larger than
`rho`; this is needed at the extra atomic OS level when `rho = delta`.
-/
def ProjectedFiberOSCellThickeningStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ f : SlopeFunction,
          ∀ {threshold : ENNReal},
            ∀ {levelCount : ℕ},
              ∀ bandData :
                  ProjectedFiberBandData
                    Y f threshold levelCount,
                ∀ base levels indexBound : ℕ,
                  3 ≤ base →
                    ∀ atomized :
                        ProjectedFiberGridAtomizationData
                          Y f bandData base levels indexBound,
                      ∀ uniform :
                          ProjectedFiberOSUniformData
                            Y f bandData
                            base levels indexBound atomized,
                        ∀ level : ℕ, level ≤ levels + 1 →
                          ∀ rho : ℝ, 0 < rho →
                            ((base ^ level : ℝ)⁻¹) ≤ rho →
                            ((base ^ levels : ℝ)⁻¹) <
                              (base : ℝ) * rho →
                            ∀ cell ∈
                                planarGridPartition
                                  base level atomized.centers,
                              (uniform.centers ∩ cell).Nonempty →
                                ∃ center ∈ uniform.centers ∩ cell,
                                  projectedFiberOSCellBand
                                      Y f bandData base levels
                                      uniform.centers cell ⊆
                                    Metric.closedBall center
                                      (((2 * base + 2 : ℕ) : ℝ) * rho) ∧
                                  volume
                                      (Metric.cthickening rho
                                        (projectedFiberOSCellBand
                                          Y f bandData base levels
                                          uniform.centers cell)) ≤
                                    ENNReal.ofReal
                                        ((((2 * base + 3 : ℕ) : ℝ) *
                                          rho) ^ 2 * Real.pi)

end Kakeya.Assouad
